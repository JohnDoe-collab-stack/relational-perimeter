#!/usr/bin/env python3
"""Check frozen Lean error sites, shared by the Bash and PowerShell gates.

Only Lean JSON error diagnostics at the recorded file/line/column count.
Unrelated errors, warnings, printed output and process failures never count.
This is fixture validation, not a semantic proof or a general secure compiler.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
CATEGORIES = {'privacy', 'dependent-type', 'semantic-type', 'termination'}
ERROR_CLASSES = {
    'privacy': ('Unknown constant ',),
    'dependent-type': ('Application type mismatch', 'Type mismatch', 'Tactic `rfl` failed', 'Not a definitional equality'),
    'semantic-type': ('Type mismatch', 'Tactic `rfl` failed', 'Not a definitional equality'),
    'termination': ('fail to show termination for',),
}
PROHIBITED = re.compile(
    r'(?<![\w\u00ab\u00bb])(?:run_cmd|run_elab|run_tac|initialize|builtin_initialize|'
    r'syntax|declare_syntax_cat|macro|macro_rules|elab|elab_rules|notation|'
    r'logError|logErrorAt|throwError|throwErrorAt)\b')
TACTIC_DIAGNOSTIC = re.compile(r'(?<![\w.])(?:fail|fail_if_success|trace|trace_state|dbg_trace)\b')
HASH_COMMAND = re.compile(r'#[A-Za-z_][A-Za-z_0-9]*')
RAW_STRING = re.compile(r'(?<![\w\x27])r(#+)?"')
INTERPOLATED_STRING = re.compile(r'(?<!\w)s!')
CHAR_LITERAL = re.compile(r"'(?:[^\\'\r\n]|\\[\\\"'rnt]|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4})'")
IDENTIFIER_SUFFIX = re.compile(r"[\w'!?]")


def fixture_code(source: str) -> str:
    """Mask comments/literals without changing positions; fail on unclosed ones.

    This is a restricted fixture-source policy, not a parser for arbitrary Lean.
    Nested block comments, line comments, quoted identifiers, ordinary/raw
    strings and character literals are handled explicitly. Interpolated
    strings are outside this policy: their holes could contain executable
    elaboration syntax. Unsupported character syntax fails closed.
    """
    result = list(source)
    index = 0
    last_literal_end = -1

    def mask(start: int, end: int) -> None:
        for offset in range(start, end):
            if source[offset] not in '\r\n':
                result[offset] = ' '

    while index < len(source):
        start = index
        if source.startswith('--', index):
            index += 2
            while index < len(source) and source[index] not in '\r\n':
                index += 1
        elif source.startswith('/-', index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith('/-', index):
                    depth += 1
                    index += 2
                elif source.startswith('-/', index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError('unterminated fixture block comment')
        elif source.startswith('s!"', index):
            raise ValueError('interpolated strings are not permitted in fixtures')
        elif source[index] == "'" and (
                index == 0 or index == last_literal_end or
                IDENTIFIER_SUFFIX.fullmatch(source[index - 1]) is None):
            # An identifier suffix (e.g. head') is not a character opener.
            # Consume exactly one scalar/escape and its closing apostrophe;
            # do not search for a later quote across executable source.
            literal = CHAR_LITERAL.match(source, index)
            if literal is None:
                raise ValueError('unsupported or unterminated fixture character literal')
            index = literal.end()
            last_literal_end = index
        elif source[index] == '\u00ab':
            end = source.find('\u00bb', index + 1)
            if end == -1:
                raise ValueError('unterminated fixture quoted identifier')
            index = end + 1
        elif (raw := RAW_STRING.match(source, index)) is not None:
            close = '"' + (raw.group(1) or '')
            end = source.find(close, index + len(raw.group(0)))
            if end == -1:
                raise ValueError('unterminated fixture raw string')
            index = end + len(close)
        elif source[index] == '"':
            index += 1
            while index < len(source):
                if source[index] == '\\':
                    if index + 1 == len(source):
                        raise ValueError('unterminated fixture string escape')
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ValueError('unterminated fixture string')
        else:
            index += 1
            continue
        mask(start, index)
    return ''.join(result)


def validate_source(source: str, fixture: str) -> None:
    code = fixture_code(source)
    # Inspect tokens everywhere, including after comments, attributes/modifiers
    # and on a line already containing a command. Only the two diagnostic
    # commands used by the reviewed fixtures are allowed.
    if (PROHIBITED.search(code) or TACTIC_DIAGNOSTIC.search(code) or INTERPOLATED_STRING.search(code) or
            any(match.group() not in {'#check', '#print'} for match in HASH_COMMAND.finditer(code))):
        raise ValueError(f'{fixture}: executable diagnostic imitation is forbidden')


def errors(output: str, fixture: str) -> list[dict]:
    records = []
    for line in output.splitlines():
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except (ValueError, TypeError) as error:
            raise ValueError(f'{fixture}: non-diagnostic output') from error
        if not isinstance(record, dict) or record.get('severity') not in ('error', 'warning', 'information'):
            raise ValueError(f'{fixture}: malformed Lean diagnostic')
        if record['severity'] == 'warning':
            raise ValueError(f'{fixture}: unexpected warning')
        if record['severity'] == 'error':
            records.append(record)
    return records


def matches(record: dict, fixture: str, line: int, column: int, needle: str) -> bool:
    path = str(record.get('fileName', '')).replace('\\', '/')
    if Path(path).is_absolute():
        try:
            path = Path(path).resolve().relative_to(ROOT.resolve()).as_posix()
        except ValueError:
            return False
    return (path.removeprefix('./') == fixture and record.get('pos') == {'line': line, 'column': column}
            and needle in record.get('data', '') and record.get('isSilent') is False)


def validate_status(status: int, fixture: str) -> None:
    if status == 0:
        raise ValueError(f'{fixture}: unexpectedly compiled')
    if status != 1:
        raise ValueError(f'{fixture}: interrupted or timed out ({status})')


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--inventory', action='store_true', help='read-only migration: print actual error sites')
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    entries = {}
    for row in (ROOT / 'scripts/expected-failures.tsv').read_text(encoding='utf-8').splitlines():
        if not row.strip() or row.startswith('#'):
            continue
        parts = row.split('\t')
        if args.inventory and len(parts) == 3:
            fixture, category, needle = parts
            sites = None
        else:
            if len(parts) != 5 or not parts[4] or not parts[2].isdigit() or not parts[3].isdigit():
                raise ValueError('invalid expected-failure inventory row')
            fixture, category, line, column, needle = parts
            sites = (int(line), int(column), needle)
        if not fixture.startswith('Tests/ExpectedFailure/') or not fixture.endswith('.lean.fail') or '..' in fixture:
            raise ValueError('invalid fixture path: ' + fixture)
        if category not in CATEGORIES:
            raise ValueError('unknown fixture category: ' + category)
        if not (ROOT / fixture).is_file():
            raise ValueError('orphan fixture entry: ' + fixture)
        if fixture in entries:
            old_category, previous, _ = entries[fixture]
            if old_category != category or sites is None or sites in previous:
                raise ValueError('duplicate fixture: ' + fixture)
            previous.append(sites)
        else:
            entries[fixture] = (category, [] if sites is None else [sites], needle)
    actual = {file.relative_to(ROOT).as_posix() for file in (ROOT / 'Tests/ExpectedFailure').rglob('*.lean.fail')}
    if not entries:
        raise ValueError('empty expected-failure inventory')
    if actual != set(entries):
        raise ValueError('uninventoried fixture: ' + ', '.join(sorted(actual - set(entries))))
    for fixture, (category, sites, old_needle) in entries.items():
        source = (ROOT / fixture).read_text(encoding='utf-8')
        validate_source(source, fixture)
        try:
            run = subprocess.run([args.lake, 'env', 'lean', '--json', fixture], cwd=ROOT,
                                 capture_output=True, text=True, encoding='utf-8', timeout=90)
        except subprocess.TimeoutExpired as error:
            raise ValueError(f'{fixture}: interrupted or timed out') from error
        validate_status(run.returncode, fixture)
        records = errors(run.stdout + run.stderr, fixture)
        if args.inventory:
            for record in records:
                if old_needle not in record['data']:
                    print(f'{fixture}: additional error for review: {record["data"]}', file=sys.stderr)
                needle = old_needle if old_needle in record['data'] else record['data'].splitlines()[0]
                print('\t'.join((fixture, category, str(record['pos']['line']), str(record['pos']['column']), needle)))
            continue
        if any(not record.get('data', '').startswith(ERROR_CLASSES[category]) for record in records):
            raise ValueError(f'{fixture}: failed for an unexpected reason (error class)')
        if len(records) != len(sites):
            raise ValueError(f'{fixture}: failed for an unexpected reason (error count {len(records)} != {len(sites)})')
        pending = list(records)
        for line, column, needle in sites:
            found = [i for i, record in enumerate(pending) if matches(record, fixture, line, column, needle)]
            if len(found) != 1:
                raise ValueError(f'{fixture}: failed for an unexpected reason (diagnostic/site mismatch)')
            pending.pop(found[0])
        print(f'EXPECTED_FAILURE_OK\t{category}\t{fixture}')
    if not args.inventory:
        print(f'Verified expected failures: {len(entries)} fixtures, exact Lean diagnostics and sites, no additional errors.')


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    sys.stderr.reconfigure(encoding='utf-8')
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'EXPECTED_FAILURE_FAILED: {error}', file=sys.stderr)
        sys.exit(1)
