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
PROHIBITED = re.compile(r'(?m)^\s*(#eval\b|run_cmd\b|#guard_msgs\b|syntax\b|macro\b|elab\b)')


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
        if PROHIBITED.search(source):
            raise ValueError(f'{fixture}: executable diagnostic imitation is forbidden')
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
