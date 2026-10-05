#!/usr/bin/env python3
"""Regression checks of fixture gates, not scientific experiments.

Real Lean checks run in disposable directories sharing built .lake artifacts.
Pure status/parser checks separately test process failure and JSON spoofing.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch


def lexical_matrix(policy) -> dict[str, int]:
    """Finite lexer regressions; neither a Lean parser nor a security proof."""
    characters = (
        """'"'""", "'a'", "'\u00ab'", "'\U0001f600'",
        r"""'\"'""", r"""'\''""", r"""'\\'""",
        r"""'\r'""", r"""'\n'""", r"""'\t'""",
        r"""'\x22'""", r"""'\u0022'""",
    )
    contexts = (
        ("", ""),
        ("/- outer /- nested -/ -/\n", "\n/- tail -/"),
        ("-- ignored run_cmd\n", "\n-- ignored logError"),
        ('def text := "run_cmd -- /-"\n', '\ndef textAfter := "logError"'),
        ('def rawText := r##"run_cmd -- /-"##\n', '\ndef rawAfter := r#"logError"#'),
        ("def head' := true\n", "\ndef tail'' := head'"),
        ("namespace Test\n", "\nend Test"),
        ("def \u00ablogError\u00bb := true\n", "\ndef \u00abrun_cmd\u00bb := false"),
    )
    positive = negative = 0
    for character in characters:
        for before, after in contexts:
            for newline in ("\n", "\r\n", "\r"):
                prefix = before + "def quoteBefore : Char := " + character + "\n"
                suffix = "\ndef quoteAfter : Char := " + character + after + "\n"
                source = (prefix + suffix).replace("\n", newline)
                policy.validate_source(source, 'lexical-matrix-positive')
                masked = policy.fixture_code(source)
                if len(masked) != len(source) or \
                        [i for i, c in enumerate(masked) if c in "\r\n"] != \
                        [i for i, c in enumerate(source) if c in "\r\n"]:
                    raise SystemExit('Lexical matrix masking changed source positions')
                positive += 1
                for command in (
                        'run_cmd logError "Application type mismatch: applyStage fresh"',
                        'example : True := by run_tac Lean.logError "Type mismatch"'):
                    source = (prefix + command + suffix).replace("\n", newline)
                    try:
                        policy.validate_source(source, 'lexical-matrix-negative')
                    except ValueError as error:
                        if 'executable diagnostic imitation is forbidden' not in str(error):
                            raise
                    else:
                        raise SystemExit('Lexical matrix masked an executable command')
                    negative += 1
    print(f'FIXTURE_LEXICAL_MATRIX_OK positive={positive} negative={negative} positions={positive}')
    return dict(positive_sources=positive, rejected_sources=negative, position_checks=positive)


def policy_checks(repo: Path) -> dict[str, int]:
    spec = importlib.util.spec_from_file_location('fixture_policy', repo / 'scripts/expected_failure_diagnostics.py')
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    permitted_sources = (
        '/- run_cmd \" /- nested #eval -/ -/\nexample : True := True.intro\n',
        '-- run_tac\r\nexample : True := True.intro\r\n',
        'def diagnosticName := \"run_cmd #eval /- --\"\n',
        'def diagnosticName := r##\"run_cmd #eval /- --\"##\n',
        'def \u00abrun_cmd\u00bb := True.intro\n',
        'def readTrace := normalization.trace source\n',
        "def quotedCharacter : Char := '\"'\n",
        r"""def escapedQuote : Char := '\"'""" + '\n',
        r"""def escapedApostrophe : Char := '\''""" + '\n',
        r"""def escapedBackslash : Char := '\\'""" + '\n',
        r"""def escapedNewline : Char := '\n'""" + '\n',
        r"""def escapedReturn : Char := '\r'""" + '\n',
        r"""def escapedTab : Char := '\t'""" + '\n',
        r"def escapedHex : Char := '\x22'" + '\n',
        r"def escapedUnicode : Char := '\u0022'" + '\n',
        "def unicodeCharacter : Char := '\u00ab'\n",
        "def consecutiveCharacters := ('a', '\"')\n",
        "def head' := true\ndef tail'' := head'\n",
    )
    for source in permitted_sources:
        policy.validate_source(source, 'lexical-positive-case')
        masked = policy.fixture_code(source)
        if len(masked) != len(source) or [i for i, ch in enumerate(masked) if ch in '\r\n'] != \
                [i for i, ch in enumerate(source) if ch in '\r\n']:
            raise SystemExit('Fixture masking changed source positions')
    for source in (
        '/- comment -/ run_cmd logError \"Type mismatch\"',
        '/- outer /- nested -/ -/ run_cmd logError \"Type mismatch\"',
        '-- comment\rrun_cmd logError \"Type mismatch\"',
        'namespace Test run_cmd logError \"Type mismatch\"',
        '@[irreducible] private elab \"bad\" : command => pure ()',
        'example : True := by run_tac Lean.logError \"Type mismatch\"',
        'example : True := by fail \"Type mismatch\"',
        'example : True := by run_tac Lean.throwError\"Type mismatch\"',
        '/- comment -/ #eval IO.println \"Type mismatch\"',
        'local syntax \"bad\" : command',
        '/- comment -/ initialize fabricated : Nat ← pure 0',
        's!\"{by run_tac Lean.logError \"Type mismatch\"}\"',
        's! /- intervening comment -/ \"{by run_tac Lean.logError}\"',
        '/- unclosed', 'def x := \"unclosed', 'def x := \"escape\\',
        'def \u00abunclosed', 'def x := r##\"unclosed',
        "def before : Char := '\"'\nrun_cmd logError \"Type mismatch\"\ndef after : Char := '\"'\n",
        r"""def before : Char := '\"'""" + '\nrun_cmd logError "Type mismatch"\n' +
            r"""def after : Char := '\"'""" + '\n',
        "def x := 'unclosed", "def x := 'ab'", r"def x := '\q'",
        "def x := '\\", "def x := ''",
    ):
        try:
            policy.validate_source(source, 'lexical-negative-case')
        except ValueError:
            pass
        else:
            raise SystemExit('Executable or malformed fixture source was accepted: ' + source)
    matrix = lexical_matrix(policy)
    first_fixture = next(row.split('\t')[0] for row in
                         (repo / 'scripts/expected-failures.tsv').read_text(encoding='utf-8').splitlines()
                         if row.strip() and not row.startswith('#'))
    original_read = Path.read_text

    for forgery in (
        '/- comment -/ run_cmd logError \"Type mismatch\"',
        """def before : Char := '"'\nrun_cmd logError "Type mismatch"\ndef after : Char := '"'\n""",
        r"""def before : Char := '\"'""" + '\nrun_cmd logError "Type mismatch"\n' +
            r"""def after : Char := '\"'""" + '\n',
    ):
        def forged_read(path, *args, **kwargs):
            if path.resolve() == (repo / first_fixture).resolve():
                return forgery
            return original_read(path, *args, **kwargs)

        with patch.object(sys, 'argv', ['expected_failure_diagnostics.py']), \
             patch.object(Path, 'read_text', forged_read), \
             patch.object(policy.subprocess, 'run') as compiler:
            try:
                policy.main()
            except ValueError as error:
                if 'executable diagnostic imitation is forbidden' not in str(error):
                    raise
            else:
                raise SystemExit('Diagnostic forgery was not refused before compilation')
            compiler.assert_not_called()
    for status in (2, 124, 137, -9):
        try:
            policy.validate_status(status, 'synthetic-process-status')
        except ValueError:
            pass
        else:
            raise SystemExit('An interrupted process was mistaken for a compiler refusal')
    for output in ('expected needle', '{"severity":"error","data":"needle"}\nnot JSON'):
        try:
            policy.errors(output, 'synthetic-printed-output')
        except ValueError:
            pass
        else:
            raise SystemExit('Printed output was mistaken for a structured Lean diagnostic')
    fake = dict(severity='error', fileName='Other.lean', pos=dict(line=12, column=13),
                data='but is expected to have type', isSilent=False)
    if policy.matches(fake, 'Tests/ExpectedFailure/ResourcePortsCannotBePermuted.lean.fail',
                      12, 13, 'but is expected to have type'):
        raise SystemExit('A foreign diagnostic site was accepted')
    with patch.object(sys, 'argv', ['expected_failure_diagnostics.py']), \
         patch.object(policy.subprocess, 'run', side_effect=subprocess.TimeoutExpired('synthetic', 90)):
        try:
            policy.main()
        except ValueError as error:
            if 'interrupted or timed out' not in str(error):
                raise
        else:
            raise SystemExit('A subprocess timeout was mistaken for a compiler refusal')
    print('FIXTURE_POLICY_SELFTEST_OK: lexical policy, process status, timeout handler, printed output and diagnostic identity')
    return matrix


def link_artifacts(source: Path, destination: Path) -> None:
    try:
        os.symlink(source, destination, target_is_directory=True)
    except OSError:
        if os.name != 'nt':
            raise
        # Junction creation only: both absolute targets are explicit and the
        # new link is inside this test's disposable directory.
        command = ("New-Item -ItemType Junction -Path '" + str(destination).replace("'", "''") +
                   "' -Target '" + str(source).replace("'", "''") + "' | Out-Null")
        subprocess.run(['powershell', '-NoProfile', '-Command', command],
                       check=True, capture_output=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, help='required for the cross-shell suite')
    parser.add_argument('--policy-only', action='store_true',
                        help='run source/diagnostic policy checks without building or launching either shell')
    parser.add_argument('--bash', default='C:/Program Files/Git/bin/bash.exe' if os.name == 'nt' else 'bash')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    if args.policy_only:
        if args.output is not None:
            parser.error('--policy-only does not write results; do not supply --output')
        policy_checks(repo)
        return
    if args.output is None:
        parser.error('--output is required unless --policy-only is used')
    if not (repo / '.lake/build').is_dir():
        raise SystemExit('Run lake build before the gate self-tests')
    if not shutil.which('pwsh'):
        raise SystemExit('PowerShell unavailable: this two-gate test cannot pass')
    policy_results = policy_checks(repo)
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = (repo / 'scripts/expected-failures.tsv').read_text(encoding='utf-8')
    rows = [line for line in manifest.splitlines() if line and not line.startswith('#')]
    unique = {line.split('\t')[0] for line in rows}
    first = rows[0].split('\t')[0]
    cases = [
        ('baseline', None), ('unlisted', 'uninventoried fixture'),
        ('orphan', 'orphan fixture entry'), ('duplicate', 'duplicate fixture'),
        ('compiles', 'unexpectedly compiled'), ('wrong-diagnostic', 'failed for an unexpected reason'),
        ('wrong-site', 'failed for an unexpected reason'), ('missing-file', 'orphan fixture entry'),
        ('extra-error', 'failed for an unexpected reason'),
        ('printed-needle', 'executable diagnostic imitation is forbidden'),
        ('commented-run-cmd', 'executable diagnostic imitation is forbidden'),
        ('nested-comment-run-cmd', 'executable diagnostic imitation is forbidden'),
        ('commented-eval', 'executable diagnostic imitation is forbidden'),
        ('tactic-diagnostic', 'executable diagnostic imitation is forbidden'),
        ('character-run-cmd', 'executable diagnostic imitation is forbidden'),
        ('escaped-character-run-cmd', 'executable diagnostic imitation is forbidden'),
        ('quoted-run-cmd', 'failed for an unexpected reason (error class)'),
        ('quoted-run-tac', 'failed for an unexpected reason (error class)'),
    ]
    records = []
    for case, expected in cases:
        with tempfile.TemporaryDirectory(prefix='fixture-gate-') as directory:
            work = Path(directory)
            shutil.copytree(repo / 'Tests/ExpectedFailure', work / 'Tests/ExpectedFailure')
            (work / 'scripts').mkdir()
            for name in ('check-expected-failures.sh', 'check-expected-failures.ps1',
                         'expected_failure_diagnostics.py', 'expected-failures.tsv'):
                shutil.copy2(repo / 'scripts' / name, work / 'scripts' / name)
            link_artifacts(repo / '.lake', work / '.lake')
            for config in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                shutil.copy2(repo / config, work / config)
            inventory = work / 'scripts/expected-failures.tsv'
            environment = dict(os.environ)
            environment['RELATIONAL_PERIMETER_PYTHON'] = sys.executable
            if case == 'unlisted':
                (work / 'Tests/ExpectedFailure/Unlisted.lean.fail').write_text('example : True := True.intro\n', encoding='utf-8')
            elif case == 'orphan':
                inventory.write_text(manifest + 'Tests/ExpectedFailure/Absent.lean.fail\tdependent-type\t1\t0\tType mismatch\n', encoding='utf-8')
            elif case == 'duplicate':
                inventory.write_text(manifest + rows[0] + '\n', encoding='utf-8')
            elif case == 'compiles':
                (work / first).write_text('example : True := True.intro\n', encoding='utf-8')
            elif case in ('wrong-diagnostic', 'wrong-site'):
                parts = rows[0].split('\t')
                parts[4 if case == 'wrong-diagnostic' else 2] = 'IMPOSSIBLE_EXPECTED_DIAGNOSTIC' if case == 'wrong-diagnostic' else '999'
                inventory.write_text(manifest.replace(rows[0], '\t'.join(parts)), encoding='utf-8')
            elif case == 'missing-file':
                (work / first).unlink()
            elif case == 'extra-error':
                original = (work / first).read_text(encoding='utf-8')
                (work / first).write_text(original + '\nexample : Nat := True.intro\n', encoding='utf-8')
            elif case == 'printed-needle':
                # The old substring gate accepted an expected message printed
                # beside an unrelated error. The new gate must not.
                (work / first).write_text('#eval IO.println "but is expected to have type"\nexample : Nat := True.intro\n', encoding='utf-8')
            elif case in ('commented-run-cmd', 'nested-comment-run-cmd'):
                # Exact successful bypass found during review: a fabricated
                # compiler message matches the frozen file, line, column,
                # error class and needle, without any actual type mismatch.
                prefix = '/- xxxxxx -/ ' if case == 'commented-run-cmd' else '/-/- x -/-/  '
                if len(prefix) != 13:
                    raise SystemExit('Diagnostic reproduction no longer matches the frozen column')
                fabricated = 'import Lean\nopen Lean Elab Command\n' + '\n' * 9 + \
                    prefix + 'run_cmd logError "Application type mismatch: applyStage fresh"\n'
                (work / first).write_text(fabricated, encoding='utf-8')
            elif case == 'commented-eval':
                (work / first).write_text('/- outer /- nested -/ -/ #eval IO.println "Type mismatch"\n', encoding='utf-8')
            elif case == 'tactic-diagnostic':
                (work / first).write_text('example : True := by fail "Type mismatch"\n', encoding='utf-8')
            elif case in ('character-run-cmd', 'escaped-character-run-cmd'):
                character = "'\"'" if case == 'character-run-cmd' else r"""'\"'"""
                # Two character quotes used to be mistaken for string
                # delimiters, hiding the actual command from the source gate.
                fabricated = 'import Lean\nopen Lean Elab Command\n' + \
                    'def quoteBefore : Char := ' + character + '\n' + '\n' * 8 + \
                    ' ' * 13 + 'run_cmd logError "Application type mismatch: applyStage fresh"\n' + \
                    'def quoteAfter : Char := ' + character + '\n'
                (work / first).write_text(fabricated, encoding='utf-8')
            elif case == 'quoted-run-cmd':
                fabricated = 'import Lean\nopen Lean Elab Command\n' + '\n' * 9 + \
                    ' ' * 13 + '\u00abrun_cmd\u00bb \u00ablogError\u00bb "Application type mismatch: applyStage fresh"\n'
                (work / first).write_text(fabricated, encoding='utf-8')
            elif case == 'quoted-run-tac':
                (work / first).write_text(
                    'import Lean\nexample : True := by\n'
                    '  \u00abrun_tac\u00bb Lean.\u00ablogError\u00bb "Type mismatch"\n'
                    '  exact True.intro\n', encoding='utf-8')
            if case in ('quoted-run-cmd', 'quoted-run-tac'):
                # These names are lexically permitted. Confirm the actual
                # compiler refusal before testing rejection by the wrappers,
                # so an unrelated tool/import failure cannot pass this case.
                lake = shutil.which('lake')
                if lake is None:
                    raise SystemExit('lake unavailable for the quoted-command compiler control')
                compiled = subprocess.run([lake, 'env', 'lean', '--json', first],
                                          cwd=work, env=environment, capture_output=True,
                                          text=True, encoding='utf-8', timeout=90)
                compiler_output = compiled.stdout + compiled.stderr
                (args.output / f'{case}-compiler.log').write_text(compiler_output, encoding='utf-8')
                diagnostics = [json.loads(line) for line in compiler_output.splitlines() if line.strip()]
                intended = ('unknown namespace ' + chr(96) + 'run_cmd' + chr(96)) \
                    if case == 'quoted-run-cmd' else 'unknown tactic'
                if compiled.returncode != 1 or not any(
                        record.get('severity') == 'error' and record.get('data') == intended
                        for record in diagnostics):
                    raise SystemExit('Quoted command failed for a reason other than the intended parser refusal')
            for surface, command in (
                ('bash', [args.bash, 'scripts/check-expected-failures.sh']),
                ('powershell', ['pwsh', '-NoProfile', '-File', 'scripts/check-expected-failures.ps1']),
            ):
                result = subprocess.run(command, cwd=work, env=environment, capture_output=True,
                                        text=True, encoding='utf-8', timeout=180)
                output = result.stdout + result.stderr
                log = args.output / f'{case}-{surface}.log'
                log.write_text(output, encoding='utf-8')
                executed = [line.split('\t')[-1] for line in output.splitlines() if line.startswith('EXPECTED_FAILURE_OK\t')]
                passed = (result.returncode == 0 and len(executed) == len(unique) and set(executed) == unique) if case == 'baseline' else (result.returncode != 0 and expected in output)
                records.append(dict(case=case, surface=surface, exit_code=result.returncode, passed=passed,
                                    fixture_calls=len(executed), log=log.name))
                print(case, surface, result.returncode, 'PASS' if passed else 'FAIL', flush=True)
    (args.output / 'results.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
    (args.output / 'policy-results.json').write_text(json.dumps(policy_results, indent=2), encoding='utf-8')
    if not all(record['passed'] for record in records):
        raise SystemExit('Fixture-gate self-test failed')


if __name__ == '__main__':
    main()
