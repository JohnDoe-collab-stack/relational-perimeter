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
import time
from unittest.mock import patch


def gate_passed(case: str, status: int | None, output: str,
                executed: list[str], unique: set[str], expected: str | None) -> bool:
    if 'interrupted or timed out' in output:
        return False
    if case == 'baseline':
        return status == 0 and len(executed) == len(unique) and set(executed) == unique
    return status == 1 and 'EXPECTED_FAILURE_FAILED:' in output and expected in output


def run_gate(command: list[str], work: Path, environment: dict[str, str],
             timeout: int) -> tuple[int | None, str, bool]:
    try:
        result = subprocess.run(command, cwd=work, env=environment, capture_output=True,
                                text=True, encoding='utf-8', timeout=timeout)
    except subprocess.TimeoutExpired as error:
        def decoded(part: str | bytes | None) -> str:
            return part.decode('utf-8', errors='replace') if isinstance(part, bytes) else part or ''
        return None, (decoded(error.stdout) + decoded(error.stderr) +
                      f'\nGATE_SELFTEST_FAILED: interrupted or timed out after {timeout} seconds\n'), True
    return result.returncode, result.stdout + result.stderr, False


def policy_checks(repo: Path) -> None:
    spec = importlib.util.spec_from_file_location('fixture_policy', repo / 'scripts/expected_failure_diagnostics.py')
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
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
    refusal = 'EXPECTED_FAILURE_FAILED: failed for an unexpected reason'
    for status in (None, 2, 124, 137, -9):
        if gate_passed('wrong-site', status, refusal, [], {'fixture'}, 'failed for an unexpected reason'):
            raise SystemExit('An interrupted gate was mistaken for the expected rejection')
    if gate_passed('wrong-site', 1, refusal + '\ninterrupted or timed out', [], {'fixture'},
                   'failed for an unexpected reason'):
        raise SystemExit('A timeout message was mistaken for the expected rejection')
    with patch.object(subprocess, 'run', side_effect=subprocess.TimeoutExpired('synthetic-gate', 17)):
        status, output, timed_out = run_gate(['synthetic-gate'], repo, dict(os.environ), 17)
    if status is not None or not timed_out or 'after 17 seconds' not in output:
        raise SystemExit('The outer timeout handler did not report a failed gate')
    print('FIXTURE_POLICY_SELFTEST_OK: process statuses, both timeout handlers, printed output and diagnostic identity')


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
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--bash', default='C:/Program Files/Git/bin/bash.exe' if os.name == 'nt' else 'bash')
    parser.add_argument('--gate-timeout-seconds', type=int,
                        help='outer deadline per gate; default: 60 + 90 * inventoried fixture count; '
                             'the exact diagnostic policy and its 90-second fixture deadline are unchanged')
    args = parser.parse_args()
    if args.gate_timeout_seconds is not None and args.gate_timeout_seconds <= 0:
        parser.error('--gate-timeout-seconds must be positive')
    repo = Path(__file__).resolve().parent.parent
    if not (repo / '.lake/build').is_dir():
        raise SystemExit('Run lake build before the gate self-tests')
    if not shutil.which('pwsh'):
        raise SystemExit('PowerShell unavailable: this two-gate test cannot pass')
    policy_checks(repo)
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = (repo / 'scripts/expected-failures.tsv').read_text(encoding='utf-8')
    rows = [line for line in manifest.splitlines() if line and not line.startswith('#')]
    unique = {line.split('\t')[0] for line in rows}
    # The previous fixed 180 seconds bounded the whole inventory, not one Lean
    # call. Cover the existing per-fixture deadline plus facade startup instead.
    # This is a reproducible outer budget, not a performance or cost guarantee.
    gate_timeout = args.gate_timeout_seconds if args.gate_timeout_seconds is not None else 60 + 90 * len(unique)
    print(f'GATE_SELFTEST_BUDGET: fixtures={len(unique)} gate_timeout_seconds={gate_timeout} '
          f'source={"explicit" if args.gate_timeout_seconds is not None else "60+90*fixtures"}', flush=True)
    first = rows[0].split('\t')[0]
    cases = [
        ('baseline', None), ('unlisted', 'uninventoried fixture'),
        ('orphan', 'orphan fixture entry'), ('duplicate', 'duplicate fixture'),
        ('compiles', 'unexpectedly compiled'), ('wrong-diagnostic', 'failed for an unexpected reason'),
        ('wrong-site', 'failed for an unexpected reason'), ('missing-file', 'orphan fixture entry'),
        ('extra-error', 'failed for an unexpected reason'),
        ('printed-needle', 'executable diagnostic imitation is forbidden'),
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
            for surface, command in (
                ('bash', [args.bash, 'scripts/check-expected-failures.sh']),
                ('powershell', ['pwsh', '-NoProfile', '-File', 'scripts/check-expected-failures.ps1']),
            ):
                started = time.monotonic()
                status, output, timed_out = run_gate(command, work, environment, gate_timeout)
                elapsed = time.monotonic() - started
                log = args.output / f'{case}-{surface}.log'
                log.write_text(output, encoding='utf-8')
                executed = [line.split('\t')[-1] for line in output.splitlines() if line.startswith('EXPECTED_FAILURE_OK\t')]
                passed = not timed_out and gate_passed(case, status, output, executed, unique, expected)
                records.append(dict(case=case, surface=surface, exit_code=status, passed=passed,
                                    fixture_calls=len(executed), timeout_seconds=gate_timeout,
                                    elapsed_seconds=round(elapsed, 3), timed_out=timed_out, log=log.name))
                print(case, surface, status, 'PASS' if passed else 'FAIL', flush=True)
    (args.output / 'results.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
    if not all(record['passed'] for record in records):
        raise SystemExit('Fixture-gate self-test failed')


if __name__ == '__main__':
    main()
