#!/usr/bin/env python3
"""Regression checks of fixture gates, not scientific experiments.

Real Lean checks run in disposable directories with independent copied artifacts.
Pure status/parser checks separately test process failure and JSON spoofing.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import tempfile
from types import SimpleNamespace
from unittest.mock import patch


# Exact bypass reported by the independent audit (M20e): a same-file command
# elaborator fabricates the frozen diagnostic of a dependent-type fixture at
# its frozen line and column, while the genuine type error is removed.
SPOOF_TARGET = 'Tests/ExpectedFailure/AcceptedTargetCannotReplaceProducedOutput.lean.fail'
SPOOF_FIXTURE = (
    'import RelationalPerimeter\n'
    'import Lean\n'
    'set_option genInjectivity false\n'
    'namespace Tests.ExpectedFailure.AcceptedTargetCannotReplaceProducedOutput\n'
    'open ConstitutiveSearch.Agent ConstitutiveSearch.EndogenousDecomposition\n'
    '\n'
    'open Lean Elab Command in\n'
    '@[command_elab Lean.Parser.Command.check] def reviewNote : CommandElab := fun stx =>\n'
    '  Lean.logAt stx m!"Application type mismatch: target = retainedExecutedOperationalTargetProfile '
    'reduction \u2192 List AnswerTarget" .error\n'
    '\n'
    'theorem harmless : True := True.intro\n'
    '\n'
    '  #check harmless\n'
    '\n'
    'end Tests.ExpectedFailure.AcceptedTargetCannotReplaceProducedOutput\n')


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
        'import RelationalPerimeter\nimport RelationalPerimeter.Agents.Constitutive.Execution\ndef importance := 1\n',
        'import RelationalPerimeter\r\ndef moduleName := 1\r\n',
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
        # Same-file attribute-registered elaborators, foreign imports and the
        # message API (audit bypass M20e and its variants).
        SPOOF_FIXTURE, SPOOF_FIXTURE.replace('import Lean\n', ''),
        'import RelationalPerimeter\nimport Lean\n',
        'import Lean.Elab.Command\n', 'import Std\n', 'public import RelationalPerimeter\n',
        'meta import RelationalPerimeter\n', ' import RelationalPerimeter\n',
        'import RelationalPerimeter\r\nimport Lean\r\n', 'import RelationalPerimeter\rimport Lean\r',
        'module\nimport RelationalPerimeter\n', 'import RelationalPerimeter /- -/ Lean\n',
        '@[term_elab Lean.Parser.Term.app] def x := 1', '@[tactic Lean.Parser.Tactic.exact] def x := 1',
        '@[simp] theorem x : True := True.intro', 'attribute [command_elab Lean.Parser.Command.check] x',
        'def x := Lean.logAt', 'def x := Lean.Meta.throwAppTypeMismatch',
        'def x := m!"Application type mismatch"', 'def x := f!"Type mismatch"',
        'def x : Lean.MessageData := default', 'def x := Lean.logInfo', 'def x := Lean.logWarning',
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
        SPOOF_FIXTURE,
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
         patch.object(policy, 'load_closure', return_value=SimpleNamespace(
             check=lambda *_: {}, unchanged=lambda *_: None)), \
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


def digest_artifacts(repo: Path) -> dict[str, str]:
    import hashlib
    return {str(path.relative_to(repo)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (repo / '.lake/build').rglob('*') if path.is_file()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, help='required for the cross-shell suite')
    parser.add_argument('--policy-only', action='store_true',
                        help='run source/diagnostic policy checks without building or launching either shell')
    parser.add_argument('--jobs', type=int, default=2, choices=(1, 2, 3, 4))
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
    spec = importlib.util.spec_from_file_location('fixture_policy_main', repo / 'scripts/expected_failure_diagnostics.py')
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    args.output.mkdir(parents=True, exist_ok=False)
    reference_artifacts = digest_artifacts(repo)
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
        ('command-elab-spoof', 'executable diagnostic imitation is forbidden'),
        ('command-elab-spoof-project-import', 'executable diagnostic imitation is forbidden'),
        ('foreign-import', 'only plain project imports are permitted'),
        ('production-lean-import', 'forbidden resolved dependency'),
        ('production-comment-import', 'forbidden resolved dependency'),
        ('production-split-import', 'forbidden resolved dependency'),
        ('production-indirect-import', 'forbidden resolved dependency'),
        ('production-unmanifested', 'unmanifested or missing production module'),
        ('production-unresolved', 'import closure: command failed'),
        ('production-stale', 'stale or invalid production artifact'),
        ('production-missing-artifact', 'missing production artifact'),
        ('closure-malformed-resolver', 'malformed dependency resolver output'),
        ('closure-timeout', 'resolver or freshness check timed out'),
        ('closure-homonym', 'forbidden resolved dependency'),
        ('closure-source-change', 'changed during validation'),
        ('closure-forced-failure', 'import closure: forced self-test refusal'),
    ]
    def run_case(case_expected):
        case, expected = case_expected
        records = []
        with tempfile.TemporaryDirectory(prefix='fixture-gate-') as directory:
            work = Path(directory)
            shutil.copytree(repo / 'RelationalPerimeter', work / 'RelationalPerimeter')
            for path in repo.glob('*.lean'):
                shutil.copy2(path, work / path.name)
            shutil.copytree(repo / 'Tests/ExpectedFailure', work / 'Tests/ExpectedFailure')
            (work / 'scripts').mkdir()
            for name in ('check-expected-failures.sh', 'check-expected-failures.ps1',
                         'expected_failure_diagnostics.py', 'expected-failures.tsv',
                         'check-fixture-import-closure.py', 'stratification.tsv'):
                shutil.copy2(repo / 'scripts' / name, work / 'scripts' / name)
            # Physical copies: mutations and Lake metadata never reach the
            # reference through a junction, symlink, hard link or shared cache.
            shutil.copytree(repo / '.lake', work / '.lake')
            for config in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                shutil.copy2(repo / config, work / config)
            inventory = work / 'scripts/expected-failures.tsv'
            environment = dict(os.environ)
            environment['RELATIONAL_PERIMETER_PYTHON'] = sys.executable
            if case.startswith(('production-', 'closure-')):
                facade = work / 'RelationalPerimeter.lean'
                original = facade.read_text(encoding='utf-8')
                if case in ('production-lean-import', 'production-comment-import', 'production-split-import'):
                    header = {'production-lean-import': 'import Lean\n',
                              'production-comment-import': '/- preceding comment -/ import Lean\n',
                              'production-split-import': 'import\n  Lean\n'}[case]
                    facade.write_text(header + original, encoding='utf-8')
                elif case in ('production-indirect-import', 'production-unmanifested'):
                    probe = work / 'RelationalPerimeter/ClosureGateProbe.lean'
                    probe.write_text('import Lean\nset_option genInjectivity false\n'
                                     'namespace ClosureGateProbe\ntheorem ok : True := True.intro\nend ClosureGateProbe\n'
                                     '/- AXIOM_AUDIT_BEGIN -/\n#print axioms ClosureGateProbe.ok\n/- AXIOM_AUDIT_END -/\n',
                                     encoding='utf-8')
                    facade.write_text('import RelationalPerimeter.ClosureGateProbe\n' + original, encoding='utf-8')
                    if case == 'production-indirect-import':
                        strata = work / 'scripts/stratification.tsv'
                        strata.write_text(strata.read_text(encoding='utf-8') +
                                          'RelationalPerimeter.ClosureGateProbe\tA17\tenforced\tDisposable import control\n',
                                          encoding='utf-8')
                elif case == 'production-unresolved':
                    facade.write_text('import ModuleThatDoesNotExist\n' + original, encoding='utf-8')
                elif case == 'production-stale':
                    facade.write_text('-- freshness self-test\n' + original, encoding='utf-8')
                elif case == 'production-missing-artifact':
                    (work / '.lake/build/lib/lean/RelationalPerimeter.olean').unlink()
                elif case == 'closure-forced-failure':
                    gate = work / 'scripts/check-fixture-import-closure.py'
                    gate.write_text(gate.read_text(encoding='utf-8').replace(
                        '    root = root.resolve()\n',
                        '    raise ValueError("import closure: forced self-test refusal")\n    root = root.resolve()\n', 1),
                        encoding='utf-8')
                elif case in ('closure-malformed-resolver', 'closure-timeout', 'closure-homonym',
                              'closure-source-change'):
                    gate = work / 'scripts/check-fixture-import-closure.py'
                    gate_source = gate.read_text(encoding='utf-8')
                    if case == 'closure-malformed-resolver':
                        gate_source = gate_source.replace('    return result.stdout\n',
                            '    return "invalid resolver record" if "--deps" in command else result.stdout\n', 1)
                    elif case == 'closure-timeout':
                        gate_source = gate_source.replace('    try:\n        result = subprocess.run(',
                            '    try:\n        if "--deps" in command:\n'
                            '            raise subprocess.TimeoutExpired(command, timeout)\n'
                            '        result = subprocess.run(', 1)
                    elif case == 'closure-homonym':
                        library = subprocess.run([shutil.which('lake'), 'env', 'lean', '--print-libdir'],
                            cwd=work, capture_output=True, text=True, encoding='utf-8', check=True).stdout.strip()
                        (work / 'alternate').mkdir()
                        shutil.copy2(Path(library) / 'Init.olean', work / 'alternate/Init.olean')
                        gate_source = gate_source.replace('    return result.stdout\n',
                            '    if "--deps" in command:\n'
                            '        lines = result.stdout.splitlines()\n'
                            '        lines[0] = str(root / "alternate/Init.olean")\n'
                            '        return "\\n".join(lines) + "\\n"\n'
                            '    return result.stdout\n', 1)
                    else:
                        gate_source = gate_source.replace('    unchanged(root, before)\n',
                            '    path = root / "RelationalPerimeter.lean"\n'
                            '    path.write_text(path.read_text(encoding="utf-8") + "\\n-- transaction change\\n", encoding="utf-8")\n'
                            '    unchanged(root, before)\n', 1)
                    gate.write_text(gate_source, encoding='utf-8')
                if case in ('production-lean-import', 'production-comment-import',
                            'production-split-import', 'production-indirect-import'):
                    built = subprocess.run([shutil.which('lake'), 'build', '+RelationalPerimeter'], cwd=work,
                                           env=environment, capture_output=True, text=True,
                                           encoding='utf-8', timeout=180)
                    (args.output / f'{case}-build.log').write_text(built.stdout + built.stderr, encoding='utf-8')
                    if built.returncode != 0:
                        raise SystemExit('Disposable import control did not build: ' + case)
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
                # Foreign imports are refused by policy, so the quoted
                # spellings are tested with the only permitted import. The
                # parser error lands on the frozen site with the wrong class.
                fabricated = 'import RelationalPerimeter\n' + '\n' * 10 + \
                    ' ' * 13 + '\u00abrun_cmd\u00bb \u00ablogError\u00bb "Application type mismatch: applyStage fresh"\n'
                (work / first).write_text(fabricated, encoding='utf-8')
            elif case == 'quoted-run-tac':
                (work / first).write_text(
                    'import RelationalPerimeter\nexample : True := by\n'
                    '  \u00abrun_tac\u00bb Lean.\u00ablogError\u00bb "Type mismatch"\n'
                    '  exact True.intro\n', encoding='utf-8')
            elif case in ('command-elab-spoof', 'command-elab-spoof-project-import'):
                spoof = SPOOF_FIXTURE if case == 'command-elab-spoof' else SPOOF_FIXTURE.replace('import Lean\n', '')
                (work / SPOOF_TARGET).write_text(spoof, encoding='utf-8')
            elif case == 'foreign-import':
                original = (work / first).read_text(encoding='utf-8')
                (work / first).write_text(original.replace('\n', '\nimport Lean\n', 1), encoding='utf-8')
            if case == 'command-elab-spoof':
                # Compiler control: the spoof really fabricates exactly the
                # frozen diagnostic at the frozen site, so only the source
                # policy can be responsible for its rejection below.
                lake = shutil.which('lake')
                if lake is None:
                    raise SystemExit('lake unavailable for the elaborator-spoof compiler control')
                compiled = subprocess.run([lake, 'env', 'lean', '--json', SPOOF_TARGET],
                                          cwd=work, env=environment, capture_output=True,
                                          text=True, encoding='utf-8', timeout=180)
                compiler_output = compiled.stdout + compiled.stderr
                (args.output / f'{case}-compiler.log').write_text(compiler_output, encoding='utf-8')
                site = next(row.split('\t') for row in rows if row.split('\t')[0] == SPOOF_TARGET)
                found = policy.errors(compiler_output, SPOOF_TARGET)
                if compiled.returncode != 1 or len(found) != 1 or not any(
                        record.get('fileName') == SPOOF_TARGET and
                        record.get('pos') == {'line': int(site[2]), 'column': int(site[3])} and
                        site[4] in record.get('data', '') and
                        record.get('data', '').startswith('Application type mismatch')
                        for record in found):
                    raise SystemExit('Elaborator spoof no longer reproduces the frozen diagnostic')
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
                intended = 'unexpected identifier; expected command' \
                    if case == 'quoted-run-cmd' else 'unknown tactic'
                if compiled.returncode != 1 or not any(
                        record.get('severity') == 'error' and record.get('data') == intended
                        for record in diagnostics):
                    raise SystemExit('Quoted command failed for a reason other than the intended parser refusal')
            for surface, command in (
                ('bash', [args.bash, 'scripts/check-expected-failures.sh']),
                ('powershell', ['pwsh', '-NoProfile', '-File', 'scripts/check-expected-failures.ps1']),
            ):
                if case == 'closure-source-change':
                    # Each surface starts from the same fresh source. The
                    # preceding surface intentionally changed its disposable
                    # source; do not mistake that residue for this test.
                    facade.write_text(original, encoding='utf-8')
                result = subprocess.run(command, cwd=work, env=environment, capture_output=True,
                                        text=True, encoding='utf-8', timeout=300)
                output = result.stdout + result.stderr
                log = args.output / f'{case}-{surface}.log'
                log.write_text(output, encoding='utf-8')
                executed = [line.split('\t')[-1] for line in output.splitlines() if line.startswith('EXPECTED_FAILURE_OK\t')]
                passed = (result.returncode == 0 and len(executed) == len(unique) and set(executed) == unique) if case == 'baseline' else (result.returncode != 0 and expected in output)
                if case.startswith(('production-', 'closure-')):
                    passed = passed and not executed and 'FIXTURE_IMPORT_CLOSURE_OK' not in output
                records.append(dict(case=case, surface=surface, exit_code=result.returncode, passed=passed,
                                    fixture_calls=len(executed), log=log.name))
                print(case, surface, result.returncode, 'PASS' if passed else 'FAIL', flush=True)
        return records
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        records = [record for group in pool.map(run_case, cases) for record in group]
    if digest_artifacts(repo) != reference_artifacts:
        raise SystemExit('Reference artifacts were changed by disposable fixture tests')
    (args.output / 'results.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
    (args.output / 'policy-results.json').write_text(json.dumps(policy_results, indent=2), encoding='utf-8')
    if not all(record['passed'] for record in records):
        raise SystemExit('Fixture-gate self-test failed')


if __name__ == '__main__':
    main()
