#!/usr/bin/env python3
"""Fail-closed import boundary for compiler-refusal fixtures.

Use Lean's resolved dependencies, never an import-text approximation. Admit
every inventoried production module and only the pinned toolchain's Init and
Init.Omega at the external boundary. Lake checks artifact freshness without
building or downloading. A transaction fingerprint also covers the subsequent
fixture compilations. This is a compiler gate, not a theorem about computation.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from pathlib import Path
import re
import subprocess
import sys

FOUNDATIONS = ('SegmentedResidualRole', 'AbstractSegmentedTurning',
               'ExactTypeTransport', 'StrongPerimetralTurning', 'RelationalPerimeter')
CONFIG = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
          'scripts/stratification.tsv', 'scripts/expected-failures.tsv',
          'scripts/check-fixture-import-closure.py', 'scripts/expected_failure_diagnostics.py')
EXTERNAL = ('Init.olean', 'Init/Omega.olean')
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')


def run(command: list[str], root: Path, timeout: int = 90) -> str:
    try:
        result = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                encoding='utf-8', timeout=timeout)
    except subprocess.TimeoutExpired as error:
        raise ValueError('import closure: resolver or freshness check timed out') from error
    if result.returncode != 0:
        raise ValueError('import closure: command failed: ' + ' '.join(command) + '\n' +
                         (result.stdout + result.stderr)[-4000:])
    if result.stderr.strip():
        raise ValueError('import closure: unexpected resolver output: ' + result.stderr[-2000:])
    return result.stdout


def inventory(root: Path) -> dict[str, Path]:
    physical = set(root.glob('*.lean'))
    physical.update((root / 'RelationalPerimeter').rglob('*.lean'))
    if any(not path.is_file() for path in physical):
        raise ValueError('import closure: missing production source')
    rows: dict[str, Path] = {}
    for line in (root / 'scripts/stratification.tsv').read_text(encoding='utf-8').splitlines():
        if not line or line.startswith('#'):
            continue
        parts = line.split('\t')
        if len(parts) != 4 or not MODULE.fullmatch(parts[0]) or parts[2] != 'enforced':
            raise ValueError('import closure: malformed production inventory')
        name = parts[0]
        if name in rows:
            raise ValueError('import closure: duplicate production module: ' + name)
        rows[name] = root / (name.replace('.', '/') + '.lean')
    if set(rows.values()) != physical:
        raise ValueError('import closure: unmanifested or missing production module: ' +
                         ', '.join(str(path.relative_to(root)) for path in
                                   sorted(set(rows.values()) ^ physical)))
    return rows


def snapshot(root: Path) -> dict[str, str]:
    paths = [root / name for name in CONFIG]
    paths += [root / (name + '.lean') for name in FOUNDATIONS]
    paths += list((root / 'RelationalPerimeter').rglob('*.lean'))
    paths += list((root / 'Tests/ExpectedFailure').rglob('*.lean.fail'))
    # Missing/replaced artifacts or metadata and concurrent source changes
    # invalidate the transaction, even if a fixture's diagnostic still matches.
    paths += list((root / '.lake/build/lib/lean').rglob('*'))
    return {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(set(paths)) if path.is_file()}


def unchanged(root: Path, before: dict[str, str]) -> None:
    after = snapshot(root)
    for name in before:
        if name.startswith('@toolchain:'):
            path = Path(name.removeprefix('@toolchain:'))
            after[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else 'missing'
    if after != before:
        raise ValueError('import closure: source, fixture or artifact changed during validation')


def resolved_paths(output: str, root: Path) -> list[Path]:
    lines = output.splitlines()
    if not lines or any(not line.strip() or line != line.strip() or '\x00' in line or
                        not line.endswith('.olean') for line in lines):
        raise ValueError('import closure: malformed dependency resolver output')
    paths = [(Path(line) if Path(line).is_absolute() else root / line).resolve() for line in lines]
    if any(not path.is_file() for path in paths):
        raise ValueError('import closure: unresolved dependency artifact')
    return paths


def check(root: Path, lake: str) -> dict[str, str]:
    root = root.resolve()
    before = snapshot(root)
    modules = inventory(root)
    pin = (root / 'lean-toolchain').read_text(encoding='utf-8').strip()
    match = re.fullmatch(r'leanprover/lean4:v(\d+\.\d+\.\d+)', pin)
    if match is None:
        raise ValueError('import closure: unsupported toolchain pin')
    version = run([lake, 'env', 'lean', '--version'], root)
    if not version.startswith('Lean (version ' + match.group(1) + ','):
        raise ValueError('import closure: resolved Lean does not match the pinned version')
    output = run([lake, 'env', 'lean', '--print-libdir'], root).strip()
    if not output or '\n' in output or '\r' in output:
        raise ValueError('import closure: malformed toolchain library path')
    libdir = Path(output).resolve()
    if not libdir.is_dir():
        raise ValueError('import closure: toolchain library directory is missing')
    allowed = {(libdir / name).resolve() for name in EXTERNAL}
    if any(not path.is_file() for path in allowed):
        raise ValueError('import closure: approved toolchain artifact is missing')
    before.update({'@toolchain:' + str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                   for path in allowed})
    local = {(root / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')).resolve(): name
             for name in modules}
    if any(not path.is_file() for path in local):
        raise ValueError('import closure: missing production artifact; run lake build first')

    def dependencies(item: tuple[str, Path]) -> tuple[str, list[Path]]:
        name, source = item
        output = run([lake, 'env', 'lean', '--deps', source.relative_to(root).as_posix()], root)
        return name, resolved_paths(output, root)

    edges = 0
    with ThreadPoolExecutor(max_workers=4) as pool:
        for name, paths in pool.map(dependencies, modules.items()):
            for path in paths:
                if path in local:
                    edges += 1
                elif path not in allowed:
                    raise ValueError('import closure: forbidden resolved dependency in ' + name + ': ' + str(path))
    # All direct local edges have been checked, including indirect routes to
    # an external module. Explicit Omega is retained; this is not a blanket
    # permission for Init.*, Std, Lean or Lake. Verify all inventory facets,
    # not only what happens to be reachable from the public root.
    targets = ['+' + name + ':olean' for name in modules]
    for start in range(0, len(targets), 35):
        try:
            run([lake, '--rehash', '--no-build', '--no-cache', 'build'] + targets[start:start + 35],
                root, timeout=180)
        except ValueError as error:
            raise ValueError('import closure: stale or invalid production artifact\n' + str(error)) from error
    unchanged(root, before)
    print(f'FIXTURE_IMPORT_CLOSURE_OK modules={len(modules)} local_edges={edges} '
          'external=Init,Init.Omega fresh=Lake-rehash-no-build', flush=True)
    return before


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    check(Path(__file__).resolve().parent.parent, args.lake)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print('FIXTURE_IMPORT_CLOSURE_FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
