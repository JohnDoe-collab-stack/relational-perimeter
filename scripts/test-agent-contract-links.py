#!/usr/bin/env python3
"""Version 1: frozen, isolated checks of the three agent contract links.

Run after a full build. Uses a detached disposable clone with physical build
artifacts, never modifies the reference, and never commits or deletes a tree.
Mutation patches, commands, hashes, exits and logs are written to a NEW output
directory. These checks complement, and do not replace, the constructive proofs.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import platform
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
EXECUTION = 'RelationalPerimeter/Agents/Constitutive/Execution.lean'
AGREEMENT = 'RelationalPerimeter/Agents/Constitutive/Agreement.lean'
PERSISTENCE = 'RelationalPerimeter/Agents/Constitutive/Persistence.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f'Mutation does not match exactly once: {old!r}')
    return text.replace(old, new, 1)


def erase_references(files):
    text = replace_once(files[PERSISTENCE],
        '(referencesExact : references = (sourcePerform source request).1.history.references)',
        '(referencesExact : Unit)')
    text = replace_once(text, '(sourcePerform source request).1.history.references rfl',
                        '(sourcePerform source request).1.history.references ()')
    text = replace_once(text,
        '| cons _ _ _ _ _ _ _ referencesExact _ _ _ _ => exact referencesExact',
        '| cons _ _ _ _ _ _ _ _ _ _ _ _ => rfl')
    return {PERSISTENCE: text}


def erase_absence(files):
    before, tail = files[EXECUTION].split('inductive ResponseEvidence ', 1)
    tail = replace_once(tail, '(absent : resolveHandle register handle = none)',
                        '(_erasedAbsence : Unit)')
    tail = replace_once(tail, '| missing _ absent => exact absent', '| missing _ _ => rfl')
    tail = replace_once(tail, '| .missing permission absent => .missing permission absent',
                        '| .missing permission _ => .missing permission ()')
    tail = replace_once(tail,
        '| missing permission absent => exact ⟨rfl, rfl, ⟨permission⟩, absent⟩',
        '| missing permission _ => exact ⟨rfl, rfl, ⟨permission⟩, (by rfl)⟩')
    return {EXECUTION: before + 'inductive ResponseEvidence ' + tail}


def runtime_bridge(files):
    text = replace_once(files[AGREEMENT],
        'sourceEvent := fun source request => (sourcePerform source request).2',
        'sourceEvent := fun source request => (executeInput (project source) request).2')
    text = replace_once(text,
        'eventLaw := fun source request => congrArg Prod.snd (sourcePerform_exact source request)',
        'eventLaw := fun _ _ => rfl')
    text = replace_once(text,
        'bridgeSourceEvent master source request = (sourcePerform source request).2 := rfl',
        'bridgeSourceEvent master source request = (sourcePerform source request).2 :=\n'
        '  (congrArg Prod.snd (sourcePerform_exact source request)).symm')
    persistence = replace_once(files[PERSISTENCE], 'bridgeRichResult := fun _ _ => rfl',
        'bridgeRichResult := fun source request =>\n'
        '      Prod.ext rfl (congrArg Prod.snd (sourcePerform_exact source request)).symm')
    return {AGREEMENT: text, PERSISTENCE: persistence}


def runtime_bridge_unused_observer(files):
    changed = runtime_bridge(files)
    changed[AGREEMENT] = replace_once(changed[AGREEMENT],
        '    (source : Source master) (request : Request) : Event :=\n'
        '  (bridge master).sourceEvent source request',
        '    (source : Source master) (request : Request) : Event :=\n'
        '  (sourcePerform source request).2')
    changed[AGREEMENT] = replace_once(changed[AGREEMENT],
        'bridgeSourceEvent master source request = (sourcePerform source request).2 :=\n'
        '  (congrArg Prod.snd (sourcePerform_exact source request)).symm',
        'bridgeSourceEvent master source request = (sourcePerform source request).2 := rfl')
    return changed


def rich_helper(files):
    helper = ('def bridgeRichEventHelper {input : Nat} (master : UnifiedMaster.Instance input)\n'
              '    (source : Source master) (request : Request) : Event :=\n'
              '  (sourcePerform source request).2\n\n')
    # master is an implicit index of Source; name it to avoid an unused binder.
    helper = helper.replace('(master :', '(_master :').replace('Source master', 'Source _master')
    text = replace_once(files[AGREEMENT], 'def bridge {input : Nat}', helper + 'def bridge {input : Nat}')
    text = replace_once(text, 'sourceEvent := fun source request => (sourcePerform source request).2',
                        'sourceEvent := fun source request => bridgeRichEventHelper master source request')
    text = replace_once(text, '/- AXIOM_AUDIT_END -/',
        '#print axioms ConstitutiveSearch.Agent.bridgeRichEventHelper\n/- AXIOM_AUDIT_END -/')
    return {AGREEMENT: text}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents or output.exists():
        raise ValueError('Output must be a new directory OUTSIDE the reference repository')
    output.mkdir(parents=True)
    inventory = subprocess.run(['git', 'ls-files', '--cached', '--others', '--exclude-standard'],
        cwd=ROOT, capture_output=True, text=True, check=True).stdout.splitlines()
    paths = [name for name in inventory if (ROOT / name).is_file()]
    before = {name: sha(ROOT / name) for name in paths}
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout.strip()
    snapshot, scratch = output / 'source-snapshot', output / 'disposable-checkout'
    snapshot.mkdir()
    for name in paths:
        target = snapshot / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, target)
    frozen = {name: (snapshot / name).read_text(encoding='utf-8')
              for name in (EXECUTION, AGREEMENT, PERSISTENCE)}
    cases = [
        ('C1-exactness-payload-erased', erase_references, 'root-reject',
         ('Tactic `rfl` failed', 'tactic \'rfl\' failed')),
        ('C3-absence-payload-erased', erase_absence, 'root-reject',
         ('Tactic `rfl` failed', 'tactic \'rfl\' failed')),
        ('C2-runtime-source-with-semantic-proofs', runtime_bridge, 'compiled-reject',
         ('AGENT_BRIDGE_FAILED: sourceEvent:',)),
        ('C2-unused-rich-observer', runtime_bridge_unused_observer, 'compiled-reject',
         ('AGENT_BRIDGE_FAILED: sourceEvent:',)),
        ('C2-legitimate-rich-helper', rich_helper, 'accept', ())]
    patches = {}
    for name, transform, expected, diagnostics in cases:
        changed = transform(frozen)
        patch = ''
        for path, new in changed.items():
            old = (snapshot / path).read_bytes().decode('utf-8')
            if '\r\n' in old:
                new = new.replace('\n', '\r\n')
            patch += ''.join(difflib.unified_diff(old.splitlines(keepends=True),
                new.splitlines(keepends=True), fromfile='a/' + path, tofile='b/' + path))
        patch_path = output / (name + '.patch')
        patch_path.write_bytes(patch.encode('utf-8'))
        patches[name] = (patch_path, tuple(changed))
    manifest = {'version': 1, 'reference_head': head, 'script_sha256': sha(Path(__file__)),
        'python': sys.version, 'platform': platform.platform(), 'source_sha256': before,
        'cases': [{'name': name, 'expectation': expected, 'diagnostics': diagnostics,
                   'patch_sha256': sha(patches[name][0])} for name, _, expected, diagnostics in cases]}
    (output / 'frozen-protocol.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')

    def run(label, command):
        log = output / (label + '.log')
        with log.open('wb') as stream:
            try:
                result = subprocess.run(command, cwd=scratch, stdout=stream, stderr=subprocess.STDOUT,
                                        timeout=900)
            except subprocess.TimeoutExpired as error:
                raise RuntimeError('Timeout is NOT a valid rejection: ' + label) from error
        record = {'label': label, 'command': command, 'exit': result.returncode,
                  'log_sha256': sha(log)}
        with (output / 'commands.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(json.dumps(record) + '\n')
        return result.returncode, log.read_text(encoding='utf-8', errors='replace')

    subprocess.run(['git', 'clone', '--shared', '--no-hardlinks', '--no-checkout', str(ROOT), str(scratch)],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    subprocess.run(['git', 'checkout', '--detach', head], cwd=scratch, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    for name in paths:
        target = scratch / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(snapshot / name, target)
    shutil.copytree(ROOT / '.lake', scratch / '.lake', symlinks=False)
    results = []
    try:
        code, version = run('toolchain', ['lake', 'env', 'lean', '--version'])
        if code or '4.33.1' not in version:
            raise RuntimeError('Wrong or unavailable pinned toolchain')
        for label, command in (
                ('control-build', ['lake', 'build']),
                ('control-codegen', [sys.executable, '-B', 'scripts/check-agent-codegen.py'])):
            code, _ = run(label, command)
            if code:
                raise RuntimeError('Unmodified control failed: ' + label)
        for name, _, expected, diagnostics in cases:
            # Restore only the three explicitly scoped source files, in the
            # disposable checkout. Reference files/artifacts are never written.
            for path in frozen:
                shutil.copy2(snapshot / path, scratch / path)
            patch_path, _ = patches[name]
            subprocess.run(['git', 'apply', '--whitespace=nowarn', '-'], cwd=scratch,
                           input=patch_path.read_bytes(), check=True)
            code, log = run(name + '-build', ['lake', 'build'])
            if expected == 'root-reject':
                if not code or not any(marker in log for marker in diagnostics):
                    raise RuntimeError('Missing substantive equality rejection: ' + name)
                if any(marker in log for marker in ('Unknown identifier', 'Unknown constant',
                        'Too many variable names', 'Invalid number of arguments')):
                    raise RuntimeError('Accidental/name-level rejection: ' + name)
            else:
                if code:
                    raise RuntimeError('Coherent mutation failed before its intended gate: ' + name)
                if 'warning:' in log:
                    raise RuntimeError('Warning in a mutation required to build cleanly: ' + name)
                code, log = run(name + '-codegen', [sys.executable, '-B', 'scripts/check-agent-codegen.py'])
                if expected == 'compiled-reject':
                    if not code or not any(marker in log for marker in diagnostics):
                        raise RuntimeError('Projected responder not rejected: ' + name)
                elif code:
                    raise RuntimeError('Legitimate rich helper rejected')
            results.append({'name': name, 'result': expected, 'matched': True})
            print('CONTRACT_LINK_CASE_OK ' + name + ': ' + expected, flush=True)
    finally:
        after = {name: sha(ROOT / name) for name in paths}
        unchanged = before == after
        report = {'cases': results, 'reference_unchanged': unchanged}
        (output / 'results.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        if not unchanged:
            raise RuntimeError('Reference changed during campaign')
    print('AGENT_CONTRACT_LINKS_OK: 5 coherent cases; reference unchanged', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print('AGENT_CONTRACT_LINKS_FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
