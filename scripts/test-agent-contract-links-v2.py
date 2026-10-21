#!/usr/bin/env python3
"""Version 2: frozen C1/C2/C3 contract-link campaign, including C2e.

Version 1 remains byte-identical historical evidence.  This version adds exact
return-origin tests for both rich fields, records every patch and command, and
runs C2e through both repository verifiers.  All mutations run in a detached,
disposable checkout; the reference repository is hash-checked before/after.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import importlib.util
import json
import os
import platform
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
EXECUTION = 'RelationalPerimeter/Agents/Constitutive/Execution.lean'
AGREEMENT = 'RelationalPerimeter/Agents/Constitutive/Agreement.lean'
PERSISTENCE = 'RelationalPerimeter/Agents/Constitutive/Persistence.lean'


def load_v1():
    path = ROOT / 'scripts/test-agent-contract-links.py'
    spec = importlib.util.spec_from_file_location('agent_contract_links_v1', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


V1 = load_v1()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f'Mutation does not match exactly once: {old!r}')
    return text.replace(old, new, 1)


def install_bridge_event(files, definition, theorem, event_expression, event_proof,
                         persistence_proof):
    text = replace_once(files[AGREEMENT], 'def bridge {input : Nat}',
                        definition + '\n' + theorem + '\n' + 'def bridge {input : Nat}')
    text = replace_once(text,
        'sourceEvent := fun source request => (sourcePerform source request).2',
        'sourceEvent := fun source request => ' + event_expression)
    text = replace_once(text,
        'eventLaw := fun source request => congrArg Prod.snd (sourcePerform_exact source request)',
        'eventLaw := fun source request =>\n'
        f'    ({event_proof}).trans (congrArg Prod.snd (sourcePerform_exact source request))')
    text = replace_once(text,
        'bridgeSourceEvent master source request = (sourcePerform source request).2 := rfl',
        'bridgeSourceEvent master source request = (sourcePerform source request).2 :=\n'
        f'  {event_proof}')
    audit_names = []
    for line in (definition + theorem).splitlines():
        if line.startswith('def ') or line.startswith('theorem '):
            audit_names.append(line.split()[1].split('{')[0])
    audits = ''.join('#print axioms ConstitutiveSearch.Agent.' + name + '\n'
                     for name in audit_names)
    text = replace_once(text, '/- AXIOM_AUDIT_END -/', audits + '/- AXIOM_AUDIT_END -/')
    persistence = replace_once(files[PERSISTENCE],
        'bridgeRichResult := fun _ _ => rfl',
        'bridgeRichResult := fun source request => ' + persistence_proof)
    return {AGREEMENT: text, PERSISTENCE: persistence}


def c2e_projected_message(files, helper=False):
    name = 'auditProjectedEventHelper' if helper else 'auditMixedEvent'
    definition = f'''def {name} {{input : Nat}} {{master : UnifiedMaster.Instance input}}
    (source : Source master) (request : Request) : Event :=
  let rich := sourcePerform source request
  match request with
  | .inspect handle var =>
      ⟨rich.2.productions,
        (decideReply source.requirement source.history.targets handle var none).message⟩
  | .propose handle var value =>
      ⟨rich.2.productions,
        (decideReply source.requirement source.history.targets handle var (some value)).message⟩
  | .advance _ => rich.2
  | .obtain _ _ => rich.2
'''
    theorem_name = name + '_exact'
    theorem = f'''theorem {theorem_name} {{input : Nat}} {{master : UnifiedMaster.Instance input}}
    (source : Source master) (request : Request) :
    {name} source request = (sourcePerform source request).2 := by
  cases request with
  | advance count => rfl
  | inspect handle var =>
      show Event.mk [] (decideReply source.requirement source.history.targets handle var none).message =
        Event.mk [] (decideReply source.requirement
          source.history.realization.materialRegister handle var none).message
      rw [source.history.realization.materialRegister_exact]
  | propose handle var value =>
      show Event.mk []
          (decideReply source.requirement source.history.targets handle var (some value)).message =
        Event.mk [] (decideReply source.requirement
          source.history.realization.materialRegister handle var (some value)).message
      rw [source.history.realization.materialRegister_exact]
  | obtain handle var => rfl
'''
    proof = f'{theorem_name} source request'
    return install_bridge_event(files, definition, theorem, f'{name} source request', proof,
                                f'Prod.ext rfl ({proof})')


def exact_event_reconstruction(files):
    definition = '''def auditExactEventReconstruction {input : Nat}
    {master : UnifiedMaster.Instance input} (source : Source master)
    (request : Request) : Event :=
  let rich := sourcePerform source request
  ⟨rich.2.productions, rich.2.message⟩
'''
    theorem = '''theorem auditExactEventReconstruction_exact {input : Nat}
    {master : UnifiedMaster.Instance input} (source : Source master)
    (request : Request) :
    auditExactEventReconstruction source request = (sourcePerform source request).2 := rfl
'''
    proof = 'auditExactEventReconstruction_exact source request'
    return install_bridge_event(files, definition, theorem,
        'auditExactEventReconstruction source request', proof, f'Prod.ext rfl ({proof})')


def independent_next_on_static_requests(files):
    definition = '''def auditMixedNext {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) : Source master :=
  let rich := sourcePerform source request
  match request with
  | .inspect _ _ => source
  | .propose _ _ _ => source
  | .advance _ => rich.1
  | .obtain _ _ => rich.1

theorem auditMixedNext_exact {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) :
    auditMixedNext source request = (sourcePerform source request).1 := by
  cases request <;> rfl

'''
    text = replace_once(files[AGREEMENT], 'def bridge {input : Nat}',
                        definition + 'def bridge {input : Nat}')
    text = replace_once(text,
        'sourceNext := fun source request => (sourcePerform source request).1',
        'sourceNext := fun source request => auditMixedNext source request')
    text = replace_once(text,
        'nextLaw := fun source request => congrArg Prod.fst (sourcePerform_exact source request)',
        'nextLaw := fun source request =>\n'
        '    (congrArg project (auditMixedNext_exact source request)).trans\n'
        '      (congrArg Prod.fst (sourcePerform_exact source request))')
    text = replace_once(text,
        'bridgeSourceNext master source request = (sourcePerform source request).1 := rfl',
        'bridgeSourceNext master source request = (sourcePerform source request).1 :=\n'
        '  auditMixedNext_exact source request')
    text = replace_once(text, '/- AXIOM_AUDIT_END -/',
        '#print axioms ConstitutiveSearch.Agent.auditMixedNext\n'
        '#print axioms ConstitutiveSearch.Agent.auditMixedNext_exact\n'
        '/- AXIOM_AUDIT_END -/')
    persistence = replace_once(files[PERSISTENCE],
        'bridgeRichResult := fun _ _ => rfl',
        'bridgeRichResult := fun source request =>\n'
        '      Prod.ext (auditMixedNext_exact source request) rfl')
    return {AGREEMENT: text, PERSISTENCE: persistence}


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
        ('C1-exactness-payload-erased', V1.erase_references, 'root-reject',
         ('Tactic `rfl` failed', "tactic 'rfl' failed")),
        ('C3-absence-payload-erased', V1.erase_absence, 'root-reject',
         ('Tactic `rfl` failed', "tactic 'rfl' failed")),
        ('C2-runtime-source-with-semantic-proofs', V1.runtime_bridge, 'compiled-reject',
         ('AGENT_BRIDGE_FAILED: sourceEvent:',)),
        ('C2-unused-rich-observer', V1.runtime_bridge_unused_observer, 'compiled-reject',
         ('AGENT_BRIDGE_FAILED: sourceEvent:',)),
        ('C2-legitimate-rich-helper', V1.rich_helper, 'accept', ()),
        ('C2e-rich-productions-projected-message', c2e_projected_message, 'compiled-reject',
         ('AGENT_BRIDGE_FAILED: sourceEvent:',)),
        ('C2e-projection-hidden-in-helper', lambda files: c2e_projected_message(files, True),
         'compiled-reject', ('AGENT_BRIDGE_FAILED: sourceEvent:',)),
        ('C2-exact-event-reconstruction', exact_event_reconstruction, 'accept', ()),
        ('C2-independent-next-on-static-requests', independent_next_on_static_requests,
         'compiled-reject', ('AGENT_BRIDGE_FAILED: sourceNext:',))]

    patches = {}
    for name, transform, expected, diagnostics in cases:
        changed = transform(frozen)
        patch = ''
        for path, new in changed.items():
            old = (snapshot / path).read_text(encoding='utf-8')
            patch += ''.join(difflib.unified_diff(old.splitlines(keepends=True),
                new.splitlines(keepends=True), fromfile='a/' + path, tofile='b/' + path))
        patch_path = output / (name + '.patch')
        patch_path.write_text(patch, encoding='utf-8', newline='')
        patches[name] = patch_path
    protocol = {'version': 2, 'reference_head': head,
        'script_sha256': sha(Path(__file__)),
        'v1_script_sha256': sha(ROOT / 'scripts/test-agent-contract-links.py'),
        'checker_sha256': sha(ROOT / 'scripts/check-agent-codegen.py'),
        'provenance_checker_sha256': sha(ROOT / 'scripts/agent_codegen_provenance.py'),
        'provenance_selftest_sha256': sha(ROOT / 'scripts/test-agent-codegen-provenance.py'),
        'python': sys.version, 'platform': platform.platform(), 'source_sha256': before,
        'cases': [{'name': name, 'expectation': expectation,
                   'diagnostics': diagnostics, 'patch_sha256': sha(patches[name])}
                  for name, _, expectation, diagnostics in cases]}
    (output / 'frozen-protocol.json').write_text(json.dumps(protocol, indent=2) + '\n',
                                                  encoding='utf-8')

    subprocess.run(['git', 'clone', '--shared', '--no-hardlinks', '--no-checkout',
                    str(ROOT), str(scratch)], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    subprocess.run(['git', 'checkout', '--detach', head], cwd=scratch, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    for name in paths:
        target = scratch / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(snapshot / name, target)
    shutil.copytree(ROOT / '.lake', scratch / '.lake', symlinks=False)

    def run(label, command, timeout=1200):
        log = output / (label + '.log')
        environment = os.environ.copy()
        environment['RELATIONAL_PERIMETER_PYTHON'] = sys.executable
        with log.open('wb') as stream:
            try:
                result = subprocess.run(command, cwd=scratch, stdout=stream,
                                        stderr=subprocess.STDOUT, timeout=timeout,
                                        env=environment)
            except subprocess.TimeoutExpired as error:
                raise RuntimeError('Timeout is NOT a valid rejection: ' + label) from error
        record = {'label': label, 'command': command, 'exit': result.returncode,
                  'log_sha256': sha(log)}
        with (output / 'commands.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(json.dumps(record) + '\n')
        return result.returncode, log.read_text(encoding='utf-8', errors='replace')

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
            for path in frozen:
                shutil.copy2(snapshot / path, scratch / path)
            subprocess.run(['git', 'apply', '--whitespace=nowarn', '-'], cwd=scratch,
                           input=patches[name].read_bytes(), check=True)
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
                code, log = run(name + '-codegen',
                                [sys.executable, '-B', 'scripts/check-agent-codegen.py'])
                if expected == 'compiled-reject':
                    if not code or not any(marker in log for marker in diagnostics):
                        raise RuntimeError('Origin substitution not rejected: ' + name)
                elif code:
                    raise RuntimeError('Legitimate exact-origin form rejected: ' + name)
                if name == 'C2e-rich-productions-projected-message':
                    for verifier, command in (
                            ('verify-sh', ['bash', 'scripts/verify.sh']),
                            ('verify-ps1', ['pwsh', '-NoProfile', '-File', 'scripts/verify.ps1'])):
                        vcode, vlog = run(name + '-' + verifier, command)
                        if not vcode or not any(marker in vlog for marker in diagnostics):
                            raise RuntimeError(verifier + ' did not reject C2e at exact-origin gate')
            results.append({'name': name, 'result': expected, 'matched': True})
            print('CONTRACT_LINK_V2_CASE_OK ' + name + ': ' + expected, flush=True)
    finally:
        after = {name: sha(ROOT / name) for name in paths}
        unchanged = before == after
        (output / 'results.json').write_text(json.dumps(
            {'cases': results, 'reference_unchanged': unchanged}, indent=2) + '\n',
            encoding='utf-8')
        if not unchanged:
            raise RuntimeError('Reference changed during campaign')
    print('AGENT_CONTRACT_LINKS_V2_OK: 9 coherent cases; C2e rejected by both verifiers; '
          'reference unchanged', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print('AGENT_CONTRACT_LINKS_V2_FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
