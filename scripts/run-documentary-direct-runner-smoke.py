#!/usr/bin/env python3
"""Independent fixed AST interpreter goldens for the terminal administrative runner.

The Python model never asks Lean for a cost or expectation. It preserves each
intrinsic event and counts native forwarding layers in compact admin blocks.
The tape is flattened only by observation, never by a documentary consumer.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
EVENTS = ('compose', 'call', 'closure', 'frame', 'trace', 'result', 'allocation')
EVENT_TAGS = dict(zip(EVENTS, (88, 87, 89, 90, 91, 93, 25)))


def done(value):
    return ('done', value)


def step(label, child):
    return ('step', label, child)


def admin(event, child, forwards=0):
    return ('admin', event, child, forwards)


def bind_forward(code, continuation):
    if code[0] == 'done':
        return admin('call', continuation(code[1]))
    if code[0] == 'step':
        return admin('closure', step(code[1], bind(code[2], continuation)))
    return admin(code[1], bind_forward(code[2], continuation), code[3] + 1)


def bind(code, continuation):
    return admin('compose', bind_forward(code, continuation))


def golden(code, source_fuel):
    if code[0] == 'done':
        return code[1], [], [86, 91, 92, 93]
    if code[0] == 'step' and source_fuel == 0:
        return None, [], [86, 93]
    is_step = code[0] == 'step'
    value, business, tape = golden(code[2], source_fuel - int(is_step))
    prefix = [86, code[1] if is_step else EVENT_TAGS[code[1]], 87, 90]
    if not is_step:
        prefix += [86, 87, 89] * code[3]
    if value is None:
        return None, [], prefix + tape + [93]
    return (value, ([code[1]] + business) if is_step else business,
            prefix + tape + ([90, 91, 92, 93] if is_step else [90, 92, 93]))


def path_golden(code, source_fuel):
    if code[0] == 'done':
        return [(0, 0, 0)]
    if code[0] == 'step' and source_fuel == 0:
        return [(1, 0, 0)]
    if code[0] == 'step':
        return [(2, code[1], 0)] + path_golden(code[2], source_fuel - 1)
    return [(3, EVENT_TAGS[code[1]], code[3])] + path_golden(code[2], source_fuel)


RECIPES = (
    ('done', done(42), '.done 42'),
    ('one', step(0, done(7)), '.step .instruction (fun _ => .done 7)'),
    ('two', step(0, step(1, done(42))), '.step .instruction (fun _ => .step .binding (fun _ => .done 42))'),
    ('bindDone', bind(done(41), lambda _: step(1, done(42))),
     '(.done 41 : Code Label Nat).bind (fun _ => .step .binding (fun _ => .done 42))'),
    ('bindStep', bind(step(0, done(41)), lambda _: step(1, done(42))),
     '(.step .instruction (fun _ => .done 41) : Code Label Nat).bind (fun _ => .step .binding (fun _ => .done 42))'),
    ('nested', bind(bind(step(0, done(40)), lambda _: step(1, done(41))), lambda _: step(23, done(42))),
     '((.step .instruction (fun _ => .done 40) : Code Label Nat).bind (fun _ => .step .binding (fun _ => .done 41))).bind (fun _ => .step .formationValues (fun _ => .done 42))'),
) + tuple((event, admin(event, step(0, done(42)), forwards),
           '.admin .' + event + ' (fun _ => .step .instruction (fun _ => .done 42)) ' + str(forwards))
          for forwards in (0, 3) for event in EVENTS)


def deep_recipes():
    code, lean = done(42), '(.done 42 : Code Label Nat)'
    rows = []
    for depth in range(13):
        node, events, forwards = code, 0, 0
        while node[0] != 'done':
            assert node[0] == 'admin'
            events += 1
            forwards += node[3]
            node = node[2]
        assert events == 2 * depth and forwards == depth * (depth - 1)
        value, business, tape = golden(code, 0)
        assert value == 42 and business == []
        assert len(tape) == 4 + 14 * depth + 3 * depth * (depth - 1)
        rows.append(('identityDepth' + str(depth), code, lean))
        code = bind(code, done)
        lean = '(' + lean + ').bind (fun value => .done value)'
    return tuple(rows)


RECIPES += deep_recipes()


def deep_business_recipes():
    code, lean = done(42), '(.done 42 : Code Label Nat)'
    for _ in range(4):
        code = step(0, code)
        lean = '(.step .instruction (fun _ => ' + lean + ') : Code Label Nat)'
    plain = ('businessFour', code, lean)
    for _ in range(8):
        code = bind(code, done)
        lean = '(' + lean + ').bind (fun value => .done value)'
    value, business, _ = golden(code, 5)
    assert value == 42 and business == [0, 0, 0, 0]
    return (plain, ('businessFourIdentityDepth8', code, lean))


RECIPES += deep_business_recipes()
SOURCE_FUELS = (0, 1, 2, 5)
FIXTURE_COUNT = len(RECIPES) * len(SOURCE_FUELS)
CLIENT = r'''
import Tests.LocalAlignment.DocumentaryControlCompactExecution
import Tests.LocalAlignment.DocumentaryCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000000
namespace DirectRunnerSmoke
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings

def tag : Label → Nat
  | .instruction => 0 | .binding => 1 | .formationValues => 23 | .formationResources => 25
  | .controlInspect => 86 | .controlCall => 87 | .controlCompose => 88
  | .controlClosure => 89 | .controlFrame => 90 | .controlTrace => 91
  | .controlWitness => 92 | .controlResult => 93 | _ => 999

structure Fixture where
  sourceFuel : Nat
  code : Code Label Nat
  value : Option Nat
  business : List Nat
  tape : List Nat
  path : List (Nat × Nat × Nat)

def pathTags : ControlCompactData.Path → List (Nat × Nat × Nat)
  | .done => [(0, 0, 0)]
  | .stop => [(1, 0, 0)]
  | .business label child => (2, tag label, 0) :: pathTags child
  | .administrative event forwards child =>
      (3, tag (ControlRunner.eventLabel event), forwards) :: pathTags child

def observation {code : Code Label Nat} {fuel budget}
    (actual : ControlCompactExecution.Run code fuel budget) (fixture : Fixture) : Bool :=
  actual.output.map (fun result => result.value) == fixture.value &&
    actual.output.map (fun result => result.labels.map tag) ==
      (fixture.value.map (fun _ => fixture.business)) &&
    actual.tape.labels.map tag == fixture.tape &&
    actual.tape.cost == fixture.tape.length && pathTags actual.path == fixture.path

def probe (fixture : Fixture) : Bool :=
  let cost := fixture.tape.length
  match ControlCompactExecution.execute fixture.sourceFuel cost fixture.code,
      ControlCompactExecution.execute fixture.sourceFuel (cost - 1) fixture.code,
      ControlCompactExecution.execute fixture.sourceFuel (cost + 17) fixture.code,
      ControlCompactExecution.execute fixture.sourceFuel 0 fixture.code with
  | some exact, none, some more, none =>
    observation exact fixture && observation more fixture &&
      exact.remaining == 0 && more.remaining == 17
  | _, _, _, _ => false

__FIXTURES__

def run : IO Unit := do
  if fixtures.length != __FIXTURE_COUNT__ || !fixtures.all probe then
    throw (IO.userError "Direct runner fixed AST mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_DIRECT_RUNNER_SMOKE_DONE\n").toArray⟩
end DirectRunnerSmoke
def main : IO Unit := DirectRunnerSmoke.run
#print axioms DirectRunnerSmoke.tag
#print axioms DirectRunnerSmoke.Fixture
#print axioms DirectRunnerSmoke.pathTags
#print axioms DirectRunnerSmoke.observation
#print axioms DirectRunnerSmoke.probe
#print axioms DirectRunnerSmoke.fixtures
#print axioms DirectRunnerSmoke.run
#print axioms main
'''


def client():
    rows = []
    for name, code, lean in RECIPES:
        for fuel in SOURCE_FUELS:
            value, business, tape = golden(code, fuel)
            value_literal = 'none' if value is None else '(some ' + str(value) + ')'
            business_literal = '[' + ', '.join(map(str, business)) + ']'
            tape_literal = '[' + ', '.join(map(str, tape)) + ']'
            path_literal = '[' + ', '.join('(' + ', '.join(map(str, row)) + ')'
                                           for row in path_golden(code, fuel)) + ']'
            rows.append(f'  -- {name}, source fuel {fuel}\n  ⟨{fuel}, {lean}, {value_literal}, {business_literal}, {tape_literal}, {path_literal}⟩')
    return (CLIENT.replace('__FIXTURES__', 'def fixtures : List Fixture := [\n' + ',\n'.join(rows) + ']')
            .replace('__FIXTURE_COUNT__', str(FIXTURE_COUNT)))


def main():
    source = client().encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-d2-direct-runner-') as directory:
        path = Path(directory) / 'Smoke.lean'
        path.write_bytes(source)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(path)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    expected = {b"'DirectRunnerSmoke." + name.encode() + b"' does not depend on any axioms"
                for name in ('tag', 'Fixture', 'pathTags', 'observation', 'probe', 'fixtures', 'run')}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_DIRECT_RUNNER_SMOKE_DONE'))
    if result.returncode or result.stderr or set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != 9:
        raise ValueError((result.stdout + result.stderr).decode('utf-8', 'replace'))
    print(f'DOCUMENTARY_DIRECT_RUNNER_SMOKE_OK: {FIXTURE_COUNT} independent fixed AST/source-fuel fixtures; '
          'all seven admin events, 0/3 forwards and identity bind depths 0..12; '
          '2n retained events, n(n-1) paid forwards; whole value, business trace and administrative tape; '
          'source stop and propagated failure; exact/short/surplus/zero final fuel; exact remaining budget; '
          'positive executed path matches independent AST including stop/event/forward count; '
          'eight clean audits; client_sha256=' + hashlib.sha256(source).hexdigest())


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_DIRECT_RUNNER_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
