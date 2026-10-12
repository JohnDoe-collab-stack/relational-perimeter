#!/usr/bin/env python3
"""Independent component fixtures: whole measured assignment and paid queries.

Golden bits, both work fields and complete paid traces are derived separately
before runtime. These local fixtures do not qualify interpreter administration.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
RECIPES = ((), ('visit',), (0,), (1,), (2,), (17,), (2, 2),
           ('visit', 2, 'visit'), (3, 1, 2))
QUERIES = (0, 1, 2, 3, 17, 41, 42, 257)


def golden(recipe, query):
    # Independent closed arithmetic, not a call to the controlled producer.
    nodes, steps = max(1, query), 0
    bit = query == 0 or query % 2 == 1
    trace = [0] * max(1, query) + [1] * max(0, query - 1)
    for command in reversed(recipe):
        if command == 'visit':
            trace = [0] + trace + [1]
            nodes += 1
        else:
            minimum = min(query, command)
            comparison = [2] * (minimum + 1) + [3] * minimum
            additions = ([4] * (nodes + 1) + [5] * nodes +
                         [4] * (steps + 1) + [5] * steps + [6])
            trace = [0] + comparison + trace + additions + [1]
            bit ^= query == command
            nodes += 1
            steps += minimum + 1
    return bit, nodes, steps, trace


PREAMBLE = r'''
import Tests.LocalAlignment.DocumentaryControlMeasuredAssignmentReader
import Tests.LocalAlignment.DocumentaryCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 65536
set_option maxHeartbeats 50000000
namespace MeasuredReaderSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings ControlMeasuredAssignmentReader

def tag : Label → Nat
  | .assignmentQueryCell => 0
  | .assignmentQueryReturn => 1
  | .naturalComparison => 2
  | .masterConstructionReturn => 3
  | .integerNaturalCell => 4
  | .integerNaturalReturn => 5
  | .masterWorkPacket => 6
  | .controlClosure => 7
  | .executionPayload => 8
  | .controlInspect => 9
  | _ => 999

structure Fixture where
  recipe : PortableAssignment.Code
  query : Var
  bit : Bool
  nodes : Nat
  steps : Nat
  trace : List Nat

def probe (fixture : Fixture) : Bool :=
  let formation := formedCode
    (⟨fixture.recipe, rfl⟩ : PortableAssignment.Formed (PortableAssignment.interpret fixture.recipe))
  let formationCost := 2 * (fixture.recipe.length + 1) + 1
  match execute formationCost formation, execute (formationCost - 1) formation,
      execute (formationCost + 13) formation with
  | some reader, none, some surplusReader =>
    reader.labels.map tag == List.replicate (fixture.recipe.length + 1) 9 ++
      List.replicate (fixture.recipe.length + 1) 7 ++ [8] &&
    reader.labels.map tag == surplusReader.labels.map tag &&
    let code := reader.value.queryCode fixture.query
    let cost := fixture.trace.length
    match execute cost code, execute (cost - 1) code, execute (cost + 13) code,
        execute cost (surplusReader.value.queryCode fixture.query) with
    | some actual, none, some surplus, some other =>
        actual.labels.map tag == fixture.trace && actual.labels.length == cost &&
        surplus.labels.map tag == fixture.trace && other.labels.map tag == fixture.trace &&
        actual.value.1.value == fixture.bit && actual.value.1.work.nodes == fixture.nodes &&
        actual.value.1.work.labelSteps == fixture.steps &&
        surplus.value.1.value == fixture.bit && surplus.value.1.work.nodes == fixture.nodes &&
        surplus.value.1.work.labelSteps == fixture.steps &&
        other.value.1.value == fixture.bit && other.value.1.work.nodes == fixture.nodes &&
        other.value.1.work.labelSteps == fixture.steps
    | _, _, _, _ => false
  | _, _, _ => false
'''
POSTAMBLE = r'''
def run : IO Unit := do
  if fixtures.length != 72 || fixtures.any (fun fixture => !(probe fixture)) then
    throw (IO.userError "Measured Reader mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_MEASURED_READER_SMOKE_DONE\n").toArray⟩
end MeasuredReaderSmoke
def main : IO Unit := MeasuredReaderSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms MeasuredReaderSmoke.tag
#print axioms MeasuredReaderSmoke.Fixture
#print axioms MeasuredReaderSmoke.probe
#print axioms MeasuredReaderSmoke.fixtures
#print axioms MeasuredReaderSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
'''


def client():
    rows = []
    for recipe in RECIPES:
        commands = ', '.join('.visit' if value == 'visit' else f'.flip {value}'
                             for value in recipe)
        for query in QUERIES:
            bit, nodes, steps, trace = golden(recipe, query)
            labels = ', '.join(map(str, trace))
            rows.append(f'  ⟨[{commands}], {query}, {str(bit).lower()}, {nodes}, {steps}, [{labels}]⟩')
    return PREAMBLE + '\ndef fixtures : List Fixture := [\n' + ',\n'.join(rows) + ']\n' + POSTAMBLE


def main():
    source = client().encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-measured-reader-') as directory:
        path = Path(directory) / 'Smoke.lean'
        path.write_bytes(source)
        result = subprocess.run(['lake', 'env', 'lean', '-Dcompiler.extract_closed=false', '--run', str(path)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode('utf-8', 'replace'))
    expected = {("'MeasuredReaderSmoke." + name + "' does not depend on any axioms").encode()
                for name in ('tag', 'Fixture', 'probe', 'fixtures', 'run')}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_MEASURED_READER_SMOKE_DONE'))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError('Unexpected runtime output: ' + result.stdout.decode('utf-8', 'replace'))
    print('DOCUMENTARY_MEASURED_READER_SMOKE_OK: 72 component fixtures; whole bit/nodes/labelSteps; '
          'actual formed readers; fixed complete local traces; exact/short/surplus fuel; six clean audits; '
          'client_sha256=' + hashlib.sha256(source).hexdigest())


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_MEASURED_READER_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
