#!/usr/bin/env python3
"""Independent whole measured transport/reader composition fixtures.

Formation traces and reader recipes are fixed before execution. The actual
returned reader is queried; no native readout supplies the controlled result.
"""
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
QUERIES = (0, 1, 2, 3, 17, 41, 42, 257)
ATOM = [86, 87, 89, 75, 89, 75]
FORMS = (
    (0, ('visit',), [86, 89, 75], 0),
    (1, (0,), ATOM, 1),
    (2, ('visit', 0, 0), [86] + ATOM + ATOM + [17, 17, 18] * 2 + [89, 75], 2),
    (3, ('visit', 'visit', 0, 0, 'visit'),
     [86, 86, 89, 75, 86] + ATOM + ATOM + [17, 17, 18] * 2 + [89, 75] +
     [17, 17, 17, 18, 18] * 2 + [89, 75], 2),
)

PREAMBLE = r'''
import Tests.LocalAlignment.DocumentaryControlMeasuredTransportReader
import Tests.LocalAlignment.DocumentaryCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 65536
set_option maxHeartbeats 50000000
namespace MeasuredTransportReaderSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings ControlMeasuredAssignmentReader

def root : GeneratedStructuralBranchContext [] := GeneratedStructuralBranchContext.root []
def source : GeneratedStructuralBranchContext [] := root.child 0 true True.intro
def target : GeneratedStructuralBranchContext [] := root.child 0 false True.intro
def received : GeneratedStructuralBranchContinuation source :=
  ⟨alternatingAssignmentBit, ⟨rfl, True.intro⟩⟩
def first : GeneratedStructuralFlipAtRelation 0 source target := ⟨rfl, rfl⟩
def second : GeneratedStructuralFlipAtRelation 0 target source := ⟨rfl, rfl⟩
def doubled : TransportCode (GeneratedStructuralFlipAtRelation 0) source source :=
  .compose (.atom first) (.atom second)

def tag : Label → Nat
  | .assignmentQueryCell => 0
  | .assignmentQueryReturn => 1
  | .naturalComparison => 2
  | .masterConstructionReturn => 75
  | .integerNaturalCell => 17
  | .integerNaturalReturn => 18
  | .masterWorkPacket => 73
  | .controlInspect => 86
  | .controlCall => 87
  | .controlClosure => 89
  | _ => 999

structure Fixture where
  kind : Nat
  query : Var
  bit : Bool
  nodes : Nat
  steps : Nat
  formation : List Nat
  trace : List Nat
  atoms : Nat

def queryProbe {assignment : Assignment} {original : MeasuredAssignment assignment}
    (reader : Reader original) (fixture : Fixture) : Bool :=
  let code := reader.queryCode fixture.query
  let fuel := fixture.trace.length
  match execute fuel code, execute (fuel - 1) code, execute (fuel + 13) code with
  | some actual, none, some more =>
    actual.labels.map tag == fixture.trace && more.labels.map tag == fixture.trace &&
    actual.value.1.value == fixture.bit && more.value.1.value == fixture.bit &&
    actual.value.1.work.nodes == fixture.nodes && more.value.1.work.nodes == fixture.nodes &&
    actual.value.1.work.labelSteps == fixture.steps && more.value.1.work.labelSteps == fixture.steps
  | _, _, _ => false

def probe {endpoint : GeneratedStructuralBranchContext []}
    (program : TransportCode (GeneratedStructuralFlipAtRelation 0) source endpoint)
    (fixture : Fixture) : Bool :=
  let code := ControlMeasuredTransportReader.code 0 program received readAlternatingAssignment alternatingReader
  let fuel := fixture.formation.length
  match execute fuel code, execute (fuel - 1) code, execute (fuel + 13) code with
  | some actual, none, some more =>
    actual.labels.map tag == fixture.formation && more.labels.map tag == fixture.formation &&
    actual.value.run.1.evaluatedAtoms == fixture.atoms &&
    actual.value.run.1.continuationApplications == fixture.atoms &&
    more.value.run.1.evaluatedAtoms == fixture.atoms &&
    more.value.run.1.continuationApplications == fixture.atoms &&
    queryProbe actual.value.reader fixture && queryProbe more.value.reader fixture
  | _, _, _ => false

def check (fixture : Fixture) : Bool :=
  match fixture.kind with
  | 0 => probe (.identity source) fixture
  | 1 => probe (.atom first) fixture
  | 2 => probe doubled fixture
  | 3 => probe (.compose (.identity source) doubled) fixture
  | _ => false
'''
POSTAMBLE = r'''
def run : IO Unit := do
  if fixtures.length != 32 || fixtures.any (fun fixture => !(check fixture)) then
    throw (IO.userError "Measured transport/reader mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_MEASURED_TRANSPORT_READER_SMOKE_DONE\n").toArray⟩
end MeasuredTransportReaderSmoke
def main : IO Unit := MeasuredTransportReaderSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms MeasuredTransportReaderSmoke.root
#print axioms MeasuredTransportReaderSmoke.source
#print axioms MeasuredTransportReaderSmoke.target
#print axioms MeasuredTransportReaderSmoke.received
#print axioms MeasuredTransportReaderSmoke.first
#print axioms MeasuredTransportReaderSmoke.second
#print axioms MeasuredTransportReaderSmoke.doubled
#print axioms MeasuredTransportReaderSmoke.tag
#print axioms MeasuredTransportReaderSmoke.Fixture
#print axioms MeasuredTransportReaderSmoke.queryProbe
#print axioms MeasuredTransportReaderSmoke.probe
#print axioms MeasuredTransportReaderSmoke.check
#print axioms MeasuredTransportReaderSmoke.fixtures
#print axioms MeasuredTransportReaderSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
'''


def client():
    model = runpy.run_path(str(ROOT / 'scripts/run-documentary-measured-reader-smoke.py'))
    rows = []
    for kind, recipe, formation, atoms in FORMS:
        for query in QUERIES:
            bit, nodes, steps, labels = model['golden'](recipe, query)
            # Translate the independently fixed component alphabet to Label tags.
            mapping = {0: 0, 1: 1, 2: 2, 3: 75, 4: 17, 5: 18, 6: 73}
            trace = ', '.join(str(mapping[label]) for label in labels)
            formed = ', '.join(map(str, formation))
            rows.append(f'  ⟨{kind}, {query}, {str(bit).lower()}, {nodes}, {steps}, [{formed}], [{trace}], {atoms}⟩')
    return PREAMBLE + '\ndef fixtures : List Fixture := [\n' + ',\n'.join(rows) + ']\n' + POSTAMBLE


def main():
    source = client().encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-measured-transport-reader-') as directory:
        path = Path(directory) / 'Smoke.lean'
        path.write_bytes(source)
        result = subprocess.run(['lake', 'env', 'lean', '-Dcompiler.extract_closed=false', '--run', str(path)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode('utf-8', 'replace'))
    names = ('root', 'source', 'target', 'received', 'first', 'second', 'doubled', 'tag',
             'Fixture', 'queryProbe', 'probe', 'check', 'fixtures', 'run')
    expected = {("'MeasuredTransportReaderSmoke." + name + "' does not depend on any axioms").encode()
                for name in names}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_MEASURED_TRANSPORT_READER_SMOKE_DONE'))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError('Unexpected runtime output: ' + result.stdout.decode('utf-8', 'replace'))
    print('DOCUMENTARY_MEASURED_TRANSPORT_READER_SMOKE_OK: 32 component fixtures; identity/atom/'
          'double/nested composition; fixed whole work and local traces; actual returned readers; '
          'exact/short/surplus fuel; fifteen clean audits; client_sha256=' + hashlib.sha256(source).hexdigest())


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_MEASURED_TRANSPORT_READER_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
