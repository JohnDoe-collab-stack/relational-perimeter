#!/usr/bin/env python3
"""Two actual master heads share the measured reader through their cursor.

The test ceiling is not a bootstrap bound. Query expectations are independent
literal recipes (flip 10, then flip 12), including both original work fields.
The compact source consumer preserves the whole value, business labels and
fuel by the general source_exact theorem; all head and query replays remain.
"""
import hashlib
from pathlib import Path
import runpy
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
QUERIES = (0, 1, 10, 12, 17, 42)
RECIPES = ((10,), (12, 10))
PREAMBLE = r'''
import Tests.LocalAlignment.DocumentaryControlCompactExecution
import Tests.LocalAlignment.DocumentaryControlMasterHeadReader
import Tests.LocalAlignment.DocumentaryMasterCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 65536
set_option maxHeartbeats 100000000
namespace MasterReaderSmoke
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
  | _ => 999

def isMasterProducer : Label → Bool | .masterProducer => true | _ => false
def isHead : Label → Bool | .masterHeadPacket => true | _ => false
def isDecisionQuery : Label → Bool | .masterNextStateQuery => true | _ => false

structure Fixture where
  stage : Nat
  query : Var
  bit : Bool
  nodes : Nat
  steps : Nat
  trace : List Nat

def queryProbe {assignment : Assignment} {original : MeasuredAssignment assignment}
    (reader : Reader original) (fixture : Fixture) : Bool :=
  let code := reader.queryCode fixture.query
  let fuel := fixture.trace.length
  match ControlCompactExecution.sourceExecute fuel code,
      ControlCompactExecution.sourceExecute (fuel - 1) code,
      ControlCompactExecution.sourceExecute (fuel + 19) code with
  | some actual, none, some more =>
    actual.labels.map tag == fixture.trace && more.labels.map tag == fixture.trace &&
    actual.value.1.value == fixture.bit && more.value.1.value == fixture.bit &&
    actual.value.1.work.nodes == fixture.nodes && more.value.1.work.nodes == fixture.nodes &&
    actual.value.1.work.labelSteps == fixture.steps && more.value.1.work.labelSteps == fixture.steps
  | _, _, _ => false

def headProbe (cursor : MasterResources.Cursor) (reader : Reader cursor.assignment.reader) :
    Option (ControlMasterHeadReader.Produced cursor) :=
  let code := ControlMasterHeadReader.code cursor reader
  match ControlCompactExecution.sourceExecute 300000 code with
  | none => none
  | some actual =>
    -- An exact-trace consistency check, not a precomputed D3 envelope.
    let fuel := actual.labels.length
    match ControlCompactExecution.sourceExecute fuel code,
        ControlCompactExecution.sourceExecute (fuel - 1) code,
        ControlCompactExecution.sourceExecute (fuel + 19) code with
    | some exact, none, some more =>
      if actual.labels.map fullTag != exact.labels.map fullTag ||
          actual.labels.map fullTag != more.labels.map fullTag ||
          (actual.labels.filter isMasterProducer).length != 7 ||
          (actual.labels.filter isHead).length != 1 ||
          (actual.labels.filter isDecisionQuery).length != 1 ||
          actual.value.head.1.next.depth != cursor.depth + 1 then none
      else some actual.value
    | _, _, _ => none
'''
POSTAMBLE = r'''
def check : Bool :=
  match ControlCompactExecution.sourceExecute 3 (formedCode
      (⟨[], rfl⟩ : PortableAssignment.Formed (PortableAssignment.sequential VariableMaster.Example.origin.assignment))) with
  | none => false
  | some initial =>
    match headProbe VariableMaster.Example.origin initial.value with
    | none => false
    | some first =>
      if !(fixtures.filter (fun fixture => fixture.stage == 1)).all (queryProbe first.reader) then false
      else match headProbe first.head.1.next first.reader with
      | none => false
      | some second => (fixtures.filter (fun fixture => fixture.stage == 2)).all (queryProbe second.reader)

def run : IO Unit := do
  if fixtures.length != 12 || !check then throw (IO.userError "Master measured reader mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_MASTER_READER_SMOKE_DONE\n").toArray⟩
end MasterReaderSmoke
def main : IO Unit := MasterReaderSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms MasterReaderSmoke.tag
#print axioms MasterReaderSmoke.fullTag
#print axioms MasterReaderSmoke.isMasterProducer
#print axioms MasterReaderSmoke.isHead
#print axioms MasterReaderSmoke.isDecisionQuery
#print axioms MasterReaderSmoke.Fixture
#print axioms MasterReaderSmoke.queryProbe
#print axioms MasterReaderSmoke.headProbe
#print axioms MasterReaderSmoke.fixtures
#print axioms MasterReaderSmoke.check
#print axioms MasterReaderSmoke.run
#print axioms main
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
'''


def client():
    model = runpy.run_path(str(ROOT / 'scripts/run-documentary-measured-reader-smoke.py'))
    rows = []
    for stage, recipe in enumerate(RECIPES, start=1):
        for query in QUERIES:
            bit, nodes, steps, trace = model['golden'](recipe, query)
            labels = ', '.join(map(str, trace))
            rows.append(f'  ⟨{stage}, {query}, {str(bit).lower()}, {nodes}, {steps}, [{labels}]⟩')
    labels_source = (ROOT / 'Tests/LocalAlignment/DocumentaryControlBindings.lean').read_text(encoding='utf-8')
    enumeration = labels_source.split('inductive Label where', 1)[1].split('\nvariable ', 1)[0]
    names = re.findall(r'^\s*\|\s*(\w+)\s*$', enumeration, re.M)
    full_tag = 'def fullTag : Label → Nat\n' + '\n'.join(
        f'  | .{name} => {index}' for index, name in enumerate(names)) + '\n\n'
    header = PREAMBLE.replace('def tag : Label → Nat', full_tag + 'def tag : Label → Nat')
    return header + '\ndef fixtures : List Fixture := [\n' + ',\n'.join(rows) + ']\n' + POSTAMBLE


def main():
    source = client().encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-master-reader-') as directory:
        path = Path(directory) / 'Smoke.lean'
        path.write_bytes(source)
        result = subprocess.run(['lake', 'env', 'lean', '-Dcompiler.extract_closed=false', '--run', str(path)], cwd=ROOT,
                                capture_output=True, timeout=7200, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode('utf-8', 'replace'))
    names = ('tag', 'fullTag', 'isMasterProducer', 'isHead', 'isDecisionQuery', 'Fixture', 'queryProbe',
             'headProbe', 'fixtures', 'check', 'run')
    expected = {("'MasterReaderSmoke." + name + "' does not depend on any axioms").encode()
                for name in names}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_MASTER_READER_SMOKE_DONE'))
    expected.add(b"'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact' does not depend on any axioms")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError('Unexpected runtime output: ' + result.stdout.decode('utf-8', 'replace'))
    print('DOCUMENTARY_MASTER_READER_SMOKE_OK: same actual master; formed initial reader; '
          'two actual heads; first returned reader feeds second cursor; 12 fixed whole-work/query-trace fixtures; '
          'exact/short/surplus query fuel; thirteen clean audits; test ceiling is not a bootstrap bound; '
          'client_sha256=' + hashlib.sha256(source).hexdigest())


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_MASTER_READER_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
