#!/usr/bin/env python3
"""Independent development probes of metered assignment requests.
Source constants, repeated and mixed flips, selected and other large queries.
Forming a reader and invoking it have separate frozen costs.

The source interpreter is ControlCompactExecution.sourceExecute; its general
source_exact refinement preserves the whole value, business labels and fuel.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryControlCompactExecution
import Tests.LocalAlignment.DocumentaryControlAssignmentApplication
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
namespace AssignmentApplicationSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings ControlMasterData ControlAssignmentApplication

def tag : Label → Nat
  | .naturalComparison => 5
  | .formationResources => 25
  | .controlClosure => 89
  | .assignmentQueryCell => 112
  | .assignmentQueryReturn => 113
  | _ => 999

def count (wanted : Nat) (labels : List Label) : Nat :=
  (labels.filter (fun label => tag label == wanted)).length

def expect (value : Bool) (selects : List Var) (query : Var) : Bool :=
  match selects with
  | [] => value
  | selected :: rest => expect (if query == selected then !value else value) rest query

def compareCost (selects : List Var) (query : Var) : Nat :=
  match selects with
  | [] => 0
  | selected :: rest => Nat.min query selected + 1 + compareCost rest query

def queryProbe {assignment : Assignment} (reader : Reader assignment)
    (selectors : List Var) (query : Var) (wanted : Bool) : Bool :=
  let program := reader.readCode query
  let comparisons := compareCost selectors query
  let exactCost := 1 + selectors.length * 2 + comparisons
  match ControlCompactExecution.sourceExecute exactCost program, ControlCompactExecution.sourceExecute (exactCost - 1) program,
      ControlCompactExecution.sourceExecute (exactCost + 7) program, ControlCompactExecution.sourceExecute (reader.queryBound query) program with
  | some actual, none, some surplus, some uniform =>
      actual.value.1 == wanted && surplus.value.1 == wanted && uniform.value.1 == wanted &&
      actual.labels.length == exactCost && exactCost <= reader.queryBound query &&
      actual.labels.map tag == surplus.labels.map tag && actual.labels.map tag == uniform.labels.map tag &&
      count 112 actual.labels == selectors.length + 1 &&
      count 113 actual.labels == selectors.length && count 5 actual.labels == comparisons &&
      !(actual.labels.map tag).contains 999
  | _, _, _, _ => false

def probe (value : Bool) (queries : List Var) : Bool :=
  let initial := constantReader value
  let one := flippedReader 41 initial
  let repeated := flippedReader 41 one
  let mixed := flippedReader 42 (flippedReader 0 one)
  queries.all (fun query =>
    queryProbe initial [] query value &&
    queryProbe one [41] query (expect value [41] query) &&
    queryProbe repeated [41,41] query (expect value [41,41] query) &&
    queryProbe mixed [41,0,42] query (expect value [41,0,42] query))

def formationProbe (value : Bool) : Bool :=
  match ControlCompactExecution.sourceExecute 3 (constantReaderCode value), ControlCompactExecution.sourceExecute 2 (constantReaderCode value),
      ControlCompactExecution.sourceExecute 10 (constantReaderCode value) with
  | some actual, none, some surplus =>
    let program := flipReaderCode 41 actual.value.1
    match ControlCompactExecution.sourceExecute 3 program, ControlCompactExecution.sourceExecute 2 program, ControlCompactExecution.sourceExecute 10 program with
    | some flipped, none, some more =>
      actual.labels.map tag == [89,89,25] && surplus.labels.map tag == actual.labels.map tag &&
      flipped.labels.map tag == [89,89,25] && more.labels.map tag == flipped.labels.map tag &&
      queryProbe flipped.value.1 [41] 41 (!value) &&
      queryProbe more.value.1 [41] 257 value &&
      queryProbe surplus.value.1 [] 42 value
    | _, _, _ => false
  | _, _, _ => false

def run : IO Unit := do
  let queries := [0,1,2,17,41,42,257]
  let checks := [probe false queries, probe true queries, formationProbe false, formationProbe true]
  if checks.length != 4 || checks.any (fun passed => !passed) then
    throw (IO.userError "Assignment application mismatch")
  let stdout ← IO.getStdout
  stdout.write "DOCUMENTARY_ASSIGNMENT_APPLICATION_SMOKE_DONE\n".toUTF8
end AssignmentApplicationSmoke

def main : IO Unit := AssignmentApplicationSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms AssignmentApplicationSmoke.tag
#print axioms AssignmentApplicationSmoke.count
#print axioms AssignmentApplicationSmoke.expect
#print axioms AssignmentApplicationSmoke.compareCost
#print axioms AssignmentApplicationSmoke.queryProbe
#print axioms AssignmentApplicationSmoke.probe
#print axioms AssignmentApplicationSmoke.formationProbe
#print axioms AssignmentApplicationSmoke.run
#print axioms main
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
"""
NAMES = ('tag', 'count', 'expect', 'compareCost', 'queryProbe', 'probe', 'formationProbe', 'run')

def main():
    source = CLIENT.encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-assignment-application-') as directory:
        client = Path(directory) / 'Smoke.lean'
        client.write_bytes(source)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode('utf-8', 'replace'))
    expected = {("'AssignmentApplicationSmoke." + name + "' does not depend on any axioms").encode()
                for name in NAMES}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_ASSIGNMENT_APPLICATION_SMOKE_DONE'))
    expected.add(b"'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact' does not depend on any axioms")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError('Unexpected runtime output: ' + result.stdout.decode('utf-8', 'replace'))
    print('DOCUMENTARY_ASSIGNMENT_APPLICATION_SMOKE_OK: fifty-six query fixtures, six formation/query observations; '
          'false/true source, repeated/mixed flips, selected/other queries including41/42/257; '
          'exact/short/surplus/uniform fuel; ten clean runtime audits; client_sha256=' +
          hashlib.sha256(source).hexdigest())

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_ASSIGNMENT_APPLICATION_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
