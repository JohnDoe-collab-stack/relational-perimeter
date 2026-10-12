#!/usr/bin/env python3
"""Fixed whole binding reads and capture from the received paid reader.

Five original occurrences have different references, values and origins. The
capture expectation counts the actual shifted queries and all five returns;
it is fixed before execution and is not a D3 bootstrap algorithm.
The compact source consumer preserves the whole value, business labels and
fuel by the general constructive source_exact theorem.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CAPTURE_TRACE = tuple(label for i in range(5)
                      for label in (86, *([84] * i), *([1] * (i + 1)), 89)) + (86, 23) + (23,) * 5
CLIENT = r'''
import Tests.LocalAlignment.DocumentaryControlCompactExecution
import Tests.LocalAlignment.DocumentaryControlBindingReader
import Tests.LocalAlignment.DocumentaryControlInterpreterCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace BindingReaderSmoke
open ConstitutiveSearch ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Snapshot Control ControlBindings ControlInterpreterCases
def tag : Label → Nat
  | .binding => 1 | .formationValues => 23 | .referenceShift => 84
  | .controlInspect => 86 | .controlClosure => 89 | _ => 999

def observed {spec}
    (table : Bindings ProgramCases.actual.1.store
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
        ProgramCases.revisedSpec, ProgramCases.baselineSpec])
    (slot : Ref [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec] spec)
    (position : Nat) (value : Int) (origins : List Nat) : Bool :=
  let found := table.read slot
  ProgramCases.bindingPosition ProgramCases.actual.1.store found == some position &&
  ProgramCases.bindingValue ProgramCases.actual.1.store found == some value &&
  found.map (fun occurrence => occurrence.1.origins) == some origins

def readProbe {spec}
    (slot : Ref [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec] spec)
    (fuel position : Nat) (value : Int) (origins : List Nat) : Bool :=
  let code := (ControlBindingReader.tableReader finalTable).readCode slot
  match ControlCompactExecution.sourceExecute fuel code,
      ControlCompactExecution.sourceExecute (fuel - 1) code,
      ControlCompactExecution.sourceExecute (fuel + 13) code with
  | some actual, none, some more =>
    actual.labels.map tag == List.replicate fuel 1 &&
    more.labels.map tag == List.replicate fuel 1 &&
    ProgramCases.bindingPosition ProgramCases.actual.1.store actual.value.1 == some position &&
    ProgramCases.bindingPosition ProgramCases.actual.1.store more.value.1 == some position &&
    ProgramCases.bindingValue ProgramCases.actual.1.store actual.value.1 == some value &&
    actual.value.1.map (fun occurrence => occurrence.1.origins) == some origins
  | _, _, _ => false

def allObserved (table : Bindings ProgramCases.actual.1.store
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec]) : Bool :=
  observed table .here 0 2 [1, 2, 1, 2] &&
  observed table (.prior .here) 1 42 [1] &&
  observed table (.prior (.prior .here)) 2 1 [1, 2] &&
  observed table (.prior (.prior (.prior .here))) 3 43 [2] &&
  observed table (.prior (.prior (.prior (.prior .here)))) 4 42 [1]

def captureProbe (expected : List Nat) : Bool :=
  let code := ControlBindingReader.captureCode _ finalTable.read (ControlBindingReader.tableReader finalTable)
  let fuel := expected.length
  match ControlCompactExecution.sourceExecute fuel code,
      ControlCompactExecution.sourceExecute (fuel - 1) code,
      ControlCompactExecution.sourceExecute (fuel + 13) code with
  | some actual, none, some more =>
    actual.labels.map tag == expected && more.labels.map tag == expected &&
    allObserved actual.value.1 && allObserved more.value.1
  | _, _, _ => false

def fixtures : List Bool :=
  [readProbe .here 1 0 2 [1, 2, 1, 2],
   readProbe (.prior .here) 2 1 42 [1],
   readProbe (.prior (.prior .here)) 3 2 1 [1, 2],
   readProbe (.prior (.prior (.prior .here))) 4 3 43 [2],
   readProbe (.prior (.prior (.prior (.prior .here)))) 5 4 42 [1],
   captureProbe __CAPTURE_TRACE__]
end BindingReaderSmoke
def main : IO Unit := do
  if BindingReaderSmoke.fixtures.all id then
    let stdout ← IO.getStdout
    stdout.write ⟨(ConstitutiveSearch.Agent.Local.Documentary.Cases.utf8
      "BINDING_READER_FIXTURES_PASS: 5 whole reads; 5-cell capture; exact/short/surplus\n").toArray⟩
  else throw (IO.userError "Binding reader fixture failed")
/- AXIOM_AUDIT_BEGIN -/
#print axioms BindingReaderSmoke.tag
#print axioms BindingReaderSmoke.observed
#print axioms BindingReaderSmoke.readProbe
#print axioms BindingReaderSmoke.allObserved
#print axioms BindingReaderSmoke.captureProbe
#print axioms BindingReaderSmoke.fixtures
#print axioms main
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
'''.replace('__CAPTURE_TRACE__', '[' + ', '.join(map(str, CAPTURE_TRACE)) + ']')


def main():
    digest = hashlib.sha256(CLIENT.encode('utf-8')).hexdigest()
    with tempfile.TemporaryDirectory(prefix='rp-d2-binding-reader-') as temp:
        path = Path(temp) / 'BindingReaderSmoke.lean'
        path.write_text(CLIENT, encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(path)], cwd=ROOT,
                                capture_output=True, text=True, encoding='utf-8', timeout=180)
    output = result.stdout + result.stderr
    expected = {"'BindingReaderSmoke." + name + "' does not depend on any axioms"
                for name in ('tag', 'observed', 'readProbe', 'allObserved', 'captureProbe', 'fixtures')}
    expected.update(("'main' does not depend on any axioms",
                     "'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact' does not depend on any axioms",
                     'BINDING_READER_FIXTURES_PASS: 5 whole reads; 5-cell capture; exact/short/surplus'))
    if (result.returncode or result.stderr or set(result.stdout.splitlines()) != expected or
            len(result.stdout.splitlines()) != len(expected)):
        print(output, file=sys.stderr)
        sys.exit(result.returncode or 1)
    print('DOCUMENTARY_BINDING_READER_SMOKE_OK: five original occurrences, references, values and origins; '
          'received reader captured without calling native bindings; 42 fixed capture labels; '
          'exact/short/surplus; eight clean audits; client_sha256=' + digest)


if __name__ == '__main__':
    main()
