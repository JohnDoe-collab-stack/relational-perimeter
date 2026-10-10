#!/usr/bin/env python3
"""Development smoke: independent integer oracle and fuel/trace matrix.
The protocol is fixed here before running; it is not a model comparison.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
OPERANDS = tuple(range(-4, 5))
WIDE = 170141183460469231731687303715884105727
FUEL_COUNT = 32


def sum_labels(left, right):
    # Declared constructor semantics, separate from the Python arithmetic oracle.
    if left >= 0 and right >= 0:
        return [19] + [17] * (right + 1) + [18] * right + [20]
    if left < 0 and right < 0:
        tail = -right - 1
        return [19] + [17] * (tail + 1) + [18] * tail + [20]
    positive, negative = (left, -right) if left >= 0 else (right, -left)
    return [19] + [17] * (min(positive, negative) + 1)


def fixture(operation, left, right):
    expected = left + right if operation == "sum" else right - left
    labels = [21] + (sum_labels(left, right) if operation == "sum" else [22] + sum_labels(right, -left))
    return operation, left, right, expected, labels


CASES = tuple(fixture(op, left, right) for op in ("sum", "difference")
              for left in OPERANDS for right in OPERANDS) + (
    fixture("sum", WIDE, 2), fixture("sum", -WIDE, -2),
    fixture("sum", WIDE, -2), fixture("difference", 2, WIDE))
assert all(len(case[4]) < FUEL_COUNT for case in CASES)


def literal(value):
    return "(" + str(value) + ")" if value < 0 else str(value)


def client_source():
    cases = ",\n".join("  ⟨." + op + ", " + literal(left) + ", " + literal(right) + ", " +
                       literal(expected) + ", [" + ", ".join(map(str, labels)) + "]⟩"
                       for op, left, right, expected, labels in CASES)
    # All labels are mapped, so adding an unqualified constructor breaks this client.
    names = ("instruction binding quotationProducer deductionProducer missingAssembly naturalComparison "
             "permissionCell permissionReturn deductionDecision deductionAssembly referencePosition "
             "referenceReturn resourceCell producerKindCell producerPortCell producerOutputKind producerAssembly "
             "integerNaturalCell integerNaturalReturn integerSign integerSignReturn integerOperation integerNegate "
             "formationValues formationWitness formationResources "
             "assemblyKind assemblyKinds assemblyKnowledge assemblyStore assemblyExtension assemblyOutput assemblyFrame assemblyPacket "
             "citationOrigin citationCheckResult citationReadout citationHead citationFormula citationOpening citationReduction citationStage "
             "citationSeed citationInput citationPreservation citationRouting citationContinuationCell citationAssignment citationCandidate "
             "citationProducer citationAuthorize citationIncorporate citationCompletion citationDecision citationPacket").split()
    tags = "\n".join("  | ." + name + " => " + str(i) for i, name in enumerate(names))
    return """import Tests.LocalAlignment.DocumentaryControlArithmetic
import Tests.LocalAlignment.DocumentaryCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryArithmeticSmoke
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings
structure Case where
  operation : Deduction.Operation
  left : Int
  right : Int
  expected : Int
  labels : List Nat
def tag : Label → Nat
""" + tags + """
def cases : List Case := [
""" + cases + """
]
def check (test : Case) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlArithmetic.code test.operation test.left test.right) with
  | none => fuel < test.labels.length
  | some actual => test.labels.length ≤ fuel &&
      actual.value.1 == test.expected && actual.labels.map tag == test.labels
def matrix : List Bool := cases.flatMap (fun test => (List.range 32).map (check test))
def run : IO Unit := do
  if matrix.length != 5312 || matrix.any (fun passed => !passed) then
    throw (IO.userError "Arithmetic value/trace/fuel mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_ARITHMETIC_SMOKE_DONE\n").toArray⟩
end DocumentaryArithmeticSmoke
def main : IO Unit := DocumentaryArithmeticSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryArithmeticSmoke.Case
#print axioms DocumentaryArithmeticSmoke.tag
#print axioms DocumentaryArithmeticSmoke.cases
#print axioms DocumentaryArithmeticSmoke.check
#print axioms DocumentaryArithmeticSmoke.matrix
#print axioms DocumentaryArithmeticSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""


def main():
    source = client_source().encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-arithmetic-smoke-") as directory:
        path = Path(directory) / "Smoke.lean"; path.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(path)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode("utf-8", "replace"))
    expected = {("'" + name + "' does not depend on any axioms").encode() for name in (
        "DocumentaryArithmeticSmoke.Case", "DocumentaryArithmeticSmoke.tag", "DocumentaryArithmeticSmoke.cases",
        "DocumentaryArithmeticSmoke.check", "DocumentaryArithmeticSmoke.matrix", "DocumentaryArithmeticSmoke.run", "main")}
    expected.add(b"DOCUMENTARY_ARITHMETIC_SMOKE_DONE")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Missing arithmetic runtime audit or unexpected output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_ARITHMETIC_SMOKE_OK: 166 cases, 5312 fuel/value/trace verdicts, "
          "all sign combinations, zero, cancellation and wide integers, seven clean runtime audits; "
          "client_sha256=" + hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_ARITHMETIC_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
