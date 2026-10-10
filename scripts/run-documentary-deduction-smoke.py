#!/usr/bin/env python3
"""Development smoke for actual quotations and admitted dependency chains.

The literal oracle varies received source facts and rule permissions. This is
not model inference or a confirmatory comparison with an unprotected agent.
"""
import argparse
import itertools
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryDeductionCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryDeductionSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Cases
open ConstitutiveSearch.Agent.Local.Documentary.DossierCases
open ConstitutiveSearch.Agent.Local.Documentary.Deduction
open ConstitutiveSearch.Agent.Local.Documentary.DeductionCases
open ConstitutiveSearch.EndogenousDecomposition

def verify : List Bool → IO Unit
  | [] => pure ()
  | verdict :: rest =>
      if verdict then verify rest
      else throw (IO.userError "Deduction, dependency or oracle verdict changed")

def locate : (kinds : List Kind) → Nat → Option ((kind : Kind) × Ref kinds kind)
  | [], _ => none
  | kind :: _, 0 => some ⟨kind, .here⟩
  | _ :: rest, index + 1 =>
      match locate rest index with
      | none => none
      | some found => some ⟨found.1, .prior found.2⟩

def matrix (a b : Nat) (allowed : List Nat) (position : Nat)
    (expected : Option Int) (count : Nat) : Bool :=
  let received : Support SourceValue context :=
    .given (⟨7, a, "Baseline"⟩, ⟨7, a, "Baseline"⟩, ⟨7, b, "Revision"⟩, PUnit.unit)
  let transforms : Deduction.Policy :=
    ⟨[differenceRule, sumRule, differenceRule], allowed⟩
  let request : Deduction.Request transforms :=
    if position == 0 then ⟨differenceRule, .here⟩
    else if position == 1 then ⟨sumRule, .prior .here⟩
    else ⟨differenceRule, .prior (.prior .here)⟩
  let receivedTasks : List (Dossier.Obligation context) :=
    [⟨⟨7, a, none⟩, privateOrigin, publicOrigin⟩,
     ⟨⟨7, b, none⟩, publicOrigin, updatedOrigin⟩]
  let start : Dossier.State received contract :=
    ⟨VariableMaster.Example.origin, Documentary.empty received contract⟩
  let quoted := quoteAll start ⟨[], Deduction.empty received contract transforms⟩ receivedTasks
  let store := quoted.2.1
  match locate store.1 1 with
  | none => false
  | some left => match locate store.1 0 with
    | none => false
    | some right =>
      let produced := Deduction.execute store.2 request left.2 right.2
      let result := produced.result
      let verdict := match locate result.1.1 0 with
        | none => false
        | some output => match expected with
          | some value =>
              meetsCheck ⟨value, some position, some [1, 2]⟩ output.1
                (result.1.2.resources.read output.2)
          | none =>
              !(meetsCheck ⟨0, some position, some [1, 2]⟩ output.1
                (result.1.2.resources.read output.2))
      (store.2.resources.read left.2 == Int.ofNat a) &&
      (store.2.resources.read right.2 == Int.ofNat b) &&
      (left.1.origins == [1]) && (right.1.origins == [2]) &&
      (result.2 == expected) && (result.1.1.length == count) && verdict &&
      Documentary.goalSucceeded (Dossier.demands receivedTasks) quoted.1.memory.items &&
      (quoted.1.cursor.depth == start.cursor.depth + 2)

def run : IO Unit := do
  verify [
    differenceDecision.result.2 == some 1,
    sumDecision.result.2 == some 2,
    forbiddenDecision.result.2 == none,
    forbiddenDecision.result.1.1.length == knowledge.resources.kinds.length,
    forbiddenAction.resources.read .here == 1,
    meetsCheck commonDemand (derivedKind duplicateRequest baseline revised) (forbiddenAction.resources.read .here),
    permittedAlternative.result.2 == some 1,
    meetsCheck deltaDemand (derivedKind differenceRequest baseline revised) (afterDifference.resources.read delta),
    meetsCheck sumDemand (derivedKind sumRequest delta delta) (afterSum.resources.read sumReference),
    !(meetsCheck forbiddenDemand (derivedKind differenceRequest baseline revised) (afterDifference.resources.read delta)),
    !(meetsCheck ⟨1, some 0, some [0, 2]⟩ (derivedKind differenceRequest baseline revised) (afterDifference.resources.read delta)),
    (form knowledge differenceRequest revised baseline).resources.read .here == -1,
    (afterSum.valid sumReference).rules == [1, 0, 0],
    (afterSum.valid sumReference).sources.map (fun output => output.item.position) == [1, 2, 1, 2],
    (afterSum.valid sumReference).sources.map (fun output => output.item.source.version) == [1, 2, 1, 2],
    (derivedKind sumRequest delta delta).origins == [1, 2, 1, 2],
    differenceRequest.2.position == 0,
    duplicateRequest.2.position == 2,
    sumDecision.result.1.1.length == 4,
    continuedQuote.2.1.1.length == 5,
    continuedQuote.2.1.2.resources.read keptSum == 2,
    continuedQuote.1.cursor.depth == quotationRun.1.cursor.depth + 1,
    Documentary.goalSucceeded (Dossier.demands tasks) quotationRun.1.memory.items,
    erasedDecision.result.2 == none]
__MATRIX__
  let stdout ← IO.getStdout
  stdout.write ⟨(utf8 "DOCUMENTARY_DEDUCTION_DOCUMENT_BEGIN\n").toArray⟩
  stdout.write ⟨ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actualDocument.toArray⟩
  stdout.write ⟨(utf8 "DOCUMENTARY_DEDUCTION_DOCUMENT_END\n").toArray⟩
end DocumentaryDeductionSmoke

def main : IO Unit := DocumentaryDeductionSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryDeductionSmoke.verify
#print axioms DocumentaryDeductionSmoke.locate
#print axioms DocumentaryDeductionSmoke.matrix
#print axioms DocumentaryDeductionSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""
EXPECTED = (
    b"> La mesure certifiee est 42.\n\n"
    b"Source 1, version 1, extrait 0, occurrence recue 1.\nFait 7 = 42.\n"
    b"> La mesure revisee est 43.\n\n"
    b"Source 1, version 2, extrait 0, occurrence recue 2.\nFait 7 = 43.\n"
    b"\nConclusion derivee : variation = 1.\n"
    b"Regle 101, occurrence du catalogue 0 : droite - gauche.\nSources recues : 1, 2.\n"
    b"\nConclusion derivee : variation + variation = 2.\n"
    b"Regle 102, occurrence du catalogue 1 : gauche + droite.\nSources recues : 1, 2, 1, 2.\n"
)
HEADER = (
    "# Dossier avec deductions effectivement produites\n\n"
    "Cas construit de développement, sans inférence du modèle. Les citations proviennent "
    "des sorties du maître. Chaque conclusion est rendue depuis sa ressource incorporée.\n\n"
).encode("utf-8")


def oracle_matrix():
    checks = []
    values = [0, 1, 2, 42, 43, 46]
    for a, b, mask, position in itertools.product(values, values, range(8), range(3)):
        allowed = [i for i in range(3) if mask & (1 << i)]
        expected = (a + b if position == 1 else b - a) if position in allowed else None
        literal = "none" if expected is None else f"(some ({expected} : Int))"
        count = 2 + int(expected is not None)
        checks.append(f"matrix {a} {b} {allowed} {position} {literal} {count}")
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Create a new Markdown artifact; never overwrite.")
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError("Output already exists; choose a fresh artifact path.")
    checks = oracle_matrix()
    groups = ["  verify [\n    " + ",\n    ".join("(" + c + ")" for c in checks[i:i + 40]) + "]"
              for i in range(0, len(checks), 40)]
    source = CLIENT.replace("__MATRIX__", "\n".join(groups))
    with tempfile.TemporaryDirectory(prefix="rp-documentary-deduction-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(source, encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=180, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean deduction smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    audit, marker, remainder = result.stdout.partition(b"DOCUMENTARY_DEDUCTION_DOCUMENT_BEGIN\n")
    required = {("'" + name + "' does not depend on any axioms").encode()
                for name in ["DocumentaryDeductionSmoke.verify", "DocumentaryDeductionSmoke.locate",
                             "DocumentaryDeductionSmoke.matrix", "DocumentaryDeductionSmoke.run", "main"]}
    if not marker or set(audit.splitlines()) != required:
        raise ValueError("Missing clean runtime audit or unexpected output: " + audit.decode("utf-8", "replace"))
    document, end, suffix = remainder.partition(b"DOCUMENTARY_DEDUCTION_DOCUMENT_END\n")
    if not end or suffix or document != EXPECTED:
        raise ValueError("Actual produced deductions differ from the independent fixture: " + repr(document))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("xb") as output:
            output.write(HEADER + document)
    print("DOCUMENTARY_DEDUCTION_SMOKE_OK: 24 fixed checks, " + str(len(checks)) +
          " literal-oracle cases, five clean runtime audits, exact actual rendered dossier")
    if args.output:
        print("DOCUMENTARY_DEDUCTION_OUTPUT: " + str(args.output))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_DEDUCTION_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
