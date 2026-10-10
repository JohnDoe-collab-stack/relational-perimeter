#!/usr/bin/env python3
"""Constructed development smoke for finite interleaved documentary programs.

An independent literal oracle varies facts, rule occurrence permissions, a
forbidden source requirement and an incorrect requested value. No model run.
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
import Tests.LocalAlignment.DocumentaryProgramCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryProgramSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Program
open ConstitutiveSearch.EndogenousDecomposition

def verify : List Bool → IO Unit
  | [] => pure ()
  | passed :: rest => if passed then verify rest else throw (IO.userError "Program or oracle verdict changed")

def eventCode : Event → Nat
  | .quoted => 0
  | .derived => 1
  | .refused => 2
  | .missing => 3

def matrix (a b : Nat) (allowed : List Nat) (position : Nat) (blockedSource : Bool)
    (target downstreamTarget : Int) (expected downstreamExpected : Option Int)
    (events : List Nat) (count : Nat) (complete : Bool) : Bool :=
  let sources : Support SourceValue Cases.context :=
    .given (⟨7, a, "Baseline"⟩, ⟨7, a, "Baseline"⟩, ⟨7, b, "Revision"⟩, PUnit.unit)
  let policy : Deduction.Policy :=
    ⟨[DeductionCases.differenceRule, DeductionCases.sumRule, DeductionCases.differenceRule], allowed⟩
  let request : Deduction.Request policy :=
    if position == 0 then ⟨DeductionCases.differenceRule, .here⟩
    else if position == 1 then ⟨DeductionCases.sumRule, .prior .here⟩
    else ⟨DeductionCases.differenceRule, .prior (.prior .here)⟩
  let baseline : Dossier.Obligation Cases.context :=
    ⟨⟨7, a, some (if blockedSource then 0 else 1)⟩, Cases.privateOrigin, Cases.publicOrigin⟩
  let revision : Dossier.Obligation Cases.context :=
    ⟨⟨7, b, some 2⟩, Cases.publicOrigin, Cases.updatedOrigin⟩
  let independent : Dossier.Obligation Cases.context :=
    ⟨⟨7, a, some 1⟩, Cases.privateOrigin, Cases.publicOrigin⟩
  let goal : Deduction.Demand := ⟨target, some position, some [1, 2]⟩
  let downstreamGoal : Deduction.Demand := ⟨downstreamTarget, some 1, some [1, 2, 1, 2]⟩
  let script : Script Cases.context policy []
      [.quotation independent.demand, .conclusion downstreamGoal, .conclusion goal,
       .quotation revision.demand, .quotation baseline.demand] :=
    .cons (.quotation baseline) (.cons (.quotation revision)
      (.cons (.conclusion request (.prior .here) .here goal)
        (.cons (.conclusion ⟨DeductionCases.sumRule, .prior .here⟩ .here .here downstreamGoal)
          (.cons (.quotation independent) .done))))
  let initial : Frame sources Cases.contract policy [] :=
    ⟨⟨VariableMaster.Example.origin, Documentary.empty sources Cases.contract⟩,
      ⟨[], Deduction.empty sources Cases.contract policy⟩, fun ref => nomatch ref⟩
  let result := Program.execute initial script
  (ProgramCases.bindingValue result.1.store (result.1.bindings (.prior (.prior .here))) == expected) &&
  (ProgramCases.bindingValue result.1.store (result.1.bindings (.prior .here)) == downstreamExpected) &&
  (ProgramCases.bindingValue result.1.store (result.1.bindings .here) == some (Int.ofNat a)) &&
  (result.2.events.map eventCode == events) && (result.1.store.1.length == count) &&
  (result.1.dossier.cursor.depth == initial.dossier.cursor.depth + 3) &&
  (succeeded result.1 == complete)

def run : IO Unit := do
  let result := ProgramCases.actual
  let sum := ProgramCases.sumRealized
  verify [
    succeeded result.1,
    result.2.events.map eventCode == [0, 0, 1, 0, 1],
    result.1.store.1.length == 5,
    result.1.dossier.cursor.depth == ProgramCases.start.dossier.cursor.depth + 3,
    result.1.store.2.resources.read sum.occurrence.2 == 2,
    sum.occurrence.1.origins == [1, 2, 1, 2],
    (result.1.store.2.valid sum.occurrence.2).rules == [1, 0, 0],
    (result.1.store.2.valid sum.occurrence.2).sources.map (fun output => output.item.source.version) == [1, 2, 1, 2],
    ProgramCases.bindingValue result.1.store ProgramCases.baselineBinding == some 42,
    ProgramCases.bindingValue result.1.store ProgramCases.repeatedBinding == some 42,
    ProgramCases.bindingPosition result.1.store ProgramCases.baselineBinding == some 4,
    ProgramCases.bindingPosition result.1.store ProgramCases.repeatedBinding == some 1,
    succeeded ProgramCases.resumed.1,
    ProgramCases.resumed.1.dossier.cursor.depth == result.1.dossier.cursor.depth,
    ProgramCases.wrongActual.2.events.map eventCode == [0, 0, 1, 1],
    !(succeeded ProgramCases.wrongActual.1),
    ProgramCases.bindingValue ProgramCases.wrongActual.1.store (ProgramCases.wrongActual.1.bindings (.prior .here)) == some 1,
    ProgramCases.bindingValue ProgramCases.wrongActual.1.store (ProgramCases.wrongActual.1.bindings .here) == some 2,
    ProgramCases.blockedActual.2.events.map eventCode == [0, 0, 2, 3, 0],
    !(succeeded ProgramCases.blockedActual.1),
    ProgramCases.blockedActual.1.store.1.length == 3,
    ProgramCases.bindingValue ProgramCases.blockedActual.1.store (ProgramCases.blockedActual.1.bindings .here) == some 42,
    ProgramCases.sourceBlockedActual.2.events.map eventCode == [2, 3, 0],
    !(succeeded ProgramCases.sourceBlockedActual.1),
    succeeded ProgramCases.erased.1,
    ProgramCases.erasedBlocked.2.events.map eventCode == [0, 0, 2, 3, 0]]
__MATRIX__
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_PROGRAM_DOCUMENT_BEGIN\n").toArray⟩
  stdout.write ⟨ProgramCases.actualDocument.toArray⟩
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_PROGRAM_DOCUMENT_END\n").toArray⟩
end DocumentaryProgramSmoke

def main : IO Unit := DocumentaryProgramSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryProgramSmoke.verify
#print axioms DocumentaryProgramSmoke.eventCode
#print axioms DocumentaryProgramSmoke.matrix
#print axioms DocumentaryProgramSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""
BASELINE = (b"> La mesure certifiee est 42.\n\n"
            b"Source 1, version 1, extrait 0, occurrence recue 1.\nFait 7 = 42.\n")
EXPECTED = BASELINE + (
    b"> La mesure revisee est 43.\n\n"
    b"Source 1, version 2, extrait 0, occurrence recue 2.\nFait 7 = 43.\n"
) + BASELINE + (
    b"\nConclusion derivee : variation + variation = 2.\n"
    b"Regle 102, occurrence du catalogue 1 : gauche + droite.\nSources recues : 1, 2, 1, 2.\n"
)
HEADER = ("# Dossier d'un programme documentaire mixte\n\n"
          "Cas construit de développement, sans inférence du modèle. Trois extractions "
          "et deux déductions sont entrelacées. Le rendu lit les productions réelles.\n\n").encode("utf-8")


def oracle_matrix():
    checks = []
    for a, b, mask, position, blocked, wrong in itertools.product(
            [0, 1, 42, 43], [0, 1, 42, 43], range(8), range(3), [False, True], [False, True]):
        allowed = [i for i in range(3) if mask & (1 << i)]
        arithmetic = a + b if position == 1 else b - a
        expected = arithmetic if not blocked and position in allowed else None
        downstream = expected * 2 if expected is not None and 1 in allowed else None
        events = [2 if blocked else 0, 0,
                  3 if blocked else (1 if expected is not None else 2),
                  3 if expected is None else (1 if downstream is not None else 2), 0]
        count = 2 + int(not blocked) + int(expected is not None) + int(downstream is not None)
        complete = not blocked and not wrong and expected is not None and downstream is not None
        literal = lambda value: "none" if value is None else f"(some ({value} : Int))"
        boolean = lambda value: "true" if value else "false"
        checks.append(f"matrix {a} {b} {allowed} {position} {boolean(blocked)} "
                      f"({arithmetic + int(wrong)}) ({arithmetic * 2}) "
                      f"{literal(expected)} {literal(downstream)} {events} {count} {boolean(complete)}")
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Create a new artifact; never overwrite.")
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError("Output exists; choose a fresh artifact path.")
    checks = oracle_matrix()
    groups = ["  verify [\n    " + ",\n    ".join("(" + c + ")" for c in checks[i:i + 40]) + "]"
              for i in range(0, len(checks), 40)]
    source = CLIENT.replace("__MATRIX__", "\n".join(groups))
    with tempfile.TemporaryDirectory(prefix="rp-documentary-program-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(source, encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=240, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean program smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    audit, marker, remainder = result.stdout.partition(b"DOCUMENTARY_PROGRAM_DOCUMENT_BEGIN\n")
    names = ["DocumentaryProgramSmoke.verify", "DocumentaryProgramSmoke.eventCode",
             "DocumentaryProgramSmoke.matrix", "DocumentaryProgramSmoke.run", "main"]
    required = {("'" + name + "' does not depend on any axioms").encode() for name in names}
    if not marker or set(audit.splitlines()) != required:
        raise ValueError("Missing clean runtime audit or unexpected output: " + audit.decode("utf-8", "replace"))
    document, end, suffix = remainder.partition(b"DOCUMENTARY_PROGRAM_DOCUMENT_END\n")
    if not end or suffix or document != EXPECTED:
        raise ValueError("Actual mixed dossier differs from the literal fixture: " + repr(document))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("xb") as output:
            output.write(HEADER + document)
    print("DOCUMENTARY_PROGRAM_SMOKE_OK: 26 fixed checks, " + str(len(checks)) +
          " literal-oracle cases, five clean runtime audits, exact mixed dossier bytes")
    if args.output:
        print("DOCUMENTARY_PROGRAM_OUTPUT: " + str(args.output))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_PROGRAM_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
