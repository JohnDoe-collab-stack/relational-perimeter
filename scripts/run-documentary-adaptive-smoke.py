#!/usr/bin/env python3
"""Constructed adaptive development cases and independent literal-state oracle.

No model inference. The oracle keeps task ports separate from the chronological
production inventory, including lawful outputs which miss the received goal.
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
import Tests.LocalAlignment.DocumentaryAdaptiveCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryAdaptiveSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Program
open ConstitutiveSearch.EndogenousDecomposition

def verify (index : Nat) : List Bool → IO Unit
  | [] => pure ()
  | passed :: rest => if passed then verify (index + 1) rest else do
      let stderr ← IO.getStderr
      stderr.write ⟨(Cases.utf8 (Nat.repr index)).toArray⟩
      throw (IO.userError "Adaptive or oracle verdict changed")

def eventCode : Event → Nat
  | .quoted => 0
  | .derived => 1
  | .refused => 2
  | .missing => 3

def routeCode : Adaptive.Route → Nat
  | .matched => 0
  | .reversed => 1
  | .absent => 2
  | .invalid => 3
  | .inspected => 4
  | .diverted => 5

def inventory {context sources contract rules} (store : @Deduction.Store context sources contract rules) : List (Option Int) :=
  (List.range store.1.length).map (fun index =>
    (Adaptive.locate store.1 index).map (fun located => store.2.resources.read located.2))

def matrix (a b : Nat) (allowed : List Nat) (blocked wrong : Bool) (mode : Nat) (forget : Bool)
    (expectedSlots expectedInventory : List (Option Int)) (expectedPositions : List (Option Nat))
    (events routes : List Nat) (inspections : List (Option Int)) (heads : Nat) (complete : Bool) : Bool :=
  let sources : Support SourceValue Cases.context :=
    .given (⟨7, a, "Baseline"⟩, ⟨7, a, "Baseline"⟩, ⟨7, b, "Revision"⟩, PUnit.unit)
  let rules : Deduction.Policy :=
    ⟨[DeductionCases.differenceRule, DeductionCases.sumRule, DeductionCases.differenceRule], allowed⟩
  let baseline : Dossier.Obligation Cases.context :=
    ⟨⟨7, a, some (if blocked then 0 else 1)⟩, Cases.privateOrigin, Cases.publicOrigin⟩
  let revision : Dossier.Obligation Cases.context := ⟨⟨7, b, some 2⟩, Cases.publicOrigin, Cases.updatedOrigin⟩
  let independent : Dossier.Obligation Cases.context := ⟨⟨7, a, some 1⟩, Cases.privateOrigin, Cases.publicOrigin⟩
  let delta := Int.ofNat b - Int.ofNat a
  let goal : Deduction.Demand := ⟨delta + (if wrong then 1 else 0), some 0, some [1, 2]⟩
  let sumGoal : Deduction.Demand := ⟨delta + delta, some 1, some [1, 2, 1, 2]⟩
  let script : Script Cases.context rules []
      [.conclusion sumGoal, .quotation independent.demand, .conclusion goal,
       .quotation revision.demand, .quotation baseline.demand] :=
    .cons (.quotation baseline) (.cons (.quotation revision)
      (.cons (.conclusion ⟨DeductionCases.differenceRule, .here⟩ (.prior .here) .here goal)
        (.cons (.quotation independent)
          (.cons (.conclusion ⟨DeductionCases.sumRule, .prior .here⟩ (.prior .here) (.prior .here) sumGoal) .done))))
  let initial : Adaptive.Session sources Cases.contract rules Nat [] :=
    ⟨⟨⟨VariableMaster.Example.origin, Documentary.empty sources Cases.contract⟩,
      ⟨[], Deduction.empty sources Cases.contract rules⟩, fun ref => nomatch ref⟩, 0, 0, none⟩
  let result := Adaptive.run (AdaptiveCases.policy mode) (AdaptiveCases.feed forget) initial script
  let summaries := result.2.summaries
  let values := [ProgramCases.bindingValue result.1.frame.store (result.1.frame.bindings .here),
    ProgramCases.bindingValue result.1.frame.store (result.1.frame.bindings (.prior .here)),
    ProgramCases.bindingValue result.1.frame.store (result.1.frame.bindings (.prior (.prior .here))),
    ProgramCases.bindingValue result.1.frame.store (result.1.frame.bindings (.prior (.prior (.prior .here)))),
    ProgramCases.bindingValue result.1.frame.store (result.1.frame.bindings (.prior (.prior (.prior (.prior .here)))))]
  let positions := [ProgramCases.bindingPosition result.1.frame.store (result.1.frame.bindings .here),
    ProgramCases.bindingPosition result.1.frame.store (result.1.frame.bindings (.prior .here)),
    ProgramCases.bindingPosition result.1.frame.store (result.1.frame.bindings (.prior (.prior .here))),
    ProgramCases.bindingPosition result.1.frame.store (result.1.frame.bindings (.prior (.prior (.prior .here)))),
    ProgramCases.bindingPosition result.1.frame.store (result.1.frame.bindings (.prior (.prior (.prior (.prior .here)))))]
  (values == expectedSlots) && (inventory result.1.frame.store == expectedInventory) &&
  (positions == expectedPositions) && (summaries.flatMap (fun summary => summary.events.map eventCode) == events) &&
  (summaries.map (fun summary => routeCode summary.route) == routes) &&
  (summaries.map (fun summary => summary.inspection.map (fun readout => readout.value)) == inspections) &&
  (result.1.frame.dossier.cursor.depth == initial.frame.dossier.cursor.depth + heads) &&
  (succeeded result.1.frame == complete) && (result.1.round == 5) &&
  (result.1.context == if forget then 1 else 5) && (result.2.attempts == events.length)

def run : IO Unit := do
  let actual := AdaptiveCases.hostile
  let terminal := AdaptiveCases.terminal
  verify 0 [
    succeeded actual.1.frame,
    actual.1.round == 5,
    actual.2.attempts == 10,
    actual.1.context == 1,
    actual.1.frame.store.1.length == 6,
    inventory actual.1.frame.store == [some 2, some 0, some 42, some 1, some 43, some 42],
    actual.1.frame.dossier.cursor.depth == AdaptiveCases.start.frame.dossier.cursor.depth + 6,
    actual.1.frame.store.2.resources.read terminal.occurrence.2 == 2,
    terminal.occurrence.1.origins == [1, 2, 1, 2],
    (actual.1.frame.store.2.valid terminal.occurrence.2).rules == [1, 0, 0],
    (actual.1.frame.store.2.valid terminal.occurrence.2).sources.map (fun item => item.item.source.version) == [1, 2, 1, 2],
    succeeded AdaptiveCases.silent.1.frame,
    succeeded AdaptiveCases.repeatedRead.1.frame,
    AdaptiveCases.repeatedRead.1.round == 5,
    AdaptiveCases.repeatedRead.2.attempts == 5,
    AdaptiveCases.repeatedRead.2.summaries.map (fun summary => routeCode summary.route) == [3, 4, 4, 4, 4],
    succeeded AdaptiveCases.wrongOrder.1.frame,
    inventory AdaptiveCases.wrongOrder.1.frame.store == [some 2, some 42, some 1, some (-1), some 43, some 42],
    AdaptiveCases.exact.2.summaries.map (fun summary => routeCode summary.route) == [0, 0, 0, 0, 0],
    succeeded AdaptiveCases.resumed.1.frame,
    succeeded AdaptiveCases.resetResumed.1.frame,
    AdaptiveCases.resumed.1.round == 5,
    AdaptiveCases.resetResumed.1.round == 5,
    AdaptiveCases.present.remaining.length == 2,
    (AdaptiveCases.present.reset (AdaptiveCases.policy 4)).session.round == 3,
    !(succeeded AdaptiveCases.blocked.1.frame),
    AdaptiveCases.blocked.2.summaries.flatMap (fun summary => summary.events.map eventCode) == [0, 0, 2, 3, 0],
    AdaptiveCases.choiceNormal.1.frame.dossier.memory.items.map (fun item => item.position) == [2],
    AdaptiveCases.choiceReversed.1.frame.dossier.memory.items.map (fun item => item.position) == [1],
    succeeded AdaptiveCases.choiceNormal.1.frame,
    succeeded AdaptiveCases.choiceReversed.1.frame]
__MATRIX__
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_ADAPTIVE_DOCUMENT_BEGIN\n").toArray⟩
  stdout.write ⟨AdaptiveCases.actualDocument.toArray⟩
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_ADAPTIVE_DOCUMENT_END\n").toArray⟩
end DocumentaryAdaptiveSmoke
def main : IO Unit := DocumentaryAdaptiveSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryAdaptiveSmoke.verify
#print axioms DocumentaryAdaptiveSmoke.eventCode
#print axioms DocumentaryAdaptiveSmoke.routeCode
#print axioms DocumentaryAdaptiveSmoke.inventory
#print axioms DocumentaryAdaptiveSmoke.matrix
#print axioms DocumentaryAdaptiveSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""


def oracle(a, b, allowed, blocked, wrong, mode):
    # Each port refers to a chronological incorporation, never just to its value.
    inventory, slots, events, routes, inspections = [], [], [], [], []
    heads = 0

    def quote(private=False):
        nonlocal heads
        heads += 1
        if private:
            events.append(2)
            return None
        value = b if len(slots) == 1 else a
        inventory.append(value)
        events.append(0)
        return len(inventory) - 1

    def deduce(rule, left, right):
        if left is None or right is None:
            events.append(3)
            return None
        if rule not in allowed:
            events.append(2)
            return None
        lv, rv = inventory[left], inventory[right]
        inventory.append(lv + rv if rule == 1 else rv - lv)
        events.append(1)
        return len(inventory) - 1

    for turn in range(5):
        inspection = None
        quotation = turn in (0, 1, 3)
        if mode == 0:
            route = 2
        elif mode == 2:
            if slots and slots[-1] is not None:
                route, inspection = 4, inventory[slots[-1]]
            else:
                route = 3
        elif mode == 3:
            route = 3
        elif mode == 4:
            route = 5
            if quotation:
                quote(private=True)
            elif turn == 2:
                deduce(2, slots[0], slots[1])
            else:
                deduce(0, slots[2], slots[2])
        elif mode == 5:
            route = 1 if quotation else 0
        elif mode == 6 and turn == 2:
            route = 5
            deduce(0, slots[1], slots[0])
        else:
            route = 0
        if quotation:
            produced = quote(private=blocked and turn == 0)
        elif turn == 2:
            produced = deduce(0, slots[0], slots[1])
        else:
            produced = deduce(1, slots[2], slots[2])
        slots.append(produced)
        routes.append(route)
        inspections.append(inspection)
    values = [None if slot is None else inventory[slot] for slot in reversed(slots)]
    positions = [None if slot is None else len(inventory) - 1 - slot for slot in reversed(slots)]
    complete = not blocked and not wrong and 0 in allowed and 1 in allowed
    return values, list(reversed(inventory)), positions, events, routes, inspections, heads, complete


def oracle_matrix():
    checks = []
    option = lambda value: "none" if value is None else f"some ({value})"
    options = lambda values: "[" + ", ".join(option(value) for value in values) + "]"
    boolean = lambda value: "true" if value else "false"
    for a, b, mask, blocked, wrong, mode, forget in itertools.product(
            [0, 42], [0, 43], range(8), [False, True], [False, True], range(8), [False, True]):
        allowed = [index for index in range(3) if mask & (1 << index)]
        values, inventory, positions, events, routes, inspections, heads, complete = oracle(a, b, allowed, blocked, wrong, mode)
        checks.append(f"matrix {a} {b} {allowed} {boolean(blocked)} {boolean(wrong)} {mode} {boolean(forget)} "
                      f"{options(values)} {options(inventory)} {options(positions)} {events} {routes} "
                      f"{options(inspections)} {heads} {boolean(complete)}")
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Create a new artifact; never overwrite.")
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError("Output exists; choose a fresh artifact path.")
    checks = oracle_matrix()
    groups = ["  verify " + str(31 + i) + " [\n    " + ",\n    ".join("(" + c + ")" for c in checks[i:i + 40]) + "]"
              for i in range(0, len(checks), 40)]
    source = CLIENT.replace("__MATRIX__", "\n".join(groups))
    with tempfile.TemporaryDirectory(prefix="rp-documentary-adaptive-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(source, encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean adaptive smoke failed: " + (result.stdout + result.stderr).decode("utf-8", "replace"))
    audit, marker, remainder = result.stdout.partition(b"DOCUMENTARY_ADAPTIVE_DOCUMENT_BEGIN\n")
    names = ["verify", "eventCode", "routeCode", "inventory", "matrix", "run"]
    required = {("'DocumentaryAdaptiveSmoke." + name + "' does not depend on any axioms").encode() for name in names}
    required.add(b"'main' does not depend on any axioms")
    if not marker or set(audit.splitlines()) != required:
        raise ValueError("Missing clean runtime audit or unexpected output: " + audit.decode("utf-8", "replace"))
    document, end, suffix = remainder.partition(b"DOCUMENTARY_ADAPTIVE_DOCUMENT_END\n")
    baseline = (b"> La mesure certifiee est 42.\n\n"
                b"Source 1, version 1, extrait 0, occurrence recue 1.\nFait 7 = 42.\n")
    expected = baseline + (b"> La mesure revisee est 43.\n\n"
                           b"Source 1, version 2, extrait 0, occurrence recue 2.\nFait 7 = 43.\n") + baseline + (
        b"\nConclusion derivee : variation + variation = 2.\n"
        b"Regle 102, occurrence du catalogue 1 : gauche + droite.\nSources recues : 1, 2, 1, 2.\n")
    if not end or suffix or document != expected:
        raise ValueError("Actual adaptive dossier differs from the literal fixture: " + repr(document))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        header = ("# Dossier accompli malgré des propositions hostiles\n\n"
                  "Cas construit de développement, sans inférence du modèle. Cinq tours, dix actions : "
                  "trois extractions proposées sont refusées, une règle proposée est refusée, "
                  "une déduction autorisée vaut 0 et reste conservée. Chaque obligation reçue est accomplie. "
                  "Le rendu lit les citations et la conclusion terminale effectives.\n\n").encode("utf-8")
        with args.output.open("xb") as output:
            output.write(header + document)
    print("DOCUMENTARY_ADAPTIVE_SMOKE_OK: 31 fixed checks, " + str(len(checks)) +
          " literal-oracle cases, seven clean runtime audits, exact adaptive dossier bytes")
    if args.output:
        print("DOCUMENTARY_ADAPTIVE_OUTPUT: " + str(args.output))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_ADAPTIVE_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
