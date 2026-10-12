#!/usr/bin/env python3
"""Frozen development probes of the opened frontier component.

Fixtures cover freshness rejection, delayed rejection, retained order and
clause deletion. Exact and short fuel use the actual trace, independently
of the component's upper bound. Deferred transport invocation is outside
this component probe; no physical or whole-fallback bound is claimed.

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
import Tests.LocalAlignment.DocumentaryControlFrontierOpening
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace FrontierOpeningSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings

abbrev Summary := List (List (Bool × Nat)) × List (Nat × Bool) × Nat

def literalSummary : Literal → Bool × Nat
  | .positive var => (true, var)
  | .negative var => (false, var)

def summary {formula : Cnf} (state : GeneratedStructuralBranchContext formula) : Summary :=
  (state.context.formula.map (fun clause => clause.map literalSummary),
    state.context.decisions.map (fun decision => (decision.var, decision.value)), state.depth)

def expected (formula : Cnf) (decisions : List (Nat × Bool)) (depth : Nat) : Summary :=
  (formula.map (fun clause => clause.map literalSummary), decisions, depth)

def repeated : GeneratedStructuralBranchContext [] :=
  (GeneratedStructuralBranchContext.root []).child 0 false True.intro

def firstDecision : GeneratedStructuralBranchContext [] :=
  (GeneratedStructuralBranchContext.root []).child 1 false True.intro

def twoDecisions : GeneratedStructuralBranchContext [] :=
  firstDecision.child 3 true ⟨(by decide), True.intro⟩

def richFormula : Cnf :=
  [[.positive 0, .negative 1], [.negative 0, .positive 2], [.positive 1, .negative 1]]

def richParent : GeneratedStructuralBranchContext richFormula :=
  (GeneratedStructuralBranchContext.root richFormula).child 0 false True.intro

def naturalLabel : Label → Bool
  | .naturalComparison => true
  | _ => false

def witnessLabel : Label → Bool
  | .formationWitness => true
  | _ => false

def weakeningDecisions : {formula residual : Cnf} → CnfWeakening formula residual → List Bool
  | _, _, .done => []
  | _, _, .drop _ tail => true :: weakeningDecisions tail
  | _, _, .keep _ tail => false :: weakeningDecisions tail

def residualProbe (formula : Cnf) (selected : Var) (bit : Bool) (wanted : Cnf)
    (weakening : List Bool) : Bool :=
  let code := ControlFrontierSyntax.residualCode selected bit formula
  let allowance := ControlFrontierSyntax.residualBound formula
  match ControlCompactExecution.sourceExecute allowance code with
  | none => false
  | some actual =>
    let length := actual.labels.length
    match ControlCompactExecution.sourceExecute length code, ControlCompactExecution.sourceExecute (length - 1) code,
        ControlCompactExecution.sourceExecute (allowance + 5) code with
    | some exact, none, some surplus =>
      actual.value.1.1.map (fun clause => clause.map literalSummary) ==
        wanted.map (fun clause => clause.map literalSummary) &&
      weakeningDecisions actual.value.1.2 == weakening &&
      weakeningDecisions exact.value.1.2 == weakening &&
      weakeningDecisions surplus.value.1.2 == weakening &&
      (actual.labels.filter witnessLabel).length == formula.length + 1 &&
      length == exact.labels.length && length == surplus.labels.length && length <= allowance
    | _, _, _ => false

def probe (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (wanted : List Summary) (minimumComparisons : Nat) : Bool :=
  let code := ControlFrontierOpening.code formula selected source
  let allowance := ControlFrontierOpening.bound formula selected source
  match ControlCompactExecution.sourceExecute allowance code with
  | none => false
  | some actual =>
    let length := actual.labels.length
    match ControlCompactExecution.sourceExecute length code, ControlCompactExecution.sourceExecute (length - 1) code,
        ControlCompactExecution.sourceExecute (allowance + 5) code with
    | some exact, none, some surplus =>
      actual.value.1.frontier.map summary == wanted &&
      exact.value.1.frontier.map summary == wanted &&
      surplus.value.1.frontier.map summary == wanted &&
      length <= allowance && length == exact.labels.length && length == surplus.labels.length &&
      minimumComparisons <= (actual.labels.filter naturalLabel).length &&
      !(ControlCompactExecution.sourceExecute 0 code).isSome
    | _, _, _ => false

def run : IO Unit := do
  let root := GeneratedStructuralBranchContext.root []
  let checks := [
    probe [] 0 [] [] 0,
    probe [] 0 [root] [expected [] [(0, false)] 1, expected [] [(0, true)] 1] 0,
    probe [] 0 [repeated] [expected [] [(0, false)] 1] 1,
    probe [] 2 [twoDecisions]
      [expected [] [(2, false), (3, true), (1, false)] 3,
        expected [] [(2, true), (3, true), (1, false)] 3] 4,
    probe [] 1 [twoDecisions] [expected [] [(3, true), (1, false)] 2] 4,
    probe [] 0 [repeated, root]
      [expected [] [(0, false)] 1, expected [] [(0, false)] 1, expected [] [(0, true)] 1] 1,
    probe richFormula 0 [GeneratedStructuralBranchContext.root richFormula]
      [expected [[.positive 0, .negative 1], [.positive 1, .negative 1]] [(0, false)] 1,
        expected [[.negative 0, .positive 2], [.positive 1, .negative 1]] [(0, true)] 1] 2,
    probe richFormula 1 [richParent]
      [expected [] [(1, false), (0, false)] 2,
        expected [[.positive 0, .negative 1]] [(1, true), (0, false)] 2] 2,
    residualProbe [] 0 false [] [],
    residualProbe richFormula 0 false
      [[.positive 0, .negative 1], [.positive 1, .negative 1]] [false, true, false],
    residualProbe richFormula 0 true
      [[.negative 0, .positive 2], [.positive 1, .negative 1]] [true, false, false]]
  if checks.length != 11 || checks.any (fun passed => !passed) then
    throw (IO.userError "Frontier opening mismatch")
  let stdout ← IO.getStdout
  stdout.write "DOCUMENTARY_FRONTIER_OPENING_SMOKE_DONE\n".toUTF8
end FrontierOpeningSmoke
def main : IO Unit := FrontierOpeningSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms FrontierOpeningSmoke.literalSummary
#print axioms FrontierOpeningSmoke.summary
#print axioms FrontierOpeningSmoke.expected
#print axioms FrontierOpeningSmoke.repeated
#print axioms FrontierOpeningSmoke.firstDecision
#print axioms FrontierOpeningSmoke.twoDecisions
#print axioms FrontierOpeningSmoke.richFormula
#print axioms FrontierOpeningSmoke.richParent
#print axioms FrontierOpeningSmoke.naturalLabel
#print axioms FrontierOpeningSmoke.witnessLabel
#print axioms FrontierOpeningSmoke.weakeningDecisions
#print axioms FrontierOpeningSmoke.residualProbe
#print axioms FrontierOpeningSmoke.probe
#print axioms FrontierOpeningSmoke.run
#print axioms main
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
"""


def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-frontier-opening-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode("utf-8", "replace"))
    names = ("literalSummary", "summary", "expected", "repeated", "firstDecision", "twoDecisions",
             "richFormula", "richParent", "naturalLabel", "witnessLabel", "weakeningDecisions",
             "residualProbe", "probe", "run")
    expected = {("'FrontierOpeningSmoke." + name + "' does not depend on any axioms").encode()
                for name in names}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_FRONTIER_OPENING_SMOKE_DONE"))
    expected.add(b"'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact' does not depend on any axioms")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Unexpected runtime output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_FRONTIER_OPENING_SMOKE_OK: eleven development checks; freshness, residuals, "
          "positive weakening, retained order and provenance depth; exact/short/surplus fuel; sixteen clean runtime audits; "
          "client_sha256=" + hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_FRONTIER_OPENING_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
