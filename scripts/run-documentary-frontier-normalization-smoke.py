#!/usr/bin/env python3
"""Development probes of the complete controlled frontier normalization.

Expected frontiers and routing constructor counts are fixed independently of
the native normalizer. Transport invocations inspect the returned routing code;
their cost is outside the local normalization allowance tested here.

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
import Tests.LocalAlignment.DocumentaryControlFrontierNormalization
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace FrontierNormalizationSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings

def tag : Label → Nat
  | .instruction => 0
  | .binding => 1
  | .quotationProducer => 2
  | .deductionProducer => 3
  | .missingAssembly => 4
  | .naturalComparison => 5
  | .permissionCell => 6
  | .permissionReturn => 7
  | .deductionDecision => 8
  | .deductionAssembly => 9
  | .referencePosition => 10
  | .referenceReturn => 11
  | .resourceCell => 12
  | .producerKindCell => 13
  | .producerPortCell => 14
  | .producerOutputKind => 15
  | .producerAssembly => 16
  | .integerNaturalCell => 17
  | .integerNaturalReturn => 18
  | .integerSign => 19
  | .integerSignReturn => 20
  | .integerOperation => 21
  | .integerNegate => 22
  | .formationValues => 23
  | .formationWitness => 24
  | .formationResources => 25
  | .assemblyKind => 26
  | .assemblyKinds => 27
  | .assemblyKnowledge => 28
  | .assemblyStore => 29
  | .assemblyExtension => 30
  | .assemblyOutput => 31
  | .assemblyFrame => 32
  | .assemblyPacket => 33
  | .citationOrigin => 34
  | .citationCheckResult => 35
  | .citationReadout => 36
  | .citationHead => 37
  | .citationFormula => 38
  | .citationOpening => 39
  | .citationReduction => 40
  | .citationStage => 41
  | .citationSeed => 42
  | .citationInput => 43
  | .citationPreservation => 44
  | .citationRouting => 45
  | .citationContinuationCell => 46
  | .citationAssignment => 47
  | .citationCandidate => 48
  | .citationProducer => 49
  | .citationAuthorize => 50
  | .citationIncorporate => 51
  | .citationCompletion => 52
  | .citationDecision => 53
  | .citationPacket => 54
  | .masterProducer => 55
  | .masterDiscover => 56
  | .masterApply => 57
  | .masterDecompose => 58
  | .masterAssemble => 59
  | .masterNextPrefix => 60
  | .masterNextSource => 61
  | .masterNextFresh => 62
  | .masterNextCursor => 63
  | .masterHeadPacket => 64
  | .masterGeneration => 65
  | .masterCandidateCell => 66
  | .masterProvenanceCell => 67
  | .masterProvenanceReturn => 68
  | .masterFilterCell => 69
  | .masterFilterReturn => 70
  | .masterDiscoveryPacket => 71
  | .assemblyDossier => 72
  | .masterWorkPacket => 73
  | .masterConstructionCell => 74
  | .masterConstructionReturn => 75
  | .masterExtractionCell => 76
  | .masterExtractionReturn => 77
  | .listAppendCell => 78
  | .listAppendReturn => 79
  | .frameRestore => 80
  | .justificationCell => 81
  | .justificationReturn => 82
  | .referenceIdentity => 83
  | .referenceShift => 84
  | .referenceComposition => 85
  | .controlInspect => 86
  | .controlCall => 87
  | .controlCompose => 88
  | .controlClosure => 89
  | .controlFrame => 90
  | .controlTrace => 91
  | .controlWitness => 92
  | .controlResult => 93
  | .masterCandidateAttempt => 94
  | .masterCandidateReturn => 95
  | .masterNextStateGeneration => 96
  | .masterNextStateQuery => 97
  | .frontierCell => 98
  | .frontierDecisionCell => 99
  | .frontierChild => 100
  | .frontierPacket => 101
  | .normalizationCell => 102
  | .normalizationInsertCell => 103
  | .normalizationSearch => 104
  | .normalizationPair => 105
  | .normalizationCode => 106
  | .normalizationPacket => 107
  | .frontierEvaluationCell => 108
  | .frontierEvaluationPacket => 109
  | .frontierEvaluationAtom => 110
  | .stagePreservation => 111
  | .assignmentQueryCell => 112
  | .assignmentQueryReturn => 113
  | .transportApplicationCell => 114
  | .transportApplicationPacket => 115
  | .transportSplitDecision => 116
  | .executionPayload => 117

abbrev Summary := List (List (Bool × Nat)) × List (Nat × Bool) × Nat

def literalSummary : Literal → Bool × Nat
  | .positive var => (true, var)
  | .negative var => (false, var)

def summary {formula : Cnf} (state : GeneratedStructuralBranchContext formula) : Summary :=
  (state.context.formula.map (fun clause => clause.map literalSummary),
    state.context.decisions.map (fun decision => (decision.var, decision.value)), state.depth)

def expected (formula : Cnf) (decisions : List (Nat × Bool)) (depth : Nat) : Summary :=
  (formula.map (fun clause => clause.map literalSummary), decisions, depth)

def root : GeneratedStructuralBranchContext [] := GeneratedStructuralBranchContext.root []
def left : GeneratedStructuralBranchContext [] := root.child 0 false True.intro
def right : GeneratedStructuralBranchContext [] := root.child 0 true True.intro
def other : GeneratedStructuralBranchContext [] := root.child 1 false True.intro
def leftDeep : GeneratedStructuralBranchContext [] := left.child 2 false (by
  change (0 ≠ 2 ∧ True); exact ⟨by decide, True.intro⟩)
def rightDeep : GeneratedStructuralBranchContext [] := right.child 2 false (by
  change (0 ≠ 2 ∧ True); exact ⟨by decide, True.intro⟩)

def symmetric : Cnf := [[.positive 0, .negative 0], [.positive 1, .negative 1]]
def symmetricLeft : GeneratedStructuralBranchContext symmetric :=
  (GeneratedStructuralBranchContext.root symmetric).child 0 false True.intro
def symmetricRight : GeneratedStructuralBranchContext symmetric :=
  (GeneratedStructuralBranchContext.root symmetric).child 0 true True.intro

def asymmetric : Cnf := [[.positive 0], [.positive 1]]
def asymmetricLeft : GeneratedStructuralBranchContext asymmetric :=
  (GeneratedStructuralBranchContext.root asymmetric).child 0 false True.intro
def asymmetricRight : GeneratedStructuralBranchContext asymmetric :=
  (GeneratedStructuralBranchContext.root asymmetric).child 0 true True.intro

def addCounts (left right : List Nat) : List Nat := List.zipWith (· + ·) left right

def routingCounts {formula : Cnf} {selected : Var} :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target → List Nat
  | _, _, .identity _ => [1, 0, 0, 0, 0, 0]
  | _, _, .swap => [0, 1, 0, 0, 0, 0]
  | _, _, .absorbFirst _ => [0, 0, 1, 0, 0, 0]
  | _, _, .absorbSecond _ => [0, 0, 0, 1, 0, 0]
  | _, _, .prepend _ code => addCounts [0, 0, 0, 0, 1, 0] (routingCounts code)
  | _, _, .compose first second =>
      addCounts [0, 0, 0, 0, 0, 1] (addCounts (routingCounts first) (routingCounts second))

def normalizationProbe (formula : Cnf) (selected : Var)
    (source : List (GeneratedStructuralBranchContext formula))
    (wanted : List Summary) (counts : List Nat) : Bool :=
  let code := ControlFrontierNormalization.code formula selected source
  let allowance := ControlFrontierNormalization.bound formula selected source
  match ControlCompactExecution.sourceExecute allowance code with
  | none => false
  | some actual =>
    let length := actual.labels.length
    match ControlCompactExecution.sourceExecute length code, ControlCompactExecution.sourceExecute (length - 1) code,
        ControlCompactExecution.sourceExecute (allowance + 5) code with
    | some exact, none, some surplus =>
      actual.value.1.retained.map summary == wanted &&
      exact.value.1.retained.map summary == wanted &&
      surplus.value.1.retained.map summary == wanted &&
      routingCounts actual.value.1.code == counts &&
      routingCounts exact.value.1.code == counts &&
      routingCounts surplus.value.1.code == counts &&
      (actual.labels.filter (fun label => tag label == 106)).length == counts.foldl (· + ·) 0 &&
      (actual.labels.filter (fun label => tag label == 102)).length == source.length + 1 &&
      actual.labels.map tag == exact.labels.map tag && actual.labels.map tag == surplus.labels.map tag &&
      length <= allowance && !(ControlCompactExecution.sourceExecute 0 code).isSome
    | _, _, _ => false

def searchProbe (formula : Cnf) (selected : Var)
    (source target : GeneratedStructuralBranchContext formula) (wanted : Bool) : Bool :=
  let code := ControlFrontierNormalizationSearch.findCode formula selected source target
  let allowance := ControlFrontierNormalizationSearch.findBound source target
  match ControlCompactExecution.sourceExecute allowance code with
  | none => false
  | some actual =>
    let length := actual.labels.length
    match ControlCompactExecution.sourceExecute length code, ControlCompactExecution.sourceExecute (length - 1) code,
        ControlCompactExecution.sourceExecute (allowance + 5) code with
    | some exact, none, some surplus =>
      actual.value.1.isSome == wanted && exact.value.1.isSome == wanted &&
      surplus.value.1.isSome == wanted && actual.labels.map tag == exact.labels.map tag &&
      actual.labels.map tag == surplus.labels.map tag && length <= allowance
    | _, _, _ => false

def continuationSummary {formula : Cnf} :
    {frontier : List (GeneratedStructuralBranchContext formula)} →
    FrontierContinuation (generatedStructuralBranchSystem formula) frontier → Nat × List Bool
  | _, .head continuation => (0, [continuation.1 0, continuation.1 1, continuation.1 2])
  | _, .tail continuation =>
      let tail := continuationSummary continuation
      (tail.1 + 1, tail.2)

def falseContinuation : GeneratedStructuralBranchContinuation left :=
  ⟨fun _ => false, ⟨rfl, True.intro⟩⟩
def trueContinuation : GeneratedStructuralBranchContinuation right :=
  ⟨fun var => var == 0, ⟨rfl, True.intro⟩⟩

def routingProbe (source : List (GeneratedStructuralBranchContext []))
    (input : FrontierContinuation (generatedStructuralBranchSystem []) source)
    (forwardWanted backwardWanted : Nat × List Bool) : Bool :=
  let code := ControlFrontierNormalization.code [] 0 source
  match ControlCompactExecution.sourceExecute (ControlFrontierNormalization.bound [] 0 source) code with
  | none => false
  | some actual =>
      let preservation := actual.value.1.preservation
      let forward := preservation.forward.map input
      let backward := preservation.backward.map forward
      continuationSummary forward == forwardWanted &&
        continuationSummary backward == backwardWanted

def run : IO Unit := do
  let absorbed := [2, 0, 1, 0, 2, 2]
  let unresolved := [3, 1, 0, 0, 3, 3]
  let checks := [
    normalizationProbe [] 0 [] [] [1, 0, 0, 0, 0, 0],
    normalizationProbe [] 0 [root] [expected [] [] 0] [2, 0, 0, 0, 1, 1],
    normalizationProbe [] 0 [root, root] [expected [] [] 0] absorbed,
    normalizationProbe [] 0 [left, right] [expected [] [(0, true)] 1] absorbed,
    normalizationProbe [] 0 [right, left] [expected [] [(0, false)] 1] absorbed,
    normalizationProbe [] 0 [left, other]
      [expected [] [(1, false)] 1, expected [] [(0, false)] 1] unresolved,
    normalizationProbe [] 0 [left, right, other]
      [expected [] [(1, false)] 1, expected [] [(0, true)] 1] [3, 2, 1, 0, 5, 5],
    normalizationProbe [] 0 [root, left]
      [expected [] [(0, false)] 1, expected [] [] 0] unresolved,
    normalizationProbe symmetric 0 [symmetricLeft, symmetricRight]
      [expected [[.positive 1, .negative 1]] [(0, true)] 1] absorbed,
    normalizationProbe asymmetric 0 [asymmetricLeft, asymmetricRight]
      [expected [[.positive 1]] [(0, true)] 1,
        expected [[.positive 0], [.positive 1]] [(0, false)] 1] unresolved,
    normalizationProbe [] 0 [leftDeep, rightDeep]
      [expected [] [(2, false), (0, true)] 2] absorbed,
    searchProbe [] 0 left right true && searchProbe [] 0 right left true,
    searchProbe [] 0 left left false,
    searchProbe [] 1 left right false,
    searchProbe asymmetric 0 asymmetricLeft asymmetricRight false,
    searchProbe symmetric 5 (GeneratedStructuralBranchContext.root symmetric)
      (GeneratedStructuralBranchContext.root symmetric) true,
    routingProbe [left, right] (.head falseContinuation)
      (0, [true, false, false]) (1, [true, false, false]),
    routingProbe [right, left] (.head trueContinuation)
      (0, [false, false, false]) (1, [false, false, false]),
    routingProbe [left, other] (.head falseContinuation)
      (1, [false, false, false]) (0, [false, false, false])]
  if checks.length != 19 || checks.any (fun passed => !passed) then
    throw (IO.userError "Frontier normalization mismatch")
  let stdout ← IO.getStdout
  stdout.write "DOCUMENTARY_FRONTIER_NORMALIZATION_SMOKE_DONE\n".toUTF8
end FrontierNormalizationSmoke

def main : IO Unit := FrontierNormalizationSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms FrontierNormalizationSmoke.tag
#print axioms FrontierNormalizationSmoke.literalSummary
#print axioms FrontierNormalizationSmoke.summary
#print axioms FrontierNormalizationSmoke.expected
#print axioms FrontierNormalizationSmoke.root
#print axioms FrontierNormalizationSmoke.left
#print axioms FrontierNormalizationSmoke.right
#print axioms FrontierNormalizationSmoke.other
#print axioms FrontierNormalizationSmoke.leftDeep
#print axioms FrontierNormalizationSmoke.rightDeep
#print axioms FrontierNormalizationSmoke.symmetric
#print axioms FrontierNormalizationSmoke.symmetricLeft
#print axioms FrontierNormalizationSmoke.symmetricRight
#print axioms FrontierNormalizationSmoke.asymmetric
#print axioms FrontierNormalizationSmoke.asymmetricLeft
#print axioms FrontierNormalizationSmoke.asymmetricRight
#print axioms FrontierNormalizationSmoke.addCounts
#print axioms FrontierNormalizationSmoke.routingCounts
#print axioms FrontierNormalizationSmoke.normalizationProbe
#print axioms FrontierNormalizationSmoke.searchProbe
#print axioms FrontierNormalizationSmoke.continuationSummary
#print axioms FrontierNormalizationSmoke.falseContinuation
#print axioms FrontierNormalizationSmoke.trueContinuation
#print axioms FrontierNormalizationSmoke.routingProbe
#print axioms FrontierNormalizationSmoke.run
#print axioms main
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
"""


def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-frontier-normalization-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode("utf-8", "replace"))
    names = ("tag", "literalSummary", "summary", "expected", "root", "left", "right", "other",
             "leftDeep", "rightDeep", "symmetric", "symmetricLeft", "symmetricRight",
             "asymmetric", "asymmetricLeft", "asymmetricRight", "addCounts", "routingCounts",
             "normalizationProbe", "searchProbe", "continuationSummary", "falseContinuation",
             "trueContinuation", "routingProbe", "run")
    expected = {("'FrontierNormalizationSmoke." + name + "' does not depend on any axioms").encode()
                for name in names}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_FRONTIER_NORMALIZATION_SMOKE_DONE"))
    expected.add(b"'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact' does not depend on any axioms")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Unexpected runtime output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_FRONTIER_NORMALIZATION_SMOKE_OK: nineteen development checks; actual retained "
          "syntax, ordered decisions, generation depth and complete paid routing constructor counts; "
          "exact/short/surplus fuel; three observable transport probes outside the cost scope; "
          "twenty-seven clean runtime audits; client_sha256=" + hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_FRONTIER_NORMALIZATION_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
