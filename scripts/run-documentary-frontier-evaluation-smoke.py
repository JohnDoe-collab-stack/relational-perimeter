#!/usr/bin/env python3
"""Fixed independent routing fixtures. Map invocations are outside formation cost.
All six constructors, actual recursive composition, received normalized codes and
the whole actual stage are checked. This is a development protocol, not a model
experiment or bootstrap/physical cost theorem.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryControlCompletion
import Tests.LocalAlignment.DocumentaryControlStagePreservation
import Tests.LocalAlignment.DocumentaryControlFrontierNormalization
import Tests.LocalAlignment.DocumentaryMasterCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace FrontierEvaluationSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings Selection

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

def root : GeneratedStructuralBranchContext [] := GeneratedStructuralBranchContext.root []
def left : GeneratedStructuralBranchContext [] := root.child 0 false True.intro
def right : GeneratedStructuralBranchContext [] := root.child 0 true True.intro
def other : GeneratedStructuralBranchContext [] := root.child 1 false True.intro

def swapRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [left, right, other] [right, left, other] := .swap

def reverseSwapRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [right, left, other] [left, right, other] := .swap

def identityRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [left, right, other] [left, right, other] := AcceptedFrontierCode.identity (action := generatedStructuralFlipAtAction [] 0) [left, right, other]

def nestedRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [left, right, other] [left, right, other] :=
  .compose swapRoute (.compose reverseSwapRoute identityRoute)

def forwardRelation : GeneratedStructuralFlipAtRelation 0 left right := ⟨rfl, rfl⟩
def reverseRelation : GeneratedStructuralFlipAtRelation 0 right left := ⟨rfl, rfl⟩
def falseContinuation : GeneratedStructuralBranchContinuation left :=
  ⟨fun _ => false, ⟨rfl, True.intro⟩⟩
def trueContinuation : GeneratedStructuralBranchContinuation right :=
  ⟨fun var => var == 0, ⟨rfl, True.intro⟩⟩
def otherContinuation : GeneratedStructuralBranchContinuation other :=
  ⟨fun _ => false, ⟨rfl, True.intro⟩⟩

abbrev View := Nat × List Bool
abbrev Observation (source : List (GeneratedStructuralBranchContext [])) :=
  FrontierContinuation (generatedStructuralBranchSystem []) source × View × View

def view {formula : Cnf} :
    {frontier : List (GeneratedStructuralBranchContext formula)} →
    FrontierContinuation (generatedStructuralBranchSystem formula) frontier → View
  | _, .head continuation => (0, [continuation.1 0, continuation.1 1, continuation.1 2, continuation.1 17])
  | _, .tail continuation =>
      let result := view continuation
      (result.1 + 1, result.2)

def count (number : Nat) (labels : List Label) : Nat :=
  (labels.filter (fun label => tag label == number)).length

def probe {source target : List (GeneratedStructuralBranchContext [])}
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0) source target)
    (nodes atoms allowance : Nat) (observations : List (Observation source)) : Bool :=
  let program := ControlFrontierEvaluation.code [] 0 route
  let budget := ControlFrontierEvaluation.bound [] 0 route
  match Control.execute budget program, Control.execute (budget - 1) program,
      Control.execute (budget + 5) program with
  | some actual, none, some surplus =>
      let preservation := actual.value.1
      budget == allowance && actual.labels.length == allowance &&
      actual.labels.map tag == surplus.labels.map tag &&
      count 108 actual.labels == nodes && count 109 actual.labels == nodes &&
      count 110 actual.labels == atoms && count 111 actual.labels == 0 &&
      count 89 actual.labels == nodes * 2 + atoms &&
      count 25 actual.labels == nodes && count 24 actual.labels == atoms &&
      !(Control.execute 0 program).isSome &&
      observations.all (fun (input, forwardWanted, backwardWanted) =>
        let forward := preservation.forward.map input
        let backward := preservation.backward.map forward
        let surplusForward := surplus.value.1.forward.map input
        let surplusBackward := surplus.value.1.backward.map surplusForward
        view forward == forwardWanted && view backward == backwardWanted &&
        view surplusForward == forwardWanted && view surplusBackward == backwardWanted)
  | _, _, _ => false

def normalizedProbe (source : List (GeneratedStructuralBranchContext []))
    (nodes atoms allowance : Nat) (observations : List (Observation source)) : Bool :=
  match Control.execute (ControlFrontierNormalization.bound [] 0 source)
      (ControlFrontierNormalization.code [] 0 source) with
  | none => false
  | some actual => probe actual.value.1.code nodes atoms allowance observations

def stageProbe : Bool :=
  let stage := MasterCases.bothRun.1
  let program := ControlStagePreservation.code stage
  let budget := ControlStagePreservation.bound stage
  let input : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
      [GeneratedStructuralBranchContext.root stage.formula] :=
    .head ⟨fun _ => false, True.intro⟩
  match Control.execute budget program, Control.execute (budget - 1) program,
      Control.execute (budget + 5) program with
  | some actual, none, some surplus =>
    let forward := actual.value.1.forward.map input
    let backward := actual.value.1.backward.map forward
    let selected := EndogenousDecomposition.VariableMaster.selected stage.head
    budget == 42 && actual.labels.length == 42 &&
    count 108 actual.labels == 7 && count 109 actual.labels == 7 &&
    count 110 actual.labels == 1 && count 111 actual.labels == 1 &&
    count 89 actual.labels == 17 && count 25 actual.labels == 8 && count 24 actual.labels == 1 &&
    actual.labels.map tag == surplus.labels.map tag &&
    (frontierAssignment forward) selected && (frontierAssignment backward) selected &&
    !(frontierAssignment forward 0) && !(frontierAssignment backward 0) &&
    (view forward).1 == 0 && (view backward).1 == 0 &&
    view (surplus.value.1.forward.map input) == view forward &&
    view (surplus.value.1.backward.map (surplus.value.1.forward.map input)) == view backward &&
    frontierAssignment (surplus.value.1.forward.map input) selected &&
    frontierAssignment (surplus.value.1.backward.map (surplus.value.1.forward.map input)) selected
  | _, _, _ => false

def decisionProbe {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (memory : Memory sources contract) (wanted : Option Nat) (nodes atoms : Nat) : Bool :=
  let program := ControlCompletion.expandedDecideCode stage memory
  let budget := ControlCompletion.expandedDecideBound stage memory
  match Control.execute budget program with
  | none => false
  | some actual =>
    let length := actual.labels.length
    match Control.execute length program, Control.execute (length - 1) program,
        Control.execute (budget + 5) program with
    | some exact, none, some surplus =>
      let position := fun (decision : Master.Decision stage memory) => match decision with
        | .blocked _ _ => none
        | .complete packet => some packet.result.2.position
      position actual.value.1 == wanted && position exact.value.1 == wanted &&
      position surplus.value.1 == wanted && length <= budget &&
      actual.labels.map tag == exact.labels.map tag && actual.labels.map tag == surplus.labels.map tag &&
      count 108 actual.labels == nodes && count 109 actual.labels == nodes &&
      count 110 actual.labels == atoms && count 111 actual.labels == (if nodes == 0 then 0 else 1)
    | _, _, _ => false

/-- Both acceptance laws in the returned packet are available, including the
backward inclusion after grouping. This client keeps the original laws. -/
theorem acceptancePreserved {source target : List (GeneratedStructuralBranchContext [])}
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0) source target)
    (actual : ControlMasterData.Actual route.eval)
    (input : FrontierContinuation (generatedStructuralBranchSystem []) source)
    (accepted : FrontierAccept (generatedStructuralBranchSystem []) source input) :
    FrontierAccept (generatedStructuralBranchSystem []) source
      (actual.1.backward.map (actual.1.forward.map input)) :=
  actual.1.backward.preservesAccept _ (actual.1.forward.preservesAccept input accepted)

def run : IO Unit := do
  let zero := [false, false, false, false]
  let one := [true, false, false, false]
  let inputs : List (Observation [left, right, other]) :=
    [(.head falseContinuation, (0, zero), (0, zero)),
     (.tail (.head trueContinuation), (1, one), (1, one)),
     (.tail (.tail (.head otherContinuation)), (2, zero), (2, zero))]
  let checks := [
    probe identityRoute 1 0 5 inputs,
    probe swapRoute 1 0 5
      [(.head falseContinuation, (1, zero), (0, zero)),
       (.tail (.head trueContinuation), (0, one), (1, one)),
       (.tail (.tail (.head otherContinuation)), (2, zero), (2, zero))],
    probe (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := [other]) forwardRelation) 1 1 8
      [(.head falseContinuation, (0, one), (1, one)),
       (.tail (.head trueContinuation), (0, one), (1, one)),
       (.tail (.tail (.head otherContinuation)), (1, zero), (2, zero))],
    probe (.absorbSecond (action := generatedStructuralFlipAtAction [] 0) (rest := [other]) reverseRelation) 1 1 8
      [(.head falseContinuation, (0, zero), (0, zero)),
       (.tail (.head trueContinuation), (0, zero), (0, zero)),
       (.tail (.tail (.head otherContinuation)), (1, zero), (2, zero))],
    probe (.prepend other (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := []) forwardRelation)) 2 1 13
      [(.head otherContinuation, (0, zero), (0, zero)),
       (.tail (.head falseContinuation), (1, one), (2, one)),
       (.tail (.tail (.head trueContinuation)), (1, one), (2, one))],
    probe (.compose swapRoute
      (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := [other]) reverseRelation)) 3 1 18
      [(.head falseContinuation, (0, zero), (0, zero)),
       (.tail (.head trueContinuation), (0, zero), (0, zero)),
       (.tail (.tail (.head otherContinuation)), (1, zero), (2, zero))],
    probe nestedRoute 5 0 25 inputs,
    normalizedProbe [left, right] 7 1 38
      [(.head falseContinuation, (0, one), (1, one)),
       (.tail (.head trueContinuation), (0, one), (1, one))],
    normalizedProbe [left, other] 10 0 50
      [(.head falseContinuation, (1, zero), (0, zero)),
       (.tail (.head otherContinuation), (0, zero), (1, zero))],
    stageProbe,
    decisionProbe MasterCases.bothRun.1 (empty Cases.sources MasterCases.bothContract) (some 1) 7 1,
    decisionProbe MasterCases.factRun.1 Cases.initial (some 1) 10 0,
    decisionProbe MasterCases.pinnedRun.1 Cases.initial none 0 0]
  if checks.length != 13 || checks.any (fun passed => !passed) then
    throw (IO.userError "Frontier evaluation mismatch")
  let stdout ← IO.getStdout
  stdout.write "DOCUMENTARY_FRONTIER_EVALUATION_SMOKE_DONE\n".toUTF8
end FrontierEvaluationSmoke

def main : IO Unit := FrontierEvaluationSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms FrontierEvaluationSmoke.tag
#print axioms FrontierEvaluationSmoke.root
#print axioms FrontierEvaluationSmoke.left
#print axioms FrontierEvaluationSmoke.right
#print axioms FrontierEvaluationSmoke.other
#print axioms FrontierEvaluationSmoke.swapRoute
#print axioms FrontierEvaluationSmoke.reverseSwapRoute
#print axioms FrontierEvaluationSmoke.identityRoute
#print axioms FrontierEvaluationSmoke.nestedRoute
#print axioms FrontierEvaluationSmoke.forwardRelation
#print axioms FrontierEvaluationSmoke.reverseRelation
#print axioms FrontierEvaluationSmoke.falseContinuation
#print axioms FrontierEvaluationSmoke.trueContinuation
#print axioms FrontierEvaluationSmoke.otherContinuation
#print axioms FrontierEvaluationSmoke.view
#print axioms FrontierEvaluationSmoke.count
#print axioms FrontierEvaluationSmoke.probe
#print axioms FrontierEvaluationSmoke.normalizedProbe
#print axioms FrontierEvaluationSmoke.stageProbe
#print axioms FrontierEvaluationSmoke.decisionProbe
#print axioms FrontierEvaluationSmoke.acceptancePreserved
#print axioms FrontierEvaluationSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""
NAMES = ('tag', 'root', 'left', 'right', 'other', 'swapRoute', 'reverseSwapRoute', 'identityRoute', 'nestedRoute', 'forwardRelation', 'reverseRelation', 'falseContinuation', 'trueContinuation', 'otherContinuation', 'view', 'count', 'probe', 'normalizedProbe', 'stageProbe', 'decisionProbe', 'acceptancePreserved', 'run')

def main():
    source = CLIENT.encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-frontier-evaluation-') as directory:
        client = Path(directory) / 'Smoke.lean'
        client.write_bytes(source)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode('utf-8', 'replace'))
    expected = {("'FrontierEvaluationSmoke." + name + "' does not depend on any axioms").encode()
                for name in NAMES}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_FRONTIER_EVALUATION_SMOKE_DONE'))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError('Unexpected runtime output: ' + result.stdout.decode('utf-8', 'replace'))
    print('DOCUMENTARY_FRONTIER_EVALUATION_SMOKE_OK: thirteen development checks, all six constructors, '
          'twenty-six forward/backward observations repeated with surplus fuel; '
          'exact/short/surplus fuel and fixed local formation costs; whole actual stage; '
          'twenty-three clean runtime audits; client_sha256=' + hashlib.sha256(source).hexdigest())

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_FRONTIER_EVALUATION_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
