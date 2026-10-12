#!/usr/bin/env python3
"""Independent development fixtures for actual bounded routing applications.
Whole continuations and their returned readers are consumed in both directions.
Exact costs are fixed by each branch before execution, not read from a trace.

The source interpreter is ControlCompactExecution.sourceExecute; its general
source_exact refinement preserves the whole value, business labels and fuel.
The retained repeated routing/reader and master probes have a 7200 s physical
timeout after the archived 300 s timeout; business fuels remain unchanged.
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
import Tests.LocalAlignment.DocumentaryControlFrontierExecutableEvaluation
import Tests.LocalAlignment.DocumentaryControlFrontierNormalization
import Tests.LocalAlignment.DocumentaryControlFrontierApplicationSplit
import Tests.LocalAlignment.DocumentaryControlFrontierExecutableOpening
import Tests.LocalAlignment.DocumentaryControlSeedApplication
import Tests.LocalAlignment.DocumentaryControlMaster
import Tests.LocalAlignment.DocumentaryMasterCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace FrontierApplicationSmoke
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.Agent.Local.Documentary
open Resources Control ControlBindings ControlMasterData Selection ControlAssignmentApplication

def tag : Label → Nat
  | .naturalComparison => 5
  | .formationWitness => 24
  | .formationResources => 25
  | .controlClosure => 89
  | .citationSeed => 42
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
  | _ => 999

def count (number : Nat) (labels : List Label) : Nat :=
  (labels.filter (fun label => tag label == number)).length

def root : GeneratedStructuralBranchContext [] := GeneratedStructuralBranchContext.root []
def left : GeneratedStructuralBranchContext [] := root.child 0 false True.intro
def right : GeneratedStructuralBranchContext [] := root.child 0 true True.intro
def other : GeneratedStructuralBranchContext [] := root.child 1 false True.intro
def falseContinuation : GeneratedStructuralBranchContinuation left :=
  ⟨fun _ => false, ⟨rfl, True.intro⟩⟩
def trueContinuation : GeneratedStructuralBranchContinuation right :=
  ⟨fun _ => true, ⟨rfl, True.intro⟩⟩
def otherContinuation : GeneratedStructuralBranchContinuation other :=
  ⟨fun _ => false, ⟨rfl, True.intro⟩⟩
def rootContinuation (value : Bool) : GeneratedStructuralBranchContinuation root :=
  ⟨fun _ => value, True.intro⟩
def forwardRelation : GeneratedStructuralFlipAtRelation 0 left right := ⟨rfl, rfl⟩
def reverseRelation : GeneratedStructuralFlipAtRelation 0 right left := ⟨rfl, rfl⟩

def swapRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [left,right,other] [right,left,other] := .swap
def reverseSwapRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [right,left,other] [left,right,other] := .swap
def identityRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [left,right,other] [left,right,other] := .identity _
def nestedRoute : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0)
    [left,right,other] [left,right,other] :=
  .compose swapRoute (.compose reverseSwapRoute identityRoute)

def position {formula : Cnf} :
    {frontier : List (GeneratedStructuralBranchContext formula)} →
    FrontierContinuation (generatedStructuralBranchSystem formula) frontier → Nat
  | _, .head _ => 0
  | _, .tail continuation => position continuation + 1

structure Observation (source : List (GeneratedStructuralBranchContext [])) where
  input : FrontierContinuation (generatedStructuralBranchSystem []) source
  reader : Reader (frontierAssignment (formula := []) (frontier := source) input)
  forwardPosition : Nat
  backwardPosition : Nat
  forwardBits : List Bool
  backwardBits : List Bool
  forwardCost : Nat
  backwardCost : Nat
  forwardFlips : Nat
  backwardFlips : Nat

def queryProbe {assignment : Assignment} (reader : Reader assignment)
    (query : Var) (wanted : Bool) (flips : Nat) : Bool :=
  let program := reader.readCode query
  let cost := 1 + 3 * flips
  match ControlCompactExecution.sourceExecute cost program, ControlCompactExecution.sourceExecute (cost - 1) program,
      ControlCompactExecution.sourceExecute (cost + 7) program, ControlCompactExecution.sourceExecute (reader.queryBound query) program with
  | some actual, none, some surplus, some uniform =>
      actual.value.1 == wanted && surplus.value.1 == wanted && uniform.value.1 == wanted &&
      actual.labels.length == cost && cost <= reader.queryBound query &&
      actual.labels.map tag == surplus.labels.map tag && actual.labels.map tag == uniform.labels.map tag &&
      count 112 actual.labels == flips + 1 && count 113 actual.labels == flips &&
      count 5 actual.labels == flips && !(actual.labels.map tag).contains 999
  | _, _, _, _ => false

def applicationProbe {frontier : List (GeneratedStructuralBranchContext [])}
    {expected : FrontierContinuation (generatedStructuralBranchSystem []) frontier} {ceiling : Nat}
    (program : Code Label (ControlFrontierApplication.Applied (formula := []) (frontier := frontier) 0 expected ceiling))
    (uniform exact wantedPosition : Nat) (bits : List Bool) (flips newlyFormed : Nat) : Bool :=
  match ControlCompactExecution.sourceExecute exact program, ControlCompactExecution.sourceExecute (exact - 1) program,
      ControlCompactExecution.sourceExecute (uniform + 7) program, ControlCompactExecution.sourceExecute uniform program with
  | some actual, none, some surplus, some bounded =>
      actual.labels.length == exact && exact <= uniform &&
      actual.labels.map tag == surplus.labels.map tag && actual.labels.map tag == bounded.labels.map tag &&
      count 112 actual.labels == 0 && count 113 actual.labels == 0 && count 5 actual.labels == 0 &&
      count 89 actual.labels == 3 * newlyFormed && count 24 actual.labels == newlyFormed && count 25 actual.labels == newlyFormed &&
      [actual.value, surplus.value, bounded.value].all (fun output =>
        position output.continuation.1 == wantedPosition && output.reader.queryBound 0 <= ceiling &&
        bits.length == 4 && ([0,1,2,17].zip bits).all (fun (query,wanted) =>
          queryProbe output.reader query wanted flips))
  | _, _, _, _ => false

def probe {source target : List (GeneratedStructuralBranchContext [])}
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0) source target)
    (nodes atoms formationCost : Nat) (observations : List (Observation source)) : Bool :=
  let program := ControlFrontierExecutableEvaluation.code [] 0 route
  let budget := ControlFrontierExecutableEvaluation.bound route
  match ControlCompactExecution.sourceExecute budget program, ControlCompactExecution.sourceExecute (budget - 1) program,
      ControlCompactExecution.sourceExecute (budget + 7) program with
  | some actual, none, some surplus =>
      budget == formationCost && actual.labels.length == formationCost &&
      actual.labels.map tag == surplus.labels.map tag &&
      count 108 actual.labels == nodes && count 109 actual.labels == nodes &&
      count 110 actual.labels == atoms && count 117 actual.labels == nodes &&
      observations.all (fun observation =>
        [actual.value.1, surplus.value.1].all (fun execution =>
          let forward := ControlFrontierApplication.forwardCode execution observation.input observation.reader
          let forwardBudget := ControlFrontierApplication.forwardBound execution observation.reader
          applicationProbe forward forwardBudget observation.forwardCost observation.forwardPosition observation.forwardBits observation.forwardFlips observation.forwardFlips &&
          match ControlCompactExecution.sourceExecute forwardBudget forward with
          | none => false
          | some output =>
              applicationProbe (ControlFrontierApplication.backwardCode execution output.value.continuation.1 output.value.reader)
                (ControlFrontierApplication.backwardBound execution output.value.reader)
                observation.backwardCost observation.backwardPosition observation.backwardBits observation.backwardFlips 0))
  | _, _, _ => false

def normalizedProbe (source : List (GeneratedStructuralBranchContext []))
    (nodes atoms formationCost : Nat) (observations : List (Observation source)) : Bool :=
  match ControlCompactExecution.sourceExecute (ControlFrontierNormalization.bound [] 0 source)
      (ControlFrontierNormalization.code [] 0 source) with
  | none => false
  | some actual => probe actual.value.1.code nodes atoms formationCost observations

def splitProgram : Code Label (Σ target, ControlFrontierApplication.ExecutablePreservation [] 0 [root,other] target) :=
  (ControlFrontierOpening.childCode root 0 false True.intro).bind (fun leftActual =>
    (ControlFrontierOpening.childCode root 0 true True.intro).bind (fun rightActual =>
      (ControlFrontierOpening.splitCode root 0 True.intro leftActual rightActual).bind (fun splitter =>
        (ControlFrontierApplication.expandCode 0 root True.intro leftActual rightActual splitter (rest := [other])).bind
          (fun execution => .done ⟨[leftActual.1,rightActual.1,other], execution.1⟩))))

def executionProbe {source : List (GeneratedStructuralBranchContext [])}
    (program : Code Label (Σ target, ControlFrontierApplication.ExecutablePreservation [] 0 source target))
    (formationExact formationUniform : Nat) (observation : Observation source) (queriesHead : Bool) : Bool :=
  match ControlCompactExecution.sourceExecute formationExact program, ControlCompactExecution.sourceExecute (formationExact - 1) program,
      ControlCompactExecution.sourceExecute (formationUniform + 7) program, ControlCompactExecution.sourceExecute formationUniform program with
  | some formed, none, some surplus, some uniform =>
    formed.labels.length == formationExact && formationExact <= formationUniform &&
    formed.labels.map tag == surplus.labels.map tag && formed.labels.map tag == uniform.labels.map tag &&
    [formed.value, surplus.value].all (fun packet =>
      let execution := packet.2
      let program := ControlFrontierApplication.forwardCode execution observation.input observation.reader
      let budget := ControlFrontierApplication.forwardBound execution observation.reader
      match ControlCompactExecution.sourceExecute observation.forwardCost program, ControlCompactExecution.sourceExecute (observation.forwardCost - 1) program,
          ControlCompactExecution.sourceExecute budget program, ControlCompactExecution.sourceExecute (budget + 7) program with
      | some output, none, some bounded, some more =>
        output.labels.length == observation.forwardCost &&
        output.labels.map tag == bounded.labels.map tag && output.labels.map tag == more.labels.map tag &&
        count 112 output.labels == (if queriesHead then 1 else 0) && count 113 output.labels == 0 &&
        count 116 output.labels == (if queriesHead then 1 else 0) && count 24 output.labels == (if queriesHead then 1 else 0) &&
        [output.value, bounded.value, more.value].all (fun applied =>
          position applied.continuation.1 == observation.forwardPosition &&
          (observation.forwardBits.zip [0,1,2,17]).all (fun (wanted,query) => queryProbe applied.reader query wanted 0) &&
          let backward := ControlFrontierApplication.backwardCode execution applied.continuation.1 applied.reader
          match ControlCompactExecution.sourceExecute observation.backwardCost backward, ControlCompactExecution.sourceExecute (observation.backwardCost - 1) backward,
              ControlCompactExecution.sourceExecute (ControlFrontierApplication.backwardBound execution applied.reader + 7) backward with
          | some returned, none, some enough =>
            returned.labels.length == observation.backwardCost && returned.labels.map tag == enough.labels.map tag &&
            count 112 returned.labels == 0 && count 116 returned.labels == 0 &&
            [returned.value,enough.value].all (fun result =>
              position result.continuation.1 == observation.backwardPosition &&
              (observation.backwardBits.zip [0,1,2,17]).all (fun (wanted,query) => queryProbe result.reader query wanted 0))
          | _,_,_ => false)
      | _,_,_,_ => false)
  | _,_,_,_ => false

def splitProbe (observation : Observation [root,other]) (isHead : Bool) : Bool :=
  executionProbe splitProgram 21 21 observation isHead

def openingProbe {source : List (GeneratedStructuralBranchContext [])}
    (observation : Observation source) (fresh : Bool) (formationExact formationUniform : Nat) : Bool :=
  let program := (ControlFrontierExecutableOpening.code [] 0 source).bind (fun produced =>
    .done ⟨produced.opening.1.frontier, produced.execution⟩)
  ControlFrontierExecutableOpening.bound [] 0 source == formationUniform &&
    executionProbe program formationExact formationUniform observation fresh

def seedProbe (left right : Bool) (selected : Var) : Bool :=
  let exact := if left || right then 6 else 2
  let program := ControlSeedApplication.code selected left right
  match ControlCompactExecution.sourceExecute exact program, ControlCompactExecution.sourceExecute (exact - 1) program,
      ControlCompactExecution.sourceExecute 6 program, ControlCompactExecution.sourceExecute 13 program with
  | some actual, none, some uniform, some surplus =>
    actual.labels.length == exact && actual.labels.map tag == uniform.labels.map tag &&
    actual.labels.map tag == surplus.labels.map tag && count 42 actual.labels == 1 && count 24 actual.labels == 1 &&
    count 89 actual.labels == (if left || right then 3 else 0) && count 25 actual.labels == (if left || right then 1 else 0) &&
    [actual.value,uniform.value,surplus.value].all (fun output => match output with
      | .blocked _ _ => !left && !right
      | .viable _ _ reader _ _ =>
          (left || right) && [0,selected,257].all (fun query =>
            reader.queryBound query == 1 && queryProbe reader query (!left) 0))
  | _,_,_,_ => false

def masterProbe {context} (cursor : EndogenousDecomposition.MasterResources.Cursor)
    (sources : Support SourceValue context) (contract : Contract) (demand : Demand)
    (left right : Location context) (memory : Memory sources contract)
    (wanted : Option Nat) (nodes atoms queryCells queryReturns : Nat) : Bool :=
  let search := ControlMaster.executableSearchCode cursor sources contract demand left right
  match ControlCompactExecution.sourceExecute 200000 search with
  | none => false
  | some formed =>
    count 108 formed.labels == nodes && count 109 formed.labels == nodes &&
    count 110 formed.labels == atoms && count 111 formed.labels == 1 &&
    count 112 formed.labels == 0 && count 113 formed.labels == 0 &&
    let program := ControlCompletion.executedDecideCode formed.value.stage.1 memory formed.value.payload
    let budget := ControlCompletion.executedDecideBound formed.value.stage.1 formed.value.payload
    match ControlCompactExecution.sourceExecute budget program with
    | none => false
    | some actual =>
      let cost := actual.labels.length
      match ControlCompactExecution.sourceExecute cost program, ControlCompactExecution.sourceExecute (cost - 1) program,
          ControlCompactExecution.sourceExecute (budget + 7) program with
      | some exact, none, some surplus =>
        let outputPosition := fun (decision : Master.Decision formed.value.stage.1 memory) => match decision with
          | .blocked _ _ => none
          | .complete packet => some packet.result.2.position
        [actual.value.1,exact.value.1,surplus.value.1].all (fun decision => outputPosition decision == wanted) &&
        cost <= budget && actual.labels.map tag == exact.labels.map tag && actual.labels.map tag == surplus.labels.map tag &&
        count 112 actual.labels == queryCells && count 113 actual.labels == queryReturns
      | _,_,_ => false

theorem acceptancePreserved {source target : List (GeneratedStructuralBranchContext [])}
    (execution : ControlFrontierApplication.ExecutablePreservation [] 0 source target)
    (input : FrontierContinuation (generatedStructuralBranchSystem []) source)
    (accepted : FrontierAccept (generatedStructuralBranchSystem []) source input) :
    FrontierAccept (generatedStructuralBranchSystem []) source
      (execution.preservation.backward.map (execution.preservation.forward.map input)) :=
  execution.preservation.backward.preservesAccept _ (execution.preservation.forward.preservesAccept input accepted)

def run : IO Unit := do
  let zero := [false,false,false,false]
  let one := [true,true,true,true]
  let flippedZero := [true,false,false,false]
  let flippedOne := [false,true,true,true]
  let checks := [
    probe identityRoute 1 0 9
      [⟨.head falseContinuation, constantReader false, 0,0,zero,zero,2,2,0,0⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 1,1,one,one,2,2,0,0⟩,
       ⟨.tail (.tail (.head otherContinuation)), constantReader false, 2,2,zero,zero,2,2,0,0⟩],
    probe swapRoute 1 0 9
      [⟨.head falseContinuation, constantReader false, 1,0,zero,zero,2,3,0,0⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 0,1,one,one,3,2,0,0⟩,
       ⟨.tail (.tail (.head otherContinuation)), constantReader false, 2,2,zero,zero,3,3,0,0⟩],
    probe (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := [other]) forwardRelation) 1 1 12
      [⟨.head falseContinuation, constantReader false, 0,1,flippedZero,flippedZero,7,2,1,1⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 0,1,one,one,2,2,0,0⟩,
       ⟨.tail (.tail (.head otherContinuation)), constantReader false, 1,2,zero,zero,2,2,0,0⟩],
    probe (.absorbSecond (action := generatedStructuralFlipAtAction [] 0) (rest := [other]) reverseRelation) 1 1 12
      [⟨.head falseContinuation, constantReader false, 0,0,zero,zero,2,2,0,0⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 0,0,flippedOne,flippedOne,8,2,1,1⟩,
       ⟨.tail (.tail (.head otherContinuation)), constantReader false, 1,2,zero,zero,3,2,0,0⟩],
    probe (show AcceptedFrontierCode (generatedStructuralFlipAtAction [] 0) [other,left,right] [other,right] from
      .prepend other (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := []) forwardRelation)) 2 1 21
      [⟨.head otherContinuation, constantReader false, 0,0,zero,zero,2,2,0,0⟩,
       ⟨.tail (.head falseContinuation), constantReader false, 1,2,flippedZero,flippedZero,9,4,1,1⟩,
       ⟨.tail (.tail (.head trueContinuation)), constantReader true, 1,2,one,one,4,4,0,0⟩],
    probe (.compose swapRoute (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := [other]) reverseRelation)) 3 1 30
      [⟨.head falseContinuation, constantReader false, 0,0,zero,zero,6,7,0,0⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 0,0,flippedOne,flippedOne,12,7,1,1⟩,
       ⟨.tail (.tail (.head otherContinuation)), constantReader false, 1,2,zero,zero,7,7,0,0⟩],
    probe nestedRoute 5 0 45
      [⟨.head falseContinuation, constantReader false, 0,0,zero,zero,11,11,0,0⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 1,1,one,one,11,11,0,0⟩,
       ⟨.tail (.tail (.head otherContinuation)), constantReader false, 2,2,zero,zero,12,12,0,0⟩],
    probe (.compose
      (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := [left]) forwardRelation)
      (.absorbFirst (action := generatedStructuralFlipAtAction [] 0) (rest := []) reverseRelation)) 3 2 33
      [⟨.head falseContinuation, constantReader false, 0,2,zero,zero,16,6,2,2⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 0,2,flippedOne,flippedOne,11,6,1,1⟩,
       ⟨.tail (.tail (.head falseContinuation)), constantReader false, 0,2,zero,zero,6,6,0,0⟩],
    normalizedProbe [left,right] 7 1 66
      [⟨.head falseContinuation, constantReader false, 0,1,flippedZero,flippedZero,11,12,1,1⟩,
       ⟨.tail (.head trueContinuation), constantReader true, 0,1,one,one,12,12,0,0⟩],
    normalizedProbe [left,other] 10 0 90
      [⟨.head falseContinuation, constantReader false, 1,0,zero,zero,12,13,0,0⟩,
       ⟨.tail (.head otherContinuation), constantReader false, 0,1,zero,zero,17,16,0,0⟩],
    splitProbe ⟨.head (rootContinuation false), constantReader false, 0,0,zero,zero,5,3,0,0⟩ true,
    splitProbe ⟨.head (rootContinuation true), constantReader true, 1,0,one,one,5,4,0,0⟩ true,
    splitProbe ⟨.tail (.head otherContinuation), constantReader false, 2,1,zero,zero,2,3,0,0⟩ false,
    openingProbe (source := [root]) ⟨.head (rootContinuation false), constantReader false, 0,0,zero,zero,9,7,0,0⟩ true 47 47,
    openingProbe (source := [root]) ⟨.head (rootContinuation true), constantReader true, 1,0,one,one,9,8,0,0⟩ true 47 47,
    openingProbe (source := [left]) ⟨.head falseContinuation, constantReader false, 0,0,zero,zero,2,2,0,0⟩ false 21 50,
    seedProbe false false 0,
    seedProbe false true 41,
    seedProbe true false 41,
    seedProbe true true 0,
    masterProbe EndogenousDecomposition.VariableMaster.Example.origin Cases.sources MasterCases.bothContract Cases.factDemand
      Cases.privateOrigin Cases.publicOrigin (empty Cases.sources MasterCases.bothContract) (some 1) 7 1 3 1,
    masterProbe EndogenousDecomposition.VariableMaster.Example.origin Cases.sources Cases.contract Cases.factDemand
      Cases.privateOrigin Cases.publicOrigin Cases.initial (some 1) 10 0 2 0,
    masterProbe EndogenousDecomposition.VariableMaster.Example.origin Cases.sources Cases.contract Cases.pinnedDemand
      Cases.privateOrigin Cases.publicOrigin Cases.initial none 7 1 0 0]
  if checks.length != 23 || checks.any (fun passed => !passed) then
    throw (IO.userError "Frontier application mismatch")
  let stdout ← IO.getStdout
  stdout.write "DOCUMENTARY_FRONTIER_APPLICATION_SMOKE_DONE\n".toUTF8
end FrontierApplicationSmoke

def main : IO Unit := FrontierApplicationSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms FrontierApplicationSmoke.tag
#print axioms FrontierApplicationSmoke.count
#print axioms FrontierApplicationSmoke.root
#print axioms FrontierApplicationSmoke.left
#print axioms FrontierApplicationSmoke.right
#print axioms FrontierApplicationSmoke.other
#print axioms FrontierApplicationSmoke.falseContinuation
#print axioms FrontierApplicationSmoke.trueContinuation
#print axioms FrontierApplicationSmoke.otherContinuation
#print axioms FrontierApplicationSmoke.rootContinuation
#print axioms FrontierApplicationSmoke.forwardRelation
#print axioms FrontierApplicationSmoke.reverseRelation
#print axioms FrontierApplicationSmoke.swapRoute
#print axioms FrontierApplicationSmoke.reverseSwapRoute
#print axioms FrontierApplicationSmoke.identityRoute
#print axioms FrontierApplicationSmoke.nestedRoute
#print axioms FrontierApplicationSmoke.position
#print axioms FrontierApplicationSmoke.Observation
#print axioms FrontierApplicationSmoke.queryProbe
#print axioms FrontierApplicationSmoke.applicationProbe
#print axioms FrontierApplicationSmoke.probe
#print axioms FrontierApplicationSmoke.normalizedProbe
#print axioms FrontierApplicationSmoke.splitProgram
#print axioms FrontierApplicationSmoke.executionProbe
#print axioms FrontierApplicationSmoke.splitProbe
#print axioms FrontierApplicationSmoke.openingProbe
#print axioms FrontierApplicationSmoke.seedProbe
#print axioms FrontierApplicationSmoke.masterProbe
#print axioms FrontierApplicationSmoke.acceptancePreserved
#print axioms FrontierApplicationSmoke.run
#print axioms main
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
"""
NAMES = ('tag','count','root','left','right','other','falseContinuation','trueContinuation',
         'otherContinuation','rootContinuation','forwardRelation','reverseRelation','swapRoute','reverseSwapRoute',
         'identityRoute','nestedRoute','position','Observation','queryProbe','applicationProbe',
         'probe','normalizedProbe','splitProgram','executionProbe','splitProbe','openingProbe','seedProbe','masterProbe','acceptancePreserved','run')

def main():
    source = CLIENT.encode('utf-8')
    with tempfile.TemporaryDirectory(prefix='rp-frontier-application-') as directory:
        client = Path(directory) / 'Smoke.lean'
        client.write_bytes(source)
        result = subprocess.run(['lake','env','lean','--run',str(client)], cwd=ROOT,
                                capture_output=True, timeout=7200, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode('utf-8','replace'))
    expected = {("'FrontierApplicationSmoke." + name + "' does not depend on any axioms").encode()
                for name in NAMES}
    expected.update((b"'main' does not depend on any axioms", b'DOCUMENTARY_FRONTIER_APPLICATION_SMOKE_DONE'))
    expected.add(b"'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact' does not depend on any axioms")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError('Unexpected runtime output: ' + result.stdout.decode('utf-8','replace'))
    print('DOCUMENTARY_FRONTIER_APPLICATION_SMOKE_OK: twenty-three fixed development checks; '
          'all six constructors, actual split children and shared complete openings; thirty-four forward/backward pairs using actual returned readers; '
          'four complete seed cases and three actual master decisions; exact/short/surplus and uniform fuel; thirty-two clean runtime audits; '
          'client_sha256=' + hashlib.sha256(source).hexdigest())

if __name__ == '__main__':
    try:
        main()
    except (OSError,ValueError,subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_FRONTIER_APPLICATION_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
