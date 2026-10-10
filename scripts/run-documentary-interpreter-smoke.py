#!/usr/bin/env python3
"""Fuel matrices over actual documentary packets, with literal expectations.

Resource reads feed the retained producer and a proved structural arithmetic
interpretation. Unary natural traversal is counted; physical primitive costs
remain a separate boundary.
Control loading receives the existing dossier/store, as in the component codec.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryControlInterpreterCases
import Tests.LocalAlignment.DocumentaryMasterCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryInterpreterSmoke
open ConstitutiveSearch
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Snapshot Control ControlBindings ControlInterpreterCases

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

def baselineLabels : List Nat :=
  [0, 37, 10, 6, 5, 6, 5, 6, 7, 7, 35,
    10, 10, 11, 6, 5, 5, 7, 12, 12, 36] ++
    List.replicate 8 5 ++ List.replicate 43 5 ++ [34, 5, 5, 35, 35, 38, 39, 40, 41,
      42, 43, 44, 45, 46, 47, 48, 49, 12, 12, 23, 24, 25, 2,
      10, 10, 11, 12, 36, 50, 51, 52, 53, 54, 33]

def refusedLabels : List Nat :=
  [0, 37, 10, 6, 5, 6, 5, 6, 7, 7, 35,
    10, 10, 11, 6, 5, 5, 7, 12, 12, 36] ++
    List.replicate 8 5 ++ List.replicate 43 5 ++ [34, 5, 35, 35, 38, 39, 40, 41, 42, 53, 54, 33]

def revisedLabels : List Nat :=
  [0, 37, 10, 10, 11, 6, 5, 5, 7, 12, 12, 36] ++
    List.replicate 8 5 ++ List.replicate 43 5 ++ [34, 5, 5, 35, 35] ++
    [10, 10, 10, 11, 11, 6, 5, 5, 6, 5, 5, 5, 7, 7, 12, 12, 12, 36] ++
    List.replicate 8 5 ++ List.replicate 44 5 ++ [34, 5, 5, 5, 35, 35, 38, 39, 40, 41,
      42, 43, 44, 45, 46, 47, 48, 49, 12, 12, 12, 23, 24, 25, 2,
      10, 10, 10, 11, 11, 12, 36, 50, 51, 52, 53, 54, 33]

def traceTag {Value : Type u} {code : Code Label Value} {labels value} :
    Eval code labels value → Nat
  | .done => 0
  | .step _ => 1

def eventTag : Event → Nat
  | .quoted => 0
  | .derived => 1
  | .refused => 2
  | .missing => 3

def stepCheck {slots spec}
    (before : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (instruction : Instruction Cases.context DeductionCases.policy slots spec)
    (bound : Nat) (labels : List Nat) (event : Event) (value : Option Int)
    (origins : Option (List Nat)) (successful : Bool) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlStep.code before instruction) with
  | none => fuel < bound
  | some actual =>
      let packet := actual.value.1
      let found := packet.next.bindings .here
      let readValue := ProgramCases.bindingValue packet.next.store found
      let readOrigins := found.map (fun occurrence => occurrence.1.origins)
      (bound ≤ fuel) && (actual.labels.map tag == labels) &&
        (eventTag packet.event == eventTag event) && (readValue == value) && (readOrigins == origins) &&
        (Program.succeeded packet.next == successful)

def readCheck {spec}
    (slot : Ref [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec] spec)
    (bound position : Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (readCode finalTable slot) with
  | none => fuel < bound
  | some actual => (bound ≤ fuel) && (actual.labels.map tag == List.replicate bound 1) &&
      (ProgramCases.bindingPosition ProgramCases.actual.1.store actual.value.1 == some position) &&
      (ProgramCases.bindingValue ProgramCases.actual.1.store actual.value.1 == some 42)

def matrices : List Bool :=
  let fuels := List.range 200
  (fuels.map (stepCheck quoteFrame quoteInstruction 106 baselineLabels .quoted (some 42) (some [1]) true)) ++
  (fuels.map (stepCheck twoFrame (.quotation ProgramCases.revisedTask) 176 revisedLabels
    .quoted (some 43) (some [2]) true)) ++
  (fuels.map (stepCheck twoFrame differenceInstruction 87
    ([0, 1, 1, 1, 10, 6, 5, 7, 12, 12, 12, 10, 10, 11, 10, 13, 13, 13, 14, 14, 14, 15, 16, 21, 22, 19] ++ List.replicate 43 17 ++ [23, 24, 25, 3, 9, 10, 10, 10, 11, 10, 26, 27, 28, 29, 30, 31, 32, 33])
    .derived (some 1) (some [1, 2]) true)) ++
  (fuels.map (stepCheck sumFrame sumInstruction 61
    [0, 1, 1, 1, 1, 10, 10, 11, 6, 5, 6, 5, 5, 7, 7, 12, 12, 12, 12,
      10, 10, 11, 10, 10, 11, 13, 13, 13, 14, 14, 14, 15, 16, 21, 19, 17, 17, 18, 20, 23, 24, 25, 3, 9,
      10, 10, 11, 10, 10, 11, 10, 10, 11, 26, 27, 28, 29, 30, 31, 32, 33]
    .derived (some 2) (some [1, 2, 1, 2]) true)) ++
  (fuels.map (stepCheck twoFrame forbiddenInstruction 23 [0, 1, 1, 1, 10, 10, 10, 11, 11, 6, 5, 6, 5, 5, 6, 7, 7, 8, 9, 30, 31, 32, 33]
    .refused none none false)) ++
  (fuels.map (stepCheck refusedFrame leftMissing 3 [0, 1, 4] .missing none none false)) ++
  (fuels.map (stepCheck refusedFrame rightMissing 5 [0, 1, 1, 1, 4] .missing none none false)) ++
  (fuels.map (stepCheck quoteFrame (.quotation ⟨Cases.pinnedDemand, Cases.privateOrigin, Cases.publicOrigin⟩)
    84 refusedLabels .refused none none false)) ++
  (fuels.map (stepCheck twoFrame
    (.conclusion DeductionCases.differenceRequest (.prior .here) .here ProgramCases.wrongDemand)
    87 ([0, 1, 1, 1, 10, 6, 5, 7, 12, 12, 12, 10, 10, 11, 10, 13, 13, 13, 14, 14, 14, 15, 16, 21, 22, 19] ++ List.replicate 43 17 ++ [23, 24, 25, 3, 9, 10, 10, 10, 11, 10, 26, 27, 28, 29, 30, 31, 32, 33])
    .derived (some 1) (some [1, 2]) false)) ++
  (fuels.map (readCheck oldest 5 4)) ++ (fuels.map (readCheck repeated 2 1))

def permissionCheck (scope : List Nat) (position cost : Nat) (found : Option Nat)
    (labels : List Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlPermission.lookupCode scope position) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) &&
      (actual.value.1.map Ref.position == found) && (actual.labels.map tag == labels)

def permissionMatrices : List Bool :=
  let fuels := List.range 39
  (fuels.map (permissionCheck [] 7 1 none [6])) ++
  (fuels.map (permissionCheck [1, 1] 1 4 (some 0) [6, 5, 5, 7])) ++
  (fuels.map (permissionCheck [3, 5, 5] 5 14 (some 1)
    [6, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5, 7, 7])) ++
  (fuels.map (permissionCheck [0, 1] 2 8 none [6, 5, 6, 5, 5, 6, 7, 7])) ++
  (fuels.map (permissionCheck [32] 32 35 (some 0) (6 :: (List.replicate 33 5 ++ [7])))) ++
  (fuels.map (permissionCheck [32] 31 35 none (6 :: (List.replicate 32 5 ++ [6, 7]))))

def positionCheck {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind)
    (position cost : Nat) (labels : List Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlReference.positionCode ref) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.value.1 == position) && (actual.labels.map tag == labels)

def positionMatrices : List Bool :=
  let fuels := List.range 24
  (fuels.map (positionCheck DeductionCases.differenceRequest.2 0 1 [10])) ++
  (fuels.map (positionCheck DeductionCases.sumRequest.2 1 3 [10, 10, 11])) ++
  (fuels.map (positionCheck DeductionCases.duplicateRequest.2 2 5 [10, 10, 10, 11, 11]))

def resourceCheck {kinds : List Nat} {kind : Nat}
    (values : Values (fun _ : Nat => Int) kinds) (ref : Ref kinds kind)
    (value : Int) (cost : Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlResources.readCode values ref) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.value.1 == value) &&
      (actual.labels.map tag == List.replicate cost 12)

def resourceMatrices : List Bool :=
  let fuels := List.range 8
  let values : Values (fun _ : Nat => Int) [7, 7, 7] := (99, -5, 99, PUnit.unit)
  (fuels.map (resourceCheck values .here 99 1)) ++
  (fuels.map (resourceCheck values (.prior .here) (-5) 2)) ++
  (fuels.map (resourceCheck values (.prior (.prior .here)) 99 3)) ++
  (fuels.map (resourceCheck (kinds := [7])
    (170141183460469231731687303715884105727, PUnit.unit) .here
    170141183460469231731687303715884105727 1))

def checkedPermission {contract demand origin}
    (checked : Selection.Checked Cases.sources contract demand origin) : Option Nat :=
  match checked with
  | .permitted permission _ => some permission.position
  | .rejected _ => none

def sourceCheck (contract : Contract) (demand : Demand) (origin : Location Cases.context)
    (cost : Nat) (labels : List Nat) (flag : Bool) (permission : Option Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlSelection.checkCode Cases.sources contract demand origin) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.labels.map tag == labels) &&
      (actual.value.1.flag == flag) && (checkedPermission actual.value.1 == permission)

def sourceMatrices : List Bool :=
  let fuels := List.range 100
  let publicLabels := [10, 10, 11, 6, 5, 5, 7, 12, 12, 36] ++
    List.replicate 8 5 ++ List.replicate 43 5 ++ [34, 5, 5, 35, 35]
  (fuels.map (sourceCheck Cases.contract ProgramCases.baselineTask.demand Cases.privateOrigin
    9 [10, 6, 5, 6, 5, 6, 7, 7, 35] false none)) ++
  (fuels.map (sourceCheck Cases.contract ProgramCases.baselineTask.demand Cases.publicOrigin
    66 publicLabels true (some 0))) ++
  (fuels.map (sourceCheck Cases.contract ⟨7, 43, some 1⟩ Cases.publicOrigin
    66 publicLabels false none)) ++
  (fuels.map (sourceCheck Cases.contract Cases.pinnedDemand Cases.publicOrigin
    65 ([10, 10, 11, 6, 5, 5, 7, 12, 12, 36] ++ List.replicate 8 5 ++
      List.replicate 43 5 ++ [34, 5, 35, 35]) false none)) ++
  (fuels.map (sourceCheck ⟨[1, 1]⟩ ProgramCases.baselineTask.demand Cases.publicOrigin
    66 publicLabels true (some 0))) ++
  (fuels.map (sourceCheck ⟨[]⟩ ProgramCases.baselineTask.demand Cases.publicOrigin
    5 [10, 10, 11, 6, 35] false none)) ++
  (fuels.map (sourceCheck ⟨[0]⟩ Cases.factDemand Cases.privateOrigin
    60 ([10, 6, 5, 7, 12, 36] ++ List.replicate 8 5 ++ List.replicate 43 5 ++ [34, 35, 35])
    true (some 0))) ++
  (fuels.map (sourceCheck Cases.contract ⟨8, 42, some 1⟩ Cases.publicOrigin
    66 publicLabels false none))

def formationPort {Kind : Type u} {Value : Kind → Type v} {context : List Kind}
    {values : Values Value context} (formation : Formation Value values) : Option Nat := by
  cases formation with
  | given _ => exact none
  | produced _ producer => exact (MasterOperations.portPositions producer.inputs).head?

def extractionCheck (origin : Location Cases.context) (cost value position : Nat)
    (labels : List Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlCitation.extractCode Cases.sources origin) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.labels.map tag == labels) &&
      ((actual.value.1.resources.read .here).value == value) &&
      (formationPort actual.value.1.resources.formation == some position)

def readoutCheck (origin : Location Cases.context) (cost value position document version : Nat)
    (labels : List Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlCitation.readoutCode (extract Cases.sources origin)) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.labels.map tag == labels) &&
      (actual.value.1.passage.key == 7) && (actual.value.1.passage.value == value) &&
      (actual.value.1.position == position) && (actual.value.1.source.document == document) &&
      (actual.value.1.source.version == version) && (actual.value.1.source.excerpt == 0)

def citationMatrices : List Bool :=
  let fuels := List.range 20
  (fuels.map (extractionCheck Cases.privateOrigin 6 42 0 [49, 12, 23, 24, 25, 2])) ++
  (fuels.map (extractionCheck Cases.publicOrigin 7 42 1 [49, 12, 12, 23, 24, 25, 2])) ++
  (fuels.map (extractionCheck Cases.updatedOrigin 8 43 2 [49, 12, 12, 12, 23, 24, 25, 2])) ++
  (fuels.map (readoutCheck Cases.privateOrigin 3 42 0 0 2 [10, 12, 36])) ++
  (fuels.map (readoutCheck Cases.publicOrigin 5 42 1 1 1 [10, 10, 11, 12, 36])) ++
  (fuels.map (readoutCheck Cases.updatedOrigin 7 43 2 1 2 [10, 10, 10, 11, 11, 12, 36]))

def continuationCheck {frontier : List (SAT.GeneratedStructuralBranchContext [])}
    (continuation : FrontierContinuation (SAT.generatedStructuralBranchSystem []) frontier)
    (cost : Nat) (value : Bool) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlCompletion.assignmentCode continuation) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.labels.map tag == List.replicate cost 46) &&
      (actual.value.1 10 == value)

def continuationMatrices : List Bool :=
  let fuels := List.range 20
  let root := SAT.GeneratedStructuralBranchContext.root []
  let first : FrontierContinuation (SAT.generatedStructuralBranchSystem []) [root] :=
    .head ⟨fun _ => false, True.intro⟩
  let second : FrontierContinuation (SAT.generatedStructuralBranchSystem []) [root, root] :=
    .tail (.head ⟨fun _ => true, True.intro⟩)
  let third : FrontierContinuation (SAT.generatedStructuralBranchSystem []) [root, root, root] :=
    .tail (.tail (.head ⟨fun _ => false, True.intro⟩))
  (fuels.map (continuationCheck first 1 false)) ++
  (fuels.map (continuationCheck second 2 true)) ++
  (fuels.map (continuationCheck third 3 false))

def decisionPermission {cursor contract demand left right stage memory} :
    @Master.Decision Cases.context cursor Cases.sources contract demand left right stage memory → Option Nat
  | .complete packet => some packet.candidate.permission.position
  | .blocked _ _ => none

def decisionCheck {cursor contract demand left right}
    (stage : Master.Stage cursor Cases.sources contract demand left right)
    (memory : Memory Cases.sources contract) (cost : Nat) (labels : List Nat)
    (position value permission : Option Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlCompletion.decideCode stage memory) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.labels.map tag == labels) &&
      (actual.value.1.result.2.map Citation.position == position) &&
      (actual.value.1.result.2.map (fun item => item.passage.value) == value) &&
      (decisionPermission actual.value.1 == permission)

def decisionMatrices : List Bool :=
  let fuels := List.range 40
  (fuels.map (decisionCheck MasterCases.factRun.1 Cases.initial 23
    [42, 43, 44, 45, 46, 47, 48, 49, 12, 12, 23, 24, 25, 2,
      10, 10, 11, 12, 36, 50, 51, 52, 53] (some 1) (some 42) (some 0))) ++
  (fuels.map (decisionCheck MasterCases.bothRun.1 (empty Cases.sources MasterCases.bothContract) 23
    [42, 43, 44, 45, 46, 47, 48, 49, 12, 12, 23, 24, 25, 2,
      10, 10, 11, 12, 36, 50, 51, 52, 53] (some 1) (some 42) (some 1))) ++
  (fuels.map (decisionCheck MasterCases.pinnedRun.1 Cases.initial 2 [42, 53] none none none))

def fromScript {slots}
    (frame : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (script : Script Cases.context DeductionCases.policy slots
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
        ProgramCases.revisedSpec, ProgramCases.baselineSpec]) : Bool :=
  match script with
  | .done => false
  | .cons instruction _ =>
      stepCheck frame instruction 106 baselineLabels .quoted (some 42) (some [1]) true 106

def fromPresent (before : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec]) : Bool :=
  fromScript before.session.frame before.remaining

def loaded : Bool :=
  let before := MemoryCases.retainedPrefix
  match PortableControl.loadPresent ControlCodec.natural
    before.session.frame.dossier before.session.frame.store _
    (PortableControl.save ControlCodec.natural (PortableControl.capture before)) with
  | none => false
  | some restored => fromPresent restored

def verify (index : Nat) : List Bool → IO Unit
  | [] => pure ()
  | passed :: rest => if passed then verify (index + 1) rest else do
      let stderr ← IO.getStderr
      stderr.write ⟨(Cases.utf8 (Nat.repr index)).toArray⟩
      throw (IO.userError "Documentary interpreter verdict changed")

def run : IO Unit := do
  let certified := sumActual.sound
  verify 0 (matrices ++ permissionMatrices ++ positionMatrices ++ resourceMatrices ++ sourceMatrices ++
    citationMatrices ++ continuationMatrices ++ decisionMatrices ++ [fromPresent MemoryCases.retainedPrefix,
    fromPresent (MemoryCases.retainedPrefix.reset (AdaptiveCases.policy 4)), loaded,
    stepCheck (Memory.project MemoryCases.leftProduced.1).session.frame
      (.quotation ProgramCases.revisedTask) 176 revisedLabels .quoted (some 43) (some [2]) true 176,
    stepCheck (Memory.project MemoryCases.rightProduced.1).session.frame
      (.quotation ProgramCases.revisedTask) 176 revisedLabels .quoted (some 43) (some [2]) true 176,
    sumActual.labels.length == 61,
    sumActual.value.1.next.store.2.resources.read terminal.occurrence.2 == 2,
    terminal.occurrence.1.origins == [1, 2, 1, 2],
    traceTag certified.1 == 1])
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_INTERPRETER_SMOKE_DONE\n").toArray⟩
end DocumentaryInterpreterSmoke
def main : IO Unit := DocumentaryInterpreterSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryInterpreterSmoke.tag
#print axioms DocumentaryInterpreterSmoke.baselineLabels
#print axioms DocumentaryInterpreterSmoke.refusedLabels
#print axioms DocumentaryInterpreterSmoke.revisedLabels
#print axioms DocumentaryInterpreterSmoke.traceTag
#print axioms DocumentaryInterpreterSmoke.eventTag
#print axioms DocumentaryInterpreterSmoke.stepCheck
#print axioms DocumentaryInterpreterSmoke.readCheck
#print axioms DocumentaryInterpreterSmoke.matrices
#print axioms DocumentaryInterpreterSmoke.permissionCheck
#print axioms DocumentaryInterpreterSmoke.permissionMatrices
#print axioms DocumentaryInterpreterSmoke.positionCheck
#print axioms DocumentaryInterpreterSmoke.positionMatrices
#print axioms DocumentaryInterpreterSmoke.resourceCheck
#print axioms DocumentaryInterpreterSmoke.resourceMatrices
#print axioms DocumentaryInterpreterSmoke.checkedPermission
#print axioms DocumentaryInterpreterSmoke.sourceCheck
#print axioms DocumentaryInterpreterSmoke.sourceMatrices
#print axioms DocumentaryInterpreterSmoke.formationPort
#print axioms DocumentaryInterpreterSmoke.extractionCheck
#print axioms DocumentaryInterpreterSmoke.readoutCheck
#print axioms DocumentaryInterpreterSmoke.citationMatrices
#print axioms DocumentaryInterpreterSmoke.continuationCheck
#print axioms DocumentaryInterpreterSmoke.continuationMatrices
#print axioms DocumentaryInterpreterSmoke.decisionPermission
#print axioms DocumentaryInterpreterSmoke.decisionCheck
#print axioms DocumentaryInterpreterSmoke.decisionMatrices
#print axioms DocumentaryInterpreterSmoke.fromScript
#print axioms DocumentaryInterpreterSmoke.fromPresent
#print axioms DocumentaryInterpreterSmoke.loaded
#print axioms DocumentaryInterpreterSmoke.verify
#print axioms DocumentaryInterpreterSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""


def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-interpreter-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean interpreter smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    expected = {("'DocumentaryInterpreterSmoke." + name + "' does not depend on any axioms").encode()
                for name in ("tag", "baselineLabels", "refusedLabels", "revisedLabels", "traceTag", "eventTag", "stepCheck", "readCheck", "matrices", "permissionCheck", "permissionMatrices", "positionCheck", "positionMatrices", "resourceCheck", "resourceMatrices", "checkedPermission", "sourceCheck", "sourceMatrices", "fromScript", "fromPresent",
                             "formationPort", "extractionCheck", "readoutCheck", "citationMatrices", "continuationCheck", "continuationMatrices",
                             "decisionPermission", "decisionCheck", "decisionMatrices", "loaded", "verify", "run")}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_INTERPRETER_SMOKE_DONE"))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Missing runtime audit or unexpected output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_INTERPRETER_SMOKE_OK: 2200 documentary, 234 permission, 72 position, 32 resource, 800 source-check, "
          "120 citation, 60 continuation and 120 decision fuel checks, nine integration checks, "
          "33 clean runtime audits; client_sha256=" + hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_INTERPRETER_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
