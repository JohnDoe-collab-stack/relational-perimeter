#!/usr/bin/env python3
"""Frozen development checks of the expanded head, assemblies and administration.

The 200000 probe is a test ceiling, not a proved bootstrap bound. Exact and
one-short probes follow the actual certified trace. No physical cost claim.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryExpandedControlCases
import Tests.LocalAlignment.DocumentaryMasterCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace ExpandedControlSmoke
open ConstitutiveSearch ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Snapshot Control ControlBindings ControlInterpreterCases ExpandedControlCases

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

def count (label : Label) (labels : List Label) : Nat :=
  (labels.filter (fun found => tag found == tag label)).length

def eventTag : Event → Nat
  | .quoted => 0
  | .derived => 1
  | .refused => 2
  | .missing => 3

def quotationCheck (before : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (task : Dossier.Obligation Cases.context) (expected : Int) (origins : List Nat) : Bool :=
  let code := ControlStep.expandedCode before (.quotation task)
  match Control.execute 200000 code with
  | none => false
  | some actual =>
    let next := actual.value.1.next
    match next.bindings .here with
    | none => false
    | some occurrence =>
      let fuel := actual.labels.length
      let exact := Control.execute fuel code
      let short := Control.execute (fuel - 1) code
      let surplus := Control.execute (fuel + 5) code
      let stable := match exact, surplus with
        | some first, some second => first.labels.map tag == second.labels.map tag
        | _, _ => false
      let event := eventTag actual.value.1.event == 0
      event && next.store.2.resources.read occurrence.2 == expected && occurrence.1.origins == origins &&
      next.dossier.cursor.depth == before.dossier.cursor.depth + 1 &&
      count .masterProducer actual.labels == 7 &&
      count .masterHeadPacket actual.labels == 1 &&
      count .masterDiscoveryPacket actual.labels == 1 &&
      count .masterGeneration actual.labels == 1 &&
      count .masterApply actual.labels == 1 &&
      count .masterNextStateGeneration actual.labels == 1 &&
      count .masterNextStateQuery actual.labels == 1 &&
      count .masterDecompose actual.labels == 1 &&
      count .masterNextCursor actual.labels == 1 &&
      count .formationResources actual.labels == 9 &&
      count .frameRestore actual.labels == 1 &&
      count .citationHead actual.labels == 0 &&
      !short.isSome && stable

def blockedCheck : Bool :=
  match Control.execute 200000 (ControlStep.expandedCode quoteFrame
      (.quotation ⟨Cases.pinnedDemand, Cases.privateOrigin, Cases.publicOrigin⟩)) with
  | none => false
  | some actual =>
    (eventTag actual.value.1.event == 2) &&
    (match actual.value.1.next.bindings .here with | none => true | _ => false) &&
    actual.value.1.next.store.1.length == quoteFrame.store.1.length &&
    count .masterProducer actual.labels == 7 &&
    count .masterHeadPacket actual.labels == 1 &&
    count .formationResources actual.labels == 7

def adminCheck (fuel budget : Nat) : Bool :=
  match Control.execute budget (ControlAdministration.executeCode fuel oneCode) with
  | none => false
  | some actual => match actual.value.1 with
    | none => fuel == 0
    | some source => source.value == 3 && source.labels.map tag == [0]

def candidateCheck : Bool :=
  match emptyCandidateExecution with
  | none => false
  | some actual => match actual.value.1.produced? with
    | none => false
    | some produced =>
      produced.source.value.context.formula.isEmpty && produced.target.value.context.formula.isEmpty &&
      produced.source.value.context.decisions.map (fun item => (item.var, item.value)) == [(0, false)] &&
      produced.target.value.context.decisions.map (fun item => (item.var, item.value)) == [(0, true)]

def relationReject (code : Code Label (ControlMasterData.Actual
    (ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelation 1 repeatedState repeatedState))) : Bool :=
  match Control.execute 100 code with
  | none => false
  | some actual => !actual.value.1.result.isSome && actual.value.1.historyTransform.nodes > 0

def deferredCheck : Bool :=
  let firstOutput := authorize Cases.contract (extract Cases.sources Cases.publicOrigin) .here
  let secondOutput := authorize Cases.contract (extract Cases.sources Cases.updatedOrigin) (.prior .here)
  let empty := Deduction.empty Cases.sources Cases.contract DeductionCases.policy
  let first := Deduction.quote empty firstOutput
  let second := Deduction.quote first secondOutput
  let firstRecipe : ControlDeferred.KnowledgeRecipe first := .quotation .empty firstOutput
  let secondRecipe : ControlDeferred.KnowledgeRecipe second := .quotation firstRecipe secondOutput
  let action := Deduction.form second DeductionCases.differenceRequest (.prior .here) .here
  let third := Deduction.incorporateDerived action .here
  let thirdRecipe : ControlDeferred.KnowledgeRecipe third :=
    .derived secondRecipe DeductionCases.differenceRequest (.prior .here) .here action .here
  let code := ControlDeferred.recipeReader thirdRecipe .here
  match Control.execute 15 code, Control.execute 14 code, Control.execute 20 code with
  | some actual, none, some surplus =>
    actual.labels.length == 15 && actual.labels.map tag == surplus.labels.map tag &&
    actual.value.1.sources.map (fun output => output.item.position) == [1, 2] &&
    actual.value.1.rules == [0]
  | _, _, _ => false

def referenceCheck : Bool :=
  let output := authorize Cases.contract (extract Cases.sources Cases.publicOrigin) .here
  let empty := Deduction.empty Cases.sources Cases.contract DeductionCases.policy
  let knowledge := Deduction.quote empty output
  let producer := Deduction.producer DeductionCases.sumRequest Ref.here Ref.here
  let recipe := ControlDeferred.ExtensionRecipe.compose
    (ControlDeferred.ExtensionRecipe.identity knowledge.resources)
    (ControlDeferred.ExtensionRecipe.produced knowledge.resources producer)
  let code := ControlDeferred.referenceCode recipe Ref.here
  match Control.execute 6 code, Control.execute 5 code with
  | some actual, none => actual.value.1.position == 1 && actual.labels.map tag == [86, 85, 86, 83, 86, 84]
  | _, _ => false

def naturalEqualityCode (left right : Nat) : Code Label (ControlMasterData.Actual (Nat.decEq left right)) :=
  (ControlMeasuredComparison.unaryCode left right).bind (fun compared =>
    .done ⟨compared.1.result, Subsingleton.elim _ _⟩)

def deduplicateCheck : Bool :=
  let code := ControlProducedImage.deduplicateCode Nat.decEq naturalEqualityCode [1, 2, 1, 3, 2]
  match Control.execute 1000 code with
  | none => false
  | some actual => actual.value.1 == [1, 3, 2]

def transportCheck
    (program : TransportCode (SAT.GeneratedStructuralFlipAtRelation 0) transportState transportState)
    (fuel atoms : Nat) (bit : Bool) : Bool :=
  let code := ControlMeasuredTransport.flipCode 0 program transportInput
  match Control.execute fuel code, Control.execute (fuel - 1) code, Control.execute (fuel + 3) code with
  | some actual, none, some surplus =>
    actual.value.1.evaluatedAtoms == atoms && actual.value.1.continuationApplications == atoms &&
    actual.value.1.output.1 0 == bit && !(actual.value.1.output.1 1) &&
    actual.labels.length == fuel && actual.labels.map tag == surplus.labels.map tag
  | _, _, _ => false

def scheduleCheck : Bool :=
  match emptyCandidateExecution with
  | none => false
  | some attempted => match attempted.value.1.produced? with
    | none => false
    | some produced =>
      let outcome : EndogenousDecomposition.RecordedDiscoveryOutcome
          (SAT.GeneratedStructuralBranchContext.root []) :=
        ⟨some ⟨0, produced⟩, [], 0, 0, 0, 0, 0, 0, .zero, .zero⟩
      let code := (ControlMeasuredSchedule.storedCode outcome ⟨0, produced.discovery⟩ rfl).bind (fun stored =>
        (ControlMeasuredSchedule.validationCode stored.1).bind (fun validation =>
        (ControlMeasuredSchedule.validatedCode validation.1).bind (fun validated =>
        (ControlMeasuredSchedule.executionCode validation.1).bind (fun execution =>
        (ControlMeasuredSchedule.executedCode execution.1).bind (fun result => .done
          (validated.1.run.success && result.1.code.size == 1 &&
            result.1.producedState.context.decisions.map (fun decision => (decision.var, decision.value)) == [(0, true)]
            && validation.1.search.result.isSome && execution.1.search.result.isSome))))))
      match Control.execute 1000 code with
      | none => false
      | some actual => actual.value

def run : IO Unit := do
  let retained := MemoryCases.retainedPrefix
  let reset := retained.reset (AdaptiveCases.policy 4)
  let bytes := PortableControl.save ControlCodec.natural (PortableControl.capture retained)
  let loaded := PortableControl.loadPresent ControlCodec.natural retained.session.frame.dossier
    retained.session.frame.store
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
        ProgramCases.revisedSpec, ProgramCases.baselineSpec] bytes
  let loadedOk := match loaded with
    | none => false
    | some present => quotationCheck present.session.frame ProgramCases.baselineTask 42 [1]
  let checks := [
    quotationCheck quoteFrame ProgramCases.baselineTask 42 [1],
    quotationCheck retained.session.frame ProgramCases.baselineTask 42 [1],
    quotationCheck reset.session.frame ProgramCases.baselineTask 42 [1],
    quotationCheck (Memory.project MemoryCases.leftProduced.1).session.frame ProgramCases.revisedTask 43 [2],
    quotationCheck (Memory.project MemoryCases.rightProduced.1).session.frame ProgramCases.revisedTask 43 [2],
    loadedOk, blockedCheck,
    leftExecution.isSome, rightExecution.isSome, forbiddenExecution.isSome,
    (Control.execute 7 (ControlStep.expandedCode refusedFrame leftMissing)).isSome == false,
    (Control.execute 9 (ControlStep.expandedCode refusedFrame rightMissing)).isSome == false,
    (Control.execute 23 (ControlStep.expandedCode twoFrame forbiddenInstruction)).isSome == false,
    adminCheck 0 2, adminCheck 1 21, adminCheck 1 26,
    (Control.execute 20 (ControlAdministration.executeCode 1 oneCode)).isSome == false,
    (Control.execute 3 shortComparator).isSome,
    !(Control.execute 2 shortComparator).isSome,
    (Control.execute 6 repeatedCandidate).isSome,
    !(Control.execute 5 repeatedCandidate).isSome,
    candidateCheck,
    (match Control.execute 100 mismatchFormula with
      | none => false
      | some actual => !actual.value.1.result.isSome && actual.value.1.historyTransform.nodes == 0),
    relationReject mismatchHistory, deferredCheck, referenceCheck,
    transportCheck (.identity transportState) 2 0 false,
    transportCheck (.atom transportRelation) 5 1 true,
    transportCheck (.compose (.atom transportRelation) (.atom transportRelation)) 18 2 false,
    deduplicateCheck, scheduleCheck]
  if checks.length != 31 || checks.any (fun passed => !passed) then
    throw (IO.userError "Expanded control mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_EXPANDED_CONTROL_SMOKE_DONE\n").toArray⟩
end ExpandedControlSmoke
def main : IO Unit := ExpandedControlSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms ExpandedControlSmoke.tag
#print axioms ExpandedControlSmoke.count
#print axioms ExpandedControlSmoke.eventTag
#print axioms ExpandedControlSmoke.quotationCheck
#print axioms ExpandedControlSmoke.blockedCheck
#print axioms ExpandedControlSmoke.adminCheck
#print axioms ExpandedControlSmoke.candidateCheck
#print axioms ExpandedControlSmoke.relationReject
#print axioms ExpandedControlSmoke.deferredCheck
#print axioms ExpandedControlSmoke.referenceCheck
#print axioms ExpandedControlSmoke.naturalEqualityCode
#print axioms ExpandedControlSmoke.deduplicateCheck
#print axioms ExpandedControlSmoke.transportCheck
#print axioms ExpandedControlSmoke.scheduleCheck
#print axioms ExpandedControlSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""

def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-expanded-control-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)],
                                cwd=ROOT, capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Expanded control smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    names = ("tag", "count", "eventTag", "quotationCheck", "blockedCheck", "adminCheck",
             "candidateCheck", "relationReject", "deferredCheck", "referenceCheck", "naturalEqualityCode",
             "deduplicateCheck", "transportCheck", "scheduleCheck", "run")
    expected = {("'ExpandedControlSmoke." + name + "' does not depend on any axioms").encode()
                for name in names}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_EXPANDED_CONTROL_SMOKE_DONE"))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Unexpected runtime output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_EXPANDED_CONTROL_SMOKE_OK: 31 development checks; sixteen clean runtime audits; "
          "client_sha256=" + hashlib.sha256(source).hexdigest())

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_EXPANDED_CONTROL_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
