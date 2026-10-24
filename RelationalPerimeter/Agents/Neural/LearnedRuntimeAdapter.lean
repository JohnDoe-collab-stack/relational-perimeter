import RelationalPerimeter.Agents.Neural.LearnedSuccessiveCurrentReference

/-!
# Learned dependent runtime adapter

This module exposes the state-indexed update language, dependent checker,
executed submission receipts, and certified successive runtime.  Its checker
consumes the predecessor-indexed engine result from the imported module.
-/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

/-- The dependent update language exposes each serialized request only at the
exact checked source that may consume it.  The second constructor is indexed by
the successor produced by the first checked update, so it cannot be submitted
at the initial agent or at an independently reconstructed aligned agent. -/
inductive LearnedRuntimeUpdate :
    {contract : LearnedOperationalContract} ->
      CheckedAgent learnedConstitutiveMetaContract contract -> Type 6 where
  | serialized (update : LearnedSerializedConstitutiveUpdate) :
      LearnedRuntimeUpdate learnedInitialCheckedAgent
  | successive
      {contract : LearnedOperationalContract}
      {current : CheckedAgent learnedConstitutiveMetaContract contract}
      (predecessor : CheckedAgent learnedConstitutiveMetaContract contract)
      (currentExact : current = predecessor)
      (contractExact : contract = .aligned)
      (predecessorExact : HEq predecessor LearnedAlignedCheckedAgent)
      (update : LearnedSerializedConstitutiveUpdate) :
      LearnedRuntimeUpdate current

/-- A decoded runtime request is indexed by the exact checked source that may
consume it.  The two constructors retain the positive decoder result and its
execution equation; no unindexed artifact can be moved between versions. -/
inductive DecodedLearnedRuntimeUpdateAtCurrent :
    {contract : LearnedOperationalContract} ->
      (current : CheckedAgent learnedConstitutiveMetaContract contract) ->
      LearnedRuntimeUpdate current -> Type 6 where
  | initial
      {source : LearnedSerializedConstitutiveUpdate}
      (decoded : DecodedLearnedSerializedConstitutiveUpdate source)
      (decodedExact :
        decodeLearnedSerializedConstitutiveUpdate source = .ok decoded) :
      DecodedLearnedRuntimeUpdateAtCurrent learnedInitialCheckedAgent
        (.serialized source)
  | successive
      {contract : LearnedOperationalContract}
      {current : CheckedAgent learnedConstitutiveMetaContract contract}
      (predecessor : CheckedAgent learnedConstitutiveMetaContract contract)
      (currentExact : current = predecessor)
      (contractExact : contract = .aligned)
      (predecessorExact : HEq predecessor LearnedAlignedCheckedAgent)
      {source : LearnedSerializedConstitutiveUpdate}
      (decoded : DecodedLearnedSuccessiveUpdate source)
      (decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded) :
      DecodedLearnedRuntimeUpdateAtCurrent current
        (.successive predecessor currentExact contractExact predecessorExact source)

def decodeLearnedRuntimeUpdateAtCurrent
    {contract : LearnedOperationalContract}
    {current : CheckedAgent learnedConstitutiveMetaContract contract}
    (update : LearnedRuntimeUpdate current) :
    Except LearnedRuntimeUpdateError
      (DecodedLearnedRuntimeUpdateAtCurrent current update) :=
  match update with
  | .serialized source =>
      match decodedExact : decodeLearnedSerializedConstitutiveUpdate source with
      | .error problem => .error problem
      | .ok decoded => .ok (.initial decoded decodedExact)
  | .successive predecessor currentExact contractExact predecessorExact source =>
      match decodedExact : decodeLearnedSuccessiveUpdate source with
      | .error problem => .error problem
      | .ok decoded =>
          .ok (.successive predecessor currentExact contractExact
            predecessorExact decoded decodedExact)

def checkDecodedLearnedRuntimeUpdateAtCurrent
    {contract : LearnedOperationalContract}
    {current : CheckedAgent learnedConstitutiveMetaContract contract}
    {update : LearnedRuntimeUpdate current}
    (decoded : DecodedLearnedRuntimeUpdateAtCurrent current update) :
    Except LearnedRuntimeUpdateError (DependentCheckedUpdateResult current) :=
  match decoded with
  | .initial target decodedExact =>
      match analyzeDecodedLearnedRuntimeUpdate _ target decodedExact with
      | .error problem => .error problem
      | .ok analysis =>
          .ok (dependentCheckedUpdateResult
            (buildIncrementalCheckedUpdate analysis.target))
  | .successive predecessor currentExact contractExact predecessorExact target
      decodedExact => by
      cases currentExact
      cases contractExact
      exact checkDecodedLearnedExtendedSerializedUpdateAtCurrent current
        (eq_of_heq predecessorExact) _ target decodedExact

def checkLearnedRuntimeUpdateAtCurrent
    {contract : LearnedOperationalContract}
    {current : CheckedAgent learnedConstitutiveMetaContract contract}
    (update : LearnedRuntimeUpdate current) :
    Except LearnedRuntimeUpdateError (DependentCheckedUpdateResult current) :=
  match update with
  | .serialized source =>
      match decodedExact : decodeLearnedSerializedConstitutiveUpdate source with
      | .error problem => .error problem
      | .ok decoded =>
          match analyzeDecodedLearnedRuntimeUpdate source decoded decodedExact with
          | .error problem => .error problem
          | .ok analysis =>
              .ok (dependentCheckedUpdateResult
                (buildIncrementalCheckedUpdate analysis.target))
  | .successive predecessor currentExact contractExact predecessorExact source => by
      cases currentExact
      cases contractExact
      exact match decodedExact : decodeLearnedSuccessiveUpdate source with
        | .error problem => .error problem
        | .ok decoded =>
            checkDecodedLearnedExtendedSerializedUpdateAtCurrent current
              (eq_of_heq predecessorExact) source decoded decodedExact

def learnedAlignedCheckedUpdate : CheckedUpdate
    learnedInitialCheckedAgent .aligned :=
  buildIncrementalCheckedUpdate learnedAlignedTargetAnalysis

def learnedAlignedDependentResult :
    DependentCheckedUpdateResult learnedInitialCheckedAgent :=
  dependentCheckedUpdateResult learnedAlignedCheckedUpdate

def learnedExtendedDependentResult :
    DependentCheckedUpdateResult LearnedAlignedCheckedAgent :=
  dependentCheckedUpdateResult learnedExtendedCheckedUpdate

def learnedDependentIncrementalChecker :
    DependentIncrementalChecker learnedConstitutiveMetaContract where
  Error := LearnedRuntimeUpdateError
  Update := LearnedRuntimeUpdate
  check := by
    intro contract current update
    exact checkLearnedRuntimeUpdateAtCurrent update

theorem learnedDependentIncrementalChecker_successive_exact
    (source : LearnedSerializedConstitutiveUpdate) :
    learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
        (.successive LearnedAlignedCheckedAgent rfl rfl (HEq.rfl) source) =
      (match decodedExact : decodeLearnedSuccessiveUpdate source with
      | .error problem => .error problem
      | .ok decoded =>
          checkDecodedLearnedExtendedSerializedUpdateAtCurrent
            LearnedAlignedCheckedAgent rfl source decoded decodedExact) := by
  change checkLearnedRuntimeUpdateAtCurrent
      (.successive LearnedAlignedCheckedAgent rfl rfl (HEq.rfl) source) = _
  unfold checkLearnedRuntimeUpdateAtCurrent
  rfl

def learnedInitialCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  initialCertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent

def learnedAlignedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .serialized learnedAlignedSerializedUpdate

def learnedBypassRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .serialized learnedBypassSerializedUpdate

def learnedExtendedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update LearnedAlignedCheckedAgent :=
  .successive LearnedAlignedCheckedAgent rfl rfl (HEq.rfl)
    learnedExtendedSerializedUpdate

def learnedWrongSuccessiveRuntimeUpdate :
    learnedDependentIncrementalChecker.Update LearnedAlignedCheckedAgent :=
  .successive LearnedAlignedCheckedAgent rfl rfl (HEq.rfl)
    learnedAlignedSerializedUpdate

theorem learnedDependentChecker_accepts_aligned :
    learnedDependentIncrementalChecker.check
        learnedInitialCertifiedRuntime.current learnedAlignedRuntimeUpdate =
      .ok learnedAlignedDependentResult := by
  rfl

opaque learnedAlignedRuntimeSubmission :
    AcceptedRuntimeSubmission learnedInitialCertifiedRuntime
      learnedAlignedRuntimeUpdate learnedAlignedDependentResult
      learnedDependentChecker_accepts_aligned :=
  acceptedRuntimeSubmissionOfCheck learnedInitialCertifiedRuntime
    learnedAlignedRuntimeUpdate learnedAlignedDependentResult
    learnedDependentChecker_accepts_aligned

def learnedAlignedCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  learnedAlignedRuntimeSubmission.next

theorem submitUpdate_learned_aligned_exact :
    submitUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate =
      .ok learnedAlignedCertifiedRuntime := by
  exact learnedAlignedRuntimeSubmission.submitted

/-- The opaque receipt keeps the executed `submitUpdate` occurrence stable for
code generation.  This theorem relates that occurrence to the old explicit
constructor for dependent reasoning only; it is never used as the material
runtime producer. -/
theorem learnedAlignedCertifiedRuntime_eq_installed :
    learnedAlignedCertifiedRuntime =
      installAcceptedUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate learnedAlignedDependentResult
        learnedDependentChecker_accepts_aligned :=
  learnedAlignedRuntimeSubmission.nextExact

theorem submitUpdate_learned_bypass_rejected :
    submitUpdate learnedInitialCertifiedRuntime
        learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency := by
  rfl

theorem learnedDependentChecker_rejects_bypass :
    learnedDependentIncrementalChecker.check
        learnedInitialCertifiedRuntime.current
        learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency := by
  rfl

theorem learned_bypass_rejected_without_successor :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime
        learnedBypassRuntimeUpdate = .ok next) :=
  submitUpdate_rejected_cannot_install learnedInitialCertifiedRuntime
    learnedBypassRuntimeUpdate .missingConstitutiveDependency
      learnedDependentChecker_rejects_bypass

/-- The second transition is accepted only at the exact successor returned by
the first transition. -/
theorem learnedDependentChecker_accepts_extended :
    learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
        learnedExtendedRuntimeUpdate =
      .ok learnedExtendedDependentResult := by
  exact (learnedDependentIncrementalChecker_successive_exact
    learnedExtendedSerializedUpdate).trans
      checkLearnedSuccessiveSourceAtCurrent_reference_exact

/-- The result consumed by the dependent runtime is the certificate assembled
from the transported and recomputed successive fragments. -/
theorem learnedDependentSuccessiveResult_consumes_structuralAssembly :
    learnedExtendedDependentResult.checked.next.certificate.structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations := by
  rfl

theorem learnedDependentChecker_rejects_wrong_successive :
    learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
        learnedWrongSuccessiveRuntimeUpdate =
      .error .unexpectedTransition := by
  exact (learnedDependentIncrementalChecker_successive_exact
    learnedAlignedSerializedUpdate).trans
      checkLearnedSuccessiveSourceAtCurrent_rejects_first

/-- The concrete learned history has two genuinely successive checked edges.
The source index of the tail is definitionally the successor returned at the
head; no independently supplied aligned source occurs in this trace. -/
def learnedTwoStepCheckedTrace :
    CheckedReconfigurationTrace learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedExtendedCheckedAgent :=
  .step learnedAlignedRuntimeUpdate learnedAlignedDependentResult (by rfl)
    (.step learnedExtendedRuntimeUpdate learnedExtendedDependentResult
      learnedDependentChecker_accepts_extended
      (.nil learnedExtendedCheckedAgent))

def learnedTwoStepCheckedTrace_sound :
    EveryCheckedStepSatisfies learnedTwoStepCheckedTrace :=
  checkedTrace_constitutivelyAligned learnedTwoStepCheckedTrace

def learnedTwoStepCheckedTrace_preservesContracts :
    EveryCheckedStepPreservesContracts learnedTwoStepCheckedTrace :=
  checkedTrace_preservesContracts learnedTwoStepCheckedTrace

/-- Persistent intent is transported through the exact aligned-to-extended
permission, while authorization is reconstructed at the exact extended state. -/
def learnedExtendedTransportedIntent :
    learnedConstitutiveMetaContract.TargetPersistentWitness .aligned .extended
      .admittedIntent :=
  learnedExtendedOperationalTransition.transport .admittedIntent
    (ULift.up AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior)

def learnedExtendedRecheckedAuthorization :
    learnedConstitutiveMetaContract.RecheckedWitness .aligned .extended
      .authorizationConsumption :=
  learnedExtendedOperationalTransition.recheck .authorizationConsumption

def learnedExtendedStepContractPreservation :
    CheckedStepContractPreservation learnedExtendedDependentResult :=
  checkedStepContractPreservation learnedExtendedDependentResult

theorem learnedExtendedStep_transportsIntent_exact :
    learnedExtendedStepContractPreservation.transportPersistent
        .admittedIntent
        (ULift.up AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior) =
      learnedExtendedTransportedIntent := by
  rfl

/-- The authorization installed in the target certificate is definitionally
the witness reconstructed by the invalidated-obligation rule of the exact
aligned-to-extended permission. -/
theorem learnedExtendedCertificateAuthorization_is_rechecked :
    learnedExtendedCheckedAgent.certificate.authorizationWitness =
      learnedExtendedRecheckedAuthorization := by
  rfl

theorem learnedAlignedRuntime_state_exact :
    learnedAlignedCertifiedRuntime.current.state = learnedAlignedState := by
  rw [learnedAlignedCertifiedRuntime_eq_installed]
  rfl

theorem learnedAlignedCertifiedRuntime_current_exact :
    HEq learnedAlignedCertifiedRuntime.current LearnedAlignedCheckedAgent := by
  rw [learnedAlignedCertifiedRuntime_eq_installed]
  rfl

/-- The first executed submission returns a runtime whose current contract is
the aligned contract.  The equality is kept separate from the heterogeneous
identity of the current agent occurrence. -/
theorem learnedAlignedSubmittedCurrentContract_eq :
    learnedAlignedCertifiedRuntime.currentContract = .aligned := by
  rw [learnedAlignedCertifiedRuntime_eq_installed]
  rfl

theorem learnedAlignedRuntime_artifact_exact :
    HEq learnedAlignedCertifiedRuntime.current.artifact
      learnedDecodedAlignedArtifact := by
  rw [learnedAlignedCertifiedRuntime_eq_installed]
  rfl

theorem learnedAlignedRuntime_certificate_from_generic_checker :
    HEq learnedAlignedCertifiedRuntime.current.certificate
      (assembleStateConstitution learnedAlignedTargetAnalysis.fragments) := by
  rw [learnedAlignedCertifiedRuntime_eq_installed]
  rfl

/-- One accepted request tied to the exact runtime occurrence that owns its
dependent update language.  Transport moves this whole causal unit together;
the update, result, and acceptance equation can therefore never be transported
by unrelated equalities. -/
structure LearnedAcceptedRuntimeRequest
    (runtime : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent) where
  update : learnedDependentIncrementalChecker.Update runtime.current
  result : DependentCheckedUpdateResult runtime.current
  accepted : learnedDependentIncrementalChecker.check runtime.current update =
    .ok result

def LearnedAcceptedRuntimeRequest.transport
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedAcceptedRuntimeRequest source) :
    LearnedAcceptedRuntimeRequest target := by
  cases exact
  exact request

theorem LearnedAcceptedRuntimeRequest.transport_result_next_state
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedAcceptedRuntimeRequest source) :
    (request.transport exact).result.checked.next.state =
      request.result.checked.next.state := by
  cases exact
  rfl

theorem LearnedAcceptedRuntimeRequest.transport_result_next_artifact
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedAcceptedRuntimeRequest source) :
    HEq (request.transport exact).result.checked.next.artifact
      request.result.checked.next.artifact := by
  cases exact
  rfl

theorem LearnedAcceptedRuntimeRequest.transport_result_next_current
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedAcceptedRuntimeRequest source) :
    HEq (request.transport exact).result.checked.next
      request.result.checked.next := by
  cases exact
  rfl

theorem LearnedAcceptedRuntimeRequest.transport_result_next_observations
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedAcceptedRuntimeRequest source) :
    (request.transport exact).result.checked.next.certificate.structuralObservations =
      request.result.checked.next.certificate.structuralObservations := by
  cases exact
  rfl

theorem LearnedAcceptedRuntimeRequest.transport_result_next_memory
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedAcceptedRuntimeRequest source) :
    (request.transport exact).result.checked.next.state.memory =
      request.result.checked.next.state.memory := by
  cases exact
  rfl

structure LearnedRejectedRuntimeRequest
    (runtime : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent) where
  update : learnedDependentIncrementalChecker.Update runtime.current
  rejected : learnedDependentIncrementalChecker.check runtime.current update =
    .error .unexpectedTransition

def LearnedRejectedRuntimeRequest.transport
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (request : LearnedRejectedRuntimeRequest source) :
    LearnedRejectedRuntimeRequest target := by
  cases exact
  exact request

def learnedExtendedRequestAtInstalledRuntime :
    LearnedAcceptedRuntimeRequest
      (installAcceptedUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate learnedAlignedDependentResult
        learnedDependentChecker_accepts_aligned) where
  update := learnedExtendedRuntimeUpdate
  result := learnedExtendedDependentResult
  accepted := learnedDependentChecker_accepts_extended

def learnedWrongRequestAtInstalledRuntime :
    LearnedRejectedRuntimeRequest
      (installAcceptedUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate learnedAlignedDependentResult
        learnedDependentChecker_accepts_aligned) where
  update := learnedWrongSuccessiveRuntimeUpdate
  rejected := learnedDependentChecker_rejects_wrong_successive

/-- The second update stores the current agent occurrence returned by the first
`submitUpdate`.  The equality field licenses its exact public domain; it does
not replace the stored predecessor by `LearnedAlignedCheckedAgent`. -/
def learnedExtendedSubmittedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedAlignedCertifiedRuntime.current :=
  .successive learnedAlignedCertifiedRuntime.current rfl
    learnedAlignedSubmittedCurrentContract_eq
    learnedAlignedCertifiedRuntime_current_exact learnedExtendedSerializedUpdate

/-- The material predecessor field of the named second request is the current
agent occurrence projected from the first executed submission. -/
theorem learnedExtendedSubmittedRuntimeUpdate_predecessor_exact :
    learnedExtendedSubmittedRuntimeUpdate =
      .successive learnedAlignedCertifiedRuntime.current rfl
        learnedAlignedSubmittedCurrentContract_eq
        learnedAlignedCertifiedRuntime_current_exact
        learnedExtendedSerializedUpdate := by
  rfl

/-- Transport a dependent checker result only after separately identifying its
contract index and its source-agent occurrence.  This helper never constructs
a source agent or a checker result. -/
def transportDependentCheckedUpdateResult
    {sourceContract targetContract : LearnedOperationalContract}
    {source : CheckedAgent learnedConstitutiveMetaContract sourceContract}
    {target : CheckedAgent learnedConstitutiveMetaContract targetContract}
    (contractExact : sourceContract = targetContract)
    (sourceExact : HEq source target)
    (result : DependentCheckedUpdateResult target) :
    DependentCheckedUpdateResult source := by
  cases contractExact
  have homogeneousExact : source = target := eq_of_heq sourceExact
  cases homogeneousExact
  exact result

theorem transportDependentCheckedUpdateResult_next_heq
    {sourceContract targetContract : LearnedOperationalContract}
    {source : CheckedAgent learnedConstitutiveMetaContract sourceContract}
    {target : CheckedAgent learnedConstitutiveMetaContract targetContract}
    (contractExact : sourceContract = targetContract)
    (sourceExact : HEq source target)
    (result : DependentCheckedUpdateResult target) :
    HEq (transportDependentCheckedUpdateResult contractExact sourceExact result
      ).checked.next result.checked.next := by
  cases contractExact
  have homogeneousExact : source = target := eq_of_heq sourceExact
  cases homogeneousExact
  rfl

theorem transportDependentCheckedUpdateResult_state_heq
    {sourceContract targetContract : LearnedOperationalContract}
    {source : CheckedAgent learnedConstitutiveMetaContract sourceContract}
    {target : CheckedAgent learnedConstitutiveMetaContract targetContract}
    (contractExact : sourceContract = targetContract)
    (sourceExact : HEq source target)
    (result : DependentCheckedUpdateResult target) :
    HEq (transportDependentCheckedUpdateResult contractExact sourceExact result
      ).checked.next.state result.checked.next.state := by
  cases contractExact
  have homogeneousExact : source = target := eq_of_heq sourceExact
  cases homogeneousExact
  rfl

theorem transportDependentCheckedUpdateResult_artifact_heq
    {sourceContract targetContract : LearnedOperationalContract}
    {source : CheckedAgent learnedConstitutiveMetaContract sourceContract}
    {target : CheckedAgent learnedConstitutiveMetaContract targetContract}
    (contractExact : sourceContract = targetContract)
    (sourceExact : HEq source target)
    (result : DependentCheckedUpdateResult target) :
    HEq (transportDependentCheckedUpdateResult contractExact sourceExact result
      ).checked.next.artifact result.checked.next.artifact := by
  cases contractExact
  have homogeneousExact : source = target := eq_of_heq sourceExact
  cases homogeneousExact
  rfl

theorem transportDependentCheckedUpdateResult_observations_eq
    {sourceContract targetContract : LearnedOperationalContract}
    {source : CheckedAgent learnedConstitutiveMetaContract sourceContract}
    {target : CheckedAgent learnedConstitutiveMetaContract targetContract}
    (contractExact : sourceContract = targetContract)
    (sourceExact : HEq source target)
    (result : DependentCheckedUpdateResult target) :
    (transportDependentCheckedUpdateResult contractExact sourceExact result
      ).checked.next.certificate.structuralObservations =
      result.checked.next.certificate.structuralObservations := by
  cases contractExact
  have homogeneousExact : source = target := eq_of_heq sourceExact
  cases homogeneousExact
  rfl

theorem transportDependentCheckedUpdateResult_memory_eq
    {sourceContract targetContract : LearnedOperationalContract}
    {source : CheckedAgent learnedConstitutiveMetaContract sourceContract}
    {target : CheckedAgent learnedConstitutiveMetaContract targetContract}
    (contractExact : sourceContract = targetContract)
    (sourceExact : HEq source target)
    (result : DependentCheckedUpdateResult target) :
    (transportDependentCheckedUpdateResult contractExact sourceExact result
      ).checked.next.state.memory = result.checked.next.state.memory := by
  cases contractExact
  have homogeneousExact : source = target := eq_of_heq sourceExact
  cases homogeneousExact
  rfl

theorem learnedDependentChecker_accepts_successiveAt
    {contract : LearnedOperationalContract}
    (current : CheckedAgent learnedConstitutiveMetaContract contract)
    (contractExact : contract = .aligned)
    (currentExact : HEq current LearnedAlignedCheckedAgent) :
    learnedDependentIncrementalChecker.check current
        (.successive current rfl contractExact currentExact
          learnedExtendedSerializedUpdate) =
      .ok (transportDependentCheckedUpdateResult contractExact currentExact
        learnedExtendedDependentResult) := by
  cases contractExact
  have homogeneousExact : current = LearnedAlignedCheckedAgent :=
    eq_of_heq currentExact
  cases homogeneousExact
  exact learnedDependentChecker_accepts_extended

theorem learnedDependentChecker_rejects_wrong_successiveAt
    {contract : LearnedOperationalContract}
    (current : CheckedAgent learnedConstitutiveMetaContract contract)
    (contractExact : contract = .aligned)
    (currentExact : HEq current LearnedAlignedCheckedAgent) :
    learnedDependentIncrementalChecker.check current
        (.successive current rfl contractExact currentExact
          learnedAlignedSerializedUpdate) =
      .error .unexpectedTransition := by
  cases contractExact
  have homogeneousExact : current = LearnedAlignedCheckedAgent :=
    eq_of_heq currentExact
  cases homogeneousExact
  exact learnedDependentChecker_rejects_wrong_successive

def learnedExtendedSubmittedDependentResult :
    DependentCheckedUpdateResult learnedAlignedCertifiedRuntime.current :=
  transportDependentCheckedUpdateResult
    learnedAlignedSubmittedCurrentContract_eq
    learnedAlignedCertifiedRuntime_current_exact learnedExtendedDependentResult

theorem learnedDependentChecker_accepts_extended_at_submitted_runtime :
    learnedDependentIncrementalChecker.check
        learnedAlignedCertifiedRuntime.current
        learnedExtendedSubmittedRuntimeUpdate =
      .ok learnedExtendedSubmittedDependentResult :=
  learnedDependentChecker_accepts_successiveAt
    learnedAlignedCertifiedRuntime.current
    learnedAlignedSubmittedCurrentContract_eq
    learnedAlignedCertifiedRuntime_current_exact

/-- The accepted request is assembled directly at the runtime occurrence
returned by the first submission.  No request or checker result is transported
from `installAcceptedUpdate`. -/
def learnedExtendedRequestAtSubmittedRuntime :
    LearnedAcceptedRuntimeRequest learnedAlignedCertifiedRuntime where
  update := learnedExtendedSubmittedRuntimeUpdate
  result := learnedExtendedSubmittedDependentResult
  accepted := learnedDependentChecker_accepts_extended_at_submitted_runtime

def learnedWrongSuccessiveSubmittedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedAlignedCertifiedRuntime.current :=
  .successive learnedAlignedCertifiedRuntime.current rfl
    learnedAlignedSubmittedCurrentContract_eq
    learnedAlignedCertifiedRuntime_current_exact learnedAlignedSerializedUpdate

theorem learnedDependentChecker_rejects_wrong_at_submitted_runtime :
    learnedDependentIncrementalChecker.check
        learnedAlignedCertifiedRuntime.current
        learnedWrongSuccessiveSubmittedRuntimeUpdate =
      .error .unexpectedTransition :=
  learnedDependentChecker_rejects_wrong_successiveAt
    learnedAlignedCertifiedRuntime.current
    learnedAlignedSubmittedCurrentContract_eq
    learnedAlignedCertifiedRuntime_current_exact

def learnedWrongRequestAtSubmittedRuntime :
    LearnedRejectedRuntimeRequest learnedAlignedCertifiedRuntime where
  update := learnedWrongSuccessiveSubmittedRuntimeUpdate
  rejected := learnedDependentChecker_rejects_wrong_at_submitted_runtime

opaque learnedExtendedRuntimeSubmission :
    AcceptedRuntimeSubmission learnedAlignedCertifiedRuntime
      learnedExtendedSubmittedRuntimeUpdate
      learnedExtendedSubmittedDependentResult
      learnedDependentChecker_accepts_extended_at_submitted_runtime :=
  acceptedRuntimeSubmissionOfCheck learnedAlignedCertifiedRuntime
    learnedExtendedSubmittedRuntimeUpdate learnedExtendedSubmittedDependentResult
    learnedDependentChecker_accepts_extended_at_submitted_runtime

def learnedExtendedCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  learnedExtendedRuntimeSubmission.next

theorem submitUpdate_learned_extended_exact :
    submitUpdate learnedAlignedCertifiedRuntime
        learnedExtendedSubmittedRuntimeUpdate =
      .ok learnedExtendedCertifiedRuntime := by
  exact learnedExtendedRuntimeSubmission.submitted

theorem learnedExtendedCertifiedRuntime_eq_installed :
    learnedExtendedCertifiedRuntime =
      installAcceptedUpdate learnedAlignedCertifiedRuntime
        learnedExtendedSubmittedRuntimeUpdate
        learnedExtendedSubmittedDependentResult
        learnedDependentChecker_accepts_extended_at_submitted_runtime :=
  learnedExtendedRuntimeSubmission.nextExact

theorem learnedRuntime_current_artifact_heq_of_eq
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target) :
    HEq source.current.artifact target.current.artifact := by
  cases exact
  rfl

theorem learnedRuntime_current_heq_of_eq
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target) : HEq source.current target.current := by
  cases exact
  rfl

theorem learnedExtendedCertifiedRuntime_current_exact :
    HEq learnedExtendedCertifiedRuntime.current
      learnedExtendedDependentResult.checked.next :=
  (learnedRuntime_current_heq_of_eq
    learnedExtendedCertifiedRuntime_eq_installed).trans
      (transportDependentCheckedUpdateResult_next_heq
        learnedAlignedSubmittedCurrentContract_eq
        learnedAlignedCertifiedRuntime_current_exact
        learnedExtendedDependentResult)

theorem learnedRuntime_current_state_heq_of_eq
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target) :
    HEq source.current.state target.current.state := by
  cases exact
  rfl

theorem learnedExtendedRuntime_state_exact :
    learnedExtendedCertifiedRuntime.current.state = learnedExtendedState := by
  apply eq_of_heq
  exact
    (learnedRuntime_current_state_heq_of_eq
      learnedExtendedCertifiedRuntime_eq_installed).trans
      ((transportDependentCheckedUpdateResult_state_heq
        learnedAlignedSubmittedCurrentContract_eq
        learnedAlignedCertifiedRuntime_current_exact
        learnedExtendedDependentResult).trans (by rfl))

theorem learnedExtendedRuntime_artifact_exact :
    HEq learnedExtendedCertifiedRuntime.current.artifact
      learnedDecodedExtendedArtifact := by
  have runtimeArtifact : HEq learnedExtendedCertifiedRuntime.current.artifact
      learnedExtendedSubmittedDependentResult.checked.next.artifact :=
    learnedRuntime_current_artifact_heq_of_eq
      learnedExtendedCertifiedRuntime_eq_installed
  exact runtimeArtifact.trans
    ((transportDependentCheckedUpdateResult_artifact_heq
      learnedAlignedSubmittedCurrentContract_eq
      learnedAlignedCertifiedRuntime_current_exact
      learnedExtendedDependentResult).trans (by rfl))

/-- Installation through `submitUpdate` retains exactly the structural
assembly produced by the successive incremental analysis. -/
theorem learnedExtendedRuntime_certificate_consumes_successiveAssembly :
    learnedExtendedCertifiedRuntime.current.certificate.structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations := by
  calc
    learnedExtendedCertifiedRuntime.current.certificate.structuralObservations =
        learnedExtendedSubmittedDependentResult.checked.next.certificate.structuralObservations :=
      congrArg
        (fun runtime => runtime.current.certificate.structuralObservations)
        learnedExtendedCertifiedRuntime_eq_installed
    _ = learnedExtendedDependentResult.checked.next.certificate.structuralObservations :=
      transportDependentCheckedUpdateResult_observations_eq
        learnedAlignedSubmittedCurrentContract_eq
        learnedAlignedCertifiedRuntime_current_exact
        learnedExtendedDependentResult
    _ = learnedSuccessiveCalculatedStructuralAssembly.observations := by rfl

theorem learnedExtendedRuntime_consumes_first_successor_memory :
    learnedExtendedCertifiedRuntime.current.state.memory =
      (learnedExtendedInstallingActionFor
        learnedAlignedCertifiedRuntime.current.state.memory).result.1 := by
  calc
    learnedExtendedCertifiedRuntime.current.state.memory =
        learnedExtendedSubmittedDependentResult.checked.next.state.memory :=
      congrArg (fun runtime => runtime.current.state.memory)
        learnedExtendedCertifiedRuntime_eq_installed
    _ = learnedExtendedDependentResult.checked.next.state.memory :=
      transportDependentCheckedUpdateResult_memory_eq
        learnedAlignedSubmittedCurrentContract_eq
        learnedAlignedCertifiedRuntime_current_exact
        learnedExtendedDependentResult
    _ = (learnedExtendedInstallingActionFor
          learnedAlignedState.memory).result.1 := by rfl
    _ = (learnedExtendedInstallingActionFor
          learnedAlignedCertifiedRuntime.current.state.memory).result.1 := by
      rw [learnedAlignedRuntime_state_exact]

theorem learned_wrong_successive_rejected_without_checked_action :
    Not (Exists fun result =>
      learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
          learnedWrongSuccessiveRuntimeUpdate = .ok result) := by
  intro accepted
  rcases accepted with ⟨result, accepted⟩
  rw [learnedDependentChecker_rejects_wrong_successive] at accepted
  cases accepted

theorem learned_wrong_successive_rejected_without_successor :
    Not (Exists fun next =>
      submitUpdate learnedAlignedCertifiedRuntime
        learnedWrongSuccessiveSubmittedRuntimeUpdate = .ok next) :=
  submitUpdate_rejected_cannot_install learnedAlignedCertifiedRuntime
    learnedWrongSuccessiveSubmittedRuntimeUpdate .unexpectedTransition
      learnedDependentChecker_rejects_wrong_at_submitted_runtime

def learnedInitialCertifiedRuntime_reachable :
    CertifiedRuntimeReachable learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedInitialCertifiedRuntime :=
  .initial

def learnedAlignedCertifiedRuntime_reachable :
    CertifiedRuntimeReachable learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedAlignedCertifiedRuntime :=
  .submitted learnedInitialCertifiedRuntime learnedAlignedCertifiedRuntime
    learnedAlignedRuntimeUpdate learnedInitialCertifiedRuntime_reachable
    submitUpdate_learned_aligned_exact

def learnedExtendedCertifiedRuntime_reachable :
    CertifiedRuntimeReachable learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedExtendedCertifiedRuntime :=
  .submitted learnedAlignedCertifiedRuntime learnedExtendedCertifiedRuntime
    learnedExtendedSubmittedRuntimeUpdate learnedAlignedCertifiedRuntime_reachable
    submitUpdate_learned_extended_exact

def learnedAlignedCertifiedRuntime_accessibility :
    CertifiedRuntimeAccessibility learnedAlignedCertifiedRuntime :=
  reachableRuntime_accessibility learnedAlignedCertifiedRuntime
    learnedAlignedCertifiedRuntime_reachable

def learnedExtendedCertifiedRuntime_accessibility :
    CertifiedRuntimeAccessibility learnedExtendedCertifiedRuntime :=
  reachableRuntime_accessibility learnedExtendedCertifiedRuntime
    learnedExtendedCertifiedRuntime_reachable

def learnedAlignedRuntime_checkedHistory :
    EveryRuntimeStepSatisfies learnedAlignedCertifiedRuntime.history :=
  learnedAlignedCertifiedRuntime.checkedHistory

def learnedAlignedRuntime_preservedContracts :
    EveryRuntimeStepPreservesContracts learnedAlignedCertifiedRuntime.history :=
  learnedAlignedCertifiedRuntime.preservedContracts

def learnedExtendedRuntime_checkedHistory :
    EveryRuntimeStepSatisfies learnedExtendedCertifiedRuntime.history :=
  learnedExtendedCertifiedRuntime.checkedHistory

def learnedExtendedRuntime_preservedContracts :
    EveryRuntimeStepPreservesContracts learnedExtendedCertifiedRuntime.history :=
  learnedExtendedCertifiedRuntime.preservedContracts
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.LearnedRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.DecodedLearnedRuntimeUpdateAtCurrent
#print axioms ConstitutiveSearch.NeuralAgent.decodeLearnedRuntimeUpdateAtCurrent
#print axioms ConstitutiveSearch.NeuralAgent.checkDecodedLearnedRuntimeUpdateAtCurrent
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedRuntimeUpdateAtCurrent
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentIncrementalChecker
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentIncrementalChecker_successive_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentChecker_accepts_successiveAt
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentChecker_rejects_wrong_successiveAt
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedSubmittedRuntimeUpdate_predecessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.transportDependentCheckedUpdateResult
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntimeSubmission
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntimeSubmission
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_certificate_consumes_successiveAssembly
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_consumes_first_successor_memory
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_preservedContracts
/- AXIOM_AUDIT_END -/
