import RelationalPerimeter.Agents.Neural.LearnedSuccessiveStructuralCone

/-!
# Autonomous checker closure for successive and post-forgetting domains

This module closes L5.  Serialized requests are decoded before any target
certificate exists.  Incremental success is reconstructed from finite local
receipts and target fragments; the complete reference checker independently
decodes the target and reruns semantic transition production.  The
post-forgetting checker uses the same meta-contract transition permissions as
the runtime and never restores a forgotten historical identity.
-/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

/-! The successive incremental engine is defined beside the dependent runtime
checker in `LearnedRuntimeAdapter`.  Consequently the runtime and the generic
checker consume the same executed analysis and the same structural assembly;
this module adds only the independent full recheck and comparison theorems. -/

/-! ## Independent complete recheck of the successive domain -/

def learnedSuccessiveDecodedFullRecheckExecution
    {source : LearnedReceivedArtifact}
    (decoded : LearnedExecutableDecodedArtifact source)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.aligned
        next := decoded.contract }) :
    FullRecheckExecution learnedExecutableMetaContractInterface
      learnedTransitionProductionKernel LearnedAlignedCheckedAgent decoded
      decision := by
  cases decoded with
  | initial => cases decision.accepted
  | aligned => cases decision.accepted
  | extended =>
      have decisionExact := decision.unique
        learnedExtendedTransitionDecision
      cases decisionExact
      exact { material := .installExtended, targetExact := rfl }
  | renamed => cases decision.accepted

def recomputeLearnedSuccessiveFullRecheckExecution
    (update : LearnedSerializedConstitutiveUpdate)
    (target : InitialCheckSuccess learnedExecutableMetaContractInterface
      update.targetReceivedArtifact)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.aligned
        next := learnedExecutableMetaContractInterface.decodedContract
          target.decodedArtifact }) :
    Except LearnedRuntimeUpdateError
      (FullRecheckExecution learnedExecutableMetaContractInterface
        learnedTransitionProductionKernel LearnedAlignedCheckedAgent
        target.decodedArtifact decision) :=
  match learnedTransitionRequestEquality update.transition
      ({ current := .aligned, next := .extended } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | .isFalse _ => .error .unexpectedTransition
  | .isTrue _transitionExact =>
      match independentLearnedRequirementInputEquality update.nextInput
          independentLearnedCertifiedInput with
      | .isFalse _ => .error .unexpectedNextInput
      | .isTrue _nextInputExact =>
          match update.intent with
          | .preserveAuthorizedBehavior =>
              if _dependencyExact :
                  primaryAuthorizationConstitutivelyConsumed
                    update.targetNetwork = true then
                if _targetExact : update.targetNetwork =
                    independentLearnedSecondSuccessorNetwork then
                  .ok (learnedSuccessiveDecodedFullRecheckExecution
                    target.decodedArtifact decision)
                else
                  .error .unsupportedTargetArtifact
              else
                .error .missingConstitutiveDependency

def learnedSuccessiveFullRecheckEngine : FullRecheckEngine
    learnedExecutableMetaContractInterface LearnedAlignedCheckedAgent where
  Update := LearnedSerializedConstitutiveUpdate
  Error := LearnedRuntimeUpdateError
  targetArtifact := LearnedSerializedConstitutiveUpdate.targetReceivedArtifact
  mapTargetError := mapLearnedFullRecheckTargetError
  transitionRejected := .unexpectedTransition
  kernel := learnedTransitionProductionKernel
  recomputeExecution := recomputeLearnedSuccessiveFullRecheckExecution

/-! ## Closed L5 witness -/

def learnedExtendedSuccessiveDecoded :
    DecodedLearnedSuccessiveUpdate learnedExtendedSerializedUpdate :=
  match exact : decodeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate with
  | .ok decoded => decoded
  | .error problem => False.elim (by cases exact)

theorem decodeLearnedExtendedSuccessive_exact :
    decodeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate =
      .ok learnedExtendedSuccessiveDecoded := by
  rfl

theorem learnedSuccessiveIncrementalAccepted :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate := by
  apply (checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate).2
  exact ⟨
    { decoded := learnedExtendedSuccessiveDecoded
      decodedExact := decodeLearnedExtendedSuccessive_exact
      receivedDecision := learnedExtendedTransitionDecision
      transitionAccepted := rfl
      authorizationConsumed := rfl
      targetNetworkExact := rfl }⟩

theorem learnedSuccessiveFullRecheckAccepted :
    FullRecheckAccepted learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate := by
  apply (checkFullUpdate_complete_for_local_conditions
    learnedSuccessiveFullRecheckEngine learnedExtendedSerializedUpdate).2
  exact ⟨
    { target := learnedExtendedCheckSuccess
      targetAccepted := checkInitial_accepts_learned_extended_artifact
      transitionDecision := learnedExtendedTransitionDecision
      transitionAccepted := rfl
      execution :=
        { material := .installExtended
          targetExact := rfl }
      executionAccepted := rfl }⟩

/-- The concrete incremental success is obtained by executing the incremental
checker.  It is a downstream readout of that computation, never an input to
the complete reference checker. -/
def learnedSuccessiveIncrementalSuccess :
    GenericIncrementalCheckSuccess learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate :=
  match exact : checkGenericIncrementalUpdate
      learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate with
  | .ok success => success
  | .error problem => False.elim (by
      have accepted := learnedSuccessiveIncrementalAccepted
      rcases accepted with ⟨success, successExact⟩
      rw [exact] at successExact
      cases successExact)

theorem checkLearnedSuccessiveIncremental_exact :
    checkGenericIncrementalUpdate learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate =
      .ok learnedSuccessiveIncrementalSuccess := by
  rfl

/-- The complete success is obtained by independently executing the complete
checker from the same serialized update. -/
def learnedSuccessiveFullRecheckSuccess :
    FullRecheckSuccess learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate :=
  match exact : checkFullUpdate learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate with
  | .ok success => success
  | .error problem => False.elim (by
      have accepted := learnedSuccessiveFullRecheckAccepted
      rcases accepted with ⟨success, successExact⟩
      rw [exact] at successExact
      cases successExact)

theorem checkLearnedSuccessiveFullRecheck_exact :
    checkFullUpdate learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate =
      .ok learnedSuccessiveFullRecheckSuccess := by
  rfl

/-- Both independent executions install the same exact successor. -/
theorem learnedSuccessiveIncrementalAndFullSuccessor_exact :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next := by
  rfl

/-- In particular, neither path substitutes a different target certificate. -/
theorem learnedSuccessiveIncrementalAndFullCertificate_exact :
    learnedSuccessiveIncrementalSuccess.checked.next.certificate =
      learnedSuccessiveFullRecheckSuccess.checked.next.certificate := by
  rfl

/-- The successive incremental certificate also consumes the assembly whose
outside-cone inputs come from the exact checked predecessor. -/
theorem learnedSuccessiveInstalledStructuralAssembly_exact :
    (learnedSuccessiveIncrementalSuccess.checked.next.certificate
        ).structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations := by
  rfl

theorem learnedSuccessiveTransport_reads_checked_source :
    learnedSuccessiveTransportedStructuralFragments =
      let source :=
        structuralObservationSnapshot LearnedAlignedCheckedAgent.certificate
      source.take 10 := by
  rfl

theorem learnedSuccessiveIncrementalAndFullAcceptance_equivalent :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate ↔
      FullRecheckAccepted learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate := by
  constructor <;> intro _
  · exact learnedSuccessiveFullRecheckAccepted
  · exact learnedSuccessiveIncrementalAccepted

/-! ## Autonomous post-forgetting continuation and contract change -/

/-- Proof-free requests accepted after forgetting.  A contract change carries
the complete received update: the target artifact, stable identities, input,
intent, and transition are decoded again before installation. -/
inductive SerializedLearnedPostForgettingRequest where
  | continueCurrent (input : IndependentLearnedFutureInput)
  | changeContract (update : LearnedSerializedConstitutiveUpdate)

def decodeLearnedPostForgettingRequest :
    SerializedLearnedPostForgettingRequest →
      PostForgettingRequest LearnedAlignedCurrentAgent
  | .continueCurrent input =>
      @PostForgettingRequest.continueCurrent learnedConstitutiveMetaContract
        .aligned LearnedAlignedCurrentAgent input
  | .changeContract _ =>
      @PostForgettingRequest.changeContract learnedConstitutiveMetaContract
        .aligned LearnedAlignedCurrentAgent .extended

inductive LearnedPostForgettingCheckError where
  | futureRefused
  | updateRefused (problem : LearnedRuntimeUpdateError)

/-- Autonomous finite conditions for one post-forgetting request.  They are
the local reflected admission or transition receipts, not the result of either
checker below. -/
inductive LearnedPostForgettingLocalConditionData :
    (source : SerializedLearnedPostForgettingRequest) → Type 7 where
  | continueCurrent
      (input : IndependentLearnedFutureInput)
      (admitted : IndependentLearnedFutureAdmission input) :
      LearnedPostForgettingLocalConditionData (.continueCurrent input)
  | changeContract
      (update : LearnedSerializedConstitutiveUpdate)
      (analysis : LearnedSuccessiveEngineAnalysis update) :
      LearnedPostForgettingLocalConditionData (.changeContract update)

/-- Independent complete-recheck receipts for the same proof-free domain. -/
inductive LearnedPostForgettingFullConditionData :
    (source : SerializedLearnedPostForgettingRequest) → Type 7 where
  | continueCurrent
      (input : IndependentLearnedFutureInput)
      (admitted : IndependentLearnedFutureAdmission input) :
      LearnedPostForgettingFullConditionData (.continueCurrent input)
  | changeContract
      (update : LearnedSerializedConstitutiveUpdate)
      (success : FullRecheckSuccess learnedSuccessiveFullRecheckEngine update) :
      LearnedPostForgettingFullConditionData (.changeContract update)

/-- Autonomous local premises for the complete post-forgetting reference.  In
the contract-changing case these are the decoder, transition, and execution
receipts of the independent full checker, not its global verdict. -/
inductive LearnedPostForgettingFullLocalConditions :
    (source : SerializedLearnedPostForgettingRequest) → Prop where
  | continueCurrent
      (input : IndependentLearnedFutureInput)
      (admitted : IndependentLearnedFutureAdmission input) :
      LearnedPostForgettingFullLocalConditions (.continueCurrent input)
  | changeContract
      (update : LearnedSerializedConstitutiveUpdate)
      (conditions : FullRecheckLocalConditions
        learnedSuccessiveFullRecheckEngine update) :
      LearnedPostForgettingFullLocalConditions (.changeContract update)

def analyzeLearnedPostForgettingIncrementally
    (source : SerializedLearnedPostForgettingRequest) :
    Except LearnedPostForgettingCheckError
      (LearnedPostForgettingLocalConditionData source) :=
  match source with
  | .continueCurrent input =>
      match decideIndependentLearnedFutureAdmission input with
      | .inl admitted => .ok (.continueCurrent input admitted)
      | .inr _ => .error .futureRefused
  | .changeContract update =>
      match analyzeLearnedSuccessiveUpdate update with
      | .error problem => .error (.updateRefused problem)
      | .ok analysis => .ok (.changeContract update analysis)

def learnedPostForgettingContinuationFromAdmission
    (input : IndependentLearnedFutureInput)
    (admitted : IndependentLearnedFutureAdmission input) :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent (.continueCurrent input) :=
  @PostForgettingPermission.continueCurrent learnedConstitutiveMetaContract
    .aligned LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent input
    (LearnedAlignedCurrentAgent.certificate.futureRealization.exact.forward
      (LearnedAlignedOperationalContract.futureSourceOfState
        LearnedAlignedCurrentAgent.state) input admitted)

def learnedPostForgettingJustificationFromDecision
    {next : LearnedOperationalContract}
    {intent : IndependentLearnedUpdateIntent}
    (intentAdmitted : AdmittedIndependentLearnedIntent intent)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.aligned, next := next }) :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent next := by
  cases next with
  | initial => cases decision.accepted
  | aligned => cases decision.accepted
  | extended =>
      exact
        { transition := decision.transition
          persistentSource := fun obligation => by
            cases obligation
            exact ULift.up intentAdmitted }

def learnedPostForgettingChangeFromDecision
    {intent : IndependentLearnedUpdateIntent}
    (intentAdmitted : AdmittedIndependentLearnedIntent intent)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.aligned,
        next := LearnedOperationalContract.extended }) :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent (.changeContract .extended) :=
  @PostForgettingPermission.changeContract learnedConstitutiveMetaContract
    .aligned LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent
    .extended
    (learnedPostForgettingJustificationFromDecision intentAdmitted decision)

def LearnedPostForgettingLocalConditionData.permission
    {source : SerializedLearnedPostForgettingRequest}
    (conditions : LearnedPostForgettingLocalConditionData source) :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent
      (decodeLearnedPostForgettingRequest source) :=
  match conditions with
  | .continueCurrent input admitted =>
      learnedPostForgettingContinuationFromAdmission input admitted
  | .changeContract _ analysis =>
      learnedPostForgettingChangeFromDecision
        analysis.executed.decoded.intentAdmitted
        (analysis.executed.receivedDecision.transportRequest
          analysis.executed.decoded.transitionExact)

/-- Incremental post-forgetting checker.  It consumes only the proof-free
request, reflects the finite admission/transition decision, and constructs the
permission from that receipt and the existing exact future realization. -/
def checkLearnedPostForgettingIncremental
    (source : SerializedLearnedPostForgettingRequest) :
    Except LearnedPostForgettingCheckError
      (PostForgettingPermission LearnedAlignedCurrentAgent
        learnedAlignedForgottenCurrentAgent
        (decodeLearnedPostForgettingRequest source)) :=
  match analyzeLearnedPostForgettingIncrementally source with
  | .error problem => .error problem
  | .ok conditions => .ok conditions.permission

def analyzeLearnedPostForgettingCompletely
    (source : SerializedLearnedPostForgettingRequest) :
    Except LearnedPostForgettingCheckError
      (LearnedPostForgettingFullConditionData source) :=
  match source with
  | .continueCurrent input =>
      match independentLearnedReducedFutureContract.decision
          learnedAlignedForgottenCurrentAgent.memory input with
      | .inl admitted => .ok (.continueCurrent input admitted)
      | .inr _ => .error .futureRefused
  | .changeContract update =>
      match checkFullUpdate learnedSuccessiveFullRecheckEngine update with
      | .error problem => .error (.updateRefused problem)
      | .ok success => .ok (.changeContract update success)

/-- Independent complete reference algorithm for the post-forgetting domain.
It repeats the reflected decisions from the serialized request and has no
argument through which an incremental result or fragment could be supplied. -/
def recheckLearnedPostForgettingCompletely
    (source : SerializedLearnedPostForgettingRequest) :
    Except LearnedPostForgettingCheckError
      (LearnedPostForgettingFullConditionData source) :=
  analyzeLearnedPostForgettingCompletely source

def ExceptAccepted {Error Result : Type _} : Except Error Result → Prop
  | .ok _ => True
  | .error _ => False

abbrev LearnedPostForgettingIncrementalAccepted
    (source : SerializedLearnedPostForgettingRequest) : Prop :=
  ExceptAccepted (analyzeLearnedPostForgettingIncrementally source)

abbrev LearnedPostForgettingFullRecheckAccepted
    (source : SerializedLearnedPostForgettingRequest) : Prop :=
  ExceptAccepted (analyzeLearnedPostForgettingCompletely source)

theorem learnedPostForgettingFullContinuation_accepts
    {input : IndependentLearnedFutureInput}
    (admitted : IndependentLearnedFutureAdmission input) :
    LearnedPostForgettingFullRecheckAccepted (.continueCurrent input) := by
  have accepted : ExceptAccepted
      (match independentLearnedReducedFutureContract.decision
          learnedAlignedForgottenCurrentAgent.memory input with
        | .inl witness => Except.ok
            (LearnedPostForgettingFullConditionData.continueCurrent input witness)
        | .inr _ => Except.error LearnedPostForgettingCheckError.futureRefused) := by
    cases decided : independentLearnedReducedFutureContract.decision
        learnedAlignedForgottenCurrentAgent.memory input with
    | inl witness => trivial
    | inr refused => exact False.elim (refused admitted)
  simpa only [LearnedPostForgettingFullRecheckAccepted,
    analyzeLearnedPostForgettingCompletely] using accepted

theorem learnedPostForgettingFullChange_accepts
    {update : LearnedSerializedConstitutiveUpdate}
    (conditions : FullRecheckLocalConditions
      learnedSuccessiveFullRecheckEngine update) :
    LearnedPostForgettingFullRecheckAccepted (.changeContract update) := by
  have fullAccepted : FullRecheckAccepted learnedSuccessiveFullRecheckEngine
      update :=
    (checkFullUpdate_complete_for_local_conditions
      learnedSuccessiveFullRecheckEngine update).2 conditions
  rcases fullAccepted with ⟨success, successExact⟩
  have accepted : ExceptAccepted
      (match checkFullUpdate learnedSuccessiveFullRecheckEngine update with
        | .error problem => Except.error
            (LearnedPostForgettingCheckError.updateRefused problem)
        | .ok checkedSuccess => Except.ok
            (LearnedPostForgettingFullConditionData.changeContract update
              checkedSuccess)) := by
    rw [successExact]
    trivial
  simpa only [LearnedPostForgettingFullRecheckAccepted,
    analyzeLearnedPostForgettingCompletely] using accepted

def learnedPostForgettingAdmittedContinuationRequest :
    SerializedLearnedPostForgettingRequest :=
  .continueCurrent learnedAdmittedFutureRequest

def learnedPostForgettingExtendedChangeRequest :
    SerializedLearnedPostForgettingRequest :=
  .changeContract learnedExtendedSerializedUpdate

def learnedPostForgettingRefusedContinuationRequest :
    SerializedLearnedPostForgettingRequest :=
  .continueCurrent learnedRefusedFutureRequest

theorem learnedPostForgettingAdmittedContinuation_incremental :
    LearnedPostForgettingIncrementalAccepted
      learnedPostForgettingAdmittedContinuationRequest := by
  trivial

theorem learnedPostForgettingAdmittedContinuation_full :
    LearnedPostForgettingFullRecheckAccepted
      learnedPostForgettingAdmittedContinuationRequest := by
  trivial

theorem learnedPostForgettingExtendedChange_incremental :
    LearnedPostForgettingIncrementalAccepted
      learnedPostForgettingExtendedChangeRequest := by
  trivial

theorem learnedPostForgettingExtendedChange_full :
    LearnedPostForgettingFullRecheckAccepted
      learnedPostForgettingExtendedChangeRequest := by
  trivial

theorem learnedPostForgettingIncrementalContinuation_accepts
    {input : IndependentLearnedFutureInput}
    (admitted : IndependentLearnedFutureAdmission input) :
    LearnedPostForgettingIncrementalAccepted (.continueCurrent input) := by
  have accepted : ExceptAccepted
      (match decideIndependentLearnedFutureAdmission input with
        | .inl witness => Except.ok
            (LearnedPostForgettingLocalConditionData.continueCurrent input witness)
        | .inr _ => Except.error LearnedPostForgettingCheckError.futureRefused) := by
    cases decided : decideIndependentLearnedFutureAdmission input with
    | inl witness => trivial
    | inr refused => exact False.elim (refused admitted)
  simpa only [LearnedPostForgettingIncrementalAccepted,
    analyzeLearnedPostForgettingIncrementally] using accepted

theorem learnedPostForgettingIncrementalChange_accepts
    {update : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis update) :
    LearnedPostForgettingIncrementalAccepted (.changeContract update) := by
  rcases completeLearnedSuccessiveAnalysis update analysis.executed with
    ⟨computed, acceptedExact⟩
  have accepted : ExceptAccepted
      (match analyzeLearnedSuccessiveUpdate update with
        | .error problem => Except.error
            (LearnedPostForgettingCheckError.updateRefused problem)
        | .ok checkedAnalysis => Except.ok
            (LearnedPostForgettingLocalConditionData.changeContract update
              checkedAnalysis)) := by
    rw [acceptedExact]
    trivial
  simpa only [LearnedPostForgettingIncrementalAccepted,
    analyzeLearnedPostForgettingIncrementally] using accepted

/-- The incremental post-forgetting checker is complete for every request in
its proof-free domain relative to its autonomous local receipts. -/
theorem learnedPostForgettingIncremental_complete
    (source : SerializedLearnedPostForgettingRequest) :
    LearnedPostForgettingIncrementalAccepted source ↔
      Nonempty (LearnedPostForgettingLocalConditionData source) := by
  constructor
  · intro accepted
    unfold LearnedPostForgettingIncrementalAccepted ExceptAccepted at accepted
    cases exact : analyzeLearnedPostForgettingIncrementally source with
    | error problem =>
        rw [exact] at accepted
        exact False.elim accepted
    | ok conditions => exact ⟨conditions⟩
  · intro available
    rcases available with ⟨conditions⟩
    cases conditions with
    | continueCurrent input admitted =>
        exact learnedPostForgettingIncrementalContinuation_accepts admitted
    | changeContract update analysis =>
        exact learnedPostForgettingIncrementalChange_accepts analysis

/-- The independent full recheck has the corresponding all-request relative
completeness theorem and receives no incremental verdict. -/
theorem learnedPostForgettingFullRecheck_complete
    (source : SerializedLearnedPostForgettingRequest) :
    LearnedPostForgettingFullRecheckAccepted source ↔
      LearnedPostForgettingFullLocalConditions source := by
  constructor
  · intro accepted
    cases source with
    | continueCurrent input =>
        have accepted' : ExceptAccepted
            (match independentLearnedReducedFutureContract.decision
                learnedAlignedForgottenCurrentAgent.memory input with
              | .inl admitted => Except.ok
                  (LearnedPostForgettingFullConditionData.continueCurrent
                    input admitted)
              | .inr _ => Except.error
                  LearnedPostForgettingCheckError.futureRefused) := by
          simpa only [LearnedPostForgettingFullRecheckAccepted,
            analyzeLearnedPostForgettingCompletely] using accepted
        cases decided : independentLearnedReducedFutureContract.decision
            learnedAlignedForgottenCurrentAgent.memory input with
        | inl admitted => exact .continueCurrent input admitted
        | inr refused =>
            rw [decided] at accepted'
            exact False.elim accepted'
    | changeContract update =>
        have accepted' : ExceptAccepted
            (match checkFullUpdate learnedSuccessiveFullRecheckEngine update with
              | .error problem => Except.error
                  (LearnedPostForgettingCheckError.updateRefused problem)
              | .ok success => Except.ok
                  (LearnedPostForgettingFullConditionData.changeContract
                    update success)) := by
          simpa only [LearnedPostForgettingFullRecheckAccepted,
            analyzeLearnedPostForgettingCompletely] using accepted
        cases checked : checkFullUpdate learnedSuccessiveFullRecheckEngine update with
        | error problem =>
            rw [checked] at accepted'
            exact False.elim accepted'
        | ok success =>
            exact .changeContract update
              ((checkFullUpdate_complete_for_local_conditions
                learnedSuccessiveFullRecheckEngine update).1 ⟨success, checked⟩)
  · intro conditions
    cases conditions with
    | continueCurrent input admitted =>
        exact learnedPostForgettingFullContinuation_accepts admitted
    | changeContract update conditions =>
        exact learnedPostForgettingFullChange_accepts conditions

/-- Relative completeness is closed for both required post-forgetting
domains: continuation under the reduced future regime and an admitted contract
change.  The right sides contain only autonomous admission/transition receipts;
neither checker verdict occurs in them. -/
theorem learnedPostForgettingRequiredRelativeCompleteness :
    (LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingAdmittedContinuationRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest)) ∧
    (LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingAdmittedContinuationRequest ↔
      LearnedPostForgettingFullLocalConditions
        learnedPostForgettingAdmittedContinuationRequest) ∧
    (LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingExtendedChangeRequest)) ∧
    (LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      LearnedPostForgettingFullLocalConditions
        learnedPostForgettingExtendedChangeRequest) := by
  exact ⟨learnedPostForgettingIncremental_complete _,
    learnedPostForgettingFullRecheck_complete _,
    learnedPostForgettingIncremental_complete _,
    learnedPostForgettingFullRecheck_complete _⟩

theorem learnedPostForgettingRefusedContinuation_rejected_incrementally :
    checkLearnedPostForgettingIncremental
        learnedPostForgettingRefusedContinuationRequest =
      .error .futureRefused := by
  rfl

theorem learnedPostForgettingRefusedContinuation_rejected_by_full_recheck :
    recheckLearnedPostForgettingCompletely
        learnedPostForgettingRefusedContinuationRequest =
      .error .futureRefused := by
  rfl

theorem learnedPostForgettingPositiveAcceptance_equivalent :
    (LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingAdmittedContinuationRequest ↔
      LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingAdmittedContinuationRequest) ∧
    (LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingExtendedChangeRequest) := by
  constructor <;> constructor <;> intro _
  · exact learnedPostForgettingAdmittedContinuation_full
  · exact learnedPostForgettingAdmittedContinuation_incremental
  · exact learnedPostForgettingExtendedChange_full
  · exact learnedPostForgettingExtendedChange_incremental

/-! ## Effectful closure: permission consumption and runtime installation -/

/-- An installed ordinary continuation remains an ordinary continuation: it
does not pretend to be a meta-contract transition. -/
structure InstalledLearnedPostForgettingContinuation
    (input : IndependentLearnedFutureInput) : Type 8 where
  permission : PostForgettingPermission LearnedAlignedCurrentAgent
    learnedAlignedForgottenCurrentAgent (.continueCurrent input)
  execution : ExecutedPostForgettingContinuation LearnedAlignedCurrentAgent
    learnedAlignedForgottenCurrentAgent input permission

def submitLearnedPostForgettingContinuation
    (input : IndependentLearnedFutureInput) :
    Except LearnedPostForgettingCheckError
      (InstalledLearnedPostForgettingContinuation input) :=
  match _checked : checkLearnedPostForgettingIncremental (.continueCurrent input) with
  | .error problem => .error problem
  | .ok permission =>
      .ok { permission := permission
            execution := executePostForgettingContinuation permission }

/-- Effectful relative completeness for ordinary post-forgetting requests.
This theorem concerns the installer itself, not merely the permission checker:
an installation exists exactly when the autonomous local admission data exist. -/
theorem submitLearnedPostForgettingContinuation_complete
    (input : IndependentLearnedFutureInput) :
    ExceptAccepted (submitLearnedPostForgettingContinuation input) ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        (.continueCurrent input)) := by
  constructor
  · intro installed
    have accepted : LearnedPostForgettingIncrementalAccepted
        (.continueCurrent input) := by
      unfold submitLearnedPostForgettingContinuation
        checkLearnedPostForgettingIncremental ExceptAccepted at installed
      unfold LearnedPostForgettingIncrementalAccepted ExceptAccepted
      cases analyzed : analyzeLearnedPostForgettingIncrementally
          (.continueCurrent input) with
      | error problem =>
          rw [analyzed] at installed
          exact False.elim installed
      | ok conditions =>
          exact True.intro
    exact (learnedPostForgettingIncremental_complete _).1 accepted
  · intro conditions
    have accepted : LearnedPostForgettingIncrementalAccepted
        (.continueCurrent input) :=
      (learnedPostForgettingIncremental_complete _).2 conditions
    unfold LearnedPostForgettingIncrementalAccepted ExceptAccepted at accepted
    unfold submitLearnedPostForgettingContinuation
      checkLearnedPostForgettingIncremental ExceptAccepted
    cases analyzed : analyzeLearnedPostForgettingIncrementally
        (.continueCurrent input) with
    | error problem =>
        rw [analyzed] at accepted
        exact False.elim accepted
    | ok conditions =>
        exact True.intro

def learnedInstalledPostForgettingContinuation :
    InstalledLearnedPostForgettingContinuation learnedAdmittedFutureRequest :=
  match exact : submitLearnedPostForgettingContinuation
      learnedAdmittedFutureRequest with
  | .ok installed => installed
  | .error problem => False.elim (by cases exact)

theorem submitLearnedPostForgettingContinuation_exact :
    submitLearnedPostForgettingContinuation learnedAdmittedFutureRequest =
      .ok learnedInstalledPostForgettingContinuation := by
  rfl

theorem learnedInstalledPostForgettingContinuation_consumes_reducedMemory :
    learnedInstalledPostForgettingContinuation.execution.outcome =
      independentLearnedReducedFutureContract.outcome
        learnedAlignedExecutedFutureForgetting.output
        [learnedAdmittedFutureRequest] := by
  rfl

theorem submitLearnedPostForgettingRefusedContinuation_rejected :
    submitLearnedPostForgettingContinuation learnedRefusedFutureRequest =
      .error .futureRefused := by
  rfl

theorem learnedPostForgettingRefusal_has_no_continuationResult :
    Not (Exists fun installed =>
      submitLearnedPostForgettingContinuation learnedRefusedFutureRequest =
        .ok installed) := by
  intro alleged
  rcases alleged with ⟨installed, alleged⟩
  rw [submitLearnedPostForgettingRefusedContinuation_rejected] at alleged
  cases alleged

/-- Contract-changing runtime inputs are accepted only at the exact aligned
agent produced by the first installed transition. -/
inductive LearnedPostForgettingRuntimeUpdate :
    {contract : LearnedOperationalContract} ->
      CheckedAgent learnedConstitutiveMetaContract contract -> Type where
  | changeContract (update : LearnedSerializedConstitutiveUpdate) :
      LearnedPostForgettingRuntimeUpdate LearnedAlignedCurrentAgent

/-- Exact post-forgetting transition material consumed before installation.
The persistent intent is transported and the invalidated authorization is
rechecked through the same justified transition that licensed the contract
change.  The checked update is then built from the independently executed
successive analysis; it is not received as a field. -/
structure ClosedLearnedPostForgettingContractChange
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent .extended) : Type 7 where
  transportedIntent : learnedConstitutiveMetaContract.TargetPersistentWitness
    .aligned .extended .admittedIntent
  transportedIntentExact : transportedIntent =
    justification.transportedPersistent .admittedIntent
  recheckedAuthorization : learnedConstitutiveMetaContract.RecheckedWitness
    .aligned .extended .authorizationConsumption
  recheckedAuthorizationExact : recheckedAuthorization =
    justification.rechecked .authorizationConsumption
  checked : CheckedUpdate LearnedAlignedCurrentAgent analysis.target.nextContract
  checkedExact : checked = buildIncrementalCheckedUpdate analysis.target

def closeLearnedPostForgettingContractChange
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent .extended) :
    ClosedLearnedPostForgettingContractChange analysis justification :=
  { transportedIntent :=
      justification.transportedPersistent .admittedIntent
    transportedIntentExact := rfl
    recheckedAuthorization :=
      justification.rechecked .authorizationConsumption
    recheckedAuthorizationExact := rfl
    checked := buildIncrementalCheckedUpdate analysis.target
    checkedExact := rfl }

/-- The concrete P5 transition material is reconstructed from the exact
analysis returned for the received aligned-to-extended update. -/
def learnedPostForgettingExtendedJustification :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent .extended :=
  learnedPostForgettingJustificationFromDecision
    learnedSuccessiveIncrementalSuccess.analysis.executed.decoded.intentAdmitted
    (learnedSuccessiveIncrementalSuccess.analysis.executed.receivedDecision.transportRequest
      learnedSuccessiveIncrementalSuccess.analysis.executed.decoded.transitionExact)

def learnedClosedPostForgettingExtendedChange :
    ClosedLearnedPostForgettingContractChange
      learnedSuccessiveIncrementalSuccess.analysis
      learnedPostForgettingExtendedJustification :=
  closeLearnedPostForgettingContractChange
    learnedSuccessiveIncrementalSuccess.analysis
    learnedPostForgettingExtendedJustification

def checkLearnedPostForgettingRuntimeUpdate
    {contract : LearnedOperationalContract}
    {current : CheckedAgent learnedConstitutiveMetaContract contract}
    (update : LearnedPostForgettingRuntimeUpdate current) :
    Except LearnedPostForgettingCheckError
      (DependentCheckedUpdateResult current) :=
  match update with
  | .changeContract source =>
      match analyzeLearnedPostForgettingIncrementally (.changeContract source) with
      | .error problem => .error problem
      | .ok conditions =>
          match _permissionExact : conditions.permission with
          | .changeContract _ justification =>
              match conditions with
              | .changeContract _ analysis =>
                  let closed := closeLearnedPostForgettingContractChange
                    analysis justification
                  .ok (dependentCheckedUpdateResult closed.checked)

def learnedPostForgettingDependentChecker :
    DependentIncrementalChecker learnedConstitutiveMetaContract where
  Error := LearnedPostForgettingCheckError
  Update := LearnedPostForgettingRuntimeUpdate
  check := by
    intro contract current update
    exact checkLearnedPostForgettingRuntimeUpdate update

def learnedPostForgettingInitialRuntime : CertifiedRuntime
    learnedPostForgettingDependentChecker LearnedAlignedCurrentAgent :=
  initialCertifiedRuntime learnedPostForgettingDependentChecker
    LearnedAlignedCurrentAgent

def learnedPostForgettingExtendedRuntimeUpdate :
    learnedPostForgettingDependentChecker.Update
      learnedPostForgettingInitialRuntime.current :=
  .changeContract learnedExtendedSerializedUpdate

theorem checkLearnedPostForgettingExtendedRuntimeUpdate_exact :
    checkLearnedPostForgettingRuntimeUpdate
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok (dependentCheckedUpdateResult
        learnedClosedPostForgettingExtendedChange.checked) := by
  rfl

def learnedPostForgettingExtendedRuntime : CertifiedRuntime
    learnedPostForgettingDependentChecker LearnedAlignedCurrentAgent :=
  match submitUpdate learnedPostForgettingInitialRuntime
      learnedPostForgettingExtendedRuntimeUpdate with
  | .ok runtime => runtime
  | .error _ => learnedPostForgettingInitialRuntime

def learnedPostForgettingInitialRuntime_reachable :
    CertifiedRuntimeReachable learnedPostForgettingDependentChecker
      LearnedAlignedCurrentAgent learnedPostForgettingInitialRuntime :=
  .initial

theorem submitUpdate_postForgettingExtended_exact :
    submitUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok learnedPostForgettingExtendedRuntime := by
  rfl

def learnedPostForgettingExtendedRuntime_reachable :
    CertifiedRuntimeReachable learnedPostForgettingDependentChecker
      LearnedAlignedCurrentAgent learnedPostForgettingExtendedRuntime :=
  .submitted learnedPostForgettingInitialRuntime
    learnedPostForgettingExtendedRuntime
    learnedPostForgettingExtendedRuntimeUpdate
    learnedPostForgettingInitialRuntime_reachable
    submitUpdate_postForgettingExtended_exact

theorem learnedPostForgettingRuntime_starts_at_installedAlignedState :
    learnedPostForgettingInitialRuntime.current =
      learnedAlignedCertifiedRuntime.current := by
  rfl

theorem learnedPostForgettingExtendedRuntime_successor_exact :
    learnedPostForgettingExtendedRuntime.current =
      learnedExtendedCertifiedRuntime.current := by
  rfl

def learnedPostForgettingExtendedRuntime_checkedHistory :
    EveryRuntimeStepSatisfies learnedPostForgettingExtendedRuntime.history :=
  learnedPostForgettingExtendedRuntime.checkedHistory

def learnedPostForgettingExtendedRuntime_preservedContracts :
    EveryRuntimeStepPreservesContracts
      learnedPostForgettingExtendedRuntime.history :=
  learnedPostForgettingExtendedRuntime.preservedContracts

theorem learnedPostForgettingBadChange_rejected_without_successor :
    Not (Exists fun next =>
      submitUpdate learnedPostForgettingInitialRuntime
        (LearnedPostForgettingRuntimeUpdate.changeContract
          learnedAlignedSerializedUpdate) = .ok next) := by
  apply submitUpdate_rejected_cannot_install learnedPostForgettingInitialRuntime
    (LearnedPostForgettingRuntimeUpdate.changeContract
      learnedAlignedSerializedUpdate)
    (.updateRefused .unexpectedTransition)
  rfl

/-- Closed F3 witness.  The earlier learned lineage, its executed reduction,
the ordinary continuation consuming the reduced memory, and the subsequent
contract-changing runtime installation are retained in one typed object.  The
two refusals state absence of an effectful result, not merely a diagnostic. -/
structure LearnedPostForgettingOperationalClosure : Type 12 where
  prior : LearnedConstitutiveAlignmentClosureCertificate
  priorExact : prior = learnedConstitutiveAlignmentClosure
  forgotten : ForgottenCurrentAgent LearnedAlignedCurrentAgent
  forgottenExact : forgotten = learnedAlignedForgottenCurrentAgent
  continuation : InstalledLearnedPostForgettingContinuation
    learnedAdmittedFutureRequest
  continuationExact : continuation = learnedInstalledPostForgettingContinuation
  continuationConsumesReducedMemory : continuation.execution.outcome =
    independentLearnedReducedFutureContract.outcome
      learnedAlignedExecutedFutureForgetting.output
      [learnedAdmittedFutureRequest]
  runtimeSource : CertifiedRuntime learnedPostForgettingDependentChecker
    LearnedAlignedCurrentAgent
  runtimeSourceExact : runtimeSource = learnedPostForgettingInitialRuntime
  closedContractChange : ClosedLearnedPostForgettingContractChange
    learnedSuccessiveIncrementalSuccess.analysis
    learnedPostForgettingExtendedJustification
  closedContractChangeExact : closedContractChange =
    learnedClosedPostForgettingExtendedChange
  transportedIntentConsumed : closedContractChange.transportedIntent =
    learnedPostForgettingExtendedJustification.transportedPersistent
      .admittedIntent
  authorizationRechecked : closedContractChange.recheckedAuthorization =
    learnedPostForgettingExtendedJustification.rechecked
      .authorizationConsumption
  checkedUpdateProduced : closedContractChange.checked =
    buildIncrementalCheckedUpdate
      learnedSuccessiveIncrementalSuccess.analysis.target
  runtimeCheckConsumesClosure :
    checkLearnedPostForgettingRuntimeUpdate
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok (dependentCheckedUpdateResult closedContractChange.checked)
  contractUpdate : learnedPostForgettingDependentChecker.Update
    runtimeSource.current
  contractUpdateExact : HEq contractUpdate
    learnedPostForgettingExtendedRuntimeUpdate
  installedRuntime : CertifiedRuntime learnedPostForgettingDependentChecker
    LearnedAlignedCurrentAgent
  installedExact : submitUpdate runtimeSource contractUpdate = .ok installedRuntime
  installedSuccessorExact : HEq installedRuntime.current
    learnedExtendedCertifiedRuntime.current
  installedReachable : CertifiedRuntimeReachable
    learnedPostForgettingDependentChecker LearnedAlignedCurrentAgent
    installedRuntime
  checkedHistory : EveryRuntimeStepSatisfies installedRuntime.history
  preservedContracts : EveryRuntimeStepPreservesContracts installedRuntime.history
  reducedMemoryDoesNotRecoverOrigin :
    (recover : IndependentLearnedOperationalMemory ->
      LearnedHistoricalStableOrigin) ->
    recover learnedAlignedExecutedFutureForgetting.output =
        learnedAlignedHistoricalForgettingInput.origin ->
    recover learnedRenamedExecutedFutureForgetting.output =
        learnedRenamedHistoricalForgettingInput.origin -> False
  refusedContinuationHasNoResult : Not (Exists fun installed =>
    submitLearnedPostForgettingContinuation learnedRefusedFutureRequest =
      .ok installed)
  refusedContractChangeHasNoSuccessor : Not (Exists fun next =>
    submitUpdate learnedPostForgettingInitialRuntime
      (LearnedPostForgettingRuntimeUpdate.changeContract
        learnedAlignedSerializedUpdate) = .ok next)

def learnedPostForgettingOperationalClosure :
    LearnedPostForgettingOperationalClosure :=
  { prior := learnedConstitutiveAlignmentClosure
    priorExact := rfl
    forgotten := learnedAlignedForgottenCurrentAgent
    forgottenExact := rfl
    continuation := learnedInstalledPostForgettingContinuation
    continuationExact := rfl
    continuationConsumesReducedMemory :=
      learnedInstalledPostForgettingContinuation_consumes_reducedMemory
    runtimeSource := learnedPostForgettingInitialRuntime
    runtimeSourceExact := rfl
    closedContractChange := learnedClosedPostForgettingExtendedChange
    closedContractChangeExact := rfl
    transportedIntentConsumed := rfl
    authorizationRechecked := rfl
    checkedUpdateProduced := rfl
    runtimeCheckConsumesClosure :=
      checkLearnedPostForgettingExtendedRuntimeUpdate_exact
    contractUpdate := learnedPostForgettingExtendedRuntimeUpdate
    contractUpdateExact := HEq.rfl
    installedRuntime := learnedPostForgettingExtendedRuntime
    installedExact := submitUpdate_postForgettingExtended_exact
    installedSuccessorExact := HEq.rfl
    installedReachable := learnedPostForgettingExtendedRuntime_reachable
    checkedHistory := learnedPostForgettingExtendedRuntime_checkedHistory
    preservedContracts := learnedPostForgettingExtendedRuntime_preservedContracts
    reducedMemoryDoesNotRecoverOrigin :=
      learnedExecutedFutureForgetting_origin_not_recoverable
    refusedContinuationHasNoResult :=
      learnedPostForgettingRefusal_has_no_continuationResult
    refusedContractChangeHasNoSuccessor :=
      learnedPostForgettingBadChange_rejected_without_successor }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessivePreCertificateGraph
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveCalculatedStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveExecutedDependencies
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedSuccessiveUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.recomputeLearnedSuccessiveFullRecheckExecution
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckEngine
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalSuccess
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveIncremental_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveFullRecheck_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.SerializedLearnedPostForgettingRequest
#print axioms ConstitutiveSearch.NeuralAgent.decodeLearnedPostForgettingRequest
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingLocalConditionData
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingFullConditionData
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedPostForgettingIncrementally
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingContinuationFromAdmission
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingJustificationFromDecision
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingLocalConditionData.permission
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedPostForgettingIncremental
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedPostForgettingCompletely
#print axioms ConstitutiveSearch.NeuralAgent.recheckLearnedPostForgettingCompletely
#print axioms ConstitutiveSearch.NeuralAgent.ExceptAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingRequiredRelativeCompleteness
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingRefusedContinuation_rejected_incrementally
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingRefusedContinuation_rejected_by_full_recheck
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingPositiveAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.InstalledLearnedPostForgettingContinuation
#print axioms ConstitutiveSearch.NeuralAgent.submitLearnedPostForgettingContinuation
#print axioms ConstitutiveSearch.NeuralAgent.submitLearnedPostForgettingContinuation_complete
#print axioms ConstitutiveSearch.NeuralAgent.learnedInstalledPostForgettingContinuation_consumes_reducedMemory
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.ClosedLearnedPostForgettingContractChange
#print axioms ConstitutiveSearch.NeuralAgent.closeLearnedPostForgettingContractChange
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedJustification
#print axioms ConstitutiveSearch.NeuralAgent.learnedClosedPostForgettingExtendedChange
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedPostForgettingRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingDependentChecker
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedPostForgettingExtendedRuntimeUpdate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingInitialRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_postForgettingExtended_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedRuntime_successor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedRuntime_checkedHistory
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedRuntime_preservedContracts
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingBadChange_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingOperationalClosure
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingOperationalClosure
/- AXIOM_AUDIT_END -/
