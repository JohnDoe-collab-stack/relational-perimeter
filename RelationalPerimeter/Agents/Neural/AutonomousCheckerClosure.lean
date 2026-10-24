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

/-! The canonical successive incremental engine is defined independently from
the dependent runtime path. The generic comparison theorems below use that
canonical engine, while the runtime checker reconstructs its analysis from the
predecessor it receives through
`analyzeDecodedLearnedSuccessiveUpdateAtCurrent`. Both establish the same
declared property on their explicit domains; they do not share one executed
analysis occurrence. This module adds the independent full recheck and the
comparison theorems. -/

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

def learnedSuccessiveFullRecheckLocalConditions :
    FullRecheckLocalConditionData learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate :=
  { target := learnedExtendedCheckSuccess
    targetAccepted := checkInitial_accepts_learned_extended_artifact
    transitionDecision := learnedExtendedTransitionDecision
    transitionAccepted := rfl
    execution :=
      { material := .installExtended
        targetExact := rfl }
    executionAccepted := rfl }

/-- The concrete incremental success is obtained by executing the incremental
checker.  It is a downstream readout of that computation, never an input to
the complete reference checker. -/
def learnedSuccessiveIncrementalReceipt :
    { success : GenericIncrementalCheckSuccess
        learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate //
      checkGenericIncrementalUpdate learnedSuccessiveIncrementalCheckerEngine
          learnedExtendedSerializedUpdate = .ok success } :=
  completeGenericIncrementalCheck learnedSuccessiveIncrementalCheckerEngine
    learnedExtendedSerializedUpdate learnedReferenceSuccessiveLocalConditions

def learnedSuccessiveIncrementalSuccess :
    GenericIncrementalCheckSuccess learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate :=
  GenericIncrementalCheckSuccess.ofAnalysis learnedReferenceSuccessiveAnalysis

theorem checkLearnedSuccessiveIncremental_exact :
    checkGenericIncrementalUpdate learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate =
      .ok learnedSuccessiveIncrementalSuccess := by
  exact learnedSuccessiveIncrementalReceipt.2

/-- The complete success is obtained by independently executing the complete
checker from the same serialized update. -/
def learnedSuccessiveFullRecheckReceipt :
    { success : FullRecheckSuccess learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate //
      checkFullUpdate learnedSuccessiveFullRecheckEngine
          learnedExtendedSerializedUpdate = .ok success } :=
  completeFullRecheck learnedSuccessiveFullRecheckEngine
    learnedExtendedSerializedUpdate learnedSuccessiveFullRecheckLocalConditions

def learnedSuccessiveFullRecheckSuccess :
    FullRecheckSuccess learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate :=
  FullRecheckSuccess.ofLocalConditions
    learnedSuccessiveFullRecheckLocalConditions

theorem checkLearnedSuccessiveFullRecheck_exact :
    checkFullUpdate learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate =
      .ok learnedSuccessiveFullRecheckSuccess := by
  exact learnedSuccessiveFullRecheckReceipt.2

/-- Both independent executions install the same exact successor. -/
theorem learnedSuccessiveIncrementalSuccess_next_exact :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedExtendedCheckedAgent := by
  change
    (buildIncrementalCheckedUpdate
      learnedReferenceSuccessiveAnalysis.target).next =
        learnedExtendedCheckedAgent
  rfl

theorem learnedSuccessiveFullRecheckSuccess_next_exact :
    learnedSuccessiveFullRecheckSuccess.checked.next =
      learnedExtendedCheckedAgent := by
  change learnedExtendedCheckSuccess.checkedAgent = learnedExtendedCheckedAgent
  rfl

theorem learnedSuccessiveIncrementalAndFullSuccessor_exact :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next := by
  exact learnedSuccessiveIncrementalSuccess_next_exact.trans
    learnedSuccessiveFullRecheckSuccess_next_exact.symm

/-- In particular, neither path substitutes a different target certificate. -/
theorem learnedSuccessiveIncrementalAndFullCertificate_exact :
    learnedSuccessiveIncrementalSuccess.checked.next.certificate =
      learnedSuccessiveFullRecheckSuccess.checked.next.certificate := by
  change
    assembleStateConstitution learnedReferenceSuccessiveAnalysis.target.fragments =
      assembleStateConstitution learnedExtendedStateFragments
  rfl

/-- The successive incremental certificate also consumes the assembly whose
outside-cone inputs come from the exact checked predecessor. -/
theorem learnedSuccessiveInstalledStructuralAssembly_exact :
    (learnedSuccessiveIncrementalSuccess.checked.next.certificate
        ).structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations := by
  change learnedReferenceSuccessiveStructuralAssembly.observations =
    learnedSuccessiveCalculatedStructuralAssembly.observations
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

/-- The declared successive domain is fixed by the proof-free request fields
checked by the decoder: transition, received network, stable naming, next
input, and intent.  This theorem makes that boundary explicit instead of
silently replacing the domain by the concrete example in later statements. -/
theorem learnedSuccessiveDeclaredDomain_source_exact
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    source = learnedExtendedSerializedUpdate := by
  cases source with
  | mk transition targetNetwork targetStableNaming nextInput intent =>
      cases conditions.executed.decoded.transitionExact
      cases conditions.executed.targetNetworkExact
      cases conditions.executed.decoded.stableNamingExact
      cases conditions.executed.decoded.nextInputExact
      cases intent
      rfl

/-- Acceptance agreement holds for every received update in the exact
successive domain, not merely for a theorem stated at the canonical spelling
of its unique supported value.  The full checker remains independent: its
acceptance is obtained through `checkFullUpdate` and its own completeness
boundary, never from the incremental verdict or certificate. -/
theorem learnedSuccessiveIncrementalAndFullAcceptance_equivalent_on_declared_domain
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
        source ↔
      FullRecheckAccepted learnedSuccessiveFullRecheckEngine source := by
  cases learnedSuccessiveDeclaredDomain_source_exact source conditions
  exact learnedSuccessiveIncrementalAndFullAcceptance_equivalent

/-- On the same declared domain, the two independently constructed reference
successes install the same successor; neither checker receives the other's
success value, verdict, or certificate. -/
theorem learnedSuccessiveIncrementalAndFullSuccessor_exact_on_declared_domain
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    Exists fun incrementalSuccess : GenericIncrementalCheckSuccess
        learnedSuccessiveIncrementalCheckerEngine source =>
      checkGenericIncrementalUpdate learnedSuccessiveIncrementalCheckerEngine
          source = .ok incrementalSuccess ∧
      Exists fun fullSuccess : FullRecheckSuccess
          learnedSuccessiveFullRecheckEngine source =>
        checkFullUpdate learnedSuccessiveFullRecheckEngine source =
            .ok fullSuccess ∧
        HEq incrementalSuccess.checked.next fullSuccess.checked.next := by
  cases learnedSuccessiveDeclaredDomain_source_exact source conditions
  exact ⟨learnedSuccessiveIncrementalSuccess,
    checkLearnedSuccessiveIncremental_exact,
    learnedSuccessiveFullRecheckSuccess,
    checkLearnedSuccessiveFullRecheck_exact,
    heq_of_eq learnedSuccessiveIncrementalAndFullSuccessor_exact⟩

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

def liftLearnedPostForgettingIncrementalChange
    (update : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError (LearnedSuccessiveEngineAnalysis update) →
      Except LearnedPostForgettingCheckError
        (LearnedPostForgettingLocalConditionData (.changeContract update))
  | .error problem => .error (.updateRefused problem)
  | .ok analysis => .ok (.changeContract update analysis)

theorem liftLearnedPostForgettingIncrementalChange_of_ok
    {update : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis update}
    (accepted : analyzeLearnedSuccessiveUpdate update = .ok analysis) :
    liftLearnedPostForgettingIncrementalChange update
        (analyzeLearnedSuccessiveUpdate update) =
      .ok (.changeContract update analysis) :=
  congrArg (liftLearnedPostForgettingIncrementalChange update) accepted

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
      liftLearnedPostForgettingIncrementalChange update
        (analyzeLearnedSuccessiveUpdate update)

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
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent
      (forgotten := learnedAlignedForgottenCurrentAgent) next := by
  cases next with
  | initial => cases decision.accepted
  | aligned => cases decision.accepted
  | extended =>
      exact
        { reducedMemory := learnedAlignedForgottenCurrentAgent.memory
          reducedMemoryExact := rfl
          transition := decision.transition
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

structure LearnedPostForgettingIncrementalAccepted
    (source : SerializedLearnedPostForgettingRequest) : Prop where
  accepted : ExceptAccepted (analyzeLearnedPostForgettingIncrementally source)

theorem learnedPostForgettingIncrementalAccepted_iff
    (source : SerializedLearnedPostForgettingRequest) :
    LearnedPostForgettingIncrementalAccepted source ↔
      ExceptAccepted (analyzeLearnedPostForgettingIncrementally source) :=
  ⟨fun accepted => accepted.accepted, fun accepted => ⟨accepted⟩⟩

structure LearnedPostForgettingFullRecheckAccepted
    (source : SerializedLearnedPostForgettingRequest) : Prop where
  accepted : ExceptAccepted (analyzeLearnedPostForgettingCompletely source)

theorem learnedPostForgettingFullRecheckAccepted_iff
    (source : SerializedLearnedPostForgettingRequest) :
    LearnedPostForgettingFullRecheckAccepted source ↔
      ExceptAccepted (analyzeLearnedPostForgettingCompletely source) :=
  ⟨fun accepted => accepted.accepted, fun accepted => ⟨accepted⟩⟩

theorem learnedPostForgettingIncrementalChange_accepts_of_analysis
    {update : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis update) :
    LearnedPostForgettingIncrementalAccepted (.changeContract update) := by
  have accepted : analyzeLearnedSuccessiveUpdate update = .ok analysis := by
    simpa only [learnedSuccessiveAnalysisOfLocalConditions_localConditions] using
        analyzeLearnedSuccessiveUpdate_of_local_conditions update
          analysis.localConditions
  refine ⟨?_⟩
  change ExceptAccepted
    (liftLearnedPostForgettingIncrementalChange update
      (analyzeLearnedSuccessiveUpdate update))
  rw [liftLearnedPostForgettingIncrementalChange_of_ok accepted]
  trivial

theorem learnedPostForgettingIncrementalChange_accepts
    {update : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis update) :
    LearnedPostForgettingIncrementalAccepted (.changeContract update) := by
  exact learnedPostForgettingIncrementalChange_accepts_of_analysis analysis

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
  exact ⟨by
    simpa only [analyzeLearnedPostForgettingCompletely] using accepted⟩

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
  exact ⟨by
    simpa only [analyzeLearnedPostForgettingCompletely] using accepted⟩

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
  exact ⟨by trivial⟩

theorem learnedPostForgettingAdmittedContinuation_full :
    LearnedPostForgettingFullRecheckAccepted
      learnedPostForgettingAdmittedContinuationRequest := by
  exact ⟨by trivial⟩

theorem learnedPostForgettingExtendedChange_incremental :
    LearnedPostForgettingIncrementalAccepted
      (.changeContract learnedExtendedSerializedUpdate) := by
  exact learnedPostForgettingIncrementalChange_accepts_of_analysis
    learnedReferenceSuccessiveAnalysis

theorem learnedPostForgettingExtendedChange_full :
    LearnedPostForgettingFullRecheckAccepted
      learnedPostForgettingExtendedChangeRequest := by
  exact learnedPostForgettingFullChange_accepts
    ⟨learnedSuccessiveFullRecheckLocalConditions⟩

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
  exact ⟨by
    simpa only [analyzeLearnedPostForgettingIncrementally] using accepted⟩

/-- The incremental post-forgetting checker is complete for every request in
its proof-free domain relative to its autonomous local receipts. -/
theorem learnedPostForgettingIncremental_complete
    (source : SerializedLearnedPostForgettingRequest) :
    LearnedPostForgettingIncrementalAccepted source ↔
      Nonempty (LearnedPostForgettingLocalConditionData source) := by
  constructor
  · intro accepted
    have accepted' := accepted.accepted
    unfold ExceptAccepted at accepted'
    cases exact : analyzeLearnedPostForgettingIncrementally source with
    | error problem =>
        rw [exact] at accepted'
        exact False.elim accepted'
    | ok conditions => exact ⟨conditions⟩
  · intro available
    rcases available with ⟨conditions⟩
    cases conditions with
    | continueCurrent input admitted =>
        exact learnedPostForgettingIncrementalContinuation_accepts admitted
    | changeContract update conditions =>
        exact learnedPostForgettingIncrementalChange_accepts conditions

/-- The independent full recheck has the corresponding all-request relative
completeness theorem and receives no incremental verdict. -/
theorem learnedPostForgettingFullRecheck_complete
    (source : SerializedLearnedPostForgettingRequest) :
    LearnedPostForgettingFullRecheckAccepted source ↔
      LearnedPostForgettingFullLocalConditions source := by
  constructor
  · intro accepted
    have acceptedValue := accepted.accepted
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
            analyzeLearnedPostForgettingCompletely] using acceptedValue
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
            analyzeLearnedPostForgettingCompletely] using acceptedValue
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
      refine ⟨?_⟩
      unfold submitLearnedPostForgettingContinuation
        checkLearnedPostForgettingIncremental ExceptAccepted at installed
      unfold ExceptAccepted
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
    have acceptedValue := accepted.accepted
    unfold ExceptAccepted at acceptedValue
    unfold submitLearnedPostForgettingContinuation
      checkLearnedPostForgettingIncremental ExceptAccepted
    cases analyzed : analyzeLearnedPostForgettingIncrementally
        (.continueCurrent input) with
    | error problem =>
        rw [analyzed] at acceptedValue
        exact False.elim acceptedValue
    | ok conditions =>
        exact True.intro

def learnedInstalledPostForgettingContinuation :
    InstalledLearnedPostForgettingContinuation learnedAdmittedFutureRequest :=
  { permission := learnedPostForgettingContinuationPermission
    execution := executePostForgettingContinuation
      learnedPostForgettingContinuationPermission }

theorem submitLearnedPostForgettingContinuation_exact :
    submitLearnedPostForgettingContinuation learnedAdmittedFutureRequest =
      .ok learnedInstalledPostForgettingContinuation := by
  rfl

theorem learnedInstalledPostForgettingContinuation_consumes_reducedMemory :
    learnedInstalledPostForgettingContinuation.execution.outcome =
      independentLearnedReducedFutureContract.outcome
        learnedAlignedExecutedFutureForgetting.output
        [learnedAdmittedFutureRequest] := by
  let expected : LearnedOperationalFutureOutcome :=
    independentLearnedReducedFutureContract.outcome
      learnedAlignedForgottenCurrentAgent.memory
      [learnedAdmittedFutureRequest]
  have executionExact :
      learnedInstalledPostForgettingContinuation.execution.outcome = expected :=
    learnedInstalledPostForgettingContinuation.execution.outcomeExact
  have memoryExact : expected =
      independentLearnedReducedFutureContract.outcome
        learnedAlignedExecutedFutureForgetting.output
        [learnedAdmittedFutureRequest] :=
    congrArg
      (fun memory => independentLearnedReducedFutureContract.outcome
        memory [learnedAdmittedFutureRequest])
      learnedAlignedForgottenMemory_is_executedReduction
  exact executionExact.trans memoryExact

theorem learnedInstalledPostForgettingContinuation_nextMemory_consumes_reducedMemory :
    learnedInstalledPostForgettingContinuation.execution.nextMemory =
      independentLearnedReducedFutureContract.next
        learnedAlignedExecutedFutureForgetting.output
        learnedAdmittedFutureRequest := by
  let expected : IndependentLearnedOperationalMemory :=
    independentLearnedReducedFutureContract.next
      learnedAlignedForgottenCurrentAgent.memory
      learnedAdmittedFutureRequest
  have executionExact :
      learnedInstalledPostForgettingContinuation.execution.nextMemory = expected :=
    learnedInstalledPostForgettingContinuation.execution.nextMemoryExact
  have memoryExact : expected =
      independentLearnedReducedFutureContract.next
        learnedAlignedExecutedFutureForgetting.output
        learnedAdmittedFutureRequest :=
    congrArg
      (fun memory => independentLearnedReducedFutureContract.next
        memory learnedAdmittedFutureRequest)
      learnedAlignedForgottenMemory_is_executedReduction
  exact executionExact.trans memoryExact

/-- Low-universe material receipt emitted from the installed continuation.
Its constructor is private: runtime updates can carry the executed reduced
memory result, but callers cannot fabricate such a receipt independently of
the continuation producer. -/
structure LearnedPostForgettingExecutionReceipt : Type 6 where
  private mk ::
  nextMemory : IndependentLearnedOperationalMemory
  outcome : LearnedOperationalFutureOutcome
  allowed : independentLearnedReducedFutureContract.Allow
    learnedAlignedForgottenCurrentAgent.memory learnedAdmittedFutureRequest
  nextMemoryExact : nextMemory =
    independentLearnedReducedFutureContract.next
      learnedAlignedForgottenCurrentAgent.memory learnedAdmittedFutureRequest
  outcomeExact : outcome = independentLearnedReducedFutureContract.outcome
    learnedAlignedForgottenCurrentAgent.memory [learnedAdmittedFutureRequest]

def executionReceiptOfInstalledPostForgettingContinuation
    (installed : InstalledLearnedPostForgettingContinuation
      learnedAdmittedFutureRequest) : LearnedPostForgettingExecutionReceipt :=
  { nextMemory := installed.execution.nextMemory
    outcome := installed.execution.outcome
    allowed := by
      cases installed.permission with
      | continueCurrent _ allowed => exact allowed
    nextMemoryExact := installed.execution.nextMemoryExact
    outcomeExact := installed.execution.outcomeExact }

/-- The canonical receipt is projected from the result of the continuation that
was actually submitted and installed.  It does not independently recompute a
canonical future from the forgetting input. -/
def learnedPostForgettingExecutionReceipt :
    LearnedPostForgettingExecutionReceipt :=
  executionReceiptOfInstalledPostForgettingContinuation
    learnedInstalledPostForgettingContinuation

theorem learnedPostForgettingExecutionReceipt_outcome_is_installed :
    learnedPostForgettingExecutionReceipt.outcome =
      learnedInstalledPostForgettingContinuation.execution.outcome := by
  rfl

theorem learnedPostForgettingExecutionReceipt_nextMemory_is_installed :
    learnedPostForgettingExecutionReceipt.nextMemory =
      learnedInstalledPostForgettingContinuation.execution.nextMemory := by
  rfl

theorem learnedPostForgettingExecutionReceipt_outcome_consumes_forgettingOutput :
    learnedPostForgettingExecutionReceipt.outcome =
      independentLearnedReducedFutureContract.outcome
        learnedAlignedExecutedFutureForgetting.output
        [learnedAdmittedFutureRequest] :=
  learnedPostForgettingExecutionReceipt_outcome_is_installed.trans
    learnedInstalledPostForgettingContinuation_consumes_reducedMemory

theorem learnedPostForgettingExecutionReceipt_nextMemory_consumes_forgettingOutput :
    learnedPostForgettingExecutionReceipt.nextMemory =
      independentLearnedReducedFutureContract.next
        learnedAlignedExecutedFutureForgetting.output
        learnedAdmittedFutureRequest :=
  learnedPostForgettingExecutionReceipt_nextMemory_is_installed.trans
    learnedInstalledPostForgettingContinuation_nextMemory_consumes_reducedMemory

/-- The contract-changing proposal is read from the result emitted by the
executed reduced-memory continuation.  The transition applies its nonidentity
Boolean complement to the decoded prior proposal.  The read is accepted only
when that result is admitted and its event agrees with the memory actually
produced by the same continuation.  Both `outcome` and `nextMemory` are
therefore material inputs to the subsequent action. -/
def LearnedPostForgettingExecutionReceipt.producedProposal
    (receipt : LearnedPostForgettingExecutionReceipt) : Bool :=
  match receipt.outcome with
  | .stop _ => false
  | .step _ allowed event _ =>
      if allowed then
        if event.outputs = receipt.nextMemory.execute
            learnedAdmittedFutureRequest.input then
          !decodeIndependentLearnedProposal event.outputs
        else false
      else false

theorem LearnedPostForgettingExecutionReceipt.producedProposal_exact
    (receipt : LearnedPostForgettingExecutionReceipt) :
    receipt.producedProposal =
      learnedExtendedState.system.proposal learnedExtendedState.input := by
  rw [LearnedPostForgettingExecutionReceipt.producedProposal,
    receipt.outcomeExact, receipt.nextMemoryExact]
  simp only [FutureContract.outcome]
  rw [FutureContract.enabled_of_admitted _ _ _ receipt.allowed]
  rw [if_pos rfl]
  change (if learnedAlignedForgottenCurrentAgent.memory.execute
        learnedAdmittedFutureRequest.input =
      learnedAlignedForgottenCurrentAgent.memory.execute
        learnedAdmittedFutureRequest.input then
        !decodeIndependentLearnedProposal
          (learnedAlignedForgottenCurrentAgent.memory.execute
            learnedAdmittedFutureRequest.input)
      else false) = _
  rw [if_pos rfl]
  rw [learnedAlignedForgottenMemory_is_executedReduction,
    show learnedAdmittedFutureRequest.input =
        independentLearnedCounterfactualInput by rfl,
    learnedAlignedExecutedFutureForgetting_admitted_output_exact]
  have targetProposalExact :
      learnedExtendedState.system.proposal learnedExtendedState.input = true :=
    learnedExtendedProposalPreservation.proposalExact.trans (by rfl)
  rw [targetProposalExact]
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
agent produced by the first installed transition.  The update carries the
private material receipt emitted from the ordinary continuation installed over
the reduced memory, so the contract-changing checker cannot reconstruct that
predecessor after the fact. -/
inductive LearnedPostForgettingRuntimeUpdate :
    {contract : LearnedOperationalContract} ->
      CheckedAgent learnedConstitutiveMetaContract contract -> Type 6 where
  | changeContract
      (receipt : LearnedPostForgettingExecutionReceipt)
      (update : LearnedSerializedConstitutiveUpdate) :
      LearnedPostForgettingRuntimeUpdate LearnedAlignedCurrentAgent

/-- Material produced by the exact post-forgetting lineage.  Formation consumes
the installed ordinary continuation over the reduced memory occurrence, then
uses the same justified contract transition to transport the persistent intent
and recheck the invalidated authorization. -/
structure LearnedPostForgettingContractResources
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended) : Type 9 where
  private mk ::
  receipt : LearnedPostForgettingExecutionReceipt
  preservedContinuation : independentLearnedReducedFutureContract.Allow
    justification.reducedMemory learnedAdmittedFutureRequest
  reducedOutcomeExact : receipt.outcome =
    independentLearnedReducedFutureContract.outcome
      justification.reducedMemory [learnedAdmittedFutureRequest]
  transportedIntent : learnedConstitutiveMetaContract.TargetPersistentWitness
    .aligned .extended .admittedIntent
  transportedIntentExact : transportedIntent =
    justification.transportedPersistent .admittedIntent
  recheckedAuthorization : learnedConstitutiveMetaContract.RecheckedWitness
    .aligned .extended .authorizationConsumption
  recheckedAuthorizationExact : recheckedAuthorization =
    justification.rechecked .authorizationConsumption

/-- Execute the resource phase from the exact reduced-memory continuation and
the exact justified transition.  No target certificate is accepted here. -/
def executeLearnedPostForgettingContractResources
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended)
    (receipt : LearnedPostForgettingExecutionReceipt) :
    LearnedPostForgettingContractResources analysis justification :=
  { receipt := receipt
    preservedContinuation := by
      rw [justification.reducedMemoryExact]
      exact receipt.allowed
    reducedOutcomeExact := receipt.outcomeExact.trans
      (congrArg
        (fun memory => independentLearnedReducedFutureContract.outcome
          memory [learnedAdmittedFutureRequest])
        justification.reducedMemoryExact).symm
    transportedIntent :=
      justification.transportedPersistent .admittedIntent
    transportedIntentExact := rfl
    recheckedAuthorization :=
      justification.rechecked .authorizationConsumption
    recheckedAuthorizationExact := rfl }

theorem LearnedPostForgettingContractResources.reducedMemory_is_executed
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (_resources : LearnedPostForgettingContractResources analysis justification) :
    justification.reducedMemory =
      learnedAlignedExecutedFutureForgetting.output :=
  justification.reducedMemoryExact.trans
    learnedAlignedForgottenMemory_is_executedReduction

def LearnedPostForgettingContractResources.baseFragments
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (_resources : LearnedPostForgettingContractResources analysis justification) :
    RecomputedStateCertificateFragments LearnedExtendedOperationalContract
      analysis.executed.decoded.target
      analysis.executed.production.targetState :=
  learnedExtendedRecomputedCertificateFragmentsFromReceived
    analysis.executed.decoded.target analysis.executed.production.targetState
    (analysis.executed.decoded.targetArtifactExact
      analysis.executed.targetNetworkExact)
    analysis.executed.production_target_exact

def LearnedPostForgettingContractResources.authorizationAtTarget
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    LearnedAuthorizationWitness analysis.executed.production.targetState := by
  rw [analysis.executed.production_target_exact]
  exact resources.recheckedAuthorization

theorem learnedAlignedExtendedOperationalTransition_unique
    (transition : OperationalContractTransition learnedConstitutiveMetaContract
      .aligned .extended) :
    transition = learnedExtendedOperationalTransition := by
  cases transition
  next sourceAdmission targetAdmission permission =>
    cases sourceAdmission
    cases targetAdmission
    cases permission
    rfl

def learnedExtendedAuthorizationWitnessFromReceived
    (state : ReconfiguredExecutionState
      LearnedExtendedOperationalContract.family)
    (stateExact : state = learnedExtendedState) :
    LearnedAuthorizationWitness state := by
  subst state
  exact learnedExtendedAuthorizationWitness

theorem learnedExtendedReceivedCausalAuthorizationPort_exact
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (state : ReconfiguredExecutionState
      LearnedExtendedOperationalContract.family)
    (targetExact : target = learnedDecodedExtendedArtifact)
    (stateExact : state = learnedExtendedState) :
    (learnedExtendedRecomputedCertificateFragmentsFromReceived target state
      targetExact stateExact).causal.witness.authorizationPort =
      (learnedExtendedAuthorizationWitnessFromReceived state
        stateExact).authorizationPort := by
  subst target
  subst state
  rfl

def LearnedPostForgettingContractResources.preservationAtTarget
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    LearnedProposalPreservation analysis.executed.production.targetState :=
  { admittedIntent := resources.transportedIntent.down
    proposalExact :=
      resources.baseFragments.proposalAction.witness.preservation.proposalExact }

theorem LearnedPostForgettingContractResources.authorizationPortExact
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    resources.baseFragments.causal.witness.authorizationPort =
      resources.authorizationAtTarget.authorizationPort := by
  have transitionExact := learnedAlignedExtendedOperationalTransition_unique
    justification.transition
  have authorizationExact : resources.recheckedAuthorization =
      learnedExtendedAuthorizationWitness := by
    rw [resources.recheckedAuthorizationExact]
    unfold JustifiedPostForgettingTransition.rechecked
      OperationalContractTransition.recheck
    rw [transitionExact]
    rfl
  have authorizationAtTargetExact : resources.authorizationAtTarget =
      learnedExtendedAuthorizationWitnessFromReceived
        analysis.executed.production.targetState
        analysis.executed.production_target_exact := by
    unfold LearnedPostForgettingContractResources.authorizationAtTarget
      learnedExtendedAuthorizationWitnessFromReceived
    cases analysis.executed.production_target_exact
    exact authorizationExact
  exact (learnedExtendedReceivedCausalAuthorizationPort_exact
    analysis.executed.decoded.target analysis.executed.production.targetState
    (analysis.executed.decoded.targetArtifactExact
      analysis.executed.targetNetworkExact)
    analysis.executed.production_target_exact).trans
      (congrArg LearnedAuthorizationWitness.authorizationPort
        authorizationAtTargetExact).symm

/-- The action certified after forgetting is reconstructed from the transported
intent, the rechecked authorization, and the proposal decoded from the actual
post-forgetting continuation receipt.  These values are inputs to the sealed
action constructor, not fields stored beside a pre-existing action. -/
def LearnedPostForgettingContractResources.action
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    LearnedActionWitness analysis.executed.production.targetState :=
  executeLearnedActionFromProducedProposal
    analysis.executed.production.targetState
    resources.receipt.producedProposal
    (resources.receipt.producedProposal_exact.trans
      (congrArg
        (fun state : ReconfiguredExecutionState
          independentLearnedRequirementFamily =>
            state.system.proposal state.input)
        analysis.executed.production_target_exact).symm)
    resources.preservationAtTarget
    resources.baseFragments.causal.witness
    resources.authorizationAtTarget resources.authorizationPortExact

/-- One material action/effect occurrence produced from the transported intent
and rechecked authorization.  The effect is indexed by that exact action, so
the installed fragments cannot replace it with an equal reconstruction. -/
def LearnedPostForgettingContractResources.actionEffect
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    LearnedEffectSatisfaction analysis.executed.production.targetState :=
  { action := resources.action
    effect := produceLearnedEffect resources.action }

def LearnedPostForgettingContractResources.effect
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    LearnedEffectWitness analysis.executed.production.targetState
      resources.actionEffect.action :=
  resources.actionEffect.effect

/-- Recomputed semantic fragments for the installed successor.  The action,
authorization, and effect fragments are produced from the post-forgetting
resources above; the remaining exact target fragments are retained from the
received analysis. -/
def LearnedPostForgettingContractResources.recomputedFragments
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    RecomputedStateCertificateFragments LearnedExtendedOperationalContract
      analysis.executed.decoded.target
      analysis.executed.production.targetState :=
  { requirement :=
      resources.baseFragments.requirement
    causal := resources.baseFragments.causal
    proposalAction := { witness := resources.actionEffect.action }
    authorization := { witness := resources.authorizationAtTarget }
    effect := { witness := resources.actionEffect }
    historical := resources.baseFragments.historical
    futures := resources.baseFragments.futures }

/-- The target analysis installed after forgetting is rebuilt with the
resource-derived fragments.  In particular, it is not the original analysis
with two independent justification fields attached afterwards. -/
def LearnedPostForgettingContractResources.targetAnalysis
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    IncrementalTargetAnalysis LearnedAlignedCurrentAgent :=
  { nextContract := .extended
    contractAdmitted := .extended
    artifact := analysis.executed.decoded.target
    state := analysis.executed.production.targetState
    targetNaming := analysis.executed.decoded.stable.naming
    preCertificateGraph := analysis.executed.preCertificateGraph
    transportedLicenses := analysis.executed.transportedLicenses
    recomputedStructural := analysis.executed.recomputedStructural
    structuralAssembly := analysis.structuralAssembly
    structuralBasis := learnedExtendedFiniteCausalBasisFromReceived
      analysis.executed.decoded.target analysis.executed.decoded.stable.naming
      (analysis.executed.decoded.targetArtifactExact
        analysis.executed.targetNetworkExact)
    structuralBasisNamingExact :=
      learnedExtendedFiniteCausalBasisFromReceived_naming_exact
        analysis.executed.decoded.target
        analysis.executed.decoded.stable.naming
        (analysis.executed.decoded.targetArtifactExact
          analysis.executed.targetNetworkExact)
    structuralSystemExact := learnedExtendedReceivedState_system_exact
      analysis.executed.decoded.target
      analysis.executed.production.targetState
      (analysis.executed.decoded.targetArtifactExact
        analysis.executed.targetNetworkExact)
      analysis.executed.production_target_exact
    structuralInputDeclared := learnedExtendedReceivedState_input_declared
      analysis.executed.production.targetState
      analysis.executed.production_target_exact
    recomputedCertificateFragments := resources.recomputedFragments
    transition := analysis.executed.extendedDecision.transition
    execution := analysis.executed.production.execution }

/-- Closed post-forgetting installation material.  The checked update is built
only from the target analysis whose semantic fragments consume the executed
post-forgetting resources. -/
structure ClosedLearnedPostForgettingContractChange
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended) : Type 10 where
  private mk ::
  resources : LearnedPostForgettingContractResources analysis justification
  checked : CheckedUpdate LearnedAlignedCurrentAgent .extended
  checkedExact : checked = buildIncrementalCheckedUpdate resources.targetAnalysis

def ClosedLearnedPostForgettingContractChange.transportedIntent
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (closed : ClosedLearnedPostForgettingContractChange analysis justification) :
    learnedConstitutiveMetaContract.TargetPersistentWitness
      .aligned .extended .admittedIntent :=
  closed.resources.transportedIntent

def ClosedLearnedPostForgettingContractChange.recheckedAuthorization
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (closed : ClosedLearnedPostForgettingContractChange analysis justification) :
    learnedConstitutiveMetaContract.RecheckedWitness
      .aligned .extended .authorizationConsumption :=
  closed.resources.recheckedAuthorization

def closeLearnedPostForgettingContractChange
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (receipt : LearnedPostForgettingExecutionReceipt)
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended) :
    ClosedLearnedPostForgettingContractChange analysis justification :=
  let resources := executeLearnedPostForgettingContractResources analysis
    justification receipt
  { resources := resources
    checked := buildIncrementalCheckedUpdate resources.targetAnalysis
    checkedExact := rfl }

/-- The post-forgetting justification is constructed from the same received
successive analysis that supplies the decoded intent and transition decision.
No canonical target analysis is substituted at this boundary. -/
def learnedPostForgettingJustificationFromAnalysis
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent
      (forgotten := learnedAlignedForgottenCurrentAgent) .extended :=
  learnedPostForgettingJustificationFromDecision
    analysis.executed.decoded.intentAdmitted
    (analysis.executed.receivedDecision.transportRequest
      analysis.executed.decoded.transitionExact)

/-- Close the contract-changing transition by consuming one and the same
received analysis for the justification, checked successor, and installation
material. -/
def closeLearnedPostForgettingContractChangeFromAnalysis
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (receipt : LearnedPostForgettingExecutionReceipt) :
    ClosedLearnedPostForgettingContractChange analysis
      (learnedPostForgettingJustificationFromAnalysis analysis) :=
  closeLearnedPostForgettingContractChange analysis receipt
    (learnedPostForgettingJustificationFromAnalysis analysis)

/-- The concrete P5 transition material is reconstructed from the exact
analysis returned for the received aligned-to-extended update. -/
def learnedPostForgettingExtendedJustification :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent
      (forgotten := learnedAlignedForgottenCurrentAgent) .extended :=
  learnedPostForgettingJustificationFromAnalysis
    learnedReferenceSuccessiveAnalysis

def learnedClosedPostForgettingExtendedChange :
    ClosedLearnedPostForgettingContractChange
      learnedReferenceSuccessiveAnalysis
      learnedPostForgettingExtendedJustification :=
  closeLearnedPostForgettingContractChangeFromAnalysis
    learnedReferenceSuccessiveAnalysis
    learnedPostForgettingExecutionReceipt

theorem LearnedPostForgettingContractResources.target_consumes_transportedIntent
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    LearnedProposalPreservation.admittedIntent
      (LearnedActionWitness.preservation
        (ProposalActionCertificateFragment.witness
          resources.targetAnalysis.recomputedCertificateFragments.proposalAction)) =
      resources.transportedIntent.down := by
  rfl

theorem LearnedPostForgettingContractResources.target_consumes_recheckedAuthorization
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    resources.targetAnalysis.recomputedCertificateFragments.authorization.witness =
      resources.authorizationAtTarget := by
  rfl

theorem LearnedPostForgettingContractResources.target_shares_action_with_effect
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    resources.targetAnalysis.recomputedCertificateFragments.effect.witness.action =
      resources.targetAnalysis.recomputedCertificateFragments.proposalAction.witness := by
  rfl

theorem LearnedPostForgettingContractResources.target_action_consumes_receipt
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    resources.targetAnalysis.recomputedCertificateFragments.proposalAction.witness.request =
      publicAgentActionChannel.command resources.receipt.producedProposal := by
  rfl

theorem LearnedPostForgettingContractResources.resourcePhase_consumes_reducedMemory
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    {justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent
        (forgotten := learnedAlignedForgottenCurrentAgent)
        .extended}
    (resources : LearnedPostForgettingContractResources analysis justification) :
    resources.receipt.outcome =
      independentLearnedReducedFutureContract.outcome
        justification.reducedMemory [learnedAdmittedFutureRequest] := by
  exact resources.reducedOutcomeExact

theorem learnedClosedPostForgettingTargetAnalysis_exact :
    learnedClosedPostForgettingExtendedChange.resources.targetAnalysis =
      learnedReferenceSuccessiveAnalysis.target := by
  have actionExact :
      learnedClosedPostForgettingExtendedChange.resources.action =
        executeLearnedAction
          learnedReferenceSuccessiveAnalysis.executed.production.targetState
          learnedClosedPostForgettingExtendedChange.resources.preservationAtTarget
          learnedClosedPostForgettingExtendedChange.resources.baseFragments.causal.witness
          learnedClosedPostForgettingExtendedChange.resources.authorizationAtTarget
          learnedClosedPostForgettingExtendedChange.resources.authorizationPortExact :=
    executeLearnedActionFromProducedProposal_eq_executeLearnedAction _ _ _ _ _ _ _
  unfold LearnedPostForgettingContractResources.targetAnalysis
    LearnedPostForgettingContractResources.recomputedFragments
    LearnedPostForgettingContractResources.actionEffect
  rw [actionExact]
  unfold learnedClosedPostForgettingExtendedChange
    closeLearnedPostForgettingContractChangeFromAnalysis
    closeLearnedPostForgettingContractChange
  rfl

/-- Build the checked successor in the fixed extended-contract fibre.  The
subtype used below lets equality of complete analyses be consumed without
silently transporting between unrelated dependent checker outputs. -/
def buildLearnedExtendedCheckedUpdate
    (analysis : IncrementalTargetAnalysis LearnedAlignedCurrentAgent)
    (contractExact : analysis.nextContract = .extended) :
    CheckedUpdate LearnedAlignedCurrentAgent .extended :=
  Eq.mp (congrArg (CheckedUpdate LearnedAlignedCurrentAgent) contractExact)
    (buildIncrementalCheckedUpdate analysis)

theorem learnedClosedPostForgettingFullRecheck_successor_exact :
    HEq learnedClosedPostForgettingExtendedChange.checked.next
      learnedSuccessiveFullRecheckSuccess.checked.next := by
  have analysisExact :
      (⟨learnedClosedPostForgettingExtendedChange.resources.targetAnalysis,
          rfl⟩ : { analysis : IncrementalTargetAnalysis
            LearnedAlignedCurrentAgent // analysis.nextContract = .extended }) =
        ⟨learnedReferenceSuccessiveAnalysis.target, rfl⟩ :=
    Subtype.ext learnedClosedPostForgettingTargetAnalysis_exact
  have rebuiltExact := congrArg
    (fun item : { analysis : IncrementalTargetAnalysis
        LearnedAlignedCurrentAgent // analysis.nextContract = .extended } =>
      buildLearnedExtendedCheckedUpdate item.1 item.2)
    analysisExact
  have closedExact : learnedClosedPostForgettingExtendedChange.checked =
      buildLearnedExtendedCheckedUpdate
        learnedClosedPostForgettingExtendedChange.resources.targetAnalysis rfl :=
    learnedClosedPostForgettingExtendedChange.checkedExact
  have referenceExact : buildLearnedExtendedCheckedUpdate
        learnedReferenceSuccessiveAnalysis.target rfl =
      learnedSuccessiveIncrementalSuccess.checked := by
    rfl
  have incrementalExact : learnedClosedPostForgettingExtendedChange.checked =
      learnedSuccessiveIncrementalSuccess.checked :=
    closedExact.trans (rebuiltExact.trans referenceExact)
  exact heq_of_eq ((congrArg CheckedUpdate.next incrementalExact).trans
    learnedSuccessiveIncrementalAndFullSuccessor_exact)

/-- Extract the exact justified change carried by the autonomous
post-forgetting permission.  The reduction index cannot be replaced here:
`permission` is formed for `learnedAlignedForgottenCurrentAgent`. -/
def learnedPostForgettingJustificationFromLocalConditions
    {source : LearnedSerializedConstitutiveUpdate}
    (conditions : LearnedPostForgettingLocalConditionData
      (.changeContract source)) :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent
      (forgotten := learnedAlignedForgottenCurrentAgent) .extended :=
  match conditions.permission with
  | .changeContract _ justification => justification

/-- Translate the received successive-analysis result into the exact checked
post-forgetting successor.  The accepted branch consumes the local conditions
returned by the autonomous post-forgetting checker, including the permission
indexed by the exact reduced-memory occurrence.  It has no argument for a
canonical replacement or a prefabricated target certificate. -/
def closeReceivedLearnedPostForgettingAnalysis
    (receipt : LearnedPostForgettingExecutionReceipt)
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedPostForgettingCheckError
        (LearnedPostForgettingLocalConditionData (.changeContract source)) →
      Except LearnedPostForgettingCheckError
        (DependentCheckedUpdateResult LearnedAlignedCurrentAgent)
  | .error problem => .error problem
  | .ok conditions =>
      match conditions with
      | .changeContract _ analysis =>
          .ok (dependentCheckedUpdateResult
            (closeLearnedPostForgettingContractChange analysis receipt
              (learnedPostForgettingJustificationFromLocalConditions
                conditions)).checked)

def checkLearnedPostForgettingRuntimeUpdate
    {contract : LearnedOperationalContract}
    {current : CheckedAgent learnedConstitutiveMetaContract contract}
    (update : LearnedPostForgettingRuntimeUpdate current) :
    Except LearnedPostForgettingCheckError
      (DependentCheckedUpdateResult current) :=
  match update with
  | .changeContract receipt source =>
      closeReceivedLearnedPostForgettingAnalysis receipt source
        (analyzeLearnedPostForgettingIncrementally (.changeContract source))

def learnedPostForgettingDependentChecker :
    DependentIncrementalChecker learnedConstitutiveMetaContract where
  Error := LearnedPostForgettingCheckError
  Update := LearnedPostForgettingRuntimeUpdate
  check := by
    intro contract current update
    exact checkLearnedPostForgettingRuntimeUpdate update

/-- If the successive analyzer returned a particular received analysis, the
runtime checker consumes precisely that analysis to construct its checked
successor.  This is the generic raccord used by the concrete public update;
it avoids proving equality with, or rebuilding, a canonical analysis. -/
theorem checkLearnedPostForgettingRuntimeUpdate_change_of_analysis
    {source : LearnedSerializedConstitutiveUpdate}
    {analysis : LearnedSuccessiveEngineAnalysis source}
    (receipt : LearnedPostForgettingExecutionReceipt)
    (accepted : analyzeLearnedSuccessiveUpdate source = .ok analysis) :
    checkLearnedPostForgettingRuntimeUpdate
        (LearnedPostForgettingRuntimeUpdate.changeContract receipt source) =
      .ok (dependentCheckedUpdateResult
        (closeLearnedPostForgettingContractChangeFromAnalysis
          analysis receipt).checked) := by
  have postForgettingAccepted :
      analyzeLearnedPostForgettingIncrementally (.changeContract source) =
        .ok (.changeContract source analysis) := by
    unfold analyzeLearnedPostForgettingIncrementally
    exact liftLearnedPostForgettingIncrementalChange_of_ok accepted
  rw [checkLearnedPostForgettingRuntimeUpdate, postForgettingAccepted]
  rfl

theorem learnedPostForgettingDependentChecker_change_exact
    (receipt : LearnedPostForgettingExecutionReceipt)
    (source : LearnedSerializedConstitutiveUpdate) :
    learnedPostForgettingDependentChecker.check LearnedAlignedCurrentAgent
        (LearnedPostForgettingRuntimeUpdate.changeContract receipt source) =
      checkLearnedPostForgettingRuntimeUpdate
        (LearnedPostForgettingRuntimeUpdate.changeContract receipt source) := by
  rfl

def learnedPostForgettingInitialRuntime : CertifiedRuntime
    learnedPostForgettingDependentChecker LearnedAlignedCurrentAgent :=
  initialCertifiedRuntime learnedPostForgettingDependentChecker
    LearnedAlignedCurrentAgent

def learnedPostForgettingExtendedRuntimeUpdate :
    learnedPostForgettingDependentChecker.Update
      learnedPostForgettingInitialRuntime.current :=
  .changeContract learnedPostForgettingExecutionReceipt
    learnedExtendedSerializedUpdate

theorem checkLearnedPostForgettingExtendedRuntimeUpdate_exact :
    checkLearnedPostForgettingRuntimeUpdate
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok (dependentCheckedUpdateResult
        learnedClosedPostForgettingExtendedChange.checked) := by
  dsimp only [learnedPostForgettingExtendedRuntimeUpdate]
  exact checkLearnedPostForgettingRuntimeUpdate_change_of_analysis
    learnedPostForgettingExecutionReceipt
    analyzeLearnedSuccessiveUpdate_reference_exact

theorem learnedPostForgettingDependentChecker_accepts_extended :
    learnedPostForgettingDependentChecker.check LearnedAlignedCurrentAgent
        (LearnedPostForgettingRuntimeUpdate.changeContract
          learnedPostForgettingExecutionReceipt
          learnedExtendedSerializedUpdate) =
      .ok (dependentCheckedUpdateResult
        learnedClosedPostForgettingExtendedChange.checked) :=
  (learnedPostForgettingDependentChecker_change_exact _ _).trans
    checkLearnedPostForgettingExtendedRuntimeUpdate_exact

opaque learnedPostForgettingExtendedRuntimeSubmission :
    AcceptedRuntimeSubmission learnedPostForgettingInitialRuntime
    learnedPostForgettingExtendedRuntimeUpdate
    (dependentCheckedUpdateResult
      learnedClosedPostForgettingExtendedChange.checked)
    learnedPostForgettingDependentChecker_accepts_extended :=
  acceptedRuntimeSubmissionOfCheck learnedPostForgettingInitialRuntime
    learnedPostForgettingExtendedRuntimeUpdate
    (dependentCheckedUpdateResult
      learnedClosedPostForgettingExtendedChange.checked)
    learnedPostForgettingDependentChecker_accepts_extended

def learnedPostForgettingExtendedRuntime : CertifiedRuntime
    learnedPostForgettingDependentChecker LearnedAlignedCurrentAgent :=
  learnedPostForgettingExtendedRuntimeSubmission.next

theorem learnedPostForgettingRuntime_current_heq_of_eq
    {source target : CertifiedRuntime learnedPostForgettingDependentChecker
      LearnedAlignedCurrentAgent}
    (runtimeExact : source = target) : HEq source.current target.current := by
  cases runtimeExact
  rfl

theorem learnedPostForgettingExtendedRuntime_eq_installed :
    learnedPostForgettingExtendedRuntime =
      installAcceptedUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate
        (dependentCheckedUpdateResult
          learnedClosedPostForgettingExtendedChange.checked)
        learnedPostForgettingDependentChecker_accepts_extended :=
  learnedPostForgettingExtendedRuntimeSubmission.nextExact

def learnedPostForgettingInitialRuntime_reachable :
    CertifiedRuntimeReachable learnedPostForgettingDependentChecker
      LearnedAlignedCurrentAgent learnedPostForgettingInitialRuntime :=
  .initial

theorem submitUpdate_postForgettingExtended_exact :
    submitUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok learnedPostForgettingExtendedRuntime := by
  exact learnedPostForgettingExtendedRuntimeSubmission.submitted

def learnedPostForgettingExtendedRuntime_reachable :
    CertifiedRuntimeReachable learnedPostForgettingDependentChecker
      LearnedAlignedCurrentAgent learnedPostForgettingExtendedRuntime :=
  .submitted learnedPostForgettingInitialRuntime
    learnedPostForgettingExtendedRuntime
    learnedPostForgettingExtendedRuntimeUpdate
    learnedPostForgettingInitialRuntime_reachable
    submitUpdate_postForgettingExtended_exact

theorem learnedPostForgettingRuntime_starts_at_installedAlignedState :
    HEq learnedPostForgettingInitialRuntime.current
      learnedAlignedCertifiedRuntime.current :=
  (by rfl : HEq learnedPostForgettingInitialRuntime.current
    LearnedAlignedCurrentAgent).trans
      learnedAlignedCertifiedRuntime_current_exact.symm

theorem learnedPostForgettingExtendedRuntime_successor_exact :
    HEq learnedPostForgettingExtendedRuntime.current
      learnedExtendedCertifiedRuntime.current :=
  (learnedPostForgettingRuntime_current_heq_of_eq
      learnedPostForgettingExtendedRuntime_eq_installed).trans
    ((by rfl : HEq
      (installAcceptedUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate
        (dependentCheckedUpdateResult
          learnedClosedPostForgettingExtendedChange.checked)
        learnedPostForgettingDependentChecker_accepts_extended).current
      learnedClosedPostForgettingExtendedChange.checked.next).trans
      (learnedClosedPostForgettingFullRecheck_successor_exact.trans
        learnedExtendedCertifiedRuntime_current_exact.symm))

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
          learnedPostForgettingExecutionReceipt
          learnedAlignedSerializedUpdate) = .ok next) := by
  apply submitUpdate_rejected_cannot_install learnedPostForgettingInitialRuntime
    (LearnedPostForgettingRuntimeUpdate.changeContract
      learnedPostForgettingExecutionReceipt learnedAlignedSerializedUpdate)
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
  continuationNextMemoryConsumesReducedMemory : continuation.execution.nextMemory =
    independentLearnedReducedFutureContract.next
      learnedAlignedExecutedFutureForgetting.output
      learnedAdmittedFutureRequest
  receipt : LearnedPostForgettingExecutionReceipt
  receiptExact : receipt = learnedPostForgettingExecutionReceipt
  receiptOutcomeIsContinuationOutput : receipt.outcome = continuation.execution.outcome
  receiptNextMemoryIsContinuationOutput : receipt.nextMemory = continuation.execution.nextMemory
  runtimeSource : CertifiedRuntime learnedPostForgettingDependentChecker
    LearnedAlignedCurrentAgent
  runtimeSourceExact : runtimeSource = learnedPostForgettingInitialRuntime
  closedContractChange : ClosedLearnedPostForgettingContractChange
    learnedSuccessiveIncrementalSuccess.analysis
    learnedPostForgettingExtendedJustification
  closedContractChangeExact : closedContractChange =
    learnedClosedPostForgettingExtendedChange
  closedResourcesConsumeReceipt : closedContractChange.resources.receipt = receipt
  transportedIntentConsumed : closedContractChange.transportedIntent =
    learnedPostForgettingExtendedJustification.transportedPersistent
      .admittedIntent
  authorizationRechecked : closedContractChange.recheckedAuthorization =
    learnedPostForgettingExtendedJustification.rechecked
      .authorizationConsumption
  reducedMemoryProduced :
    learnedPostForgettingExtendedJustification.reducedMemory =
      learnedAlignedExecutedFutureForgetting.output
  reducedContinuationPreserved :
    independentLearnedReducedFutureContract.Allow
      learnedPostForgettingExtendedJustification.reducedMemory
      learnedAdmittedFutureRequest
  targetConsumesTransportedIntent :
    LearnedProposalPreservation.admittedIntent
      (LearnedActionWitness.preservation
        (ProposalActionCertificateFragment.witness
          closedContractChange.resources.targetAnalysis.recomputedCertificateFragments.proposalAction)) =
      closedContractChange.resources.transportedIntent.down
  targetConsumesRecheckedAuthorization :
    closedContractChange.resources.targetAnalysis.recomputedCertificateFragments.authorization.witness =
      closedContractChange.resources.authorizationAtTarget
  targetSharesActionWithEffect :
    closedContractChange.resources.targetAnalysis.recomputedCertificateFragments.effect.witness.action =
      closedContractChange.resources.targetAnalysis.recomputedCertificateFragments.proposalAction.witness
  targetActionConsumesReceipt :
    closedContractChange.resources.targetAnalysis.recomputedCertificateFragments.proposalAction.witness.request =
      publicAgentActionChannel.command closedContractChange.resources.receipt.producedProposal
  resourcePhaseConsumesReducedMemory :
    closedContractChange.resources.receipt.outcome =
      independentLearnedReducedFutureContract.outcome
        learnedPostForgettingExtendedJustification.reducedMemory
        [learnedAdmittedFutureRequest]
  checkedUpdateProduced : closedContractChange.checked =
    buildIncrementalCheckedUpdate
      closedContractChange.resources.targetAnalysis
  fullRecheckSuccessorExact : HEq closedContractChange.checked.next
    learnedSuccessiveFullRecheckSuccess.checked.next
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
        learnedPostForgettingExecutionReceipt
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
    continuationNextMemoryConsumesReducedMemory :=
      learnedInstalledPostForgettingContinuation_nextMemory_consumes_reducedMemory
    receipt := learnedPostForgettingExecutionReceipt
    receiptExact := rfl
    receiptOutcomeIsContinuationOutput :=
      learnedPostForgettingExecutionReceipt_outcome_is_installed
    receiptNextMemoryIsContinuationOutput :=
      learnedPostForgettingExecutionReceipt_nextMemory_is_installed
    runtimeSource := learnedPostForgettingInitialRuntime
    runtimeSourceExact := rfl
    closedContractChange := learnedClosedPostForgettingExtendedChange
    closedContractChangeExact := rfl
    closedResourcesConsumeReceipt := rfl
    transportedIntentConsumed := rfl
    authorizationRechecked := rfl
    reducedMemoryProduced :=
      LearnedPostForgettingContractResources.reducedMemory_is_executed
        learnedClosedPostForgettingExtendedChange.resources
    reducedContinuationPreserved :=
      LearnedPostForgettingContractResources.preservedContinuation
        learnedClosedPostForgettingExtendedChange.resources
    targetConsumesTransportedIntent :=
      LearnedPostForgettingContractResources.target_consumes_transportedIntent
        learnedClosedPostForgettingExtendedChange.resources
    targetConsumesRecheckedAuthorization :=
      LearnedPostForgettingContractResources.target_consumes_recheckedAuthorization
        learnedClosedPostForgettingExtendedChange.resources
    targetSharesActionWithEffect :=
      LearnedPostForgettingContractResources.target_shares_action_with_effect
        learnedClosedPostForgettingExtendedChange.resources
    targetActionConsumesReceipt :=
      LearnedPostForgettingContractResources.target_action_consumes_receipt
        learnedClosedPostForgettingExtendedChange.resources
    resourcePhaseConsumesReducedMemory :=
      LearnedPostForgettingContractResources.resourcePhase_consumes_reducedMemory
        learnedClosedPostForgettingExtendedChange.resources
    checkedUpdateProduced := rfl
    fullRecheckSuccessorExact :=
      learnedClosedPostForgettingFullRecheck_successor_exact
    runtimeCheckConsumesClosure :=
      checkLearnedPostForgettingExtendedRuntimeUpdate_exact
    contractUpdate := learnedPostForgettingExtendedRuntimeUpdate
    contractUpdateExact := HEq.rfl
    installedRuntime := learnedPostForgettingExtendedRuntime
    installedExact := submitUpdate_postForgettingExtended_exact
    installedSuccessorExact :=
      learnedPostForgettingExtendedRuntime_successor_exact
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
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalReceipt
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalSuccess
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveIncremental_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckReceipt
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveFullRecheck_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalSuccess_next_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveFullRecheckSuccess_next_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveDeclaredDomain_source_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullAcceptance_equivalent_on_declared_domain
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullSuccessor_exact_on_declared_domain
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingIncrementalChange_accepts_of_analysis
#print axioms ConstitutiveSearch.NeuralAgent.SerializedLearnedPostForgettingRequest
#print axioms ConstitutiveSearch.NeuralAgent.decodeLearnedPostForgettingRequest
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingLocalConditionData
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingFullConditionData
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedPostForgettingIncrementally
#print axioms ConstitutiveSearch.NeuralAgent.liftLearnedPostForgettingIncrementalChange
#print axioms ConstitutiveSearch.NeuralAgent.liftLearnedPostForgettingIncrementalChange_of_ok
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
#print axioms ConstitutiveSearch.NeuralAgent.learnedInstalledPostForgettingContinuation_nextMemory_consumes_reducedMemory
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingExecutionReceipt
#print axioms ConstitutiveSearch.NeuralAgent.executionReceiptOfInstalledPostForgettingContinuation
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExecutionReceipt
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExecutionReceipt_outcome_is_installed
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExecutionReceipt_nextMemory_is_installed
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExecutionReceipt_outcome_consumes_forgettingOutput
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExecutionReceipt_nextMemory_consumes_forgettingOutput
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingExecutionReceipt.producedProposal
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingExecutionReceipt.producedProposal_exact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources
#print axioms ConstitutiveSearch.NeuralAgent.executeLearnedPostForgettingContractResources
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.reducedMemory_is_executed
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.baseFragments
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.authorizationAtTarget
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedExtendedOperationalTransition_unique
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedAuthorizationWitnessFromReceived
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedReceivedCausalAuthorizationPort_exact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.preservationAtTarget
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.authorizationPortExact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.action
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.actionEffect
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.effect
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.recomputedFragments
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.targetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.ClosedLearnedPostForgettingContractChange
#print axioms ConstitutiveSearch.NeuralAgent.closeLearnedPostForgettingContractChange
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingJustificationFromAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.closeLearnedPostForgettingContractChangeFromAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedJustification
#print axioms ConstitutiveSearch.NeuralAgent.learnedClosedPostForgettingExtendedChange
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.target_consumes_transportedIntent
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.target_consumes_recheckedAuthorization
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.target_shares_action_with_effect
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.target_action_consumes_receipt
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingContractResources.resourcePhase_consumes_reducedMemory
#print axioms ConstitutiveSearch.NeuralAgent.learnedClosedPostForgettingTargetAnalysis_exact
#print axioms ConstitutiveSearch.NeuralAgent.buildLearnedExtendedCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedClosedPostForgettingFullRecheck_successor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingJustificationFromLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.closeReceivedLearnedPostForgettingAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedPostForgettingRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingDependentChecker
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedPostForgettingRuntimeUpdate_change_of_analysis
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingDependentChecker_change_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingDependentChecker_accepts_extended
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedPostForgettingExtendedRuntimeUpdate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedRuntimeSubmission
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingRuntime_current_heq_of_eq
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedRuntime_eq_installed
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
