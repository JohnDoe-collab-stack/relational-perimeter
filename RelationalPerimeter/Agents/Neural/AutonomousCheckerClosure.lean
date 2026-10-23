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

/-! ## Successive incremental analysis from serialized material -/

def learnedSuccessiveCalculatedStructuralAssembly :
    CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      learnedSuccessiveTransportedStructuralFragments
      learnedSuccessiveRecomputedStructuralFragments :=
  certifyCalculatedIncrementalStructuralAssembly rfl rfl

def learnedSuccessiveTargetAnalysisFromDecision
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      ({ current := .aligned, next := .extended } :
        ContractTransitionRequest learnedConstitutiveMetaContract)) :
    IncrementalTargetAnalysis LearnedAlignedCheckedAgent :=
  { nextContract := .extended
    contractAdmitted := .extended
    artifact := learnedDecodedExtendedArtifact
    state := learnedExtendedState
    targetNaming := learnedExtendedStableNaming
    preCertificateGraph := learnedSuccessivePreCertificateGraph
    transportedLicenses := learnedSuccessiveLicensedStructuralTransports
    recomputedStructural := learnedSuccessiveRecomputedStructuralFragments
    structuralAssembly := learnedSuccessiveCalculatedStructuralAssembly
    structuralBasis := learnedExtendedFiniteCausalBasis
    structuralBasisNamingExact := rfl
    structuralSystemExact := rfl
    structuralInputDeclared := .tail (.tail .head)
    recomputedCertificateFragments :=
      learnedExtendedRecomputedCertificateFragments
    transition := decision.transition
    execution := by
      have decisionExact := decision.unique
        learnedExtendedTransitionDecision
      cases decisionExact
      exact learnedExtendedReferenceTransitionProduction.execution }

structure LearnedSuccessiveExecutedDependencies
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  decoded : DecodedLearnedSuccessiveUpdate source
  decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded
  receivedDecision : AcceptedTransitionDecision
    learnedExecutableMetaContractInterface source.transition
  transitionAccepted :
    decideTransition learnedExecutableMetaContractInterface source.transition =
      some receivedDecision
  authorizationConsumed :
    primaryAuthorizationConstitutivelyConsumed source.targetNetwork = true
  targetNetworkExact :
    source.targetNetwork = independentLearnedSecondSuccessorNetwork

structure LearnedSuccessiveEngineAnalysis
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  private mk ::
  executed : LearnedSuccessiveExecutedDependencies source

def LearnedSuccessiveEngineAnalysis.target
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    IncrementalTargetAnalysis LearnedAlignedCheckedAgent := by
  have transitionExact := analysis.executed.decoded.transitionExact
  exact learnedSuccessiveTargetAnalysisFromDecision
    (analysis.executed.receivedDecision.transportRequest transitionExact)

def analyzeLearnedSuccessiveUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError (LearnedSuccessiveEngineAnalysis source) :=
  match decodedExact : decodeLearnedSuccessiveUpdate source with
  | .error problem => .error problem
  | .ok decoded =>
      match transitionAccepted :
          decideTransition learnedExecutableMetaContractInterface
            source.transition with
      | none => .error .unexpectedTransition
      | some receivedDecision =>
          if authorizationConsumed :
              primaryAuthorizationConstitutivelyConsumed
                source.targetNetwork = true then
            if targetNetworkExact : source.targetNetwork =
                independentLearnedSecondSuccessorNetwork then
              .ok (.mk
                { decoded := decoded
                  decodedExact := decodedExact
                  receivedDecision := receivedDecision
                  transitionAccepted := transitionAccepted
                  authorizationConsumed := authorizationConsumed
                  targetNetworkExact := targetNetworkExact })
            else
              .error .unsupportedTargetArtifact
          else
            .error .missingConstitutiveDependency

abbrev LearnedSuccessiveLocalConditionData :=
  LearnedSuccessiveExecutedDependencies

def completeLearnedSuccessiveAnalysis
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    { analysis : LearnedSuccessiveEngineAnalysis source //
      analyzeLearnedSuccessiveUpdate source = .ok analysis } := by
  unfold analyzeLearnedSuccessiveUpdate
  split
  · have impossible := ‹decodeLearnedSuccessiveUpdate source = .error _›.symm.trans
      conditions.decodedExact
    cases impossible
  · rename_i decoded decodedExact
    have decodedValueExact : decoded = conditions.decoded :=
      Except.ok.inj (decodedExact.symm.trans conditions.decodedExact)
    cases decodedValueExact
    split
    · have impossible :=
        ‹decideTransition learnedExecutableMetaContractInterface
            source.transition = none›.symm.trans
          conditions.transitionAccepted
      cases impossible
    · rename_i receivedDecision transitionAccepted
      have decisionExact : receivedDecision = conditions.receivedDecision :=
        Option.some.inj
          (transitionAccepted.symm.trans conditions.transitionAccepted)
      cases decisionExact
      rw [dif_pos conditions.authorizationConsumed,
        dif_pos conditions.targetNetworkExact]
      exact ⟨.mk conditions, rfl⟩

def learnedSuccessiveLocalConditionsOfSuccess
    (source : LearnedSerializedConstitutiveUpdate)
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (_accepted : analyzeLearnedSuccessiveUpdate source = .ok analysis) :
    LearnedSuccessiveLocalConditionData source :=
  analysis.executed

def learnedSuccessiveIncrementalCheckerEngine :
    IncrementalCheckerEngine LearnedAlignedCheckedAgent :=
  { Update := LearnedSerializedConstitutiveUpdate
    Error := LearnedRuntimeUpdateError
    Analysis := LearnedSuccessiveEngineAnalysis
    analyze := analyzeLearnedSuccessiveUpdate
    LocalConditions := LearnedSuccessiveLocalConditionData
    complete := completeLearnedSuccessiveAnalysis
    localOfSuccess := learnedSuccessiveLocalConditionsOfSuccess
    target := fun analysis => analysis.target }

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

/-- Proof-free requests accepted by the post-forgetting checker.  The intent
is serialized with a contract change so the persistent source witness must be
reconstructed from received data rather than inserted by the checker. -/
inductive SerializedLearnedPostForgettingRequest where
  | continueCurrent (input : IndependentLearnedFutureInput)
  | changeContract (next : LearnedOperationalContract)
      (intent : IndependentLearnedUpdateIntent)

def decodeLearnedPostForgettingRequest :
    SerializedLearnedPostForgettingRequest →
      PostForgettingRequest LearnedAlignedCurrentAgent
  | .continueCurrent input =>
      @PostForgettingRequest.continueCurrent learnedConstitutiveMetaContract
        .aligned LearnedAlignedCurrentAgent input
  | .changeContract next _ =>
      @PostForgettingRequest.changeContract learnedConstitutiveMetaContract
        .aligned LearnedAlignedCurrentAgent next

inductive LearnedPostForgettingCheckError where
  | futureRefused
  | transitionRefused

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
      (next : LearnedOperationalContract)
      (intent : IndependentLearnedUpdateIntent)
      (intentAdmitted : AdmittedIndependentLearnedIntent intent)
      (decision : AcceptedTransitionDecision
        learnedExecutableMetaContractInterface
        { current := LearnedOperationalContract.aligned, next := next }) :
      LearnedPostForgettingLocalConditionData (.changeContract next intent)

def analyzeLearnedPostForgettingIncrementally
    (source : SerializedLearnedPostForgettingRequest) :
    Except LearnedPostForgettingCheckError
      (LearnedPostForgettingLocalConditionData source) :=
  match source with
  | .continueCurrent input =>
      match decideIndependentLearnedFutureAdmission input with
      | .inl admitted => .ok (.continueCurrent input admitted)
      | .inr _ => .error .futureRefused
  | .changeContract next intent =>
      match intent with
      | .preserveAuthorizedBehavior =>
          match decideTransition learnedExecutableMetaContractInterface
              { current := .aligned, next := next } with
          | none => .error .transitionRefused
          | some decision =>
              .ok (.changeContract next .preserveAuthorizedBehavior
                .preserveAuthorizedBehavior decision)

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
    {next : LearnedOperationalContract}
    {intent : IndependentLearnedUpdateIntent}
    (intentAdmitted : AdmittedIndependentLearnedIntent intent)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.aligned, next := next }) :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent (.changeContract next) :=
  .changeContract next
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
  | .changeContract _ _ intentAdmitted decision =>
      learnedPostForgettingChangeFromDecision intentAdmitted decision

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
      (LearnedPostForgettingLocalConditionData source) :=
  match source with
  | .continueCurrent input =>
      match independentLearnedReducedFutureContract.decision
          learnedAlignedForgottenCurrentAgent.memory input with
      | .inl admitted => .ok (.continueCurrent input admitted)
      | .inr _ => .error .futureRefused
  | .changeContract next intent =>
      match intent with
      | .preserveAuthorizedBehavior =>
          match decideTransition learnedExecutableMetaContractInterface
              { current := .aligned, next := next } with
          | none => .error .transitionRefused
          | some decision =>
              .ok (.changeContract next .preserveAuthorizedBehavior
                .preserveAuthorizedBehavior decision)

/-- Independent complete reference algorithm for the post-forgetting domain.
It repeats the reflected decisions from the serialized request and has no
argument through which an incremental result or fragment could be supplied. -/
def recheckLearnedPostForgettingCompletely
    (source : SerializedLearnedPostForgettingRequest) :
    Except LearnedPostForgettingCheckError
      (PostForgettingPermission LearnedAlignedCurrentAgent
        learnedAlignedForgottenCurrentAgent
        (decodeLearnedPostForgettingRequest source)) :=
  match analyzeLearnedPostForgettingCompletely source with
  | .error problem => .error problem
  | .ok conditions => .ok conditions.permission

def ExceptAccepted {Error Result : Type _} : Except Error Result → Prop
  | .ok _ => True
  | .error _ => False

abbrev LearnedPostForgettingIncrementalAccepted
    (source : SerializedLearnedPostForgettingRequest) : Prop :=
  ExceptAccepted (analyzeLearnedPostForgettingIncrementally source)

abbrev LearnedPostForgettingFullRecheckAccepted
    (source : SerializedLearnedPostForgettingRequest) : Prop :=
  ExceptAccepted (analyzeLearnedPostForgettingCompletely source)

def learnedPostForgettingAdmittedContinuationRequest :
    SerializedLearnedPostForgettingRequest :=
  .continueCurrent learnedAdmittedFutureRequest

def learnedPostForgettingExtendedChangeRequest :
    SerializedLearnedPostForgettingRequest :=
  .changeContract .extended .preserveAuthorizedBehavior

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
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest)) ∧
    (LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingExtendedChangeRequest)) ∧
    (LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingExtendedChangeRequest)) := by
  have continuationConditions : Nonempty
      (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest) :=
    ⟨.continueCurrent learnedAdmittedFutureRequest
      learnedAdmittedFutureRequestWitness⟩
  have changeConditions : Nonempty
      (LearnedPostForgettingLocalConditionData
        learnedPostForgettingExtendedChangeRequest) :=
    ⟨.changeContract .extended .preserveAuthorizedBehavior
      .preserveAuthorizedBehavior learnedExtendedTransitionDecision⟩
  constructor
  · constructor
    · intro _
      exact continuationConditions
    · intro _
      exact learnedPostForgettingAdmittedContinuation_incremental
  · constructor
    · constructor
      · intro _
        exact continuationConditions
      · intro _
        exact learnedPostForgettingAdmittedContinuation_full
    · constructor
      · constructor
        · intro _
          exact changeConditions
        · intro _
          exact learnedPostForgettingExtendedChange_incremental
      · constructor
        · intro _
          exact changeConditions
        · intro _
          exact learnedPostForgettingExtendedChange_full

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
/- AXIOM_AUDIT_END -/
