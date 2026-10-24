import RelationalPerimeter.Agents.Neural.LearnedContractFutureDivergence
import RelationalPerimeter.Agents.Neural.ReconfiguredExactForgetting
import RelationalPerimeter.Agents.Neural.AutonomousContractTransitions
import RelationalPerimeter.Constitution.Continuation.ExactSeparation

/-!
# Constitutive closure of learned futures and executed forgetting

The installed learned successor supplies the future source used here.  The
contract has both admitted and refused requests, its immediate readout does
not expose the serialized network, and a nonempty executed continuation is
required to separate the aligned and bypass sources.  The resulting finite
separator constrains every exact realization of this fixed contract.

Two independently admitted stable-identity histories are then consumed by an
executed action/effect trace.  The reduced operational memory retains the
complete future behavior but omits the historical identity.  Recovery of that
identity is rejected after forgetting.
-/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

/-! ## Admission, refusal, and a necessary nonempty continuation -/

/-! The observations below are indexed by the exact states produced by the
single transition kernel used in L3.  No independently reconstructed state or
future source is accepted. -/

abbrev LearnedAlignedProducedState :=
  learnedReferenceTransitionProduction.targetState

abbrev LearnedExtendedProducedState :=
  learnedExtendedReferenceTransitionProduction.targetState

theorem learnedAlignedProducedState_exact :
    LearnedAlignedProducedState = learnedAlignedState := by
  rfl

theorem learnedExtendedProducedState_exact :
    LearnedExtendedProducedState = learnedExtendedState := by
  rfl

def learnedAlignedProducedFutureObservation :
    ContractFutureObservationAt LearnedAlignedOperationalContract
      LearnedAlignedProducedState :=
  contractFutureObservationAt LearnedAlignedProducedState

def learnedExtendedProducedFutureObservation :
    ContractFutureObservationAt LearnedExtendedOperationalContract
      LearnedExtendedProducedState :=
  contractFutureObservationAt LearnedExtendedProducedState

theorem learnedAlignedProducedFutureSource_exact :
    learnedAlignedProducedFutureObservation.source =
      learnedCandidateFutureSource learnedAlignedCandidateAtInitial := by
  rfl

theorem learnedAlignedRuntimeFutureSource_is_produced :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedCertifiedRuntime.current.state =
      learnedAlignedProducedFutureObservation.source := by
  rw [learnedAlignedRuntime_state_exact]
  rfl

theorem learnedExtendedRuntimeFutureSource_is_produced :
    LearnedExtendedOperationalContract.futureSourceOfState
        learnedExtendedCertifiedRuntime.current.state =
      learnedExtendedProducedFutureObservation.source := by
  rw [learnedExtendedRuntime_state_exact]
  rfl

def learnedAdmittedFutureRequest : IndependentLearnedFutureInput :=
  { input := independentLearnedCounterfactualInput }

def learnedRefusedFutureRequest : IndependentLearnedFutureInput :=
  { input :=
      { requirement := false
        context := false
        authorization := true } }

def learnedAdmittedFutureRequestWitness :
    independentLearnedFutureContract.Allow
      (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
      learnedAdmittedFutureRequest :=
  { requirementDiffers := rfl }

theorem learnedAdmittedFutureRequest_enabled :
    independentLearnedFutureContract.enabled
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedAdmittedFutureRequest = true := by
  rfl

theorem learnedRefusedFutureRequest_disabled :
    independentLearnedFutureContract.enabled
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedRefusedFutureRequest = false := by
  rfl

theorem learnedRefusedFutureRequest_has_no_witness
    (witness : independentLearnedFutureContract.Allow
      (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
      learnedRefusedFutureRequest) : False := by
  cases witness.requirementDiffers

theorem learnedAlignedBypass_immediate_read_equal :
    independentLearnedFutureContract.read
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) =
      independentLearnedFutureContract.read
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) := by
  rfl

theorem learnedAlignedBypass_empty_future_equal :
    independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) [] =
      independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) [] := by
  rfl

def learnedAlignedBypassFutureSeparator : FutureSeparator
    independentLearnedFutureContract
    (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
    (learnedCandidateFutureSource learnedBypassCandidateAtInitial) where
  requests := learnedOperationalCounterfactualRequests
  different := learnedAlignedBypass_operationalFuture_different

theorem learnedAlignedBypass_separator_nonempty :
    learnedAlignedBypassFutureSeparator.requests ≠ [] :=
  learnedOperationalCounterfactualRequests_nonempty

/-! ## RC4: every exact realization preserves the produced separation -/

theorem learnedEveryExactRealizationSeparatesAlignedFromBypass
    (Memory : Type 3)
    (realization : ExactRealization independentLearnedFutureContract Memory) :
    realization.project
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) ≠
      realization.project
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) :=
  realization.distinct_memory_of_separator
    learnedAlignedBypassFutureSeparator

def learnedBehavioralFutureRealization : ExactRealization
    independentLearnedFutureContract IndependentLearnedOperationalMemory :=
  independentLearnedFutureSimulation.toExactRealization

theorem learnedBehavioralFutureRealization_preserves_every_finite_future
    (source : IndependentLearnedFutureSource)
    (requests : List IndependentLearnedFutureInput) :
    independentLearnedFutureContract.outcome source requests =
      independentLearnedReducedFutureContract.outcome
        (independentLearnedFutureProjection source) requests :=
  learnedBehavioralFutureRealization.outcome_exact source requests

/-! ## Two admitted histories and their executed forgetting -/

def learnedRenamedIdentitySerializedUpdate :
    LearnedSerializedConstitutiveUpdate :=
  { learnedAlignedSerializedUpdate with
    targetStableNaming := learnedRenamedSerializedNaming }

def learnedRenamedIdentityRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .serialized learnedRenamedIdentitySerializedUpdate

def learnedRenamedIdentityCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  match submitUpdate learnedInitialCertifiedRuntime
      learnedRenamedIdentityRuntimeUpdate with
  | .ok runtime => runtime
  | .error _ => learnedInitialCertifiedRuntime

theorem submitUpdate_learned_renamed_identity_exact :
    submitUpdate learnedInitialCertifiedRuntime
        learnedRenamedIdentityRuntimeUpdate =
      .ok learnedRenamedIdentityCertifiedRuntime := by
  rfl

theorem learnedRenamedIdentityRuntime_state_exact :
    learnedRenamedIdentityCertifiedRuntime.current.state =
      learnedAlignedState := by
  rfl

inductive LearnedHistoricalStableOrigin : Type 3 where
  | aligned
  | renamed

def LearnedHistoricalStableOrigin.runtime :
    LearnedHistoricalStableOrigin ->
      CertifiedRuntime learnedDependentIncrementalChecker
        learnedInitialCheckedAgent
  | .aligned => learnedAlignedCertifiedRuntime
  | .renamed => learnedRenamedIdentityCertifiedRuntime

def LearnedHistoricalStableOrigin.serializedNaming :
    LearnedHistoricalStableOrigin -> SerializedStableArtifactNaming
  | .aligned => learnedAlignedSerializedNaming
  | .renamed => learnedRenamedSerializedNaming

def LearnedHistoricalStableOrigin.admittedNaming
    (origin : LearnedHistoricalStableOrigin) :
    LearnedAdmittedStableNaming origin.serializedNaming :=
  match origin with
  | .aligned => .aligned
  | .renamed => .renamed

def LearnedHistoricalStableOrigin.firstInputSerial :
    LearnedHistoricalStableOrigin -> Nat
  | .aligned => 0
  | .renamed => 1100

def transportLearnedRuntimeInputIndex
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (index : Fin source.current.artifact.system.inputCount) :
    Fin target.current.artifact.system.inputCount := by
  cases exact
  exact index

theorem learnedRuntimeInputSerial_transport_exact
    {source target : CertifiedRuntime learnedDependentIncrementalChecker
      learnedInitialCheckedAgent}
    (exact : source = target)
    (index : Fin source.current.artifact.system.inputCount) :
    target.current.certificate.basis.naming.inputSerial
        (transportLearnedRuntimeInputIndex exact index) =
      source.current.certificate.basis.naming.inputSerial index := by
  cases exact
  rfl

def learnedAlignedInstalledFirstInputIndex :
    Fin (installAcceptedUpdate learnedInitialCertifiedRuntime
      learnedAlignedRuntimeUpdate learnedAlignedDependentResult
      learnedDependentChecker_accepts_aligned).current.artifact.system.inputCount :=
  ⟨0, by decide⟩

def learnedAlignedRuntimeFirstInputIndex :
    Fin learnedAlignedCertifiedRuntime.current.artifact.system.inputCount :=
  transportLearnedRuntimeInputIndex
    learnedAlignedCertifiedRuntime_eq_installed.symm
    learnedAlignedInstalledFirstInputIndex

def LearnedHistoricalStableOrigin.runtimeFirstInputSerial :
    LearnedHistoricalStableOrigin -> Nat
  | .aligned => by
      exact learnedAlignedCertifiedRuntime.current.certificate.basis.naming.inputSerial
        learnedAlignedRuntimeFirstInputIndex
  | .renamed =>
      learnedRenamedIdentityCertifiedRuntime.current.certificate.basis.naming.inputSerial
        ⟨0, by decide⟩

theorem LearnedHistoricalStableOrigin.runtime_state_exact
    (origin : LearnedHistoricalStableOrigin) :
    origin.runtime.current.state = learnedAlignedState := by
  cases origin with
  | aligned => exact learnedAlignedRuntime_state_exact
  | renamed => rfl

theorem LearnedHistoricalStableOrigin.runtime_identity_exact
    (origin : LearnedHistoricalStableOrigin) :
    origin.runtimeFirstInputSerial = origin.firstInputSerial := by
  cases origin with
  | aligned =>
      exact (learnedRuntimeInputSerial_transport_exact
        learnedAlignedCertifiedRuntime_eq_installed.symm
        learnedAlignedInstalledFirstInputIndex).trans (by rfl)
  | renamed => rfl

theorem learnedHistoricalStableOrigins_distinct :
    LearnedHistoricalStableOrigin.aligned ≠
      LearnedHistoricalStableOrigin.renamed := by
  intro impossible
  cases impossible

theorem learnedHistoricalStableOrigin_identities_distinct :
    LearnedHistoricalStableOrigin.aligned.firstInputSerial ≠
      LearnedHistoricalStableOrigin.renamed.firstInputSerial := by
  decide

/-! The origin-bearing state exists before the action.  The action in the
forgetting trace is indexed by this exact value, so historical identity is not
added retrospectively to an already reduced execution. -/
structure LearnedHistoricalPreActionState
    (origin : LearnedHistoricalStableOrigin) : Type 3 where
  historicalNaming : SerializedStableArtifactNaming
  historicalNamingExact : historicalNaming = origin.serializedNaming
  installedIdentity : Nat
  installedIdentityExact : installedIdentity =
    origin.firstInputSerial

def LearnedHistoricalPreActionState.executionState
    {origin : LearnedHistoricalStableOrigin}
    (_state : LearnedHistoricalPreActionState origin) :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  origin.runtime.current.state

def executeLearnedHistoricalPreActionState
    (origin : LearnedHistoricalStableOrigin) :
    LearnedHistoricalPreActionState origin := by
  cases origin with
  | aligned =>
      exact
        { historicalNaming := learnedAlignedSerializedNaming
          historicalNamingExact := rfl
          installedIdentity := 0
          installedIdentityExact := rfl }
  | renamed =>
      exact
        { historicalNaming := learnedRenamedSerializedNaming
          historicalNamingExact := rfl
          installedIdentity := 1100
          installedIdentityExact := rfl }

theorem learnedHistoricalPreActionIdentities_distinct :
    (executeLearnedHistoricalPreActionState .aligned).installedIdentity ≠
      (executeLearnedHistoricalPreActionState .renamed).installedIdentity := by
  decide

theorem learnedHistoricalPreAction_runtimeIdentity_exact
    (origin : LearnedHistoricalStableOrigin) :
    (executeLearnedHistoricalPreActionState origin).installedIdentity =
      origin.runtimeFirstInputSerial := by
  exact
    (executeLearnedHistoricalPreActionState origin).installedIdentityExact.trans
      (origin.runtime_identity_exact).symm

structure LearnedHistoricalFutureForgettingTrace
    (origin : LearnedHistoricalStableOrigin) : Type 3 where
  preAction : LearnedHistoricalPreActionState origin
  action : LearnedActionWitness preAction.executionState
  effect : LearnedEffectWitness preAction.executionState action
  effectExact : effect = produceLearnedEffect action

def transportLearnedAction
    {source target :
      ReconfiguredExecutionState independentLearnedRequirementFamily}
    (exact : source = target)
    (action : LearnedActionWitness source) : LearnedActionWitness target := by
  cases exact
  exact action

theorem transportLearnedAction_heq
    {source target :
      ReconfiguredExecutionState independentLearnedRequirementFamily}
    (exact : source = target)
    (action : LearnedActionWitness source) :
    HEq (transportLearnedAction exact action) action := by
  cases exact
  rfl

theorem transportLearnedAction_effect_targetState
    {source target :
      ReconfiguredExecutionState independentLearnedRequirementFamily}
    (exact : source = target)
    (action : LearnedActionWitness source) :
    (produceLearnedEffect (transportLearnedAction exact action)).targetState =
      (produceLearnedEffect action).targetState := by
  cases exact
  rfl

def learnedHistoricalActionFor
    (origin : LearnedHistoricalStableOrigin) :
    LearnedActionWitness
      (executeLearnedHistoricalPreActionState origin).executionState :=
  transportLearnedAction origin.runtime_state_exact.symm learnedAlignedAction

def executeLearnedHistoricalFutureForgettingTrace
    (origin : LearnedHistoricalStableOrigin) :
    LearnedHistoricalFutureForgettingTrace origin := by
  exact
  { preAction := executeLearnedHistoricalPreActionState origin
    action := learnedHistoricalActionFor origin
    effect := produceLearnedEffect (learnedHistoricalActionFor origin)
    effectExact := rfl }

theorem learnedHistoricalActionFor_exact
    (origin : LearnedHistoricalStableOrigin) :
    HEq (learnedHistoricalActionFor origin) learnedAlignedAction := by
  exact transportLearnedAction_heq origin.runtime_state_exact.symm
    learnedAlignedAction

def learnedHistoricalFutureForgettingProgram :
    HistoricalForgettingProgram LearnedHistoricalStableOrigin
      IndependentLearnedOperationalMemory where
  Trace := LearnedHistoricalFutureForgettingTrace
  execute := executeLearnedHistoricalFutureForgettingTrace
  reduce := fun _ trace => independentLearnedFutureProjection
    (LearnedAlignedOperationalContract.futureSourceOfState
      trace.effect.targetState)

def learnedAlignedHistoricalForgettingInput :
    HistoricalForgettingInput learnedHistoricalFutureForgettingProgram :=
  { origin := .aligned }

def learnedRenamedHistoricalForgettingInput :
    HistoricalForgettingInput learnedHistoricalFutureForgettingProgram :=
  { origin := .renamed }

def learnedAlignedExecutedFutureForgetting :=
  executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
    learnedAlignedHistoricalForgettingInput

def learnedRenamedExecutedFutureForgetting :=
  executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
    learnedRenamedHistoricalForgettingInput

theorem learnedHistoricalFutureForgetting_targetState_exact
    (origin : LearnedHistoricalStableOrigin) :
    (executeLearnedHistoricalFutureForgettingTrace origin).effect.targetState =
      learnedAlignedEffect.targetState := by
  exact transportLearnedAction_effect_targetState
    origin.runtime_state_exact.symm learnedAlignedAction

theorem learnedHistoricalForgettingInputs_distinct :
    learnedAlignedHistoricalForgettingInput ≠
      learnedRenamedHistoricalForgettingInput :=
  HistoricalForgettingInput.ne_of_origin_ne
    learnedHistoricalStableOrigins_distinct

theorem learnedExecutedFutureForgetting_outputs_equal :
    learnedAlignedExecutedFutureForgetting.output =
      learnedRenamedExecutedFutureForgetting.output := by
  change independentLearnedFutureProjection
      (LearnedAlignedOperationalContract.futureSourceOfState
        (executeLearnedHistoricalFutureForgettingTrace .aligned).effect.targetState) =
    independentLearnedFutureProjection
      (LearnedAlignedOperationalContract.futureSourceOfState
        (executeLearnedHistoricalFutureForgettingTrace .renamed).effect.targetState)
  rw [learnedHistoricalFutureForgetting_targetState_exact .aligned]
  rw [learnedHistoricalFutureForgetting_targetState_exact .renamed]

theorem learnedExecutedFutureForgetting_output_exact
    (origin : LearnedHistoricalStableOrigin) :
    (executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
      { origin := origin }).output =
      independentLearnedFutureProjection
        (LearnedAlignedOperationalContract.futureSourceOfState
          learnedAlignedEffect.targetState) := by
  change independentLearnedFutureProjection
      (LearnedAlignedOperationalContract.futureSourceOfState
        (executeLearnedHistoricalFutureForgettingTrace origin).effect.targetState) = _
  rw [learnedHistoricalFutureForgetting_targetState_exact]

theorem learnedExecutedFutureForgetting_preserves_every_finite_future
    (origin : LearnedHistoricalStableOrigin)
    (requests : List IndependentLearnedFutureInput) :
    independentLearnedFutureContract.outcome
        (LearnedAlignedOperationalContract.futureSourceOfState
          learnedAlignedEffect.targetState) requests =
      independentLearnedReducedFutureContract.outcome
        (executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
          { origin := origin }).output requests := by
  rw [learnedExecutedFutureForgetting_output_exact origin]
  exact learnedBehavioralFutureRealization.outcome_exact
    (LearnedAlignedOperationalContract.futureSourceOfState
      learnedAlignedEffect.targetState) requests

theorem learnedExecutedFutureForgetting_origin_not_recoverable
    (recover : IndependentLearnedOperationalMemory ->
      LearnedHistoricalStableOrigin)
    (recoversAligned :
      recover learnedAlignedExecutedFutureForgetting.output =
        learnedAlignedHistoricalForgettingInput.origin)
    (recoversRenamed :
      recover learnedRenamedExecutedFutureForgetting.output =
        learnedRenamedHistoricalForgettingInput.origin) : False :=
  ExecutedHistoricalForgetting.origin_not_recoverable
    learnedAlignedExecutedFutureForgetting
    learnedRenamedExecutedFutureForgetting
    learnedHistoricalStableOrigins_distinct
    learnedExecutedFutureForgetting_outputs_equal
    recover recoversAligned recoversRenamed

/-! ## Continuation and contract transition after forgetting

This section deliberately uses the unique meta-contract interface introduced
in L1.  It does not define a learned-only permission language.  Installation
remains a later L5--L8 obligation. -/

/-- The current aligned agent is the exact successor returned by the accepted
first checker result.  The certified runtime installs this very value; using
the result projection here keeps later dependent interfaces tied to the
executed transition without recomputing the runtime match. -/
abbrev LearnedAlignedCurrentAgent :=
  learnedAlignedDependentResult.checked.next

theorem learnedAlignedRuntime_current_is_checkedResult :
    HEq learnedAlignedCertifiedRuntime.current LearnedAlignedCurrentAgent :=
  learnedAlignedCertifiedRuntime_current_exact

def learnedAlignedForgottenCurrentAgent :
    ForgottenCurrentAgent LearnedAlignedCurrentAgent :=
  forgetCurrentAgent LearnedAlignedCurrentAgent

theorem learnedAlignedForgottenMemory_is_executedReduction :
    learnedAlignedForgottenCurrentAgent.memory =
      learnedAlignedExecutedFutureForgetting.output := by
  let projected : IndependentLearnedOperationalMemory :=
    independentLearnedFutureProjection
      (LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedEffect.targetState)
  have forgottenExact : learnedAlignedForgottenCurrentAgent.memory = projected := by
    rfl
  have executionExact : learnedAlignedExecutedFutureForgetting.output = projected :=
    learnedExecutedFutureForgetting_output_exact .aligned
  exact forgottenExact.trans executionExact.symm

def learnedPostForgettingContinuationPermission :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent
      (.continueCurrent learnedAdmittedFutureRequest) :=
  @PostForgettingPermission.continueCurrent learnedConstitutiveMetaContract
    .aligned LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent
    learnedAdmittedFutureRequest
    (LearnedAlignedCurrentAgent.certificate.futureRealization.exact.forward
      (LearnedAlignedOperationalContract.futureSourceOfState
        LearnedAlignedCurrentAgent.state)
      learnedAdmittedFutureRequest learnedAdmittedFutureRequestWitness)

theorem learnedPostForgettingRefusedFuture_stays_refused
    (permission : PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent
      (.continueCurrent learnedRefusedFutureRequest)) : False := by
  cases permission with
  | continueCurrent _ admitted =>
      exact learnedRefusedFutureRequest_has_no_witness
        (LearnedAlignedCurrentAgent.certificate.futureRealization.exact.backward
          (LearnedAlignedOperationalContract.futureSourceOfState
            LearnedAlignedCurrentAgent.state)
          learnedRefusedFutureRequest admitted)

def learnedJustifiedExtendedTransitionAfterForgetting :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent .extended :=
  { transition := learnedExtendedOperationalTransition
    persistentSource := fun obligation => by
      cases obligation
      exact ULift.up
        AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior }

def learnedPostForgettingContractChangePermission :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent (.changeContract .extended) :=
  @PostForgettingPermission.changeContract learnedConstitutiveMetaContract
    .aligned LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent
    .extended learnedJustifiedExtendedTransitionAfterForgetting

def learnedPostForgettingTransportedIntent :
    learnedConstitutiveMetaContract.TargetPersistentWitness .aligned .extended
      .admittedIntent :=
  learnedJustifiedExtendedTransitionAfterForgetting.transportedPersistent
    .admittedIntent

def learnedPostForgettingRecheckedAuthorization :
    learnedConstitutiveMetaContract.RecheckedWitness .aligned .extended
      .authorizationConsumption :=
  learnedJustifiedExtendedTransitionAfterForgetting.rechecked
    .authorizationConsumption

theorem learnedPostForgettingReturnToInitial_refused
    (justification : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent .initial) : False := by
  nomatch justification.transition.permission

/-! ## One closed L4 / RC4 witness -/

structure LearnedFutureForgettingRC4Certificate : Type 8 where
  alignedFutureSourceProduced :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedCertifiedRuntime.current.state =
      learnedAlignedProducedFutureObservation.source
  extendedFutureSourceProduced :
    LearnedExtendedOperationalContract.futureSourceOfState
        learnedExtendedCertifiedRuntime.current.state =
      learnedExtendedProducedFutureObservation.source
  futureSourceExact :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedCertifiedRuntime.current.state =
      learnedCandidateFutureSource learnedAlignedCandidateAtInitial
  admittedRequest : independentLearnedFutureContract.Allow
    (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
    learnedAdmittedFutureRequest
  refusedRequest : independentLearnedFutureContract.enabled
    (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
    learnedRefusedFutureRequest = false
  immediateReadEqual : independentLearnedFutureContract.read
      (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) =
    independentLearnedFutureContract.read
      (learnedCandidateFutureSource learnedBypassCandidateAtInitial)
  separator : FutureSeparator independentLearnedFutureContract
    (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
    (learnedCandidateFutureSource learnedBypassCandidateAtInitial)
  separatorNonempty : separator.requests ≠ []
  allExactRealizationsSeparate :
    forall (Memory : Type 3)
      (realization : ExactRealization independentLearnedFutureContract Memory),
      realization.project
          (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) ≠
        realization.project
          (learnedCandidateFutureSource learnedBypassCandidateAtInitial)
  positiveRealization : ExactRealization independentLearnedFutureContract
    IndependentLearnedOperationalMemory
  historiesAdmitted : forall origin : LearnedHistoricalStableOrigin,
    LearnedAdmittedStableNaming origin.serializedNaming
  historiesDistinct : learnedAlignedHistoricalForgettingInput ≠
    learnedRenamedHistoricalForgettingInput
  installedIdentitiesDistinct :
    LearnedHistoricalStableOrigin.aligned.firstInputSerial ≠
      LearnedHistoricalStableOrigin.renamed.firstInputSerial
  forgottenOutputsEqual : learnedAlignedExecutedFutureForgetting.output =
    learnedRenamedExecutedFutureForgetting.output
  everyFuturePreserved : forall origin requests,
    independentLearnedFutureContract.outcome
        (LearnedAlignedOperationalContract.futureSourceOfState
          learnedAlignedEffect.targetState) requests =
      independentLearnedReducedFutureContract.outcome
        (executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
          { origin := origin }).output requests
  originNotRecoverable : forall
      (recover : IndependentLearnedOperationalMemory ->
        LearnedHistoricalStableOrigin),
      recover learnedAlignedExecutedFutureForgetting.output =
          learnedAlignedHistoricalForgettingInput.origin ->
        recover learnedRenamedExecutedFutureForgetting.output =
          learnedRenamedHistoricalForgettingInput.origin -> False
  reducedMemoryConsumed : learnedAlignedForgottenCurrentAgent.memory =
    learnedAlignedExecutedFutureForgetting.output
  continuationTransported : PostForgettingPermission
    LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent
    (.continueCurrent learnedAdmittedFutureRequest)
  refusedContinuationRejected : PostForgettingPermission
      LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent
      (.continueCurrent learnedRefusedFutureRequest) -> False
  contractChangeJustified : JustifiedPostForgettingTransition
    LearnedAlignedCurrentAgent .extended
  contractChangeAuthorized : PostForgettingPermission
    LearnedAlignedCurrentAgent learnedAlignedForgottenCurrentAgent
    (.changeContract .extended)
  persistentIntentTransported :
    learnedConstitutiveMetaContract.TargetPersistentWitness .aligned .extended
      .admittedIntent
  authorizationRechecked :
    learnedConstitutiveMetaContract.RecheckedWitness .aligned .extended
      .authorizationConsumption
  forbiddenHistoricalReturn : JustifiedPostForgettingTransition
      LearnedAlignedCurrentAgent .initial -> False

def learnedFutureForgettingRC4 : LearnedFutureForgettingRC4Certificate :=
  { alignedFutureSourceProduced :=
      learnedAlignedRuntimeFutureSource_is_produced
    extendedFutureSourceProduced :=
      learnedExtendedRuntimeFutureSource_is_produced
    futureSourceExact := learnedAlignedRuntime_futureSource_exact
    admittedRequest := learnedAdmittedFutureRequestWitness
    refusedRequest := learnedRefusedFutureRequest_disabled
    immediateReadEqual := learnedAlignedBypass_immediate_read_equal
    separator := learnedAlignedBypassFutureSeparator
    separatorNonempty := learnedAlignedBypass_separator_nonempty
    allExactRealizationsSeparate :=
      learnedEveryExactRealizationSeparatesAlignedFromBypass
    positiveRealization := learnedBehavioralFutureRealization
    historiesAdmitted := LearnedHistoricalStableOrigin.admittedNaming
    historiesDistinct := learnedHistoricalForgettingInputs_distinct
    installedIdentitiesDistinct :=
      learnedHistoricalStableOrigin_identities_distinct
    forgottenOutputsEqual := learnedExecutedFutureForgetting_outputs_equal
    everyFuturePreserved :=
      learnedExecutedFutureForgetting_preserves_every_finite_future
    originNotRecoverable :=
      learnedExecutedFutureForgetting_origin_not_recoverable
    reducedMemoryConsumed :=
      learnedAlignedForgottenMemory_is_executedReduction
    continuationTransported := learnedPostForgettingContinuationPermission
    refusedContinuationRejected :=
      learnedPostForgettingRefusedFuture_stays_refused
    contractChangeJustified :=
      learnedJustifiedExtendedTransitionAfterForgetting
    contractChangeAuthorized :=
      learnedPostForgettingContractChangePermission
    persistentIntentTransported := learnedPostForgettingTransportedIntent
    authorizationRechecked := learnedPostForgettingRecheckedAuthorization
    forbiddenHistoricalReturn :=
      learnedPostForgettingReturnToInitial_refused }

/-! ## Joint closure on the independently learned artifact lineage -/

theorem learnedInitialAlignedNeuronCounts_distinct :
    independentLearnedInitialNetwork.neurons.length ≠
      independentLearnedFirstSuccessorNetwork.neurons.length := by
  decide

theorem learnedAlignedExtendedNeuronCounts_distinct :
    independentLearnedFirstSuccessorNetwork.neurons.length ≠
      independentLearnedSecondSuccessorNetwork.neurons.length := by
  decide

/-- The learned execution lineage stores the actual results returned by the
dependent checker.  Its second request is indexed by the successor returned
by its first result, so neither edge can be detached from the artifact that
precedes it. -/
structure LearnedArtifactExecutionLineage : Type 9 where
  initial : CheckedAgent learnedConstitutiveMetaContract .initial
  initialExact : initial = learnedInitialCheckedAgent
  firstUpdate : learnedDependentIncrementalChecker.Update initial
  firstResult : DependentCheckedUpdateResult initial
  firstAccepted :
    learnedDependentIncrementalChecker.check initial firstUpdate =
      .ok firstResult
  firstUpdateExact : HEq firstUpdate learnedAlignedRuntimeUpdate
  firstResultExact : HEq firstResult learnedAlignedDependentResult
  secondUpdate :
    learnedDependentIncrementalChecker.Update firstResult.checked.next
  secondResult : DependentCheckedUpdateResult firstResult.checked.next
  secondAccepted :
    learnedDependentIncrementalChecker.check firstResult.checked.next
        secondUpdate =
      .ok secondResult
  secondUpdateExact : HEq secondUpdate learnedExtendedRuntimeUpdate
  secondResultExact : HEq secondResult learnedExtendedDependentResult
  finalExact : HEq secondResult.checked.next learnedExtendedCheckedAgent

def learnedArtifactExecutionLineage : LearnedArtifactExecutionLineage :=
  { initial := learnedInitialCheckedAgent
    initialExact := rfl
    firstUpdate := learnedAlignedRuntimeUpdate
    firstResult := learnedAlignedDependentResult
    firstAccepted := rfl
    firstUpdateExact := HEq.rfl
    firstResultExact := HEq.rfl
    secondUpdate := learnedExtendedRuntimeUpdate
    secondResult := learnedExtendedDependentResult
    secondAccepted := learnedDependentChecker_accepts_extended
    secondUpdateExact := HEq.rfl
    secondResultExact := HEq.rfl
    finalExact := HEq.rfl }

def LearnedArtifactExecutionLineage.trace
    (lineage : LearnedArtifactExecutionLineage) :
    CheckedReconfigurationTrace learnedDependentIncrementalChecker
      lineage.initial lineage.secondResult.checked.next :=
  .step lineage.firstUpdate lineage.firstResult lineage.firstAccepted
    (.step lineage.secondUpdate lineage.secondResult lineage.secondAccepted
      (.nil lineage.secondResult.checked.next))

def LearnedArtifactExecutionLineage.sound
    (lineage : LearnedArtifactExecutionLineage) :
    EveryCheckedStepSatisfies lineage.trace :=
  checkedTrace_constitutivelyAligned lineage.trace

def LearnedArtifactExecutionLineage.preservesContracts
    (lineage : LearnedArtifactExecutionLineage) :
    EveryCheckedStepPreservesContracts lineage.trace :=
  checkedTrace_preservesContracts lineage.trace

theorem learnedArtifactExecutionLineage_trace_exact :
    learnedArtifactExecutionLineage.trace = learnedTwoStepCheckedTrace := by
  rfl

theorem learnedAlignedHistoricalOrigin_runtime_exact :
    LearnedHistoricalStableOrigin.aligned.runtime =
      learnedAlignedCertifiedRuntime := by
  rfl

/-- Terminal evidence for L8.  This is not a checklist of unrelated closed
theorems: it stores the dependent learned lineage, the exact runtimes it
installs, the state-indexed causal witnesses carried by those runtimes, the
source-indexed local structural reuse, and the future and forgetting
certificates whose sources are the installed aligned state.  The exactness
fields prevent evidence from another artifact, state, update, or run from
being substituted into the package. -/
structure LearnedConstitutiveAlignmentClosureCertificate : Type 12 where
  learningProtocol : String
  learningProtocolExact : learningProtocol = independentLearningProtocolSha256
  learningData : String
  learningDataExact : learningData = independentLearningDataSha256
  learningGenerator : String
  learningGeneratorExact : learningGenerator = independentLearningGeneratorSha256
  learnedArtifact : String
  learnedArtifactExact : learnedArtifact = independentLearnedArtifactSha256
  initialArtifactAccepted : independentLearnedInitialNetworkAccepted = true
  initialAlignedNonidentity : independentLearnedInitialNetwork.neurons.length ≠
    independentLearnedFirstSuccessorNetwork.neurons.length
  alignedExtendedNonidentity :
    independentLearnedFirstSuccessorNetwork.neurons.length ≠
      independentLearnedSecondSuccessorNetwork.neurons.length
  alignedReconfiguration : CertifiedReconfiguration
    (builder := learnedAlignedReconfigurationBuilder)
    (sourceSystem := learnedDecodedInitialArtifact.system)
    (sourceInput := independentLearnedCertifiedInput)
    (nextInput := independentLearnedCertifiedInput)
  alignedReconfigurationExact :
    alignedReconfiguration = learnedAlignedCertifiedReconfiguration
  extendedReconfiguration : CertifiedReconfiguration
    (builder := learnedExtendedReconfigurationBuilder)
    (sourceSystem := learnedDecodedAlignedArtifact.system)
    (sourceInput := independentLearnedCertifiedInput)
    (nextInput := independentLearnedCertifiedInput)
  extendedReconfigurationExact :
    extendedReconfiguration = learnedExtendedCertifiedReconfiguration
  alignedSourceTransformationNonidentity :
    learnedAlignedComposedSourceTransformation 0 = 1
  alignedSourceTransformationExact :
    (ActivationOccurrence.neuronOutput learnedAlignedPrimaryNeuron :
      ActivationOccurrence
        (learnedDecodedAlignedArtifact.system.run
          independentLearnedCertifiedInput)).value =
      learnedAlignedComposedSourceTransformation
        (ActivationOccurrence.receivedInput learnedAlignedContextPort :
          ActivationOccurrence
            (learnedDecodedAlignedArtifact.system.run
              independentLearnedCertifiedInput)).value
  extendedSourceTransformationNonidentity :
    learnedExtendedComposedSourceTransformation 0 = 1
  extendedSourceTransformationExact :
    (ActivationOccurrence.neuronOutput learnedExtendedPrimaryNeuron :
      ActivationOccurrence
        (learnedDecodedExtendedArtifact.system.run
          independentLearnedCertifiedInput)).value =
      learnedExtendedComposedSourceTransformation
        (ActivationOccurrence.receivedInput learnedExtendedContextPort :
          ActivationOccurrence
            (learnedDecodedExtendedArtifact.system.run
              independentLearnedCertifiedInput)).value
  declaredInputCoverage : forall current : IndependentLearnedCurrentCase,
    Listed current.input.toRequirementInput independentLearnedDeclaredInputs
  firstProduction : ExecutedTransitionProduction
    learnedTransitionProductionKernel learnedInitialCheckedAgent
      learnedOperationalTransition learnedReferenceTransitionMaterial
  firstProductionExact : firstProduction = learnedReferenceTransitionProduction
  secondProduction : ExecutedTransitionProduction
    learnedTransitionProductionKernel LearnedAlignedCheckedAgent
      learnedExtendedOperationalTransition
      learnedExtendedReferenceTransitionMaterial
  secondProductionExact :
    secondProduction = learnedExtendedReferenceTransitionProduction
  lineage : LearnedArtifactExecutionLineage
  lineageExact : lineage = learnedArtifactExecutionLineage
  lineageSound : EveryCheckedStepSatisfies lineage.trace
  lineagePreservesContracts : EveryCheckedStepPreservesContracts lineage.trace
  initialRuntime : CertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent
  initialRuntimeExact : initialRuntime = learnedInitialCertifiedRuntime
  alignedRuntime : CertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent
  alignedRuntimeExact : alignedRuntime = learnedAlignedCertifiedRuntime
  extendedRuntime : CertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent
  extendedRuntimeExact : extendedRuntime = learnedExtendedCertifiedRuntime
  alignedInstalled :
    submitUpdate learnedInitialCertifiedRuntime learnedAlignedRuntimeUpdate =
      .ok learnedAlignedCertifiedRuntime
  extendedInstalled :
    submitUpdate learnedAlignedCertifiedRuntime
      learnedExtendedSubmittedRuntimeUpdate =
      .ok learnedExtendedCertifiedRuntime
  extendedAccessible : CertifiedRuntimeAccessibility extendedRuntime
  initialCausal : LearnedExecutedCausalWitness learnedInitialState
  initialCausalExact : initialCausal = learnedInitialCausalWitness
  alignedCausal : LearnedExecutedCausalWitness learnedAlignedState
  alignedCausalExact : alignedCausal = learnedAlignedCausalWitness
  extendedCausal : LearnedExecutedCausalWitness learnedExtendedState
  extendedCausalExact : extendedCausal = learnedExtendedCausalWitness
  localReuseLicenses : List (LicensedStructuralTransport
    learnedInitialCheckedAgent.certificate learnedPreCertificateGraph)
  localReuseLicensesExact :
    localReuseLicenses = learnedLicensedStructuralTransports
  localReusePayloadFromLicenses :
    licensedStructuralEntries localReuseLicenses =
      learnedTransportedStructuralFragments
  localReuse : CalculatedIncrementalStructuralAssembly
    learnedInitialCheckedAgent.certificate learnedPreCertificateGraph
      learnedTransportedStructuralFragments learnedRecomputedStructuralFragments
  localReuseExact : localReuse = learnedCalculatedStructuralAssembly
  localReuseInstalled :
    HEq alignedRuntime.current.certificate
      (assembleStateConstitution learnedAlignedTargetAnalysis.fragments)
  firstProducedStateInstalled :
    firstProduction.targetState = alignedRuntime.current.state
  secondProducedStateInstalled :
    secondProduction.targetState = extendedRuntime.current.state
  incrementalFullSuccessorExact :
    learnedAlignedGenericIncrementalSuccess.checked.next =
      learnedAlignedFullRecheckSuccess.checked.next
  incrementalFullCertificateExact :
    learnedAlignedGenericIncrementalSuccess.checked.next.certificate =
      learnedAlignedFullRecheckSuccess.checked.next.certificate
  checkerComplete : forall update : LearnedSerializedConstitutiveUpdate,
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine update ↔
      GenericIncrementalUpdateLocalConditions
        learnedIncrementalCheckerEngine update
  divergence : LearnedOperationalFutureDivergenceCertificate
  divergenceExact : divergence = learnedOperationalFutureDivergence
  futureSourceFromInstalledRuntime :
    LearnedAlignedOperationalContract.futureSourceOfState
        alignedRuntime.current.state =
      learnedCandidateFutureSource divergence.alignedCandidate
  forgetting : LearnedFutureForgettingRC4Certificate
  forgettingExact : forgetting = learnedFutureForgettingRC4
  forgettingConsumesAlignedRuntime :
    LearnedHistoricalStableOrigin.aligned.runtime = alignedRuntime
  renamedHistoryInstalledFromSameInitial :
    submitUpdate learnedInitialCertifiedRuntime
        learnedRenamedIdentityRuntimeUpdate =
      .ok learnedRenamedIdentityCertifiedRuntime
  bypassRejectedBySameInitial :
    submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency
  bypassHasNoInstalledSuccessor :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
        .ok next)

def learnedConstitutiveAlignmentClosure :
    LearnedConstitutiveAlignmentClosureCertificate :=
  { learningProtocol := independentLearningProtocolSha256
    learningProtocolExact := rfl
    learningData := independentLearningDataSha256
    learningDataExact := rfl
    learningGenerator := independentLearningGeneratorSha256
    learningGeneratorExact := rfl
    learnedArtifact := independentLearnedArtifactSha256
    learnedArtifactExact := rfl
    initialArtifactAccepted := independentLearnedInitialNetwork_decodes
    initialAlignedNonidentity := learnedInitialAlignedNeuronCounts_distinct
    alignedExtendedNonidentity := learnedAlignedExtendedNeuronCounts_distinct
    alignedReconfiguration := learnedAlignedCertifiedReconfiguration
    alignedReconfigurationExact := rfl
    extendedReconfiguration := learnedExtendedCertifiedReconfiguration
    extendedReconfigurationExact := rfl
    alignedSourceTransformationNonidentity :=
      learnedAlignedComposedSourceTransformation_nonidentity
    alignedSourceTransformationExact :=
      learnedAlignedComposedSourceTransformation_output_exact
    extendedSourceTransformationNonidentity :=
      learnedExtendedComposedSourceTransformation_nonidentity
    extendedSourceTransformationExact :=
      learnedExtendedComposedSourceTransformation_output_exact
    declaredInputCoverage := independentLearnedDeclaredInputs_complete
    firstProduction := learnedReferenceTransitionProduction
    firstProductionExact := rfl
    secondProduction := learnedExtendedReferenceTransitionProduction
    secondProductionExact := rfl
    lineage := learnedArtifactExecutionLineage
    lineageExact := rfl
    lineageSound := learnedArtifactExecutionLineage.sound
    lineagePreservesContracts :=
      learnedArtifactExecutionLineage.preservesContracts
    initialRuntime := learnedInitialCertifiedRuntime
    initialRuntimeExact := rfl
    alignedRuntime := learnedAlignedCertifiedRuntime
    alignedRuntimeExact := rfl
    extendedRuntime := learnedExtendedCertifiedRuntime
    extendedRuntimeExact := rfl
    alignedInstalled := submitUpdate_learned_aligned_exact
    extendedInstalled := submitUpdate_learned_extended_exact
    extendedAccessible := learnedExtendedCertifiedRuntime_accessibility
    initialCausal := learnedInitialCausalWitness
    initialCausalExact := rfl
    alignedCausal := learnedAlignedCausalWitness
    alignedCausalExact := rfl
    extendedCausal := learnedExtendedCausalWitness
    extendedCausalExact := rfl
    localReuseLicenses := learnedLicensedStructuralTransports
    localReuseLicensesExact := rfl
    localReusePayloadFromLicenses := rfl
    localReuse := learnedCalculatedStructuralAssembly
    localReuseExact := rfl
    localReuseInstalled :=
      learnedAlignedRuntime_certificate_from_generic_checker
    firstProducedStateInstalled := by
      exact Eq.trans (by rfl) learnedAlignedRuntime_state_exact.symm
    secondProducedStateInstalled := by
      rw [learnedExtendedRuntime_state_exact]
      rfl
    incrementalFullSuccessorExact :=
      learnedAlignedIncrementalAndFullSuccessor_exact
    incrementalFullCertificateExact :=
      learnedAlignedIncrementalAndFullCertificate_exact
    checkerComplete := fun update =>
      checkGenericIncrementalUpdate_complete_for_local_conditions
        learnedIncrementalCheckerEngine update
    divergence := learnedOperationalFutureDivergence
    divergenceExact := rfl
    futureSourceFromInstalledRuntime := learnedAlignedRuntime_futureSource_exact
    forgetting := learnedFutureForgettingRC4
    forgettingExact := rfl
    forgettingConsumesAlignedRuntime :=
      learnedAlignedHistoricalOrigin_runtime_exact
    renamedHistoryInstalledFromSameInitial :=
      submitUpdate_learned_renamed_identity_exact
    bypassRejectedBySameInitial := submitUpdate_learned_bypass_rejected
    bypassHasNoInstalledSuccessor := learned_bypass_rejected_without_successor }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedBypassFutureSeparator
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedProducedFutureObservation
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedProducedFutureObservation
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntimeFutureSource_is_produced
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntimeFutureSource_is_produced
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedProducedFutureSource_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedEveryExactRealizationSeparatesAlignedFromBypass
#print axioms ConstitutiveSearch.NeuralAgent.learnedBehavioralFutureRealization
#print axioms ConstitutiveSearch.NeuralAgent.LearnedHistoricalPreActionState
#print axioms ConstitutiveSearch.NeuralAgent.executeLearnedHistoricalPreActionState
#print axioms ConstitutiveSearch.NeuralAgent.transportLearnedRuntimeInputIndex
#print axioms ConstitutiveSearch.NeuralAgent.learnedRuntimeInputSerial_transport_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntimeFirstInputIndex
#print axioms ConstitutiveSearch.NeuralAgent.learnedHistoricalPreActionIdentities_distinct
#print axioms ConstitutiveSearch.NeuralAgent.learnedHistoricalPreAction_runtimeIdentity_exact
#print axioms ConstitutiveSearch.NeuralAgent.transportLearnedAction
#print axioms ConstitutiveSearch.NeuralAgent.transportLearnedAction_heq
#print axioms ConstitutiveSearch.NeuralAgent.transportLearnedAction_effect_targetState
#print axioms ConstitutiveSearch.NeuralAgent.learnedHistoricalActionFor
#print axioms ConstitutiveSearch.NeuralAgent.learnedHistoricalFutureForgetting_targetState_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedHistoricalFutureForgettingProgram
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutedFutureForgetting_preserves_every_finite_future
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutedFutureForgetting_origin_not_recoverable
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedForgottenMemory_is_executedReduction
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_current_is_checkedResult
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingContinuationPermission
#print axioms ConstitutiveSearch.NeuralAgent.learnedJustifiedExtendedTransitionAfterForgetting
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingContractChangePermission
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingTransportedIntent
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingRecheckedAuthorization
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingReturnToInitial_refused
#print axioms ConstitutiveSearch.NeuralAgent.LearnedFutureForgettingRC4Certificate
#print axioms ConstitutiveSearch.NeuralAgent.learnedFutureForgettingRC4
#print axioms ConstitutiveSearch.NeuralAgent.LearnedArtifactExecutionLineage
#print axioms ConstitutiveSearch.NeuralAgent.learnedArtifactExecutionLineage
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedInitialNeuronCount
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFirstSuccessorNeuronCount
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedSecondSuccessorNeuronCount
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialAlignedNeuronCounts_distinct
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedExtendedNeuronCounts_distinct
#print axioms ConstitutiveSearch.NeuralAgent.LearnedArtifactExecutionLineage.sound
#print axioms ConstitutiveSearch.NeuralAgent.LearnedArtifactExecutionLineage.preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedHistoricalOrigin_runtime_exact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedConstitutiveAlignmentClosureCertificate
#print axioms ConstitutiveSearch.NeuralAgent.learnedConstitutiveAlignmentClosure
/- AXIOM_AUDIT_END -/
