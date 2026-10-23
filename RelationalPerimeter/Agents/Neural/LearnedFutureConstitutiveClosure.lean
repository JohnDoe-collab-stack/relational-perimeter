import RelationalPerimeter.Agents.Neural.LearnedContractFutureDivergence
import RelationalPerimeter.Agents.Neural.ReconfiguredExactForgetting
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

def LearnedHistoricalStableOrigin.runtimeFirstInputSerial :
    LearnedHistoricalStableOrigin -> Nat
  | .aligned =>
      learnedAlignedCertifiedRuntime.current.certificate.basis.naming.inputSerial
        ⟨0, by decide⟩
  | .renamed =>
      learnedRenamedIdentityCertifiedRuntime.current.certificate.basis.naming.inputSerial
        ⟨0, by decide⟩

theorem LearnedHistoricalStableOrigin.runtime_state_exact
    (origin : LearnedHistoricalStableOrigin) :
    origin.runtime.current.state = learnedAlignedState := by
  cases origin <;> rfl

theorem LearnedHistoricalStableOrigin.runtime_identity_exact
    (origin : LearnedHistoricalStableOrigin) :
    origin.runtimeFirstInputSerial = origin.firstInputSerial := by
  cases origin <;> rfl

theorem learnedHistoricalStableOrigins_distinct :
    LearnedHistoricalStableOrigin.aligned ≠
      LearnedHistoricalStableOrigin.renamed := by
  intro impossible
  cases impossible

theorem learnedHistoricalStableOrigin_identities_distinct :
    LearnedHistoricalStableOrigin.aligned.firstInputSerial ≠
      LearnedHistoricalStableOrigin.renamed.firstInputSerial := by
  decide

structure LearnedHistoricalFutureForgettingTrace
    (origin : LearnedHistoricalStableOrigin) : Type 3 where
  historicalNaming : SerializedStableArtifactNaming
  historicalNamingExact : historicalNaming = origin.serializedNaming
  runtimeStateExact : origin.runtime.current.state = learnedAlignedState
  installedIdentityExact : origin.runtimeFirstInputSerial =
    origin.firstInputSerial
  action : LearnedActionWitness origin.runtime.current.state
  effect : LearnedEffectWitness origin.runtime.current.state
  effectExact : effect = produceLearnedEffect action

def executeLearnedHistoricalFutureForgettingTrace
    (origin : LearnedHistoricalStableOrigin) :
    LearnedHistoricalFutureForgettingTrace origin := by
  cases origin with
  | aligned =>
      exact
        { historicalNaming := learnedAlignedSerializedNaming
          historicalNamingExact := rfl
          runtimeStateExact := rfl
          installedIdentityExact := rfl
          action := learnedAlignedAction
          effect := learnedAlignedEffect
          effectExact := rfl }
  | renamed =>
      exact
        { historicalNaming := learnedRenamedSerializedNaming
          historicalNamingExact := rfl
          runtimeStateExact := rfl
          installedIdentityExact := rfl
          action := learnedAlignedAction
          effect := learnedAlignedEffect
          effectExact := rfl }

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

theorem learnedHistoricalForgettingInputs_distinct :
    learnedAlignedHistoricalForgettingInput ≠
      learnedRenamedHistoricalForgettingInput :=
  HistoricalForgettingInput.ne_of_origin_ne
    learnedHistoricalStableOrigins_distinct

theorem learnedExecutedFutureForgetting_outputs_equal :
    learnedAlignedExecutedFutureForgetting.output =
      learnedRenamedExecutedFutureForgetting.output := by
  rfl

theorem learnedExecutedFutureForgetting_output_exact
    (origin : LearnedHistoricalStableOrigin) :
    (executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
      { origin := origin }).output =
      independentLearnedFutureProjection
        (LearnedAlignedOperationalContract.futureSourceOfState
          learnedAlignedEffect.targetState) := by
  cases origin <;> rfl

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

/-! ## Contract change after forgetting -/

inductive LearnedPostForgettingRequest : Type 3 where
  | continueFuture (input : IndependentLearnedFutureInput)
  | recoverHistoricalIdentity

inductive LearnedPostForgettingPermission
    (memory : IndependentLearnedOperationalMemory) :
    LearnedPostForgettingRequest -> Type 3 where
  | continueFuture
      (input : IndependentLearnedFutureInput)
      (admitted : independentLearnedReducedFutureContract.Allow memory input) :
      LearnedPostForgettingPermission memory (.continueFuture input)

def decideLearnedPostForgettingRequest
    (memory : IndependentLearnedOperationalMemory)
    (request : LearnedPostForgettingRequest) :
    PSum (LearnedPostForgettingPermission memory request)
      (LearnedPostForgettingPermission memory request -> False) :=
  match request with
  | .recoverHistoricalIdentity => .inr (fun witness => nomatch witness)
  | .continueFuture input =>
      match independentLearnedReducedFutureContract.decision memory input with
      | .inl admitted => .inl (.continueFuture input admitted)
      | .inr refused => .inr (fun witness => by
          cases witness with
          | continueFuture _ admitted => exact refused admitted)

def learnedPostForgettingContinuationPermission :
    LearnedPostForgettingPermission
      learnedAlignedExecutedFutureForgetting.output
      (.continueFuture learnedAdmittedFutureRequest) :=
  .continueFuture learnedAdmittedFutureRequest
    learnedAdmittedFutureRequestWitness

theorem learnedPostForgettingRecovery_refused
    (permission : LearnedPostForgettingPermission
      learnedAlignedExecutedFutureForgetting.output
      .recoverHistoricalIdentity) : False := by
  nomatch permission

theorem learnedPostForgettingRefusedFuture_stays_refused
    (permission : LearnedPostForgettingPermission
      learnedAlignedExecutedFutureForgetting.output
      (.continueFuture learnedRefusedFutureRequest)) : False := by
  cases permission with
  | continueFuture _ admitted =>
      exact learnedRefusedFutureRequest_has_no_witness admitted

/-! ## One closed L4 / RC4 witness -/

structure LearnedFutureForgettingRC4Certificate : Type 5 where
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
  continuationTransported : LearnedPostForgettingPermission
    learnedAlignedExecutedFutureForgetting.output
    (.continueFuture learnedAdmittedFutureRequest)
  refusedContinuationRejected : LearnedPostForgettingPermission
      learnedAlignedExecutedFutureForgetting.output
      (.continueFuture learnedRefusedFutureRequest) -> False
  recoveryRefused : LearnedPostForgettingPermission
      learnedAlignedExecutedFutureForgetting.output
      .recoverHistoricalIdentity -> False

def learnedFutureForgettingRC4 : LearnedFutureForgettingRC4Certificate :=
  { futureSourceExact := learnedAlignedRuntime_futureSource_exact
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
    continuationTransported := learnedPostForgettingContinuationPermission
    refusedContinuationRejected :=
      learnedPostForgettingRefusedFuture_stays_refused
    recoveryRefused := learnedPostForgettingRecovery_refused }

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
    secondAccepted := rfl
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
  learnedArtifact : String
  learnedArtifactExact : learnedArtifact = independentLearnedArtifactSha256
  initialArtifactAccepted : independentLearnedInitialNetworkAccepted = true
  initialAlignedNonidentity : independentLearnedInitialNetwork.neurons.length ≠
    independentLearnedFirstSuccessorNetwork.neurons.length
  alignedExtendedNonidentity :
    independentLearnedFirstSuccessorNetwork.neurons.length ≠
      independentLearnedSecondSuccessorNetwork.neurons.length
  declaredInputCoverage : forall current : IndependentLearnedCurrentCase,
    Listed current.input.toRequirementInput independentLearnedDeclaredInputs
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
    submitUpdate learnedAlignedCertifiedRuntime learnedExtendedRuntimeUpdate =
      .ok learnedExtendedCertifiedRuntime
  extendedAccessible : CertifiedRuntimeAccessibility extendedRuntime
  initialCausal : LearnedExecutedCausalWitness learnedInitialState
  initialCausalExact : initialCausal = learnedInitialCausalWitness
  alignedCausal : LearnedExecutedCausalWitness learnedAlignedState
  alignedCausalExact : alignedCausal = learnedAlignedCausalWitness
  extendedCausal : LearnedExecutedCausalWitness learnedExtendedState
  extendedCausalExact : extendedCausal = learnedExtendedCausalWitness
  localReuse : CalculatedIncrementalStructuralAssembly
    learnedInitialCheckedAgent.certificate learnedPreCertificateGraph
      learnedTransportedStructuralFragments learnedRecomputedStructuralFragments
  localReuseExact : localReuse = learnedCalculatedStructuralAssembly
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
    learnedArtifact := independentLearnedArtifactSha256
    learnedArtifactExact := rfl
    initialArtifactAccepted := independentLearnedInitialNetwork_decodes
    initialAlignedNonidentity := learnedInitialAlignedNeuronCounts_distinct
    alignedExtendedNonidentity := learnedAlignedExtendedNeuronCounts_distinct
    declaredInputCoverage := independentLearnedDeclaredInputs_complete
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
    localReuse := learnedCalculatedStructuralAssembly
    localReuseExact := rfl
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
#print axioms ConstitutiveSearch.NeuralAgent.learnedEveryExactRealizationSeparatesAlignedFromBypass
#print axioms ConstitutiveSearch.NeuralAgent.learnedBehavioralFutureRealization
#print axioms ConstitutiveSearch.NeuralAgent.learnedHistoricalFutureForgettingProgram
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutedFutureForgetting_preserves_every_finite_future
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutedFutureForgetting_origin_not_recoverable
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingRecovery_refused
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
