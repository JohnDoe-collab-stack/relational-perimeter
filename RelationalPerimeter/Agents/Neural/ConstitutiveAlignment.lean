import RelationalPerimeter.Agents.Neural.PublicExactForgetting

/-!
# Generic constitutive neural alignment chain

The terminal certificate is one dependent chain:

* the incorporated causal role belongs to the exact native run;
* its signal transformation determines the action;
* the executed effect determines the initial reconfigured state;
* that state is consumed by the stagewise reconfigured continuation;
* two distinct historical origins are consumed by one declared forgetting
  program;
* the two computed outputs are each identified with the projection of the
  terminal state produced by that continuation;
* future preservation and non-recoverability are established on those
  computed outputs.

In particular, the forgetting layer cannot be instantiated by wrapping an
independently supplied terminal state in a constant function.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism ContinuationSignatures

/-- Positive evidence that two distinct historical inputs were actually
consumed by the same forgetting program and computed the declared reduced
target. Future preservation and non-recoverability concern those computed
outputs, not states supplied independently after execution. -/
structure ConstitutiveForgettingPolicy
    {History Reduced Input Event Observation : Type 3}
    (program : HistoricalForgettingProgram History Reduced)
    (target : Reduced)
    (contract : FutureContract Reduced Input Event Observation) : Type 4 where
  leftInput : HistoricalForgettingInput program
  rightInput : HistoricalForgettingInput program
  originsDistinct : leftInput.origin ≠ rightInput.origin
  leftExecution : ExecutedHistoricalForgetting program leftInput
  rightExecution : ExecutedHistoricalForgetting program rightInput
  leftOutputExact : leftExecution.output = target
  rightOutputExact : rightExecution.output = target

namespace ConstitutiveForgettingPolicy

theorem outputsEqual
    {History Reduced Input Event Observation : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {target : Reduced}
    {contract : FutureContract Reduced Input Event Observation}
    (policy : ConstitutiveForgettingPolicy program target contract) :
    policy.leftExecution.output = policy.rightExecution.output :=
  policy.leftOutputExact.trans policy.rightOutputExact.symm

theorem futureEquivalent
    {History Reduced Input Event Observation : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {target : Reduced}
    {contract : FutureContract Reduced Input Event Observation}
    (policy : ConstitutiveForgettingPolicy program target contract) :
    FutureEquivalent contract policy.leftExecution.output
      policy.rightExecution.output :=
  ExecutedHistoricalForgetting.same_output_same_future
    policy.leftExecution policy.rightExecution contract policy.outputsEqual

theorem originNotRecoverable
    {History Reduced Input Event Observation : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {target : Reduced}
    {contract : FutureContract Reduced Input Event Observation}
    (policy : ConstitutiveForgettingPolicy program target contract) :
    forall recover : Reduced -> History,
      recover policy.leftExecution.output = policy.leftInput.origin ->
      recover policy.rightExecution.output = policy.rightInput.origin -> False :=
  fun recover leftExact rightExact =>
    ExecutedHistoricalForgetting.origin_not_recoverable
      policy.leftExecution policy.rightExecution policy.originsDistinct
      policy.outputsEqual recover leftExact rightExact

end ConstitutiveForgettingPolicy

/-- A single generic typed witness chain from an executed native role through
action, reconfiguration, continuation, and executed historical forgetting.
The forgetting target is selected from the continuation's produced final
state through `finalProjection`. -/
structure ConstitutiveAlignmentCertificate
    {RequirementCase Context Proposal : Type}
    (family : RequirementFamily RequirementCase Context Proposal)
    (system : NativeSystem (RequirementInput family) Proposal)
    (encoding : RequirementEncoding system)
    (decoder : SingleOutputRequirementDecoder encoding)
    (channel : AgentActionChannel Proposal)
    (builder : ReconfigurationBuilder family)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next))
    (History Reduced : Type 3)
    (source next : RequirementInput family)
    (future : List (RequirementInput family))
    (actionMemory : Agent.Memory)
    (forgettingProgram : HistoricalForgettingProgram History Reduced)
    (finalProjection : ReconfiguredExecutionState family -> Reduced)
    {FutureInput FutureObservation : Type 3}
    (futureContract : FutureContract Reduced FutureInput Agent.Event
      FutureObservation) : Type 4 where
  incorporation : RequirementIncorporation encoding source
  transformation : RequirementSignalTransformation decoder incorporation
  action : ActionRealization channel transformation actionMemory
  effect : EffectRealization action
  initialState : ReconfiguredExecutionState family
  initialSystemExact : initialState.system = system
  initialInputExact : initialState.input = source
  effectConsumed : initialState.memory = effect.successor
  continuation :
    ReconfiguredInteractionHistory builder channel certify
      initialState (next :: future)
  continuationRequestsExact :
    continuation.requests = requiredRequests channel (next :: future)
  continuationExecutionExact :
    (continuation.finalState.memory, continuation.events) =
      Agent.executeRequests initialState.memory continuation.requests
  forgetting : ConstitutiveForgettingPolicy forgettingProgram
    (finalProjection continuation.finalState) futureContract

/-- Assemble the terminal certificate from a dependent chain of generic
witnesses. The forgetting witness must target the projection of this exact
continuation's final state. -/
def assembleConstitutiveAlignment
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system)
    (decoder : SingleOutputRequirementDecoder encoding)
    (channel : AgentActionChannel Proposal)
    (builder : ReconfigurationBuilder family)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next))
    {History Reduced : Type 3}
    {source next : RequirementInput family}
    {future : List (RequirementInput family)}
    (actionMemory : Agent.Memory)
    (forgettingProgram : HistoricalForgettingProgram History Reduced)
    (finalProjection : ReconfiguredExecutionState family -> Reduced)
    {FutureInput FutureObservation : Type 3}
    (futureContract : FutureContract Reduced FutureInput Agent.Event
      FutureObservation)
    (incorporation : RequirementIncorporation encoding source)
    (transformation : RequirementSignalTransformation decoder incorporation)
    (action : ActionRealization channel transformation actionMemory)
    (effect : EffectRealization action)
    (initialState : ReconfiguredExecutionState family)
    (initialSystemExact : initialState.system = system)
    (initialInputExact : initialState.input = source)
    (effectConsumed : initialState.memory = effect.successor)
    (continuation : ReconfiguredInteractionHistory builder channel certify
      initialState (next :: future))
    (forgetting : ConstitutiveForgettingPolicy forgettingProgram
      (finalProjection continuation.finalState) futureContract) :
    ConstitutiveAlignmentCertificate family system encoding decoder channel
      builder certify History Reduced source next future actionMemory
      forgettingProgram finalProjection futureContract :=
  { incorporation := incorporation
    transformation := transformation
    action := action
    effect := effect
    initialState := initialState
    initialSystemExact := initialSystemExact
    initialInputExact := initialInputExact
    effectConsumed := effectConsumed
    continuation := continuation
    continuationRequestsExact := continuation.requests_exact
    continuationExecutionExact := continuation.execution_exact
    forgetting := forgetting }

namespace ConstitutiveAlignmentCertificate

/-- The first continuation stage is available because a terminal alignment
certificate always carries a nonempty continuation indexed by `next :: future`.
This projection exposes the exact certified stage; it does not reconstruct a
stage from graph reachability. -/
def headStage
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {channel : AgentActionChannel Proposal}
    {builder : ReconfigurationBuilder family}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {History Reduced : Type 3}
    {source next : RequirementInput family}
    {future : List (RequirementInput family)}
    {actionMemory : Agent.Memory}
    {forgettingProgram : HistoricalForgettingProgram History Reduced}
    {finalProjection : ReconfiguredExecutionState family -> Reduced}
    {FutureInput FutureObservation : Type 3}
    {futureContract : FutureContract Reduced FutureInput Agent.Event
      FutureObservation}
    (certificate : ConstitutiveAlignmentCertificate family system encoding
      decoder channel builder certify History Reduced source next future
      actionMemory forgettingProgram finalProjection futureContract) :
    ReconfiguredCausalStage builder channel certify certificate.initialState
      next :=
  match certificate.continuation with
  | .step stage _ => stage

end ConstitutiveAlignmentCertificate

/-- C15: an exact scientific decomposition of one terminal certificate.

The fields are deliberately separated by epistemic status.  Received
contracts are recorded as the exact parameters under which the certificate
was built.  Produced facts are execution equations.  Derived facts eliminate
the constitutive witnesses.  Authorization records only the incorporated
permission used by the first reconfiguration.  Preservation, forgetting, and
irrecoverability are then stated independently.

This structure therefore does not promote `Reaches` to interventional
causality, does not receive the final proposal equality as an assumption, does
not call the complete current state a reduced memory, and does not generalize
the public instance beyond the generic certificate from which it is obtained.
-/
structure ConstitutiveScientificDecomposition
    {RequirementCase Context Proposal : Type}
    (family : RequirementFamily RequirementCase Context Proposal)
    (system : NativeSystem (RequirementInput family) Proposal)
    (encoding : RequirementEncoding system)
    (decoder : SingleOutputRequirementDecoder encoding)
    (channel : AgentActionChannel Proposal)
    (builder : ReconfigurationBuilder family)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next))
    (History Reduced : Type 3)
    (source next : RequirementInput family)
    (future : List (RequirementInput family))
    (actionMemory : Agent.Memory)
    (forgettingProgram : HistoricalForgettingProgram History Reduced)
    (finalProjection : ReconfiguredExecutionState family -> Reduced)
    {FutureInput FutureObservation : Type 3}
    (futureContract : FutureContract Reduced FutureInput Agent.Event
      FutureObservation)
    (certificate : ConstitutiveAlignmentCertificate family system encoding
      decoder channel builder certify History Reduced source next future
      actionMemory forgettingProgram finalProjection futureContract) : Type 4 where
  /- Received contracts and mechanisms. -/
  receivedActionContract : AgentActionChannel Proposal
  receivedActionContractExact : receivedActionContract = channel
  receivedReconfigurationContract : ReconfigurationBuilder family
  receivedReconfigurationContractExact :
    receivedReconfigurationContract = builder
  receivedCertifier : (current : ReconfiguredExecutionState family) ->
    (required : RequirementInput family) ->
    CertifiedReconfiguration (builder := builder)
      (sourceSystem := current.system) (sourceInput := current.input)
      (nextInput := required)
  receivedCertifierExact : receivedCertifier = certify
  receivedForgettingProgram : HistoricalForgettingProgram History Reduced
  receivedForgettingProgramExact : receivedForgettingProgram = forgettingProgram
  receivedFutureContract :
    FutureContract Reduced FutureInput Agent.Event FutureObservation
  receivedFutureContractExact : receivedFutureContract = futureContract

  /- Data produced by the declared executions. -/
  producedCausalIncorporation : CausalRole system source
    (.receivedInput encoding.port)
  producedActionExecution :
    certificate.action.result =
      Agent.executeInput actionMemory certificate.action.request
  producedEffectExecution :
    (certificate.effect.successor, certificate.effect.event) =
      Agent.executeInput actionMemory certificate.action.request
  producedContinuationExecution :
    (certificate.continuation.finalState.memory,
      certificate.continuation.events) =
      Agent.executeRequests certificate.initialState.memory
        certificate.continuation.requests
  producedLeftForgettingTrace :
    certificate.forgetting.leftExecution.trace =
      forgettingProgram.execute certificate.forgetting.leftInput.origin
  producedRightForgettingTrace :
    certificate.forgetting.rightExecution.trace =
      forgettingProgram.execute certificate.forgetting.rightInput.origin
  producedLeftForgettingReduction :
    certificate.forgetting.leftExecution.output =
      forgettingProgram.reduce certificate.forgetting.leftInput.origin
        certificate.forgetting.leftExecution.trace
  producedRightForgettingReduction :
    certificate.forgetting.rightExecution.output =
      forgettingProgram.reduce certificate.forgetting.rightInput.origin
        certificate.forgetting.rightExecution.trace
  producedLeftForgettingExecution :
    certificate.forgetting.leftExecution.output =
      forgettingProgram.run certificate.forgetting.leftInput.origin
  producedRightForgettingExecution :
    certificate.forgetting.rightExecution.output =
      forgettingProgram.run certificate.forgetting.rightInput.origin

  /- Conclusions derived by eliminating the constitutive witnesses. -/
  derivedInitialProposal :
    system.proposal source =
      family.requiredProposal source.requirement source.context
  derivedInitialRequest :
    certificate.action.request =
      channel.command
        (family.requiredProposal source.requirement source.context)
  derivedHeadProposal :
    certificate.headStage.proposal =
      family.requiredProposal next.requirement next.context

  /- Authorization is recorded as authorization, not as execution. -/
  authorizedHeadPermission : IncorporatedReconfigurationPermission family
    builder.permissionVariable next
  authorizedHeadPermissionExact :
    authorizedHeadPermission =
      certificate.headStage.action.certificate.configuration.authorization

  /- What the declared future contract preserves. -/
  preservedFuture : FutureEquivalent futureContract
    certificate.forgetting.leftExecution.output
    certificate.forgetting.rightExecution.output

  /- What the executed reduction forgets. -/
  forgottenOriginsDistinct :
    certificate.forgetting.leftInput.origin ≠
      certificate.forgetting.rightInput.origin
  forgottenOutputsEqual :
    certificate.forgetting.leftExecution.output =
      certificate.forgetting.rightExecution.output

  /- What cannot be recovered from the common reduced result. -/
  originIrrecoverable : forall recover : Reduced -> History,
    recover certificate.forgetting.leftExecution.output =
        certificate.forgetting.leftInput.origin ->
    recover certificate.forgetting.rightExecution.output =
        certificate.forgetting.rightInput.origin -> False

/-- Decompose one certificate without adding a new assumption.  Every field is
obtained from the exact witness already consumed by the terminal chain. -/
def decomposeConstitutiveAlignment
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {channel : AgentActionChannel Proposal}
    {builder : ReconfigurationBuilder family}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {History Reduced : Type 3}
    {source next : RequirementInput family}
    {future : List (RequirementInput family)}
    {actionMemory : Agent.Memory}
    {forgettingProgram : HistoricalForgettingProgram History Reduced}
    {finalProjection : ReconfiguredExecutionState family -> Reduced}
    {FutureInput FutureObservation : Type 3}
    {futureContract : FutureContract Reduced FutureInput Agent.Event
      FutureObservation}
    (certificate : ConstitutiveAlignmentCertificate family system encoding
      decoder channel builder certify History Reduced source next future
      actionMemory forgettingProgram finalProjection futureContract) :
    ConstitutiveScientificDecomposition family system encoding decoder channel
      builder certify History Reduced source next future actionMemory
      forgettingProgram finalProjection futureContract certificate :=
  { receivedActionContract := channel
    receivedActionContractExact := rfl
    receivedReconfigurationContract := builder
    receivedReconfigurationContractExact := rfl
    receivedCertifier := certify
    receivedCertifierExact := rfl
    receivedForgettingProgram := forgettingProgram
    receivedForgettingProgramExact := rfl
    receivedFutureContract := futureContract
    receivedFutureContractExact := rfl
    producedCausalIncorporation := certificate.incorporation.role
    producedActionExecution := certificate.action.execution_exact
    producedEffectExecution := certificate.effect.effect_exact
    producedContinuationExecution := certificate.continuationExecutionExact
    producedLeftForgettingTrace :=
      certificate.forgetting.leftExecution.traceExact
    producedRightForgettingTrace :=
      certificate.forgetting.rightExecution.traceExact
    producedLeftForgettingReduction :=
      certificate.forgetting.leftExecution.outputExact
    producedRightForgettingReduction :=
      certificate.forgetting.rightExecution.outputExact
    producedLeftForgettingExecution :=
      certificate.forgetting.leftExecution.executionExact
    producedRightForgettingExecution :=
      certificate.forgetting.rightExecution.executionExact
    derivedInitialProposal := proposal_aligned certificate.transformation
    derivedInitialRequest := certificate.action.request_exact
    derivedHeadProposal := certificate.headStage.proposal_required_exact
    authorizedHeadPermission :=
      certificate.headStage.action.certificate.configuration.authorization
    authorizedHeadPermissionExact := rfl
    preservedFuture := certificate.forgetting.futureEquivalent
    forgottenOriginsDistinct := certificate.forgetting.originsDistinct
    forgottenOutputsEqual := certificate.forgetting.outputsEqual
    originIrrecoverable := certificate.forgetting.originNotRecoverable }

/-- The future contract used after the public forgetting execution. Its source
is already the reduced state: the historical origin is absent from its type. -/
def publicAlignmentFutureContract :
    FutureContract Agent.Memory
      (ULift.{3} Agent.Request) Agent.Event OperationalMemoryReadout :=
  reconfiguredOperationalMemoryFutureContract

/-- The public policy contains the two actual forgetting executions. Both
outputs are connected to the terminal state produced by the same public
continuation. -/
def publicAlignmentForgettingPolicy
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    ConstitutiveForgettingPolicy
      (publicHistoricalForgettingProgram source future)
      (publicReconfiguredInteractionHistory source future).finalState.memory
      publicAlignmentFutureContract :=
  { leftInput := publicLeftHistoricalForgettingInput source future
    rightInput := publicRightHistoricalForgettingInput source future
    originsDistinct := public_historical_operational_states_distinct
    leftExecution := publicLeftExecutedForgetting source future
    rightExecution := publicRightExecutedForgetting source future
    leftOutputExact := public_left_executed_forgetting_exact source future
    rightOutputExact := public_right_executed_forgetting_exact source future }

abbrev PublicConstitutiveAlignmentCertificate
    (source next : PublicRequirementInput)
    (future : List PublicRequirementInput) : Type 4 :=
  ConstitutiveAlignmentCertificate publicRequirementFamily
    publicRequirementSystem publicRequirementEncoding publicRequirementDecoder
    publicAgentActionChannel publicReconfigurationBuilder
    publicReconfigurationCertificateForState PublicHistoricalOperationalState
    Agent.Memory
    source next future publicActionMemory
    (publicHistoricalForgettingProgram source (next :: future))
    ReconfiguredExecutionState.memory
    publicAlignmentFutureContract

namespace PublicConstitutiveAlignmentCertificate

variable {source next : PublicRequirementInput}
    {future : List PublicRequirementInput}

def forgottenLeftInput
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :=
  certificate.forgetting.leftInput

def forgottenRightInput
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :=
  certificate.forgetting.rightInput

def forgottenLeftExecution
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :=
  certificate.forgetting.leftExecution

def forgottenRightExecution
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :=
  certificate.forgetting.rightExecution

theorem forgottenInputsDistinct
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :
    certificate.forgottenLeftInput ≠ certificate.forgottenRightInput :=
  HistoricalForgettingInput.ne_of_origin_ne
    certificate.forgetting.originsDistinct

theorem forgottenLeftExecutionExact
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :
    certificate.forgottenLeftExecution.output =
      certificate.continuation.finalState.memory :=
  certificate.forgetting.leftOutputExact

theorem forgottenRightExecutionExact
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :
    certificate.forgottenRightExecution.output =
      certificate.continuation.finalState.memory :=
  certificate.forgetting.rightOutputExact

theorem forgottenStatesEqual
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :
    certificate.forgottenLeftExecution.output =
      certificate.forgottenRightExecution.output :=
  certificate.forgetting.outputsEqual

theorem forgottenFutureEquivalent
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :
    FutureEquivalent publicAlignmentFutureContract
      certificate.forgottenLeftExecution.output
      certificate.forgottenRightExecution.output :=
  certificate.forgetting.futureEquivalent

theorem forgottenOriginNotRecoverable
    (certificate : PublicConstitutiveAlignmentCertificate source next future) :
    forall recover : Agent.Memory -> PublicHistoricalOperationalState,
      recover certificate.forgottenLeftExecution.output =
          certificate.forgottenLeftInput.origin ->
      recover certificate.forgottenRightExecution.output =
          certificate.forgottenRightInput.origin ->
      False :=
  certificate.forgetting.originNotRecoverable

end PublicConstitutiveAlignmentCertificate

/-- The public certificate specializes the generic terminal constructor to
one actual continuation and the forgetting executions computed from the same
source and future. -/
def constitutive_alignment
    (source next : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    PublicConstitutiveAlignmentCertificate source next future :=
  assembleConstitutiveAlignment publicRequirementEncoding
    publicRequirementDecoder publicAgentActionChannel
    publicReconfigurationBuilder publicReconfigurationCertificateForState
    publicActionMemory
    (publicHistoricalForgettingProgram source (next :: future))
    ReconfiguredExecutionState.memory
    publicAlignmentFutureContract
    (publicRequirementIncorporation source)
    (publicRequirementSignalTransformation source)
    (publicAction source) (publicEffect source)
    (publicInitialReconfiguredState source) rfl rfl rfl
    (publicReconfiguredInteractionHistory source (next :: future))
    (publicAlignmentForgettingPolicy source (next :: future))

/-- The public scientific decomposition is only the specialization of the
generic decomposition to the public certificate.  It does not turn the public
instance into a theorem about arbitrary neural systems. -/
def publicConstitutiveScientificDecomposition
    (source next : PublicRequirementInput)
    (future : List PublicRequirementInput) :=
  decomposeConstitutiveAlignment
    (constitutive_alignment source next future)

/-! ## Closed substantive public instance -/

def publicSubstantiveSource : PublicRequirementInput :=
  ⟨.scopeZero, .direct⟩

def publicSubstantiveNext : PublicRequirementInput :=
  ⟨.scopeOne, .direct⟩

def publicSubstantiveContextualNext : PublicRequirementInput :=
  ⟨.scopeZero, .reversed⟩

def publicSubstantiveAlignment :
    PublicConstitutiveAlignmentCertificate publicSubstantiveSource
      publicSubstantiveNext [publicSubstantiveContextualNext] :=
  constitutive_alignment publicSubstantiveSource publicSubstantiveNext
    [publicSubstantiveContextualNext]

/-- C12 is closed by one concrete instance rather than by an inventory of
unrelated examples.  Its two-step continuation consumes two received
requirements and two contexts.  Every later field is tied either to this exact
alignment chain or to the public reconfiguration mechanism it executes. -/
structure PublicSubstantiveInstanceCertificate : Type 4 where
  requirementsDistinct :
    publicSubstantiveSource.requirement ≠ publicSubstantiveNext.requirement
  contextsDistinct :
    publicSubstantiveSource.context ≠ publicSubstantiveContextualNext.context
  contextualProposalsDistinct :
    publicRequirementFamily.requiredProposal
        publicSubstantiveSource.requirement publicSubstantiveSource.context ≠
      publicRequirementFamily.requiredProposal
        publicSubstantiveContextualNext.requirement
        publicSubstantiveContextualNext.context
  reconfiguredOutputCountNontrivial :
    (publicReconfiguration publicSubstantiveSource
      publicSubstantiveNext).targetSystem.producedCount = 2
  signalTransformationNonidentity :
    publicRequirementEncoding.code publicSubstantiveSource.requirement
        publicSubstantiveSource.context ≠
      publicRequirementDecoder.terminalRepresentation
        publicSubstantiveSource.requirement publicSubstantiveSource.context
  actionPreservesRequiredDistinction :
    DistinctAccordingToActionContract publicAgentActionChannel
      (publicAction publicSubstantiveSource).request
      (publicAction publicSubstantiveNext).request
  sourceStateChangesReconfiguration :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeOne, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩
  nextRequirementChangesReconfiguration :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeOne, .direct⟩).targetSystem.outputValues
        ⟨.scopeOne, .direct⟩
  nextContextChangesReconfiguration :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .reversed⟩).targetSystem.outputValues
        ⟨.scopeZero, .reversed⟩
  authorizationConsumed :
    ((publicReconfiguration publicSubstantiveSource
        publicSubstantiveNext).targetSystem.encode
        publicSubstantiveNext).read
        (publicRequiredMechanismTransport publicSubstantiveSource
          publicSubstantiveNext).authorizationPort =
      publicReconfigurationBuilder.authorizationCode
        publicSubstantiveNext
        (publicReconfiguration publicSubstantiveSource
          publicSubstantiveNext).permission
  continuationHasTwoSteps :
    publicSubstantiveAlignment.continuation.requests.length = 2
  forgettingExecuted :
    publicSubstantiveAlignment.forgottenLeftExecution.output =
      publicSubstantiveAlignment.continuation.finalState.memory
  memoryStrictlyReduced :
    forall recover : Agent.Memory -> PublicHistoricalOrigin,
      recover publicSubstantiveAlignment.forgottenLeftExecution.output =
          publicSubstantiveAlignment.forgottenLeftInput.origin.origin ->
      recover publicSubstantiveAlignment.forgottenRightExecution.output =
          publicSubstantiveAlignment.forgottenRightInput.origin.origin -> False
  futureAdmissionExecuted :
    publicAlignmentFutureContract.enabled
      publicSubstantiveAlignment.continuation.finalState.memory
      publicTerminalAdmittedRequest = true
  futureRefusalExecuted :
    publicAlignmentFutureContract.enabled
      publicSubstantiveAlignment.continuation.finalState.memory
      publicTerminalRefusedRequest = false

def publicSubstantiveInstance : PublicSubstantiveInstanceCertificate where
  requirementsDistinct := by
    intro same
    cases same
  contextsDistinct := by
    intro same
    cases same
  contextualProposalsDistinct := by decide
  reconfiguredOutputCountNontrivial := rfl
  signalTransformationNonidentity :=
    publicRequirementTransformationNonidentity publicSubstantiveSource
  actionPreservesRequiredDistinction :=
    public_actions_preserve_required_proposal_distinction
      publicSubstantiveSource publicSubstantiveNext (by
        change false ≠ true
        intro impossible
        cases impossible)
  sourceStateChangesReconfiguration :=
    public_reconfiguration_source_changes_output
  nextRequirementChangesReconfiguration :=
    public_reconfiguration_requirement_changes_output
  nextContextChangesReconfiguration :=
    public_reconfiguration_context_changes_output
  authorizationConsumed :=
    (publicRequiredMechanismTransport publicSubstantiveSource
      publicSubstantiveNext).authorizationExact
  continuationHasTwoSteps := rfl
  forgettingExecuted :=
    publicSubstantiveAlignment.forgottenLeftExecutionExact
  memoryStrictlyReduced :=
    public_executed_forgetting_origin_not_recoverable
      publicSubstantiveSource
      [publicSubstantiveNext, publicSubstantiveContextualNext]
  futureAdmissionExecuted :=
    public_terminal_admitted_request_enabled publicSubstantiveSource
      [publicSubstantiveNext, publicSubstantiveContextualNext]
  futureRefusalExecuted :=
    public_terminal_refused_request_disabled publicSubstantiveSource
      [publicSubstantiveNext, publicSubstantiveContextualNext]

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveForgettingPolicy
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveForgettingPolicy.outputsEqual
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveForgettingPolicy.futureEquivalent
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveForgettingPolicy.originNotRecoverable
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveAlignmentCertificate
#print axioms ConstitutiveSearch.NeuralAgent.assembleConstitutiveAlignment
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveAlignmentCertificate.headStage
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveScientificDecomposition
#print axioms ConstitutiveSearch.NeuralAgent.decomposeConstitutiveAlignment
#print axioms ConstitutiveSearch.NeuralAgent.publicAlignmentFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.publicAlignmentForgettingPolicy
#print axioms ConstitutiveSearch.NeuralAgent.PublicConstitutiveAlignmentCertificate
#print axioms ConstitutiveSearch.NeuralAgent.constitutive_alignment
#print axioms ConstitutiveSearch.NeuralAgent.publicConstitutiveScientificDecomposition
#print axioms ConstitutiveSearch.NeuralAgent.publicSubstantiveSource
#print axioms ConstitutiveSearch.NeuralAgent.publicSubstantiveNext
#print axioms ConstitutiveSearch.NeuralAgent.publicSubstantiveContextualNext
#print axioms ConstitutiveSearch.NeuralAgent.publicSubstantiveAlignment
#print axioms ConstitutiveSearch.NeuralAgent.PublicSubstantiveInstanceCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicSubstantiveInstance
/- AXIOM_AUDIT_END -/
