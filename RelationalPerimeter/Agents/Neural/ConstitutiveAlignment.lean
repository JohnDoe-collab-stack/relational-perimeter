import RelationalPerimeter.Agents.Neural.PublicExactForgetting

/-!
# Closed constitutive neural alignment chain

The final result is data in `Type`, not a conjunction of independently closed
propositions. Its fields form one dependent chain:

* the incorporated causal role belongs to the exact native run;
* its signal preservation determines the action;
* the executed effect determines the initial reconfigured state;
* that state is consumed by the stagewise reconfigured continuation;
* the final state produced by that continuation initializes the
  exact-forgetting realization.

Consequently no witness can be replaced by an unrelated inhabitant hidden
behind `Nonempty`, and no fixed pre-reconfiguration system can be used for the
recursive tail.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism ContinuationSignatures

/-- A single typed witness chain from the executed native role through action,
reconfiguration, continuation, and exact historical forgetting. -/
structure ConstitutiveAlignmentCertificate
    (source next : PublicRequirementInput)
    (future : List PublicRequirementInput) : Type 4 where
  incorporation :
    RequirementIncorporation publicRequirementEncoding source
  preservation :
    RequirementSignalPreservation publicRequirementDecoder incorporation
  action :
    ActionRealization publicAgentActionChannel preservation publicActionMemory
  effect : EffectRealization action
  initialState : ReconfiguredExecutionState publicRequirementFamily
  initialSystemExact : initialState.system = publicRequirementSystem
  initialInputExact : initialState.input = source
  effectConsumed : initialState.memory = effect.successor
  continuation :
    ReconfiguredInteractionHistory publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      initialState (next :: future)
  continuationRequestsExact :
    continuation.requests =
      requiredRequests publicAgentActionChannel (next :: future)
  continuationExecutionExact :
    (continuation.finalState.memory, continuation.events) =
      Agent.executeRequests initialState.memory continuation.requests
  forgettingInitialState :
    PublicHistoricalOrigin ->
      ReconfiguredExecutionState publicRequirementFamily
  forgettingInitialExact :
    forall origin, forgettingInitialState origin = continuation.finalState
  forgottenLeft :
    ReconfiguredHistoricalSource PublicHistoricalOrigin
      publicRequirementFamily publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      forgettingInitialState
  forgottenRight :
    ReconfiguredHistoricalSource PublicHistoricalOrigin
      publicRequirementFamily publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      forgettingInitialState
  forgottenOriginsDistinct : forgottenLeft.origin ≠ forgottenRight.origin
  forgottenStatesEqual : forgottenLeft.currentState = forgottenRight.currentState
  forgettingRealization :
    ExactRealization
      (reconfiguredFutureContract
        (channel := publicAgentActionChannel)
        (certify := publicReconfigurationCertificateForState)
        (initialState := forgettingInitialState))
      (ReconfiguredExecutionState publicRequirementFamily)
  forgottenFutureEquivalent :
    FutureEquivalent
      (reconfiguredFutureContract
        (channel := publicAgentActionChannel)
        (certify := publicReconfigurationCertificateForState)
        (initialState := forgettingInitialState))
      forgottenLeft forgottenRight
  forgottenOriginNotRecoverable :
    forall recover : ReconfiguredExecutionState publicRequirementFamily ->
        PublicHistoricalOrigin,
      recover forgottenLeft.currentState = forgottenLeft.origin ->
      recover forgottenRight.currentState = forgottenRight.origin -> False

/-- The public certificate is constructed entirely from the public execution.
Every recursive continuation step consumes the target state produced by the
preceding reconfiguration, and exact forgetting consumes the final state
produced by that continuation. -/
def constitutive_alignment
    (source next : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    ConstitutiveAlignmentCertificate source next future := by
  let incorporation := publicRequirementIncorporation source
  let preservation := publicRequirementSignalPreservation source
  let action := publicAction source
  let effect := publicEffect source
  let initialState := publicInitialReconfiguredState source
  let continuation :=
    publicReconfiguredInteractionHistory source (next :: future)
  let forgettingInitialState :
      PublicHistoricalOrigin ->
        ReconfiguredExecutionState publicRequirementFamily :=
    fun _ => continuation.finalState
  let forgottenLeft :
      ReconfiguredHistoricalSource PublicHistoricalOrigin
        publicRequirementFamily publicReconfigurationBuilder
        publicAgentActionChannel publicReconfigurationCertificateForState
        forgettingInitialState :=
    .initial (ULift.up publicHistoricalMaster.distinctPair.left)
  let forgottenRight :
      ReconfiguredHistoricalSource PublicHistoricalOrigin
        publicRequirementFamily publicReconfigurationBuilder
        publicAgentActionChannel publicReconfigurationCertificateForState
        forgettingInitialState :=
    .initial (ULift.up publicHistoricalMaster.distinctPair.right)
  have originsDistinct : forgottenLeft.origin ≠ forgottenRight.origin :=
    fun same => publicHistoricalMaster.distinctPair.distinct
      (congrArg ULift.down same)
  have statesEqual : forgottenLeft.currentState = forgottenRight.currentState :=
    rfl
  exact
    { incorporation := incorporation
      preservation := preservation
      action := action
      effect := effect
      initialState := initialState
      initialSystemExact := rfl
      initialInputExact := rfl
      effectConsumed := rfl
      continuation := continuation
      continuationRequestsExact := continuation.requests_exact
      continuationExecutionExact := continuation.execution_exact
      forgettingInitialState := forgettingInitialState
      forgettingInitialExact := fun _ => rfl
      forgottenLeft := forgottenLeft
      forgottenRight := forgottenRight
      forgottenOriginsDistinct := originsDistinct
      forgottenStatesEqual := statesEqual
      forgettingRealization :=
        reconfiguredStateRealization
          (channel := publicAgentActionChannel)
          (certify := publicReconfigurationCertificateForState)
          (initialState := forgettingInitialState)
      forgottenFutureEquivalent :=
        reconfigured_same_state_same_future statesEqual
      forgottenOriginNotRecoverable := fun recover left right =>
        reconfigured_origin_not_recoverable forgottenLeft forgottenRight
          originsDistinct statesEqual recover left right }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveAlignmentCertificate
#print axioms ConstitutiveSearch.NeuralAgent.constitutive_alignment
/- AXIOM_AUDIT_END -/
