import RelationalPerimeter.Agents.Neural.PublicExactForgetting

namespace Tests.Mechanisms.NeuralExactForgettingRegression
open ConstitutiveSearch.NeuralAgent ConstitutiveSearch.ContinuationSignatures

theorem historical_sources_remain_distinct :
    publicLeftHistoricalSource.origin ≠ publicRightHistoricalSource.origin :=
  public_historical_origins_distinct

theorem forgetting_starts_from_executed_action_memory :
    publicLeftHistoricalSource.currentMemory
        publicRequirementSignalTransformation publicAgentActionChannel =
      publicActionMemory :=
  public_left_historical_memory_is_action_memory

theorem future_step_uses_executed_effect
    (input : ULift.{3} PublicRequirementInput) :
    ((interactionFutureContract publicRequirementSignalTransformation
      publicAgentActionChannel).next publicLeftHistoricalSource input).currentMemory
        publicRequirementSignalTransformation publicAgentActionChannel =
      (coveredInteractionEffect publicRequirementSignalTransformation
        publicAgentActionChannel
        (publicLeftHistoricalSource.currentMemory
          publicRequirementSignalTransformation publicAgentActionChannel)
        input.down).successor :=
  interaction_future_next_memory_exact publicRequirementSignalTransformation
    publicAgentActionChannel publicLeftHistoricalSource input

theorem exact_signature_criterion :
    interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicLeftHistoricalSource =
      interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicRightHistoricalSource ↔
    FutureEquivalent
      (interactionFutureContract publicRequirementSignalTransformation
        publicAgentActionChannel)
      publicLeftHistoricalSource publicRightHistoricalSource :=
  forgotten_iff_future_indistinguishable publicRequirementSignalTransformation
    publicAgentActionChannel publicLeftHistoricalSource
    publicRightHistoricalSource

theorem every_covered_future_is_preserved
    (future : List (ULift.{3} PublicRequirementInput)) :
    (interactionFutureContract publicRequirementSignalTransformation
        publicAgentActionChannel).outcome publicLeftHistoricalSource future =
      (interactionFutureContract publicRequirementSignalTransformation
        publicAgentActionChannel).outcome publicRightHistoricalSource future :=
  public_forgotten_sources_same_future future

theorem no_signature_decoder_recovers_both_histories
    (recover : List (Outcome ConstitutiveSearch.Agent.Event
      ConstitutiveSearch.Agent.Memory) -> PublicHistoricalOrigin)
    (leftExact :
      recover (interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicLeftHistoricalSource) =
          publicLeftHistoricalSource.origin)
    (rightExact :
      recover (interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicRightHistoricalSource) =
          publicRightHistoricalSource.origin) : False :=
  public_historical_origin_not_recoverable recover leftExact rightExact

theorem executed_forgetting_inputs_are_distinct
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    publicLeftHistoricalForgettingInput source future ≠
      publicRightHistoricalForgettingInput source future :=
  public_historical_forgetting_inputs_distinct source future

theorem operational_sources_are_distinct_before_forgetting :
    publicLeftHistoricalOperationalState ≠
      publicRightHistoricalOperationalState :=
  public_historical_operational_states_distinct

theorem operational_sources_retain_distinct_origins_before_forgetting :
    publicLeftHistoricalOperationalState.origin ≠
      publicRightHistoricalOperationalState.origin :=
  public_historical_origins_distinct

theorem operational_current_states_are_distinct_before_forgetting :
    publicLeftHistoricalOperationalState.current ≠
      publicRightHistoricalOperationalState.current :=
  public_historical_current_states_distinct

theorem operational_current_inputs_are_distinct_before_forgetting :
    publicLeftHistoricalOperationalState.current.input ≠
      publicRightHistoricalOperationalState.current.input :=
  public_historical_current_inputs_distinct

def left_forgetting_has_an_executed_head
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :=
  (publicLeftExecutedForgetting source future).trace.headStage

def right_forgetting_has_an_executed_head
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :=
  (publicRightExecutedForgetting source future).trace.headStage

theorem executed_heads_produce_the_same_memory
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).trace.headStage.nextState.memory =
      (publicRightExecutedForgetting source future).trace.headStage.nextState.memory :=
  public_forgetting_head_memories_equal source future

theorem left_forgetting_retains_the_executed_trace
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).trace =
      executePublicHistoricalForgettingTrace
        publicLeftHistoricalOperationalState source future :=
  public_left_forgetting_trace_exact source future

theorem left_forgetting_output_is_read_from_its_trace
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicLeftExecutedForgetting source future).trace.finalState.memory :=
  public_left_forgetting_output_is_trace_memory source future

theorem left_forgetting_output_is_executed_continuation
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicReconfiguredInteractionHistory source future).finalState.memory :=
  public_left_executed_forgetting_exact source future

theorem right_forgetting_output_is_executed_continuation
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicRightExecutedForgetting source future).output =
      (publicReconfiguredInteractionHistory source future).finalState.memory :=
  public_right_executed_forgetting_exact source future

theorem forgetting_output_equality_is_execution_derived
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicRightExecutedForgetting source future).output :=
  public_executed_forgetting_outputs_equal source future

theorem executed_forgetting_preserves_every_future
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    FutureEquivalent
      reconfiguredOperationalMemoryFutureContract
      (publicLeftExecutedForgetting source future).output
      (publicRightExecutedForgetting source future).output :=
  public_executed_forgetting_preserves_future source future

theorem complete_state_and_reduced_memory_have_identical_covered_outcomes
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (requests : List (ULift.{3} ConstitutiveSearch.Agent.Request)) :
    (reconfiguredOperationalStateFutureContract
        (family := publicRequirementFamily)).outcome
        (publicReconfiguredInteractionHistory source future).finalState requests =
      reconfiguredOperationalMemoryFutureContract.outcome
        (publicReconfiguredInteractionHistory source future).finalState.memory
        requests :=
  public_terminal_memory_preserves_every_future source future requests

def reduced_memory_preserves_authorization_forward
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (input : ULift.{3} ConstitutiveSearch.Agent.Request)
    (witness : (reconfiguredOperationalStateFutureContract
      (family := publicRequirementFamily)).Allow state input) :
    reconfiguredOperationalMemoryFutureContract.Allow state.memory input :=
  publicReconfiguredOperationalMemoryRealization.forward state input witness

def reduced_memory_preserves_authorization_backward
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (input : ULift.{3} ConstitutiveSearch.Agent.Request)
    (witness : reconfiguredOperationalMemoryFutureContract.Allow
      state.memory input) :
    (reconfiguredOperationalStateFutureContract
      (family := publicRequirementFamily)).Allow state input :=
  publicReconfiguredOperationalMemoryRealization.backward state input witness

theorem reduced_memory_next_is_exact
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (input : ULift.{3} ConstitutiveSearch.Agent.Request) :
    ((reconfiguredOperationalStateFutureContract
      (family := publicRequirementFamily)).next state input).memory =
      reconfiguredOperationalMemoryFutureContract.next state.memory input :=
  publicReconfiguredOperationalMemoryRealization.next_exact state input

theorem reduced_memory_event_is_exact
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (input : ULift.{3} ConstitutiveSearch.Agent.Request) :
    (reconfiguredOperationalStateFutureContract
      (family := publicRequirementFamily)).event state input =
      reconfiguredOperationalMemoryFutureContract.event state.memory input :=
  publicReconfiguredOperationalMemoryRealization.event_exact state input

theorem reduced_memory_readout_is_exact
    (state : ReconfiguredExecutionState publicRequirementFamily) :
    (reconfiguredOperationalStateFutureContract
      (family := publicRequirementFamily)).read state =
      reconfiguredOperationalMemoryFutureContract.read state.memory :=
  publicReconfiguredOperationalMemoryRealization.read_exact state

theorem terminal_contract_executes_an_admission
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    reconfiguredOperationalMemoryFutureContract.enabled
      (publicReconfiguredInteractionHistory source future).finalState.memory
      publicTerminalAdmittedRequest = true :=
  public_terminal_admitted_request_enabled source future

theorem terminal_contract_executes_a_refusal
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    reconfiguredOperationalMemoryFutureContract.enabled
      (publicReconfiguredInteractionHistory source future).finalState.memory
      publicTerminalRefusedRequest = false :=
  public_terminal_refused_request_disabled source future

theorem immediate_readout_does_not_expose_every_future_distinction :
    reconfiguredOperationalMemoryFutureContract.read
        publicTerminalSeparatorLeft =
      reconfiguredOperationalMemoryFutureContract.read
        publicTerminalSeparatorRight :=
  public_terminal_separator_same_immediate_readout

theorem a_nonempty_future_distinguishes_the_separator :
    reconfiguredOperationalMemoryFutureContract.outcome
        publicTerminalSeparatorLeft [publicTerminalSeparatingRequest] ≠
      reconfiguredOperationalMemoryFutureContract.outcome
        publicTerminalSeparatorRight [publicTerminalSeparatingRequest] :=
  public_terminal_nonempty_future_is_necessary

theorem executed_forgetting_cannot_recover_both_origins
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (recover : ConstitutiveSearch.Agent.Memory -> PublicHistoricalOrigin)
    (leftExact :
      recover (publicLeftExecutedForgetting source future).output =
        (publicLeftHistoricalForgettingInput source future).origin.origin)
    (rightExact :
      recover (publicRightExecutedForgetting source future).output =
        (publicRightHistoricalForgettingInput source future).origin.origin) : False :=
  public_executed_forgetting_origin_not_recoverable source future recover
    leftExact rightExact

end Tests.Mechanisms.NeuralExactForgettingRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.historical_sources_remain_distinct
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.forgetting_starts_from_executed_action_memory
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.future_step_uses_executed_effect
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.exact_signature_criterion
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.every_covered_future_is_preserved
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.no_signature_decoder_recovers_both_histories
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.executed_forgetting_inputs_are_distinct
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.operational_sources_are_distinct_before_forgetting
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.operational_sources_retain_distinct_origins_before_forgetting
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.operational_current_states_are_distinct_before_forgetting
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.operational_current_inputs_are_distinct_before_forgetting
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.left_forgetting_has_an_executed_head
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.right_forgetting_has_an_executed_head
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.executed_heads_produce_the_same_memory
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.left_forgetting_retains_the_executed_trace
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.left_forgetting_output_is_read_from_its_trace
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.left_forgetting_output_is_executed_continuation
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.right_forgetting_output_is_executed_continuation
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.forgetting_output_equality_is_execution_derived
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.executed_forgetting_preserves_every_future
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.complete_state_and_reduced_memory_have_identical_covered_outcomes
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.reduced_memory_preserves_authorization_forward
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.reduced_memory_preserves_authorization_backward
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.reduced_memory_next_is_exact
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.reduced_memory_event_is_exact
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.reduced_memory_readout_is_exact
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.terminal_contract_executes_an_admission
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.terminal_contract_executes_a_refusal
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.immediate_readout_does_not_expose_every_future_distinction
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.a_nonempty_future_distinguishes_the_separator
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.executed_forgetting_cannot_recover_both_origins
/- AXIOM_AUDIT_END -/
