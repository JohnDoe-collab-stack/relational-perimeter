import RelationalPerimeter.Agents.Neural.PublicActionRealization
import RelationalPerimeter.Agents.Neural.ExactForgetting
import RelationalPerimeter.Agents.Neural.ReconfiguredExactForgetting

/-! Closed public witness of exact produced-origin forgetting. -/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures EndogenousDecomposition

def publicHistoricalMaster : UnifiedMaster.Instance 0 :=
  UnifiedMaster.publicInstance 0

def publicHistoricalRequirement : Agent.Requirement :=
  Agent.singletonRequirement 0

abbrev PublicHistoricalOrigin : Type 3 :=
  ULift.{3} (RoleOccurrenceProfile publicHistoricalMaster.roles)

def publicHistoricalInitialMemory
    (origin : PublicHistoricalOrigin) : Agent.Memory :=
  Agent.start publicHistoricalMaster publicHistoricalRequirement origin.down

abbrev PublicHistoricalInteractionSource : Type 3 :=
  HistoricalInteractionSource PublicHistoricalOrigin
    publicHistoricalInitialMemory publicRequirementFamily

def publicLeftHistoricalSource : PublicHistoricalInteractionSource :=
  .initial (ULift.up publicHistoricalMaster.distinctPair.left)

def publicRightHistoricalSource : PublicHistoricalInteractionSource :=
  .initial (ULift.up publicHistoricalMaster.distinctPair.right)

theorem public_historical_origins_distinct :
    publicLeftHistoricalSource.origin ≠ publicRightHistoricalSource.origin :=
  fun same => publicHistoricalMaster.distinctPair.distinct
    (congrArg ULift.down same)

theorem public_historical_memories_equal :
    publicLeftHistoricalSource.currentMemory
        publicRequirementSignalTransformation publicAgentActionChannel =
      publicRightHistoricalSource.currentMemory
        publicRequirementSignalTransformation publicAgentActionChannel :=
  Agent.initial_memories_equal publicHistoricalMaster
    publicHistoricalRequirement publicHistoricalMaster.distinctPair.left
    publicHistoricalMaster.distinctPair.right

theorem public_left_historical_memory_is_action_memory :
    publicLeftHistoricalSource.currentMemory
        publicRequirementSignalTransformation publicAgentActionChannel =
      publicActionMemory :=
  rfl

theorem public_forgotten_sources_same_signature :
    interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicLeftHistoricalSource =
      interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicRightHistoricalSource :=
  same_memory_same_interaction_signature publicRequirementSignalTransformation
    publicAgentActionChannel public_historical_memories_equal

theorem public_forgotten_sources_same_future :
    FutureEquivalent
      (interactionFutureContract publicRequirementSignalTransformation
        publicAgentActionChannel)
      publicLeftHistoricalSource publicRightHistoricalSource :=
  (forgotten_iff_future_indistinguishable publicRequirementSignalTransformation
    publicAgentActionChannel publicLeftHistoricalSource
    publicRightHistoricalSource).mp public_forgotten_sources_same_signature

theorem public_historical_origin_not_recoverable
    (recover : List (Outcome Agent.Event Agent.Memory) -> PublicHistoricalOrigin)
    (recoversLeft :
      recover (interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicLeftHistoricalSource) =
          publicLeftHistoricalSource.origin)
    (recoversRight :
      recover (interactionSignature publicRequirementSignalTransformation
        publicAgentActionChannel publicRightHistoricalSource) =
          publicRightHistoricalSource.origin) : False :=
  forgotten_origin_not_recoverable publicRequirementSignalTransformation
    publicAgentActionChannel publicLeftHistoricalSource
    publicRightHistoricalSource public_historical_origins_distinct
    public_historical_memories_equal recover recoversLeft recoversRight

/-- Execute the source action from an explicitly supplied historical memory.
No terminal state is supplied independently. -/
def publicHistoricalInitialReconfiguredStateFromMemory
    (memory : Agent.Memory) (source : PublicRequirementInput) :
    ReconfiguredExecutionState publicRequirementFamily :=
  { system := publicRequirementSystem
    input := source
    memory :=
      (realizeEffect
        (realizeAction publicAgentActionChannel
          (publicRequirementSignalTransformation source) memory)).successor }

/-- Run the complete reconfigured continuation from the historical memory and
return the terminal state produced by that execution. -/
def publicHistoricalTerminalStateFromMemory
    (memory : Agent.Memory) (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    ReconfiguredExecutionState publicRequirementFamily :=
  (executeReconfiguredInteractions publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    (publicHistoricalInitialReconfiguredStateFromMemory memory source)
    future).finalState

/-- The historical origin is consumed by the actual initial-memory
construction and then by the complete source-action and reconfiguration
execution. -/
def publicHistoricalTerminalState
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (origin : PublicHistoricalOrigin) :
    ReconfiguredExecutionState publicRequirementFamily :=
  publicHistoricalTerminalStateFromMemory
    (publicHistoricalInitialMemory origin) source future

theorem public_historical_initial_memory_eq_action_memory
    (origin : PublicHistoricalOrigin) :
    publicHistoricalInitialMemory origin = publicActionMemory :=
  (Agent.initial_memories_equal publicHistoricalMaster
    publicHistoricalRequirement origin.down
    publicHistoricalMaster.distinctPair.left).trans rfl

theorem public_historical_terminal_state_exact
    (origin : PublicHistoricalOrigin) (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    publicHistoricalTerminalState source future origin =
      (publicReconfiguredInteractionHistory source future).finalState := by
  unfold publicHistoricalTerminalState
  rw [public_historical_initial_memory_eq_action_memory]
  rfl

/-- The strictly reduced output of the historical execution.  It is computed
from the complete terminal state but retains only its operational memory;
the terminal native system and requirement are absent. -/
def publicHistoricalTerminalMemory
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (origin : PublicHistoricalOrigin) : Agent.Memory :=
  (publicHistoricalTerminalState source future origin).memory

theorem public_historical_terminal_memory_exact
    (origin : PublicHistoricalOrigin) (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    publicHistoricalTerminalMemory source future origin =
      (publicReconfiguredInteractionHistory source future).finalState.memory :=
  congrArg ReconfiguredExecutionState.memory
    (public_historical_terminal_state_exact origin source future)

/-- The operational input before forgetting.  Unlike `Agent.Memory`, this
state positively retains the constituted origin together with the exact memory
from which the continuation must execute.  The origin is therefore present in
the operational source and is removed only by the executed projection below. -/
structure PublicHistoricalOperationalState : Type 3 where
  origin : PublicHistoricalOrigin
  memory : Agent.Memory
  memoryExact : memory = publicHistoricalInitialMemory origin

def publicHistoricalOperationalState
    (origin : PublicHistoricalOrigin) : PublicHistoricalOperationalState :=
  { origin := origin
    memory := publicHistoricalInitialMemory origin
    memoryExact := rfl }

def publicLeftHistoricalOperationalState :
    PublicHistoricalOperationalState :=
  publicHistoricalOperationalState
    (ULift.up publicHistoricalMaster.distinctPair.left)

def publicRightHistoricalOperationalState :
    PublicHistoricalOperationalState :=
  publicHistoricalOperationalState
    (ULift.up publicHistoricalMaster.distinctPair.right)

theorem public_historical_operational_states_distinct :
    publicLeftHistoricalOperationalState ≠
      publicRightHistoricalOperationalState := by
  intro same
  exact public_historical_origins_distinct
    (congrArg PublicHistoricalOperationalState.origin same)

/-- The source-indexed trace executed before forgetting.  Its initial state is
built from the memory carried by the rich historical source. -/
abbrev PublicHistoricalForgettingTrace
    (historical : PublicHistoricalOperationalState)
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :=
  ReconfiguredInteractionHistory publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    (publicHistoricalInitialReconfiguredStateFromMemory historical.memory source)
    future

def executePublicHistoricalForgettingTrace
    (historical : PublicHistoricalOperationalState)
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    PublicHistoricalForgettingTrace historical source future :=
  executeReconfiguredInteractions publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    (publicHistoricalInitialReconfiguredStateFromMemory historical.memory source)
    future

/-- Read only the terminal memory from the executed, source-indexed trace. -/
def reducePublicHistoricalForgettingTrace
    (historical : PublicHistoricalOperationalState)
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (trace : PublicHistoricalForgettingTrace historical source future) :
    Agent.Memory :=
  trace.finalState.memory

/-- Execute the complete continuation from the historically informed
operational state and return only the terminal memory read from that exact
trace.  The result type has no origin field. -/
def executePublicHistoricalForgetting
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (historical : PublicHistoricalOperationalState) : Agent.Memory :=
  reducePublicHistoricalForgettingTrace historical source future
    (executePublicHistoricalForgettingTrace historical source future)

theorem execute_public_historical_forgetting_exact
    (historical : PublicHistoricalOperationalState)
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    executePublicHistoricalForgetting source future historical =
      (publicReconfiguredInteractionHistory source future).finalState.memory := by
  unfold executePublicHistoricalForgetting
  change (publicHistoricalTerminalStateFromMemory historical.memory source
      future).memory = _
  calc
    _ = (publicHistoricalTerminalStateFromMemory
          (publicHistoricalInitialMemory historical.origin) source future).memory :=
      congrArg
        (fun memory =>
          (publicHistoricalTerminalStateFromMemory memory source future).memory)
        historical.memoryExact
    _ = _ := congrArg ReconfiguredExecutionState.memory
      (public_historical_terminal_state_exact historical.origin source future)

/-- C8–C9's public forgetting program. It consumes the rich operational
state carrying the origin, executes from its exact historical memory, and
returns the terminal operational memory.  Neither the complete terminal state
nor the forgotten origin occurs in the output type. -/
def publicHistoricalForgettingProgram
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    HistoricalForgettingProgram PublicHistoricalOperationalState Agent.Memory where
  Trace := fun historical =>
    PublicHistoricalForgettingTrace historical source future
  execute := fun historical =>
    executePublicHistoricalForgettingTrace historical source future
  reduce := fun historical trace =>
    reducePublicHistoricalForgettingTrace historical source future trace

def publicLeftHistoricalForgettingInput
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    HistoricalForgettingInput
      (publicHistoricalForgettingProgram source future) :=
  { origin := publicLeftHistoricalOperationalState }

def publicRightHistoricalForgettingInput
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    HistoricalForgettingInput
      (publicHistoricalForgettingProgram source future) :=
  { origin := publicRightHistoricalOperationalState }

def publicLeftExecutedForgetting
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :=
  executeHistoricalForgetting (publicHistoricalForgettingProgram source future)
    (publicLeftHistoricalForgettingInput source future)

def publicRightExecutedForgetting
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :=
  executeHistoricalForgetting (publicHistoricalForgettingProgram source future)
    (publicRightHistoricalForgettingInput source future)

theorem public_left_forgetting_trace_exact
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).trace =
      executePublicHistoricalForgettingTrace
        publicLeftHistoricalOperationalState source future :=
  (publicLeftExecutedForgetting source future).traceExact

theorem public_right_forgetting_trace_exact
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicRightExecutedForgetting source future).trace =
      executePublicHistoricalForgettingTrace
        publicRightHistoricalOperationalState source future :=
  (publicRightExecutedForgetting source future).traceExact

theorem public_left_forgetting_output_is_trace_memory
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicLeftExecutedForgetting source future).trace.finalState.memory :=
  (publicLeftExecutedForgetting source future).outputExact

theorem public_right_forgetting_output_is_trace_memory
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicRightExecutedForgetting source future).output =
      (publicRightExecutedForgetting source future).trace.finalState.memory :=
  (publicRightExecutedForgetting source future).outputExact

theorem public_historical_forgetting_inputs_distinct
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    publicLeftHistoricalForgettingInput source future ≠
      publicRightHistoricalForgettingInput source future :=
  HistoricalForgettingInput.ne_of_origin_ne
    public_historical_operational_states_distinct

theorem public_left_executed_forgetting_exact
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicReconfiguredInteractionHistory source future).finalState.memory :=
  (publicLeftExecutedForgetting source future).executionExact.trans
    (execute_public_historical_forgetting_exact
      (publicLeftHistoricalForgettingInput source future).origin source future)

theorem public_right_executed_forgetting_exact
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicRightExecutedForgetting source future).output =
      (publicReconfiguredInteractionHistory source future).finalState.memory :=
  (publicRightExecutedForgetting source future).executionExact.trans
    (execute_public_historical_forgetting_exact
      (publicRightHistoricalForgettingInput source future).origin source future)

/-- Equality is obtained only after both historically distinct inputs have run
the forgetting program and have been related to the actually executed public
continuation. -/
theorem public_executed_forgetting_outputs_equal
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicRightExecutedForgetting source future).output :=
  ExecutedHistoricalForgetting.outputs_equal_of_common_target
    (publicLeftExecutedForgetting source future)
    (publicRightExecutedForgetting source future)
    (public_left_executed_forgetting_exact source future)
    (public_right_executed_forgetting_exact source future)

theorem public_executed_forgetting_preserves_future
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    FutureEquivalent
      reconfiguredOperationalMemoryFutureContract
      (publicLeftExecutedForgetting source future).output
      (publicRightExecutedForgetting source future).output :=
  ExecutedHistoricalForgetting.same_output_same_future
    (publicLeftExecutedForgetting source future)
    (publicRightExecutedForgetting source future)
    reconfiguredOperationalMemoryFutureContract
    (public_executed_forgetting_outputs_equal source future)

/-- Closed public witness that the strict memory projection preserves the
complete reconfigured future contract exactly. -/
def publicReconfiguredOperationalMemoryRealization :
    ExactRealization
      (reconfiguredOperationalStateFutureContract
        (family := publicRequirementFamily)) Agent.Memory :=
  reconfiguredOperationalMemoryRealization
    (family := publicRequirementFamily)

/-- Every covered future of the complete terminal execution is exactly the
future computed from its strictly reduced operational memory. -/
theorem public_terminal_memory_preserves_every_future
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (requests : List (ULift.{3} Agent.Request)) :
    (reconfiguredOperationalStateFutureContract
        (family := publicRequirementFamily)).outcome
        (publicReconfiguredInteractionHistory source future).finalState requests =
      reconfiguredOperationalMemoryFutureContract.outcome
        (publicReconfiguredInteractionHistory source future).finalState.memory
        requests :=
  publicReconfiguredOperationalMemoryRealization.outcome_exact
    (publicReconfiguredInteractionHistory source future).finalState requests

/-- A request admitted by every terminal operational memory. -/
def publicTerminalAdmittedRequest : ULift.{3} Agent.Request :=
  ⟨.advance 1⟩

/-- A request outside the scope retained by the public terminal memory. -/
def publicTerminalRefusedRequest : ULift.{3} Agent.Request :=
  ⟨.obtain 0 1⟩

theorem public_terminal_requirement_exact
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    (publicReconfiguredInteractionHistory source future).finalState.memory.requirement =
      publicActionMemory.requirement := by
  have execution := congrArg
    (fun result : Agent.Memory × List Agent.Event => result.1.requirement)
    (public_reconfigured_execution_exact source future)
  have effect := congrArg
    (fun result : Agent.Memory × Agent.Event => result.1.requirement)
    (public_effect_exact source)
  exact execution.trans
    ((Agent.requirement_persists (publicEffect source).successor
      (requiredRequests publicAgentActionChannel future)).trans
        (effect.trans
          (Agent.executeInput_requirement publicActionMemory
            (publicAction source).request)))

theorem public_terminal_admitted_request_enabled
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    reconfiguredOperationalMemoryFutureContract.enabled
      (publicReconfiguredInteractionHistory source future).finalState.memory
      publicTerminalAdmittedRequest = true :=
  rfl

theorem public_terminal_refused_request_disabled
    (source : PublicRequirementInput) (future : List PublicRequirementInput) :
    reconfiguredOperationalMemoryFutureContract.enabled
      (publicReconfiguredInteractionHistory source future).finalState.memory
      publicTerminalRefusedRequest = false := by
  have absent :
      (publicReconfiguredInteractionHistory source future).finalState.memory.requirement.permission
          1 = none := by
    rw [public_terminal_requirement_exact source future]
    rfl
  have impossible :
      Agent.Admission
        (publicReconfiguredInteractionHistory source future).finalState.memory.requirement
        (publicReconfiguredInteractionHistory source future).finalState.memory.register
        (.obtain 0 1) -> False :=
    fun witness =>
      Agent.resolvePermission_none _ _ absent witness.down
  unfold FutureContract.enabled
  cases chosen : reconfiguredOperationalMemoryFutureContract.decision
      (publicReconfiguredInteractionHistory source future).finalState.memory
      publicTerminalRefusedRequest with
  | inl witness =>
      exact False.elim (impossible witness)
  | inr _ => rfl

/-- Two operational memories with the same immediate readout.  They differ
only in the received requirement, while their visible tables are both empty. -/
def publicTerminalSeparatorLeft : Agent.Memory :=
  { requirement := singletonRequirement 0
    live := publicActionMemory.live
    register := [] }

def publicTerminalSeparatorRight : Agent.Memory :=
  { requirement := singletonRequirement 1
    live := publicActionMemory.live
    register := [] }

def publicTerminalSeparatingRequest : ULift.{3} Agent.Request :=
  ⟨.obtain 0 0⟩

theorem public_terminal_separator_same_immediate_readout :
    reconfiguredOperationalMemoryFutureContract.read
        publicTerminalSeparatorLeft =
      reconfiguredOperationalMemoryFutureContract.read
        publicTerminalSeparatorRight :=
  rfl

theorem public_terminal_separator_left_admitted :
    reconfiguredOperationalMemoryFutureContract.enabled
      publicTerminalSeparatorLeft publicTerminalSeparatingRequest = true :=
  rfl

theorem public_terminal_separator_right_refused :
    reconfiguredOperationalMemoryFutureContract.enabled
      publicTerminalSeparatorRight publicTerminalSeparatingRequest = false :=
  rfl

/-- The empty future cannot distinguish the separator memories through the
contract readout, while the one-request future must distinguish them through
the executed admission decision. -/
theorem public_terminal_nonempty_future_is_necessary :
    reconfiguredOperationalMemoryFutureContract.outcome
        publicTerminalSeparatorLeft [publicTerminalSeparatingRequest] ≠
      reconfiguredOperationalMemoryFutureContract.outcome
        publicTerminalSeparatorRight [publicTerminalSeparatingRequest] := by
  intro same
  have decision := congrArg Outcome.right same
  change true = false at decision
  cases decision

theorem public_executed_forgetting_origin_not_recoverable
    (source : PublicRequirementInput) (future : List PublicRequirementInput)
    (recover : Agent.Memory -> PublicHistoricalOrigin)
    (recoversLeft :
      recover (publicLeftExecutedForgetting source future).output =
        (publicLeftHistoricalForgettingInput source future).origin.origin)
    (recoversRight :
      recover (publicRightExecutedForgetting source future).output =
        (publicRightHistoricalForgettingInput source future).origin.origin) : False := by
  apply public_historical_origins_distinct
  exact recoversLeft.symm.trans
    ((congrArg recover
      (public_executed_forgetting_outputs_equal source future)).trans
        recoversRight)

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalMaster
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalRequirement
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalInitialMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicLeftHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.publicRightHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_origins_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_memories_equal
#print axioms ConstitutiveSearch.NeuralAgent.public_left_historical_memory_is_action_memory
#print axioms ConstitutiveSearch.NeuralAgent.public_forgotten_sources_same_signature
#print axioms ConstitutiveSearch.NeuralAgent.public_forgotten_sources_same_future
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_origin_not_recoverable
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalInitialReconfiguredStateFromMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalTerminalStateFromMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalTerminalState
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_initial_memory_eq_action_memory
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_terminal_state_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalTerminalMemory
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_terminal_memory_exact
#print axioms ConstitutiveSearch.NeuralAgent.PublicHistoricalOperationalState
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalOperationalState
#print axioms ConstitutiveSearch.NeuralAgent.publicLeftHistoricalOperationalState
#print axioms ConstitutiveSearch.NeuralAgent.publicRightHistoricalOperationalState
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_operational_states_distinct
#print axioms ConstitutiveSearch.NeuralAgent.PublicHistoricalForgettingTrace
#print axioms ConstitutiveSearch.NeuralAgent.executePublicHistoricalForgettingTrace
#print axioms ConstitutiveSearch.NeuralAgent.reducePublicHistoricalForgettingTrace
#print axioms ConstitutiveSearch.NeuralAgent.executePublicHistoricalForgetting
#print axioms ConstitutiveSearch.NeuralAgent.execute_public_historical_forgetting_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalForgettingProgram
#print axioms ConstitutiveSearch.NeuralAgent.publicLeftHistoricalForgettingInput
#print axioms ConstitutiveSearch.NeuralAgent.publicRightHistoricalForgettingInput
#print axioms ConstitutiveSearch.NeuralAgent.publicLeftExecutedForgetting
#print axioms ConstitutiveSearch.NeuralAgent.publicRightExecutedForgetting
#print axioms ConstitutiveSearch.NeuralAgent.public_left_forgetting_trace_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_right_forgetting_trace_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_left_forgetting_output_is_trace_memory
#print axioms ConstitutiveSearch.NeuralAgent.public_right_forgetting_output_is_trace_memory
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_forgetting_inputs_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_left_executed_forgetting_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_right_executed_forgetting_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_executed_forgetting_outputs_equal
#print axioms ConstitutiveSearch.NeuralAgent.public_executed_forgetting_preserves_future
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredOperationalMemoryRealization
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_memory_preserves_every_future
#print axioms ConstitutiveSearch.NeuralAgent.publicTerminalAdmittedRequest
#print axioms ConstitutiveSearch.NeuralAgent.publicTerminalRefusedRequest
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_requirement_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_admitted_request_enabled
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_refused_request_disabled
#print axioms ConstitutiveSearch.NeuralAgent.publicTerminalSeparatorLeft
#print axioms ConstitutiveSearch.NeuralAgent.publicTerminalSeparatorRight
#print axioms ConstitutiveSearch.NeuralAgent.publicTerminalSeparatingRequest
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_separator_same_immediate_readout
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_separator_left_admitted
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_separator_right_refused
#print axioms ConstitutiveSearch.NeuralAgent.public_terminal_nonempty_future_is_necessary
#print axioms ConstitutiveSearch.NeuralAgent.public_executed_forgetting_origin_not_recoverable
/- AXIOM_AUDIT_END -/
