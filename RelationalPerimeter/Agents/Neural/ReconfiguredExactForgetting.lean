import RelationalPerimeter.Agents.Neural.ReconfiguredContinuation
import RelationalPerimeter.Agents.ContinuationSignatures.ReachableAgent
import RelationalPerimeter.Constitution.Continuation.Minimality

/-!
# Exact forgetting for a reconfigured continuation

The rich source remembers its constituted origin and covered past. Its current
operational state is computed only by executing the reconfiguration certificate
produced from the preceding state. Two realizations are distinguished. The
historical realization exposes the current reconfigured state. C9 then projects
that state to the strictly poorer `Agent.Memory`: its current system, current
requirement, constituted origin and covered past are absent. Exact transport
laws prove that this smaller memory nevertheless preserves the authorizations,
transitions, events, readouts, and every covered finite future.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures NativeMechanism

/-- An executable forgetting program separates the source-indexed execution
trace from its reduced readout.  `execute` must positively construct a trace
for the supplied history; `reduce` may then omit historical distinctions from
the material that continues operationally. -/
structure HistoricalForgettingProgram (History Reduced : Type 3) where
  Trace : History -> Type 3
  execute : (origin : History) -> Trace origin
  reduce : (origin : History) -> Trace origin -> Reduced

def HistoricalForgettingProgram.run
    (program : HistoricalForgettingProgram History Reduced)
    (origin : History) : Reduced :=
  program.reduce origin (program.execute origin)

/-- The input to forgetting positively contains the historical origin that is
about to be consumed. -/
structure HistoricalForgettingInput
    {History Reduced : Type 3}
    (program : HistoricalForgettingProgram History Reduced) where
  origin : History

/-- A forgetting execution retains the exact source-indexed trace and records
the reduced output obtained from that trace.  The private constructor prevents
callers from pairing an unrelated trace with a post-hoc output. -/
structure ExecutedHistoricalForgetting
    {History Reduced : Type 3}
    (program : HistoricalForgettingProgram History Reduced)
    (input : HistoricalForgettingInput program) where
  private mk ::
  trace : program.Trace input.origin
  output : Reduced
  traceExact : trace = program.execute input.origin
  outputExact : output = program.reduce input.origin trace

theorem ExecutedHistoricalForgetting.executionExact
    {History Reduced : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {input : HistoricalForgettingInput program}
    (execution : ExecutedHistoricalForgetting program input) :
    execution.output = program.run input.origin := by
  calc
    execution.output = program.reduce input.origin execution.trace :=
      execution.outputExact
    _ = program.reduce input.origin (program.execute input.origin) :=
      congrArg (program.reduce input.origin) execution.traceExact
    _ = program.run input.origin := rfl

def executeHistoricalForgetting
    {History Reduced : Type 3}
    (program : HistoricalForgettingProgram History Reduced)
    (input : HistoricalForgettingInput program) :
    ExecutedHistoricalForgetting program input :=
  .mk (program.execute input.origin)
    (program.reduce input.origin (program.execute input.origin)) rfl rfl

theorem HistoricalForgettingInput.ne_of_origin_ne
    {History Reduced : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {left right : HistoricalForgettingInput program}
    (different : left.origin ≠ right.origin) : left ≠ right := by
  intro same
  exact different (congrArg HistoricalForgettingInput.origin same)

theorem ExecutedHistoricalForgetting.outputs_equal_of_common_target
    {History Reduced : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {leftInput rightInput : HistoricalForgettingInput program}
    (left : ExecutedHistoricalForgetting program leftInput)
    (right : ExecutedHistoricalForgetting program rightInput)
    {target : Reduced}
    (leftExact : left.output = target)
    (rightExact : right.output = target) :
    left.output = right.output :=
  leftExact.trans rightExact.symm

theorem ExecutedHistoricalForgetting.same_output_same_future
    {History Reduced Input Event Observation : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {leftInput rightInput : HistoricalForgettingInput program}
    (left : ExecutedHistoricalForgetting program leftInput)
    (right : ExecutedHistoricalForgetting program rightInput)
    (contract : FutureContract Reduced Input Event Observation)
    (same : left.output = right.output) :
    FutureEquivalent contract left.output right.output := by
  intro requests
  rw [same]

theorem ExecutedHistoricalForgetting.origin_not_recoverable
    {History Reduced : Type 3}
    {program : HistoricalForgettingProgram History Reduced}
    {leftInput rightInput : HistoricalForgettingInput program}
    (left : ExecutedHistoricalForgetting program leftInput)
    (right : ExecutedHistoricalForgetting program rightInput)
    (originsDistinct : leftInput.origin ≠ rightInput.origin)
    (outputsEqual : left.output = right.output)
    (recover : Reduced -> History)
    (recoversLeft : recover left.output = leftInput.origin)
    (recoversRight : recover right.output = rightInput.origin) : False := by
  apply originsDistinct
  exact recoversLeft.symm.trans
    ((congrArg recover outputsEqual).trans recoversRight)

inductive ReconfiguredHistoricalSource
    (History : Type 3)
    {RequirementCase Context Proposal : Type}
    (family : RequirementFamily RequirementCase Context Proposal)
    (builder : ReconfigurationBuilder family)
    (channel : AgentActionChannel Proposal)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next))
    (initialState : History -> ReconfiguredExecutionState family) : Type 3 where
  | initial (origin : History) :
      ReconfiguredHistoricalSource History family builder channel certify
        initialState
  | step
      (prior : ReconfiguredHistoricalSource History family builder channel
        certify initialState)
      (next : RequirementInput family) :
      ReconfiguredHistoricalSource History family builder channel certify
        initialState

def ReconfiguredHistoricalSource.origin
    {History : Type 3}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {initialState : History -> ReconfiguredExecutionState family} :
    ReconfiguredHistoricalSource History family builder channel certify
      initialState -> History
  | .initial origin => origin
  | .step prior _ => prior.origin

def ReconfiguredHistoricalSource.currentState
    {History : Type 3}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {initialState : History -> ReconfiguredExecutionState family} :
    ReconfiguredHistoricalSource History family builder channel certify
      initialState -> ReconfiguredExecutionState family
  | .initial origin => initialState origin
  | .step prior next =>
      (executeReconfiguredAction channel prior.currentState next
        (certify prior.currentState next)).targetState

def reconfiguredFutureContract
    {History : Type 3}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {initialState : History -> ReconfiguredExecutionState family} :
    FutureContract
      (ReconfiguredHistoricalSource History family builder channel certify
        initialState)
      (ULift.{3} (RequirementInput family)) Agent.Event Agent.Memory where
  next := fun source input => .step source input.down
  event := fun source input =>
    (executeReconfiguredAction channel source.currentState input.down
      (certify source.currentState input.down)).result.2
  read := fun source => source.currentState.memory
  Allow := fun _ _ => PUnit
  decision := fun _ _ => .inl PUnit.unit

def reducedReconfiguredFutureContract
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} :
    FutureContract (ReconfiguredExecutionState family)
      (ULift.{3} (RequirementInput family)) Agent.Event Agent.Memory where
  next := fun source input =>
    (executeReconfiguredAction channel source input.down
      (certify source input.down)).targetState
  event := fun source input =>
    (executeReconfiguredAction channel source input.down
      (certify source input.down)).result.2
  read := fun source => source.memory
  Allow := fun _ _ => PUnit
  decision := fun _ _ => .inl PUnit.unit

/-- The observable part of the terminal operational contract.  It exposes the
authorized answer table, not the complete memory that also contains the live
engine and the retained requirement. -/
abbrev OperationalMemoryReadout : Type 3 :=
  ULift.{3} (List (Nat × SAT.Var × Bool))

/-- The terminal contract before forgetting.  Requests are genuine agent
requests.  Their admission is decided from the current requirement and
register, and a transition executes the same proof-carrying agent operation
that is available after projection.  The native system and neural input remain
present in the source type but are not read by this terminal layer. -/
def reconfiguredOperationalStateFutureContract
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal} :
    FutureContract (ReconfiguredExecutionState family)
      (ULift.{3} Agent.Request) Agent.Event OperationalMemoryReadout where
  next := fun source request =>
    { system := source.system
      input := source.input
      memory := (Agent.executeInput source.memory request.down).1 }
  event := fun source request =>
    (Agent.executeInput source.memory request.down).2
  read := fun source =>
    ⟨Agent.table source.memory.register
      source.memory.requirement.realizedScope⟩
  Allow := fun source request =>
    Agent.Admission source.memory.requirement source.memory.register
      request.down
  decision := fun source request =>
    ReachableAgent.decideAdmission source.memory request.down

/-- The strictly reduced terminal contract is the existing complete runtime
agent contract.  It contains admitted and refused requests, executes their
decisions, and observes only the authorized table rather than the entire
memory. -/
def reconfiguredOperationalMemoryFutureContract :
    FutureContract Agent.Memory (ULift.{3} Agent.Request)
      Agent.Event OperationalMemoryReadout :=
  ReachableAgent.runtimeContract

/-- Exact C9–C10 realization of the full reconfigured state by its operational
memory.  Authorization witnesses are transported in both directions, and
transition, event and readout equality hold for every request. -/
def reconfiguredOperationalMemoryRealization
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal} :
    ExactRealization
      (reconfiguredOperationalStateFutureContract (family := family))
      Agent.Memory where
  reduced := reconfiguredOperationalMemoryFutureContract
  project := ReconfiguredExecutionState.memory
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := fun _ _ _ => rfl
  forward_backward := fun _ _ _ => rfl
  next_exact := fun _ _ => rfl
  event_exact := fun _ _ => rfl
  read_exact := fun _ => rfl

theorem reconfiguredOperationalMemory_outcome_exact
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    (source : ReconfiguredExecutionState family)
    (future : List (ULift.{3} Agent.Request)) :
    (reconfiguredOperationalStateFutureContract (family := family)).outcome
        source future =
      reconfiguredOperationalMemoryFutureContract.outcome source.memory
        future :=
  (reconfiguredOperationalMemoryRealization (family := family)).outcome_exact
    source future

def reconfiguredStateRealization
    {History : Type 3}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {initialState : History -> ReconfiguredExecutionState family} :
    ExactRealization
      (reconfiguredFutureContract (channel := channel) (certify := certify)
        (initialState := initialState))
      (ReconfiguredExecutionState family) where
  reduced := reducedReconfiguredFutureContract
    (channel := channel) (certify := certify)
  project := ReconfiguredHistoricalSource.currentState
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := by intro _ _ witness; cases witness; rfl
  forward_backward := by intro _ _ witness; cases witness; rfl
  next_exact := fun _ _ => rfl
  event_exact := fun _ _ => rfl
  read_exact := fun _ => rfl

theorem reconfigured_same_state_same_future
    {History : Type 3}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {initialState : History -> ReconfiguredExecutionState family}
    {left right : ReconfiguredHistoricalSource History family builder channel
      certify initialState}
    (same : left.currentState = right.currentState) :
    FutureEquivalent
      (reconfiguredFutureContract (channel := channel) (certify := certify)
        (initialState := initialState)) left right :=
  (reconfiguredStateRealization (channel := channel) (certify := certify)
    (initialState := initialState)).equal_memory_same_futures same

theorem reconfigured_origin_not_recoverable
    {History : Type 3}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {initialState : History -> ReconfiguredExecutionState family}
    (left right : ReconfiguredHistoricalSource History family builder channel
      certify initialState)
    (originsDistinct : left.origin ≠ right.origin)
    (same : left.currentState = right.currentState)
    (recover : ReconfiguredExecutionState family -> History)
    (recoversLeft : recover left.currentState = left.origin)
    (recoversRight : recover right.currentState = right.origin) : False := by
  apply originsDistinct
  rw [← recoversLeft, ← recoversRight, same]

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalForgettingProgram
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalForgettingProgram.run
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalForgettingInput
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedHistoricalForgetting
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedHistoricalForgetting.executionExact
#print axioms ConstitutiveSearch.NeuralAgent.executeHistoricalForgetting
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalForgettingInput.ne_of_origin_ne
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedHistoricalForgetting.outputs_equal_of_common_target
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedHistoricalForgetting.same_output_same_future
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedHistoricalForgetting.origin_not_recoverable
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredHistoricalSource.origin
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredHistoricalSource.currentState
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.reducedReconfiguredFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredOperationalStateFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredOperationalMemoryFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredOperationalMemoryRealization
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredOperationalMemory_outcome_exact
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredStateRealization
#print axioms ConstitutiveSearch.NeuralAgent.reconfigured_same_state_same_future
#print axioms ConstitutiveSearch.NeuralAgent.reconfigured_origin_not_recoverable
/- AXIOM_AUDIT_END -/
