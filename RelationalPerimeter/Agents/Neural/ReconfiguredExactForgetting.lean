import RelationalPerimeter.Agents.Neural.ReconfiguredContinuation
import RelationalPerimeter.Constitution.Continuation.Minimality

/-!
# Exact forgetting for a reconfigured continuation

The rich source remembers its constituted origin and covered past.  Its
current operational state is nevertheless computed only by executing the
reconfiguration certificate produced from the preceding state.  The exact
realization forgets the origin and past while retaining the current native
system, current requirement and current agent memory: precisely the material
needed to continue the same reconfiguration recursion.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures NativeMechanism

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
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredHistoricalSource.origin
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredHistoricalSource.currentState
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.reducedReconfiguredFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.reconfiguredStateRealization
#print axioms ConstitutiveSearch.NeuralAgent.reconfigured_same_state_same_future
#print axioms ConstitutiveSearch.NeuralAgent.reconfigured_origin_not_recoverable
/- AXIOM_AUDIT_END -/
