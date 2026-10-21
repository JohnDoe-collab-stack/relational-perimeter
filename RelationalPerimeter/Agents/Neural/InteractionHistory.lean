import RelationalPerimeter.Agents.Neural.ActionRealization

/-!
# Finite neural-agent continuation

Each head action is produced from the current memory and current covered
requirement.  The recursive call receives only the successor produced by that
head and the remaining inputs.  No future tail occurs in the type of the head
action.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

universe u v w

inductive InteractionHistory
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    (incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input)
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    Agent.Memory -> List (RequirementInput family) ->
      Type (max 3 (max u (max v w))) where
  | nil (memory : Agent.Memory) :
      InteractionHistory incorporation transformation channel memory []
  | step {memory : Agent.Memory} {input : RequirementInput family}
      {future : List (RequirementInput family)}
      (action : ActionRealization channel (transformation input) memory)
      (effect : EffectRealization action)
      (tail : InteractionHistory incorporation transformation channel
        effect.successor future) :
      InteractionHistory incorporation transformation channel memory
        (input :: future)

def executeInteractions
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    (incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input)
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    (memory : Agent.Memory) -> (inputs : List (RequirementInput family)) ->
      InteractionHistory incorporation transformation channel memory inputs
  | memory, [] => .nil memory
  | memory, input :: future =>
      let action := realizeAction channel (transformation input) memory
      let effect := realizeEffect action
      .step action effect
        (executeInteractions incorporation transformation channel
          effect.successor future)

def InteractionHistory.requests
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    {transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input)}
    {channel : AgentActionChannel Proposal} {memory inputs} :
    InteractionHistory incorporation transformation channel memory inputs ->
      List Agent.Request
  | .nil _ => []
  | .step action _ tail => action.request :: tail.requests

def InteractionHistory.events
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    {transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input)}
    {channel : AgentActionChannel Proposal} {memory inputs} :
    InteractionHistory incorporation transformation channel memory inputs ->
      List Agent.Event
  | .nil _ => []
  | .step _ effect tail => effect.event :: tail.events

def InteractionHistory.finalMemory
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    {transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input)}
    {channel : AgentActionChannel Proposal} {memory inputs} :
    InteractionHistory incorporation transformation channel memory inputs ->
      Agent.Memory
  | .nil memory => memory
  | .step _ _ tail => tail.finalMemory

def requiredRequests
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (channel : AgentActionChannel Proposal) :
    List (RequirementInput family) -> List Agent.Request
  | [] => []
  | input :: future =>
      channel.command
        (family.requiredProposal input.requirement input.context) ::
          requiredRequests channel future

theorem InteractionHistory.requests_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    {transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input)}
    {channel : AgentActionChannel Proposal} {memory inputs}
    (history : InteractionHistory incorporation transformation channel memory inputs) :
    history.requests = requiredRequests channel inputs := by
  induction history with
  | nil => rfl
  | step action effect tail ih =>
      change action.request :: tail.requests = _
      rw [action.request_exact, ih]
      rfl

/-- The data exposed by an interaction history are exactly the result of
executing, in order, the requests carried by that history.  This is stronger
than pointwise request agreement: the successor memory produced at each step
is the memory consumed by the recursive tail. -/
theorem InteractionHistory.execution_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    {transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input)}
    {channel : AgentActionChannel Proposal} {memory inputs}
    (history : InteractionHistory incorporation transformation channel memory inputs) :
    (history.finalMemory, history.events) =
      Agent.executeRequests memory history.requests := by
  induction history with
  | nil => rfl
  | step action effect tail ih =>
      have successorExact :
          effect.successor =
            (Agent.executeInput _ action.request).1 :=
        congrArg Prod.fst effect.effect_exact
      have eventExact :
          effect.event =
            (Agent.executeInput _ action.request).2 :=
        congrArg Prod.snd effect.effect_exact
      change (tail.finalMemory, effect.event :: tail.events) =
        ((Agent.executeRequests
          (Agent.executeInput _ action.request).1 tail.requests).1,
         (Agent.executeInput _ action.request).2 ::
          (Agent.executeRequests
            (Agent.executeInput _ action.request).1 tail.requests).2)
      rw [← successorExact, ← eventExact]
      have finalMemoryExact :
          tail.finalMemory =
            (Agent.executeRequests effect.successor tail.requests).1 :=
        congrArg (fun result : Agent.Memory × List Agent.Event => result.1) ih
      have eventsExact :
          tail.events =
            (Agent.executeRequests effect.successor tail.requests).2 :=
        congrArg (fun result : Agent.Memory × List Agent.Event => result.2) ih
      exact Prod.ext finalMemoryExact
        (congrArg (List.cons effect.event) eventsExact)

theorem finite_continuation_aligned
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    (incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input)
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) (memory : Agent.Memory)
    (inputs : List (RequirementInput family)) :
    (executeInteractions incorporation transformation channel memory inputs).requests =
      requiredRequests channel inputs :=
  (executeInteractions incorporation transformation channel memory inputs).requests_exact

theorem finite_continuation_execution_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    (incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input)
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) (memory : Agent.Memory)
    (inputs : List (RequirementInput family)) :
    let history :=
      executeInteractions incorporation transformation channel memory inputs
    (history.finalMemory, history.events) =
      Agent.executeRequests memory (requiredRequests channel inputs) := by
  dsimp only
  rw [← (executeInteractions incorporation transformation channel memory
    inputs).requests_exact]
  exact (executeInteractions incorporation transformation channel memory
    inputs).execution_exact

def InteractionHistory.headRequest
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    {transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input)}
    {channel : AgentActionChannel Proposal} {memory inputs} :
    InteractionHistory incorporation transformation channel memory inputs ->
      Option Agent.Request
  | .nil _ => none
  | .step action _ _ => some action.request

theorem head_horizon_independent
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    (incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input)
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) (memory : Agent.Memory)
    (input : RequirementInput family)
    (left right : List (RequirementInput family)) :
    (executeInteractions incorporation transformation channel memory
      (input :: left)).headRequest =
    (executeInteractions incorporation transformation channel memory
      (input :: right)).headRequest :=
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.executeInteractions
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory.requests
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory.events
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory.finalMemory
#print axioms ConstitutiveSearch.NeuralAgent.requiredRequests
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory.requests_exact
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory.execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.finite_continuation_aligned
#print axioms ConstitutiveSearch.NeuralAgent.finite_continuation_execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.InteractionHistory.headRequest
#print axioms ConstitutiveSearch.NeuralAgent.head_horizon_independent
/- AXIOM_AUDIT_END -/
