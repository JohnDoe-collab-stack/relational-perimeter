import RelationalPerimeter.Agents.Neural.Reconfiguration

/-!
# Continuation through executed reconfiguration

The state carried by this continuation contains the native system that was
actually produced at the preceding step.  The next certificate is constructed
from that system and its exact run.  Its target system produces the request
that is executed, and that same target system is then passed to the recursive
tail.  No fixed source system or independently reconstructed target can enter
the recursion.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

universe u v w

structure ReconfiguredExecutionState
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal) where
  system : NativeSystem (RequirementInput family) Proposal
  input : RequirementInput family
  memory : Agent.Memory

structure ReconfiguredActionEffect
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    (channel : AgentActionChannel Proposal)
    (source : ReconfiguredExecutionState family)
    (next : RequirementInput family) : Type (max 3 (max u (max v w))) where
  private mk ::
  certificate : CertifiedReconfiguration (builder := builder)
    (sourceSystem := source.system) (sourceInput := source.input)
    (nextInput := next)
  request : Agent.Request
  requestExact : request = channel.command
    (certificate.configuration.targetSystem.proposal next)
  result : Agent.Memory × Agent.Event
  evidence : Agent.RequestEvidence source.memory request result
  resultExact : result = Agent.executeInput source.memory request

def executeReconfiguredAction
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    (channel : AgentActionChannel Proposal)
    (source : ReconfiguredExecutionState family)
    (next : RequirementInput family)
    (certificate : CertifiedReconfiguration (builder := builder)
      (sourceSystem := source.system) (sourceInput := source.input)
      (nextInput := next)) :
    ReconfiguredActionEffect (builder := builder) channel source next :=
  let request := channel.command
    (certificate.configuration.targetSystem.proposal next)
  let produced := Agent.executeProducedInput source.memory request
  .mk certificate request rfl produced.1 produced.2 rfl

theorem ReconfiguredActionEffect.request_required_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (action : ReconfiguredActionEffect (builder := builder) channel source next) :
    action.request = channel.command
      (family.requiredProposal next.requirement next.context) :=
  action.requestExact.trans
    (congrArg channel.command action.certificate.transport.proposalExact)

def ReconfiguredActionEffect.targetState
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (action : ReconfiguredActionEffect (builder := builder) channel source next) :
    ReconfiguredExecutionState family :=
  { system := action.certificate.configuration.targetSystem
    input := next
    memory := action.result.1 }

inductive ReconfiguredInteractionHistory
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (builder : ReconfigurationBuilder family)
    (channel : AgentActionChannel Proposal)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)) :
    ReconfiguredExecutionState family -> List (RequirementInput family) ->
      Type (max 3 (max u (max v w))) where
  | nil (source : ReconfiguredExecutionState family) :
      ReconfiguredInteractionHistory builder channel certify source []
  | step {source : ReconfiguredExecutionState family}
      {next : RequirementInput family} {future : List (RequirementInput family)}
      (action : ReconfiguredActionEffect (builder := builder) channel source next)
      (actionExact : action = executeReconfiguredAction channel source next
        (certify source next))
      (tail : ReconfiguredInteractionHistory builder channel certify
        action.targetState future) :
      ReconfiguredInteractionHistory builder channel certify source
        (next :: future)

def executeReconfiguredInteractions
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (builder : ReconfigurationBuilder family)
    (channel : AgentActionChannel Proposal)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)) :
    (source : ReconfiguredExecutionState family) ->
    (inputs : List (RequirementInput family)) ->
      ReconfiguredInteractionHistory builder channel certify source inputs
  | source, [] => .nil source
  | source, next :: future =>
      let action := executeReconfiguredAction channel source next
        (certify source next)
      .step action rfl
        (executeReconfiguredInteractions builder channel certify
          action.targetState future)

def ReconfiguredInteractionHistory.requests
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} {source inputs} :
    ReconfiguredInteractionHistory builder channel certify source inputs ->
      List Agent.Request
  | .nil _ => []
  | .step action _ tail => action.request :: tail.requests

def ReconfiguredInteractionHistory.events
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} {source inputs} :
    ReconfiguredInteractionHistory builder channel certify source inputs ->
      List Agent.Event
  | .nil _ => []
  | .step action _ tail => action.result.2 :: tail.events

def ReconfiguredInteractionHistory.finalState
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} {source inputs} :
    ReconfiguredInteractionHistory builder channel certify source inputs ->
      ReconfiguredExecutionState family
  | .nil source => source
  | .step _ _ tail => tail.finalState

theorem ReconfiguredInteractionHistory.requests_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} {source inputs}
    (history : ReconfiguredInteractionHistory builder channel certify source inputs) :
    history.requests = requiredRequests channel inputs := by
  induction history with
  | nil => rfl
  | step action _ tail ih =>
      change action.request :: tail.requests = _
      rw [action.request_required_exact, ih]
      rfl

theorem ReconfiguredInteractionHistory.execution_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} {source inputs}
    (history : ReconfiguredInteractionHistory builder channel certify source inputs) :
    (history.finalState.memory, history.events) =
      Agent.executeRequests source.memory history.requests := by
  induction history with
  | nil => rfl
  | step action _ tail ih =>
      have finalMemoryExact :
          tail.finalState.memory =
            (Agent.executeRequests action.targetState.memory tail.requests).1 :=
        congrArg Prod.fst ih
      have eventsExact :
          tail.events =
            (Agent.executeRequests action.targetState.memory tail.requests).2 :=
        congrArg Prod.snd ih
      change (tail.finalState.memory, action.result.2 :: tail.events) =
        ((Agent.executeRequests
          (Agent.executeInput _ action.request).1 tail.requests).1,
         (Agent.executeInput _ action.request).2 ::
          (Agent.executeRequests
            (Agent.executeInput _ action.request).1 tail.requests).2)
      rw [← action.resultExact]
      exact Prod.ext finalMemoryExact
        (congrArg (List.cons action.result.2) eventsExact)

def ReconfiguredInteractionHistory.headRequest
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)} {source inputs} :
    ReconfiguredInteractionHistory builder channel certify source inputs ->
      Option Agent.Request
  | .nil _ => none
  | .step action _ _ => some action.request

theorem reconfigured_head_horizon_independent
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (builder : ReconfigurationBuilder family)
    (channel : AgentActionChannel Proposal)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next))
    (source : ReconfiguredExecutionState family)
    (next : RequirementInput family)
    (left right : List (RequirementInput family)) :
    (executeReconfiguredInteractions builder channel certify source
      (next :: left)).headRequest =
    (executeReconfiguredInteractions builder channel certify source
      (next :: right)).headRequest :=
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredExecutionState
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredActionEffect
#print axioms ConstitutiveSearch.NeuralAgent.executeReconfiguredAction
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredActionEffect.request_required_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredActionEffect.targetState
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.executeReconfiguredInteractions
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.requests
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.events
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.finalState
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.requests_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.headRequest
#print axioms ConstitutiveSearch.NeuralAgent.reconfigured_head_horizon_independent
/- AXIOM_AUDIT_END -/
