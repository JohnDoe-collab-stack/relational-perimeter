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
    (congrArg channel.command
      action.certificate.derivation.proposal_exact)

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

/-- One causally complete step of the reconfigured continuation.  The step is
not a graph edge followed by an independently supplied action: its action is
the canonical execution of the certificate produced for the exact source
state and next requirement.  That certificate contains the three full
interventional `CausalRole`s consumed by the reconfiguration: source proposal,
received requirement, and incorporated authorization. -/
structure ReconfiguredCausalStage
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
    (next : RequirementInput family) : Type (max 3 (max u (max v w))) where
  private mk ::
  action : ReconfiguredActionEffect (builder := builder) channel source next
  actionExact : action = executeReconfiguredAction channel source next
    (certify source next)

/-- Execute exactly one causally complete stage.  There is no future tail in
the input of this constructor. -/
def executeReconfiguredCausalStage
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
    (next : RequirementInput family) :
    ReconfiguredCausalStage builder channel certify source next :=
  .mk (executeReconfiguredAction channel source next (certify source next)) rfl

def ReconfiguredCausalStage.sourceRole
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    CausalRole stage.action.certificate.configuration.targetSystem next
      (.receivedInput stage.action.certificate.transport.sourcePort) :=
  stage.action.certificate.transport.sourceRole

def ReconfiguredCausalStage.requirementRole
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    CausalRole stage.action.certificate.configuration.targetSystem next
      (.receivedInput stage.action.certificate.transport.requirementPort) :=
  stage.action.certificate.transport.requirementRole

def ReconfiguredCausalStage.authorizationRole
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    CausalRole stage.action.certificate.configuration.targetSystem next
      (.receivedInput stage.action.certificate.transport.authorizationPort) :=
  stage.action.certificate.transport.authorizationRole

def ReconfiguredCausalStage.proposal
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    Proposal :=
  stage.action.certificate.configuration.targetSystem.proposal next

theorem ReconfiguredCausalStage.proposal_required_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    stage.proposal = family.requiredProposal next.requirement next.context :=
  stage.action.certificate.derivation.proposal_exact

def ReconfiguredCausalStage.request
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    Agent.Request :=
  stage.action.request

theorem ReconfiguredCausalStage.request_from_proposal
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    stage.request = channel.command stage.proposal :=
  stage.action.requestExact

def ReconfiguredCausalStage.effect
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    Agent.Memory × Agent.Event :=
  stage.action.result

theorem ReconfiguredCausalStage.effect_from_request
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    stage.effect = Agent.executeInput source.memory stage.request :=
  stage.action.resultExact

def ReconfiguredCausalStage.nextState
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    ReconfiguredExecutionState family :=
  stage.action.targetState

theorem ReconfiguredCausalStage.nextState_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    (stage : ReconfiguredCausalStage builder channel certify source next) :
    stage.nextState =
      { system := stage.action.certificate.configuration.targetSystem
        input := next
        memory := stage.effect.1 } :=
  rfl

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
      (stage : ReconfiguredCausalStage builder channel certify source next)
      (tail : ReconfiguredInteractionHistory builder channel certify
        stage.nextState future) :
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
      let stage := executeReconfiguredCausalStage builder channel certify
        source next
      .step stage
        (executeReconfiguredInteractions builder channel certify
          stage.nextState future)

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
  | .step stage tail => stage.request :: tail.requests

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
  | .step stage tail => stage.effect.2 :: tail.events

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
  | .step _ tail => tail.finalState

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
  | step stage tail ih =>
      change stage.request :: tail.requests = _
      rw [stage.request_from_proposal, stage.proposal_required_exact, ih]
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
  | step stage tail ih =>
      have finalMemoryExact :
          tail.finalState.memory =
            (Agent.executeRequests stage.nextState.memory tail.requests).1 :=
        congrArg Prod.fst ih
      have eventsExact :
          tail.events =
            (Agent.executeRequests stage.nextState.memory tail.requests).2 :=
        congrArg Prod.snd ih
      change (tail.finalState.memory, stage.effect.2 :: tail.events) =
        ((Agent.executeRequests
          (Agent.executeInput _ stage.request).1 tail.requests).1,
         (Agent.executeInput _ stage.request).2 ::
          (Agent.executeRequests
            (Agent.executeInput _ stage.request).1 tail.requests).2)
      rw [← stage.effect_from_request]
      exact Prod.ext finalMemoryExact
        (congrArg (List.cons stage.effect.2) eventsExact)

/-- The exact causal head stored by a nonempty executed history.  Its source
and requirement remain the indices of the history itself. -/
def ReconfiguredInteractionHistory.headStage
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    {future : List (RequirementInput family)}
    (history : ReconfiguredInteractionHistory builder channel certify source
      (next :: future)) :
    ReconfiguredCausalStage builder channel certify source next :=
  match history with
  | .step stage _ => stage

/-- The tail consumes definitionally the state produced by the exact stored
head.  It cannot be indexed by the preceding state or by a separately rebuilt
successor. -/
def ReconfiguredInteractionHistory.tail
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {channel : AgentActionChannel Proposal}
    {certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next)}
    {source : ReconfiguredExecutionState family}
    {next : RequirementInput family}
    {future : List (RequirementInput family)}
    (history : ReconfiguredInteractionHistory builder channel certify source
      (next :: future)) :
    ReconfiguredInteractionHistory builder channel certify
      history.headStage.nextState future :=
  match history with
  | .step _ tail => tail

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
  | .step stage _ => some stage.request

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
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage
#print axioms ConstitutiveSearch.NeuralAgent.executeReconfiguredCausalStage
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.sourceRole
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.requirementRole
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.authorizationRole
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.proposal
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.proposal_required_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.request
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.request_from_proposal
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.effect
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.effect_from_request
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.nextState
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredCausalStage.nextState_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.executeReconfiguredInteractions
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.requests
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.events
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.finalState
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.requests_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.headStage
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.tail
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredInteractionHistory.headRequest
#print axioms ConstitutiveSearch.NeuralAgent.reconfigured_head_horizon_independent
/- AXIOM_AUDIT_END -/
