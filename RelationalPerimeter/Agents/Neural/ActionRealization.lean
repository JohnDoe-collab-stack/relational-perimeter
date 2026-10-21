import RelationalPerimeter.Agents.Neural.ProposalAlignment
import RelationalPerimeter.Agents.Constitutive.Execution

/-!
# From an aligned proposal to an executed agent action

The command is computed from the proposal occurrence produced by the native
run.  The action result is then the output of the existing proof-carrying agent
executor.  Neither a command nor an effect can be supplied independently.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

universe u v w

/-- The operational interpretation of a proposal.  It contains no result and
therefore cannot certify an action by itself. -/
structure AgentActionChannel (Proposal : Type w) where
  command : Proposal -> Agent.Request

/-- A proposal-alignment witness followed by the actual agent executor.
The private constructor prevents clients from replacing either the command or
the produced result while retaining this type. -/
structure ActionRealization
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    (channel : AgentActionChannel Proposal)
    (preservation : RequirementSignalPreservation decoder incorporation)
    (memory : Agent.Memory) : Type 3 where
  private mk ::
  request : Agent.Request
  requestExact :
    request = channel.command (system.proposalOccurrence input).value
  result : Agent.Memory × Agent.Event
  evidence : Agent.RequestEvidence memory request result
  resultExact : result = Agent.executeInput memory request

/-- Execute the command read from the proposal that was aligned through the
native run. -/
def realizeAction
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    (channel : AgentActionChannel Proposal)
    (preservation : RequirementSignalPreservation decoder incorporation)
    (memory : Agent.Memory) :
    ActionRealization channel preservation memory :=
  let request := channel.command (system.proposalOccurrence input).value
  let produced := Agent.executeProducedInput memory request
  .mk request rfl produced.1 produced.2 rfl

theorem ActionRealization.request_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    {channel : AgentActionChannel Proposal}
    {preservation : RequirementSignalPreservation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel preservation memory) :
    action.request =
      channel.command (family.requiredProposal input.requirement input.context) := by
  exact action.requestExact.trans
    (congrArg channel.command (proposal_aligned preservation))

theorem ActionRealization.execution_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    {channel : AgentActionChannel Proposal}
    {preservation : RequirementSignalPreservation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel preservation memory) :
    action.result = Agent.executeInput memory action.request :=
  action.resultExact

/-- The effect layer is explicitly distinct from action execution.  Its fields
are fixed to the successor and event produced by that execution. -/
structure EffectRealization
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    {channel : AgentActionChannel Proposal}
    {preservation : RequirementSignalPreservation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel preservation memory) : Type 3 where
  private mk ::
  successor : Agent.Memory
  event : Agent.Event
  successorExact : successor = action.result.1
  eventExact : event = action.result.2

def realizeEffect
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    {channel : AgentActionChannel Proposal}
    {preservation : RequirementSignalPreservation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel preservation memory) :
    EffectRealization action :=
  .mk action.result.1 action.result.2 rfl rfl

theorem EffectRealization.effect_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    {channel : AgentActionChannel Proposal}
    {preservation : RequirementSignalPreservation decoder incorporation}
    {memory : Agent.Memory}
    {action : ActionRealization channel preservation memory}
    (effect : EffectRealization action) :
    (effect.successor, effect.event) = Agent.executeInput memory action.request := by
  rw [effect.successorExact, effect.eventExact]
  exact action.execution_exact

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.AgentActionChannel
#print axioms ConstitutiveSearch.NeuralAgent.ActionRealization
#print axioms ConstitutiveSearch.NeuralAgent.realizeAction
#print axioms ConstitutiveSearch.NeuralAgent.ActionRealization.request_exact
#print axioms ConstitutiveSearch.NeuralAgent.ActionRealization.execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.EffectRealization
#print axioms ConstitutiveSearch.NeuralAgent.realizeEffect
#print axioms ConstitutiveSearch.NeuralAgent.EffectRealization.effect_exact
/- AXIOM_AUDIT_END -/
