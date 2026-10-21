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

/-- The operational interpretation of a proposal.  Besides the command, the
channel declares exactly which proposal distinctions must remain operational
distinctions and exactly which proposal collisions it permits.  It contains no
result and therefore cannot certify an action by itself. -/
structure AgentActionChannel (Proposal : Type w) where
  command : Proposal -> Agent.Request
  proposalDistinction : Proposal -> Proposal -> Prop
  collisionPermission : Proposal -> Proposal -> Prop
  preservesDistinction : forall {left right},
    proposalDistinction left right -> command left ≠ command right
  collisionExact : forall {left right},
    collisionPermission left right ↔ command left = command right

/-- A distinction that the proposal contract requires the action channel to
preserve. -/
abbrev DistinctAccordingToProposalContract
    {Proposal : Type w} (channel : AgentActionChannel Proposal)
    (left right : Proposal) : Prop :=
  channel.proposalDistinction left right

/-- Operational distinction is literal distinction of the requests submitted
to the executor. -/
def DistinctAccordingToActionContract
    {Proposal : Type w} (_channel : AgentActionChannel Proposal)
    (left right : Agent.Request) : Prop :=
  left ≠ right

/-- A collision is permitted only through the channel's declared collision
contract. -/
abbrev CollisionPermittedByProposalContract
    {Proposal : Type w} (channel : AgentActionChannel Proposal)
    (left right : Proposal) : Prop :=
  channel.collisionPermission left right

theorem AgentActionChannel.preserves_required_distinction
    {Proposal : Type w} (channel : AgentActionChannel Proposal)
    {left right : Proposal}
    (distinct : DistinctAccordingToProposalContract channel left right) :
    DistinctAccordingToActionContract channel
      (channel.command left) (channel.command right) :=
  channel.preservesDistinction distinct

theorem AgentActionChannel.collision_characterized
    {Proposal : Type w} (channel : AgentActionChannel Proposal)
    {left right : Proposal} :
    CollisionPermittedByProposalContract channel left right ↔
      channel.command left = channel.command right :=
  channel.collisionExact

theorem AgentActionChannel.required_distinction_forbids_collision
    {Proposal : Type w} (channel : AgentActionChannel Proposal)
    {left right : Proposal}
    (distinct : DistinctAccordingToProposalContract channel left right)
    (permitted : CollisionPermittedByProposalContract channel left right) :
    False :=
  channel.preserves_required_distinction distinct
    (channel.collision_characterized.mp permitted)

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
    (transformation : RequirementSignalTransformation decoder incorporation)
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
    (transformation : RequirementSignalTransformation decoder incorporation)
    (memory : Agent.Memory) :
    ActionRealization channel transformation memory :=
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
    {transformation : RequirementSignalTransformation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel transformation memory) :
    action.request =
      channel.command (family.requiredProposal input.requirement input.context) := by
  exact action.requestExact.trans
    (congrArg channel.command (proposal_aligned transformation))

theorem ActionRealization.execution_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    {channel : AgentActionChannel Proposal}
    {transformation : RequirementSignalTransformation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel transformation memory) :
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
    {transformation : RequirementSignalTransformation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel transformation memory) : Type 3 where
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
    {transformation : RequirementSignalTransformation decoder incorporation}
    {memory : Agent.Memory}
    (action : ActionRealization channel transformation memory) :
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
    {transformation : RequirementSignalTransformation decoder incorporation}
    {memory : Agent.Memory}
    {action : ActionRealization channel transformation memory}
    (effect : EffectRealization action) :
    (effect.successor, effect.event) = Agent.executeInput memory action.request := by
  rw [effect.successorExact, effect.eventExact]
  exact action.execution_exact

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.AgentActionChannel
#print axioms ConstitutiveSearch.NeuralAgent.DistinctAccordingToProposalContract
#print axioms ConstitutiveSearch.NeuralAgent.DistinctAccordingToActionContract
#print axioms ConstitutiveSearch.NeuralAgent.CollisionPermittedByProposalContract
#print axioms ConstitutiveSearch.NeuralAgent.AgentActionChannel.preserves_required_distinction
#print axioms ConstitutiveSearch.NeuralAgent.AgentActionChannel.collision_characterized
#print axioms ConstitutiveSearch.NeuralAgent.AgentActionChannel.required_distinction_forbids_collision
#print axioms ConstitutiveSearch.NeuralAgent.ActionRealization
#print axioms ConstitutiveSearch.NeuralAgent.realizeAction
#print axioms ConstitutiveSearch.NeuralAgent.ActionRealization.request_exact
#print axioms ConstitutiveSearch.NeuralAgent.ActionRealization.execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.EffectRealization
#print axioms ConstitutiveSearch.NeuralAgent.realizeEffect
#print axioms ConstitutiveSearch.NeuralAgent.EffectRealization.effect_exact
/- AXIOM_AUDIT_END -/
