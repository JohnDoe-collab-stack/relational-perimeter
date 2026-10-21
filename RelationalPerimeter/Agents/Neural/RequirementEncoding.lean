import RelationalPerimeter.Mechanisms.Native.Explanation
import RelationalPerimeter.Agents.Constitutive.Requirement

/-!
# Requirements received and incorporated by a native execution

The requirement is not an output label.  A family names the received
requirement and the proposal required in one context.  The requirement and its
context are encoded jointly at one declared input occurrence of the native
run.  Equality of codes must reflect equality of requirements when the context
is fixed.  Context sensitivity is established where the required proposal
actually distinguishes contexts; contexts equivalent for a contract need not
be separated globally.  Incorporation additionally requires that this very
input occurrence has an executed causal role in the produced proposal.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

universe u v w

structure RequirementFamily
    (RequirementCase : Type u) (Context : Type v) (Proposal : Type w) where
  received : RequirementCase -> Agent.Requirement
  requiredProposal : RequirementCase -> Context -> Proposal

structure RequirementInput
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal) where
  requirement : RequirementCase
  context : Context

def RequirementInput.receivedRequirement
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (input : RequirementInput family) : Agent.Requirement :=
  family.received input.requirement

structure RequirementEncoding
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (system : NativeSystem (RequirementInput family) Proposal) where
  port : Fin system.inputCount
  code : RequirementCase -> Context -> Activation
  inputExact : forall input,
    (system.encode input).read port = code input.requirement input.context
  requirementReflecting : forall one two context,
    code one context = code two context ->
      family.received one = family.received two

theorem encoded_requirement_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system)
    (input : RequirementInput family) :
    (ActivationOccurrence.receivedInput encoding.port :
      ActivationOccurrence (system.run input)).value =
        encoding.code input.requirement input.context :=
  encoding.inputExact input

structure RequirementIncorporation
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system)
    (input : RequirementInput family) where
  role : CausalRole system input (.receivedInput encoding.port)

def incorporated_requirement_has_executed_path
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {input : RequirementInput family}
    (incorporation : RequirementIncorporation encoding input) :
    Sigma fun output : Fin system.outputs.sources.length =>
      Reaches (system.run input) (.receivedInput encoding.port)
        (.neuronOutput (system.outputs.sources.get output)) :=
  causal_role_has_executed_path incorporation.role

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.RequirementFamily
#print axioms ConstitutiveSearch.NeuralAgent.RequirementInput
#print axioms ConstitutiveSearch.NeuralAgent.RequirementInput.receivedRequirement
#print axioms ConstitutiveSearch.NeuralAgent.RequirementEncoding
#print axioms ConstitutiveSearch.NeuralAgent.encoded_requirement_exact
#print axioms ConstitutiveSearch.NeuralAgent.RequirementIncorporation
#print axioms ConstitutiveSearch.NeuralAgent.incorporated_requirement_has_executed_path
/- AXIOM_AUDIT_END -/
