import RelationalPerimeter.Agents.Neural.ProposalAlignment

/-!
# Sensitivity to distinct received requirements

The same context is held fixed.  Distinct received requirements must have
distinct required proposals, while their actual proposals are obtained from
the two executed transformation witnesses.  Consequently a constant encoder or
a constant proposal cannot inhabit the separating result.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

universe u v w

structure SeparatingRequirements
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal)
    (left right : RequirementCase) (context : Context) where
  receivedDistinct : family.received left ≠ family.received right
  requiredDistinct :
    family.requiredProposal left context ≠
      family.requiredProposal right context

theorem separating_requirement_codes
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system)
    {left right : RequirementCase} {context : Context}
    (separation : SeparatingRequirements family left right context) :
    encoding.code left context ≠ encoding.code right context := by
  intro same
  exact separation.receivedDistinct
    (encoding.requirementReflecting left right context same)

/-- Two contexts are separated for one fixed received requirement.  Both the
contexts themselves and the proposals required from them are distinct. -/
structure SeparatingContexts
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal)
    (requirement : RequirementCase) (left right : Context) where
  contextsDistinct : left ≠ right
  requiredDistinct :
    family.requiredProposal requirement left ≠
      family.requiredProposal requirement right

theorem separating_terminal_representations
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    (decoder : SingleOutputRequirementDecoder encoding)
    {requirement : RequirementCase} {left right : Context}
    (separation : SeparatingContexts family requirement left right) :
    decoder.terminalRepresentation requirement left ≠
      decoder.terminalRepresentation requirement right := by
  intro same
  apply separation.requiredDistinct
  rw [← decoder.decodeRepresentation requirement left,
      ← decoder.decodeRepresentation requirement right, same]

theorem separating_executed_proposals
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {left right : RequirementCase} {context : Context}
    (separation : SeparatingRequirements family left right context)
    {leftIncorporation : RequirementIncorporation encoding
      (RequirementInput.mk left context)}
    {rightIncorporation : RequirementIncorporation encoding
      (RequirementInput.mk right context)}
    (leftTransformation :
      RequirementSignalTransformation decoder leftIncorporation)
    (rightTransformation :
      RequirementSignalTransformation decoder rightIncorporation) :
    system.proposal (RequirementInput.mk left context) ≠
      system.proposal (RequirementInput.mk right context) := by
  intro same
  apply separation.requiredDistinct
  rw [← proposal_aligned leftTransformation,
      ← proposal_aligned rightTransformation]
  exact same

theorem separating_contextual_executed_proposals
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {requirement : RequirementCase} {left right : Context}
    (separation : SeparatingContexts family requirement left right)
    {leftIncorporation : RequirementIncorporation encoding
      (RequirementInput.mk requirement left)}
    {rightIncorporation : RequirementIncorporation encoding
      (RequirementInput.mk requirement right)}
    (leftTransformation :
      RequirementSignalTransformation decoder leftIncorporation)
    (rightTransformation :
      RequirementSignalTransformation decoder rightIncorporation) :
    system.proposal (RequirementInput.mk requirement left) ≠
      system.proposal (RequirementInput.mk requirement right) := by
  intro same
  apply separation.requiredDistinct
  rw [← proposal_aligned leftTransformation,
      ← proposal_aligned rightTransformation]
  exact same

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.SeparatingRequirements
#print axioms ConstitutiveSearch.NeuralAgent.separating_requirement_codes
#print axioms ConstitutiveSearch.NeuralAgent.SeparatingContexts
#print axioms ConstitutiveSearch.NeuralAgent.separating_terminal_representations
#print axioms ConstitutiveSearch.NeuralAgent.separating_executed_proposals
#print axioms ConstitutiveSearch.NeuralAgent.separating_contextual_executed_proposals
/- AXIOM_AUDIT_END -/
