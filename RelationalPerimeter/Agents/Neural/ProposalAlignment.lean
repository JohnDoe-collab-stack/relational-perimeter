import RelationalPerimeter.Agents.Neural.RequirementEncoding

/-!
# Proposal alignment through the executed native run

For the present one-output contract, decoding is specified only on the signal
that the requirement encoder produced.  A preservation witness must connect
that signal to the declared output occurrence selected by the causal role.
The alignment theorem then eliminates the actual output readout; it does not
consult a proposal table or apply an output filter.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

universe u v w

structure SingleOutputRequirementDecoder
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system) where
  output : Fin system.producedCount
  portsExact : system.outputs.sources = [output]
  decodeCode : forall requirement context,
    system.decode [encoding.code requirement] =
      family.requiredProposal requirement context

inductive RequirementSignalPath
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system)
    (input : RequirementInput family) :
    ActivationOccurrence (system.run input) -> Type where
  | origin : RequirementSignalPath encoding input
      (.receivedInput encoding.port)
  | step {source target : ActivationOccurrence (system.run input)}
      (prior : RequirementSignalPath encoding input source)
      (edge : ReadsFrom (system.run input) source target)
      (preserved : target.value = source.value) :
      RequirementSignalPath encoding input target

theorem RequirementSignalPath.signalExact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {input : RequirementInput family}
    {target : ActivationOccurrence (system.run input)} :
    RequirementSignalPath encoding input target ->
      target.value = encoding.code input.requirement
  | .origin => encoded_requirement_exact encoding input
  | .step prior _ preserved => preserved.trans prior.signalExact

structure RequirementSignalPreservation
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    (decoder : SingleOutputRequirementDecoder encoding)
    {input : RequirementInput family}
    (incorporation : RequirementIncorporation encoding input) where
  roleOutputExact :
    system.outputs.sources.get incorporation.role.output = decoder.output
  path : RequirementSignalPath encoding input
    (.neuronOutput decoder.output)

theorem proposal_aligned
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    (preservation : RequirementSignalPreservation decoder incorporation) :
    system.proposal input =
      family.requiredProposal input.requirement input.context := by
  unfold NativeSystem.proposal NativeSystem.outputValues readOutputs
  rw [decoder.portsExact]
  change system.decode [
    (ActivationOccurrence.neuronOutput decoder.output :
      ActivationOccurrence (system.run input)).value] = _
  rw [preservation.path.signalExact]
  exact decoder.decodeCode input.requirement input.context

def aligned_proposal_formation
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    (_preservation : RequirementSignalPreservation decoder incorporation) :
    ProposalFormedBy system input (system.proposalOccurrence input) :=
  proposalFormation system input

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.SingleOutputRequirementDecoder
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPath
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPath.signalExact
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPreservation
#print axioms ConstitutiveSearch.NeuralAgent.proposal_aligned
#print axioms ConstitutiveSearch.NeuralAgent.aligned_proposal_formation
/- AXIOM_AUDIT_END -/
