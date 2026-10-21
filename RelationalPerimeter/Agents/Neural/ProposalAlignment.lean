import RelationalPerimeter.Agents.Neural.RequirementEncoding

/-!
# Proposal alignment through the executed native run

For the present one-output contract, decoding is specified on a terminal
representation of the requirement.  A transformation path connects the
received code to that representation through local functions whose equations
hold at the exact source and target occurrences of the executed run.  The
alignment theorem eliminates the actual output readout; it does not consult a
proposal table or apply an output filter.
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
  terminalRepresentation : RequirementCase -> Context -> Activation
  decodeRepresentation : forall requirement context,
    system.decode [terminalRepresentation requirement context] =
      family.requiredProposal requirement context

/-- One local transformation as it was executed between two exact
occurrences of one native run.  The function is data; `outputExact` certifies
that this function produced the target value from the source value. -/
structure ExecutedSignalTransformation
    {inputCount producedCount : Nat}
    {program : NetworkProgram inputCount producedCount}
    (run : NativeRun program)
    (source target : ActivationOccurrence run) where
  transform : Activation -> Activation
  edge : ReadsFrom run source target
  outputExact : target.value = transform source.value

inductive RequirementSignalPath
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    (encoding : RequirementEncoding system)
    (input : RequirementInput family) :
    ActivationOccurrence (system.run input) ->
      (Activation -> Activation) -> Type where
  | origin : RequirementSignalPath encoding input
      (.receivedInput encoding.port) (fun value => value)
  | step {source target : ActivationOccurrence (system.run input)}
      {accumulated : Activation -> Activation}
      (prior : RequirementSignalPath encoding input source accumulated)
      (transition :
        ExecutedSignalTransformation (system.run input) source target) :
      RequirementSignalPath encoding input target
        (fun value => transition.transform (accumulated value))

theorem RequirementSignalPath.signalExact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {input : RequirementInput family}
    {target : ActivationOccurrence (system.run input)}
    {accumulated : Activation -> Activation} :
    RequirementSignalPath encoding input target accumulated ->
      target.value = accumulated
        (encoding.code input.requirement input.context)
  | .origin => encoded_requirement_exact encoding input
  | .step prior transition =>
      transition.outputExact.trans
        (congrArg transition.transform prior.signalExact)

structure RequirementSignalTransformation
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    (decoder : SingleOutputRequirementDecoder encoding)
    {input : RequirementInput family}
    (incorporation : RequirementIncorporation encoding input) where
  roleOutputExact :
    system.outputs.sources.get incorporation.role.output = decoder.output
  transform : Activation -> Activation
  path : RequirementSignalPath encoding input
    (.neuronOutput decoder.output) transform
  terminalExact :
    transform (encoding.code input.requirement input.context) =
      decoder.terminalRepresentation input.requirement input.context

theorem proposal_aligned
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    (transformation :
      RequirementSignalTransformation decoder incorporation) :
    system.proposal input =
      family.requiredProposal input.requirement input.context := by
  unfold NativeSystem.proposal NativeSystem.outputValues readOutputs
  rw [decoder.portsExact]
  change system.decode [
    (ActivationOccurrence.neuronOutput decoder.output :
      ActivationOccurrence (system.run input)).value] = _
  rw [transformation.path.signalExact, transformation.terminalExact]
  exact decoder.decodeRepresentation input.requirement input.context

def aligned_proposal_formation
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {input : RequirementInput family}
    {incorporation : RequirementIncorporation encoding input}
    (_transformation :
      RequirementSignalTransformation decoder incorporation) :
    ProposalFormedBy system input (system.proposalOccurrence input) :=
  proposalFormation system input

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.SingleOutputRequirementDecoder
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedSignalTransformation
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPath
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPath.signalExact
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalTransformation
#print axioms ConstitutiveSearch.NeuralAgent.proposal_aligned
#print axioms ConstitutiveSearch.NeuralAgent.aligned_proposal_formation
/- AXIOM_AUDIT_END -/
