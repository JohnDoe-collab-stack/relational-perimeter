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

/-- One local transformation as it was executed between two exact occurrences
of one native run.  Its only field is the effective edge that the executed
neuron consumed.  The transformation function and its exactness equation are
derived below from that neuron, its exact prefix, and the selected source;
callers cannot install a function after observing the target value. -/
structure ExecutedSignalTransformation
    {inputCount producedCount : Nat}
    {program : NetworkProgram inputCount producedCount}
    (run : NativeRun program)
    (source target : ActivationOccurrence run) where
  edge : EffectiveReadsFrom run source target

def executedEdgeSignalTransform
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {source target : ActivationOccurrence run}
    (edge : EffectiveReadsFrom run source target) :
    Activation -> Activation :=
  match edge with
  | .executedEdge destination edge _ _ =>
      match edge.source with
      | .receivedInput index => fun replacement =>
          fireNeuron (program.neuronAt destination)
            (run.inputs.replace index replacement)
            (run.trace.activationsBefore destination)
      | .priorNeuron index => fun replacement =>
          fireNeuron (program.neuronAt destination) run.inputs
            ((run.trace.activationsBefore destination).replace index replacement)

theorem executedEdgeSignalOutputExact
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {source target : ActivationOccurrence run}
    (edge : EffectiveReadsFrom run source target) :
    target.value = executedEdgeSignalTransform edge source.value := by
  cases edge with
  | executedEdge destination edge member weightNonzero =>
      cases edge with
      | mk edgeSource weight =>
          cases edgeSource with
          | receivedInput index =>
              change run.activations.read destination =
                fireNeuron (program.neuronAt destination)
                  (run.inputs.replace index (run.inputs.read index))
                  (run.trace.activationsBefore destination)
              rw [SizedActivations.replace_self]
              exact run.trace.neuron_output_exact destination
          | priorNeuron index =>
              change run.activations.read destination =
                fireNeuron (program.neuronAt destination) run.inputs
                  ((run.trace.activationsBefore destination).replace index
                    (run.activations.read
                      ⟨index.val, Nat.lt_trans index.isLt destination.isLt⟩))
              rw [← run.trace.activationsBefore_read_exact destination index]
              rw [SizedActivations.replace_self]
              exact run.trace.neuron_output_exact destination

def ExecutedSignalTransformation.transform
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {source target : ActivationOccurrence run}
    (transition : ExecutedSignalTransformation run source target) :
    Activation -> Activation :=
  executedEdgeSignalTransform transition.edge

theorem ExecutedSignalTransformation.outputExact
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {source target : ActivationOccurrence run}
    (transition : ExecutedSignalTransformation run source target) :
    target.value = transition.transform source.value :=
  executedEdgeSignalOutputExact transition.edge

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
#print axioms ConstitutiveSearch.NeuralAgent.executedEdgeSignalTransform
#print axioms ConstitutiveSearch.NeuralAgent.executedEdgeSignalOutputExact
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedSignalTransformation.transform
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedSignalTransformation.outputExact
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPath
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalPath.signalExact
#print axioms ConstitutiveSearch.NeuralAgent.RequirementSignalTransformation
#print axioms ConstitutiveSearch.NeuralAgent.proposal_aligned
#print axioms ConstitutiveSearch.NeuralAgent.aligned_proposal_formation
/- AXIOM_AUDIT_END -/
