import RelationalPerimeter.Mechanisms.Native.Execution

/-!
# Native mechanistic occurrences

Occurrences are indexed by an executed run and a position. Equal activation
values do not identify received-input and neuron-output occurrences, nor two
uses of the same parameter in different runs.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

inductive ActivationOccurrence
    {inputCount produced : Nat}
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) where
  | receivedInput (index : Fin inputCount)
  | neuronOutput (index : Fin produced)

def ActivationOccurrence.value
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program} : ActivationOccurrence run -> Activation
  | .receivedInput index => run.inputs.read index
  | .neuronOutput index => run.activations.read index

def NetworkProgram.sourceOccurrence
    {inputCount produced : Nat}
    (program : NetworkProgram inputCount produced)
    (run : NativeRun program) (target : Fin produced) :
    SourceIndex inputCount target.val -> ActivationOccurrence run
  | .receivedInput index => .receivedInput index
  | .priorNeuron index =>
      .neuronOutput ⟨index.val, Nat.lt_trans index.isLt target.isLt⟩

def NetworkProgram.activationsBefore
    {inputCount produced : Nat}
    (program : NetworkProgram inputCount produced)
    (run : NativeRun program) (target : Fin produced) :
    SizedActivations target.val :=
  run.trace.activationsBefore target

structure ProposalOccurrence
    (system : NativeSystem Input Proposal) (input : Input) where
  value : Proposal
  valueExact : value = system.proposal input

def NativeSystem.proposalOccurrence
    (system : NativeSystem Input Proposal) (input : Input) :
    ProposalOccurrence system input :=
  { value := system.proposal input
    valueExact := rfl }

structure ParameterResource
    (program : NetworkProgram inputCount produced) where
  target : Fin produced
  edge : WeightedInput inputCount target.val
  member : edge ∈ (program.neuronAt target).inputs

structure WeightUseOccurrence
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) where
  resource : ParameterResource program
  readSource : ActivationOccurrence run
  sourceExact : readSource =
    program.sourceOccurrence run resource.target resource.edge.source

inductive MechanismScale where
  | parameter
  | weightUse
  | neuron
  | functionalUnit
  | circuit
  | layer

structure OutputOccurrence
    (system : NativeSystem Input Proposal) (input : Input) where
  port : Fin system.outputs.sources.length
  activation : Activation
  activationExact : activation =
    (system.run input).activations.read (system.outputs.sources.get port)

def occurrencePosition
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program} : ActivationOccurrence run -> Nat
  | .receivedInput index => index.val
  | .neuronOutput index => program.inputCount + index.val

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.ActivationOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.ActivationOccurrence.value
#print axioms ConstitutiveSearch.NativeMechanism.NetworkProgram.sourceOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.NetworkProgram.activationsBefore
#print axioms ConstitutiveSearch.NativeMechanism.ProposalOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.NativeSystem.proposalOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.ParameterResource
#print axioms ConstitutiveSearch.NativeMechanism.WeightUseOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.OutputOccurrence
/- AXIOM_AUDIT_END -/
