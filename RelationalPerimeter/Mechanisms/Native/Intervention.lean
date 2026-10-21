import RelationalPerimeter.Mechanisms.Native.Circuit

/-!
# Native interventions and causal-use witnesses

An intervention changes exactly one received input or one neuron output and
then executes the same chronological program. Causal usefulness requires a
change at the declared output and after decoding; nonzero activation alone is
kept separate.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

inductive InterventionFocus (inputCount produced : Nat) where
  | input : Fin inputCount -> InterventionFocus inputCount produced
  | neuron : Fin produced -> InterventionFocus inputCount produced

def ActivationOccurrence.interventionFocus
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program} :
    ActivationOccurrence run -> InterventionFocus inputCount produced
  | .receivedInput index => .input index
  | .neuronOutput index => .neuron index

def NativeRun.valueAt
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :
    InterventionFocus inputCount produced -> Activation
  | .input index => run.inputs.read index
  | .neuron index => run.activations.read index

structure Intervention
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) where
  focus : InterventionFocus inputCount produced
  replacement : Activation
  changesValue : replacement ≠ run.valueAt focus

def Intervention.focusOccurrence
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (intervention : Intervention run) : ActivationOccurrence run :=
  match intervention.focus with
  | .input index => .receivedInput index
  | .neuron index => .neuronOutput index

def executeWithNeuronOverride {inputCount : Nat} :
    {produced : Nat} ->
    NetworkProgram inputCount produced ->
    SizedActivations inputCount -> Nat -> Activation ->
    SizedActivations produced
  | _, .empty, _, _, _ => SizedActivations.empty
  | _, .extend (produced := priorCount) prior neuron,
      inputs, target, replacement =>
      let priorValues :=
        executeWithNeuronOverride prior inputs target replacement
      let computed := fireNeuron neuron inputs priorValues
      SizedActivations.snoc priorValues
        (if target = priorCount then replacement else computed)

def executeIntervened
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (intervention : Intervention run) : SizedActivations produced :=
  match intervention.focus with
  | .input index =>
      executeProgram program
        (run.inputs.replace index intervention.replacement)
  | .neuron index =>
      executeWithNeuronOverride program run.inputs index.val
        intervention.replacement

def intervenedOutputs
    (system : NativeSystem Input Proposal)
    (input : Input)
    (intervention : Intervention (system.run input)) : List Activation :=
  readOutputs system.outputs
    (executeIntervened intervention)

def intervenedValue
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (intervention : Intervention run) :
    ActivationOccurrence run -> Activation
  | .receivedInput index =>
      match intervention.focus with
      | .input focus =>
          (run.inputs.replace focus intervention.replacement).read index
      | .neuron _ => run.inputs.read index
  | .neuronOutput index => (executeIntervened intervention).read index

structure OccurrenceChanged
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (intervention : Intervention run)
    (occurrence : ActivationOccurrence run) where
  different : intervenedValue intervention occurrence ≠ occurrence.value

/-- An executed edge is effective only when its declared weight is nonzero.
This prevents graph membership alone, in particular a decorative zero-weight
edge, from witnessing causal propagation. -/
inductive EffectiveReadsFrom
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :
    ActivationOccurrence run -> ActivationOccurrence run -> Type where
  | executedEdge
      (target : Fin produced)
      (edge : WeightedInput inputCount target.val)
      (member : edge ∈ (program.neuronAt target).inputs)
      (weightNonzero : edge.weight ≠ 0) :
      EffectiveReadsFrom run (program.sourceOccurrence run target edge.source)
        (.neuronOutput target)

def EffectiveReadsFrom.toReadsFrom
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {source target : ActivationOccurrence run} :
    EffectiveReadsFrom run source target -> ReadsFrom run source target
  | .executedEdge destination edge member _ =>
      .executedEdge destination edge member

inductive ExecutedChangePath
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (intervention : Intervention run) : ActivationOccurrence run -> Type where
  | origin : ExecutedChangePath intervention intervention.focusOccurrence
  | step {source target : ActivationOccurrence run}
      (prior : ExecutedChangePath intervention source)
      (edge : EffectiveReadsFrom run source target)
      (targetChanged : OccurrenceChanged intervention target) :
      ExecutedChangePath intervention target

def ExecutedChangePath.toReaches
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {intervention : Intervention run}
    {target : ActivationOccurrence run} :
    ExecutedChangePath intervention target ->
      Reaches run intervention.focusOccurrence target
  | .origin => .refl _
  | .step prior edge _ =>
      prior.toReaches.trans (.step edge.toReadsFrom (.refl _))

inductive NontrivialExecutedChangePath
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (intervention : Intervention run) : ActivationOccurrence run -> Type where
  | step {source target : ActivationOccurrence run}
      (prior : ExecutedChangePath intervention source)
      (edge : EffectiveReadsFrom run source target)
      (targetChanged : OccurrenceChanged intervention target) :
      NontrivialExecutedChangePath intervention target

def NontrivialExecutedChangePath.toChangePath
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {intervention : Intervention run}
    {target : ActivationOccurrence run} :
    NontrivialExecutedChangePath intervention target ->
      ExecutedChangePath intervention target
  | .step prior edge changed => .step prior edge changed

def NontrivialExecutedChangePath.toReaches
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {intervention : Intervention run}
    {target : ActivationOccurrence run} :
    NontrivialExecutedChangePath intervention target ->
      Reaches run intervention.focusOccurrence target
  | path => path.toChangePath.toReaches

structure ChangesTarget
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) (intervention : Intervention run)
    (target : OutputPorts produced) where
  different :
    readOutputs target
        (executeIntervened intervention) ≠
      readOutputs target run.activations

structure ChangesProposal
    (system : NativeSystem Input Proposal) (input : Input)
    (intervention : Intervention (system.run input)) where
  different :
    system.decode (intervenedOutputs system input intervention) ≠
      system.proposal input

structure CausalRole
    (system : NativeSystem Input Proposal) (input : Input)
    (focus : ActivationOccurrence (system.run input)) where
  intervention : Intervention (system.run input)
  focusExact : intervention.focusOccurrence = focus
  output : Fin system.outputs.sources.length
  propagation : NontrivialExecutedChangePath intervention
    (.neuronOutput (system.outputs.sources.get output))
  targetChange : ChangesTarget (system.run input) intervention system.outputs
  proposalChange : ChangesProposal system input intervention

def causal_role_has_executed_path
    {system : NativeSystem Input Proposal} {input : Input}
    {focus : ActivationOccurrence (system.run input)}
    (role : CausalRole system input focus) :
    Sigma fun output : Fin system.outputs.sources.length =>
      Reaches (system.run input) focus
        (.neuronOutput (system.outputs.sources.get output)) :=
  ⟨role.output,
    Eq.mp
      (congrArg
        (fun source => Reaches (system.run input) source
          (.neuronOutput (system.outputs.sources.get role.output)))
        role.focusExact)
      role.propagation.toReaches⟩

structure ContributesTo
    (system : NativeSystem Input Proposal) (input : Input)
    (source : ActivationOccurrence (system.run input))
    (target : ProposalOccurrence system input) where
  role : CausalRole system input source
  targetExact : target.value = system.proposal input

def Activated
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (occurrence : ActivationOccurrence run) : Prop :=
  occurrence.value ≠ 0

def UsefulForProposal
    (system : NativeSystem Input Proposal) (input : Input)
    (occurrence : ActivationOccurrence (system.run input)) : Type :=
  CausalRole system input occurrence

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.InterventionFocus
#print axioms ConstitutiveSearch.NativeMechanism.Intervention
#print axioms ConstitutiveSearch.NativeMechanism.Intervention.focusOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.executeWithNeuronOverride
#print axioms ConstitutiveSearch.NativeMechanism.executeIntervened
#print axioms ConstitutiveSearch.NativeMechanism.intervenedOutputs
#print axioms ConstitutiveSearch.NativeMechanism.intervenedValue
#print axioms ConstitutiveSearch.NativeMechanism.OccurrenceChanged
#print axioms ConstitutiveSearch.NativeMechanism.EffectiveReadsFrom
#print axioms ConstitutiveSearch.NativeMechanism.EffectiveReadsFrom.toReadsFrom
#print axioms ConstitutiveSearch.NativeMechanism.ExecutedChangePath
#print axioms ConstitutiveSearch.NativeMechanism.ExecutedChangePath.toReaches
#print axioms ConstitutiveSearch.NativeMechanism.NontrivialExecutedChangePath
#print axioms ConstitutiveSearch.NativeMechanism.NontrivialExecutedChangePath.toChangePath
#print axioms ConstitutiveSearch.NativeMechanism.NontrivialExecutedChangePath.toReaches
#print axioms ConstitutiveSearch.NativeMechanism.ChangesTarget
#print axioms ConstitutiveSearch.NativeMechanism.ChangesProposal
#print axioms ConstitutiveSearch.NativeMechanism.CausalRole
#print axioms ConstitutiveSearch.NativeMechanism.causal_role_has_executed_path
#print axioms ConstitutiveSearch.NativeMechanism.ContributesTo
#print axioms ConstitutiveSearch.NativeMechanism.Activated
#print axioms ConstitutiveSearch.NativeMechanism.UsefulForProposal
/- AXIOM_AUDIT_END -/
