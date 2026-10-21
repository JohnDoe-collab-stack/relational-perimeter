import RelationalPerimeter.Mechanisms.Native.Occurrence

/-!
# Constitutive relations of native mechanism occurrences

Edges are witnessed by membership in the executed program. Formation, order,
use and propagation are separate relations; none is inferred from activation
equality or from an interpretive label.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

inductive ReadsFrom
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :
    ActivationOccurrence run -> ActivationOccurrence run -> Type where
  | executedEdge
      (target : Fin produced)
      (edge : WeightedInput inputCount target.val)
      (member : edge ∈ (program.neuronAt target).inputs) :
      ReadsFrom run (program.sourceOccurrence run target edge.source)
        (.neuronOutput target)

inductive ConsecutiveReadsFrom
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :
    List (ActivationOccurrence run) -> Type where
  | nil : ConsecutiveReadsFrom run []
  | singleton (only : ActivationOccurrence run) :
      ConsecutiveReadsFrom run [only]
  | cons (edge : ReadsFrom run source target)
      (tail : ConsecutiveReadsFrom run (target :: rest)) :
      ConsecutiveReadsFrom run (source :: target :: rest)

structure PropagatesTo
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (source target : ActivationOccurrence run) where
  path : List (ActivationOccurrence run)
  begins : path.head? = some source
  ends : path.getLast? = some target
  consecutive : ConsecutiveReadsFrom run path

inductive Reaches
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :
    ActivationOccurrence run -> ActivationOccurrence run -> Type where
  | refl (occurrence : ActivationOccurrence run) :
      Reaches run occurrence occurrence
  | step (edge : ReadsFrom run source middle)
      (tail : Reaches run middle target) : Reaches run source target

def Reaches.trans
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {source middle target : ActivationOccurrence run} :
    Reaches run source middle -> Reaches run middle target ->
      Reaches run source target
  | .refl _, tail => tail
  | .step edge rest, tail => .step edge (rest.trans tail)

inductive FormedBy
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) : ActivationOccurrence run -> Type where
  | received (index : Fin inputCount) :
      FormedBy run (.receivedInput index)
  | neuron (target : Fin produced)
      (outputExact :
        (ActivationOccurrence.neuronOutput target : ActivationOccurrence run).value =
          fireNeuron (program.neuronAt target)
            run.inputs (program.activationsBefore run target)) :
      FormedBy run (.neuronOutput target)

def formedBy
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :
    (occurrence : ActivationOccurrence run) -> FormedBy run occurrence
  | .receivedInput index => .received index
  | .neuronOutput target =>
      .neuron target (run.trace.neuron_output_exact target)

structure ProposalFormedBy
    (system : NativeSystem Input Proposal) (input : Input)
    (proposal : ProposalOccurrence system input) where
  sourceValues : List Activation
  sourceExact : sourceValues = system.outputValues input
  outputExact : proposal.value = system.decode sourceValues

def proposalFormation
    (system : NativeSystem Input Proposal) (input : Input) :
    ProposalFormedBy system input (system.proposalOccurrence input) :=
  { sourceValues := system.outputValues input
    sourceExact := rfl
    outputExact := rfl }

structure WritesTo
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (use : WeightUseOccurrence run)
    (target : ActivationOccurrence run) where
  targetExact : target = .neuronOutput use.resource.target

structure Precedes
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (left right : ActivationOccurrence run) where
  less : occurrencePosition left < occurrencePosition right

structure UsedBy
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (source target : ActivationOccurrence run) where
  propagation : PropagatesTo source target

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.ReadsFrom
#print axioms ConstitutiveSearch.NativeMechanism.ConsecutiveReadsFrom
#print axioms ConstitutiveSearch.NativeMechanism.PropagatesTo
#print axioms ConstitutiveSearch.NativeMechanism.Reaches
#print axioms ConstitutiveSearch.NativeMechanism.Reaches.trans
#print axioms ConstitutiveSearch.NativeMechanism.FormedBy
#print axioms ConstitutiveSearch.NativeMechanism.formedBy
#print axioms ConstitutiveSearch.NativeMechanism.ProposalFormedBy
#print axioms ConstitutiveSearch.NativeMechanism.proposalFormation
#print axioms ConstitutiveSearch.NativeMechanism.WritesTo
#print axioms ConstitutiveSearch.NativeMechanism.Precedes
#print axioms ConstitutiveSearch.NativeMechanism.UsedBy
/- AXIOM_AUDIT_END -/
