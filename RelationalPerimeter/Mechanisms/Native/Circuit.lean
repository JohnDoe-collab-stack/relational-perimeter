import RelationalPerimeter.Mechanisms.Native.Relations
import RelationalPerimeter.Constitution.Resources.TypedReferences

/-!
# Constitutive circuit boundaries and mechanism scales

The reconstructed circuit is the exact causal cone of one target in one
executed run. Its member family is constituted by executed `Reaches` witnesses
in both directions: no unrelated graph can add a decorative member, and no
executed path can be omitted from the canonical reconstruction.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

abbrev ExecutedEdge
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) :=
  Sigma fun source : ActivationOccurrence run =>
    Sigma fun target : ActivationOccurrence run => ReadsFrom run source target

structure BoundaryContains
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    (edges : List (ExecutedEdge run))
    (source target : ActivationOccurrence run) where
  item : ExecutedEdge run
  reference : Resources.Ref edges item
  sourceExact : item.1 = source
  targetExact : item.2.1 = target

structure GroupBoundary
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program)
    (members : List (ActivationOccurrence run)) where
  incoming : List (ExecutedEdge run)
  outgoing : List (ExecutedEdge run)
  incomingExact : forall source target,
    Nonempty (BoundaryContains incoming source target) <->
      (source ∈ members -> False) /\ target ∈ members
  outgoingExact : forall source target,
    Nonempty (BoundaryContains outgoing source target) <->
      source ∈ members /\ (target ∈ members -> False)

def executionDepth
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program} : ActivationOccurrence run -> Nat
  | .receivedInput _ => 0
  | .neuronOutput index => program.depthAt index

structure SameExecutionDepth
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program)
    (members : List (ActivationOccurrence run)) where
  depth : Nat
  exact : forall occurrence, occurrence ∈ members ->
    executionDepth occurrence = depth

structure ConstructedCircuit
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program)
    (target : ActivationOccurrence run) where
  private mk ::
  Contains : ActivationOccurrence run -> Type
  memberPath : forall occurrence, Contains occurrence ->
    Reaches run occurrence target
  pathMember : forall occurrence, Reaches run occurrence target ->
    Contains occurrence

def reconstructCircuit
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) (target : ActivationOccurrence run) :
    ConstructedCircuit run target :=
  { Contains := fun occurrence => Reaches run occurrence target
    memberPath := fun _ path => path
    pathMember := fun _ path => path }

def reconstructed_member_to_path
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) (target occurrence : ActivationOccurrence run)
    (member : (reconstructCircuit run target).Contains occurrence) :
    Reaches run occurrence target := member

def reconstructed_path_to_member
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) (target occurrence : ActivationOccurrence run)
    (path : Reaches run occurrence target) :
    (reconstructCircuit run target).Contains occurrence := path

structure CircuitContainsEdge
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {target : ActivationOccurrence run}
    (circuit : ConstructedCircuit run target)
    (source destination : ActivationOccurrence run) where
  sourceMember : circuit.Contains source
  destinationMember : circuit.Contains destination
  edge : ReadsFrom run source destination

inductive MechanismOccurrence
    {program : NetworkProgram inputCount produced}
    (run : NativeRun program) : MechanismScale -> Type 1 where
  | parameter (resource : ParameterResource program) :
      MechanismOccurrence run .parameter
  | weightUse (occurrence : WeightUseOccurrence run) :
      MechanismOccurrence run .weightUse
  | neuron (index : Fin produced) :
      MechanismOccurrence run .neuron
  | functionalUnit (members : List (ActivationOccurrence run))
      (nonempty : members ≠ [])
      (boundary : GroupBoundary run members) :
      MechanismOccurrence run .functionalUnit
  | circuit {target : ActivationOccurrence run}
      (value : ConstructedCircuit run target) :
      MechanismOccurrence run .circuit
  | layer (members : List (ActivationOccurrence run))
      (nonempty : members ≠ [])
      (sameDepth : SameExecutionDepth run members) :
      MechanismOccurrence run .layer

def membersOf
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program} :
    {scale : MechanismScale} ->
    MechanismOccurrence run scale -> ActivationOccurrence run -> Type
  | .parameter, .parameter _, _ => Empty
  | .weightUse, .weightUse use, occurrence =>
      Resources.Ref
        [use.readSource, .neuronOutput use.resource.target] occurrence
  | .neuron, .neuron index, occurrence =>
      Resources.Ref [.neuronOutput index] occurrence
  | .functionalUnit, .functionalUnit members _ _, occurrence =>
      Resources.Ref members occurrence
  | .circuit, .circuit circuit, occurrence => circuit.Contains occurrence
  | .layer, .layer members _ _, occurrence =>
      Resources.Ref members occurrence

structure ComposesWith
    {program : NetworkProgram inputCount produced}
    {run : NativeRun program}
    {scale : MechanismScale}
    (occurrence : ActivationOccurrence run)
    (group : MechanismOccurrence run scale) where
  member : membersOf group occurrence

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.ExecutedEdge
#print axioms ConstitutiveSearch.NativeMechanism.BoundaryContains
#print axioms ConstitutiveSearch.NativeMechanism.GroupBoundary
#print axioms ConstitutiveSearch.NativeMechanism.executionDepth
#print axioms ConstitutiveSearch.NativeMechanism.SameExecutionDepth
#print axioms ConstitutiveSearch.NativeMechanism.ConstructedCircuit
#print axioms ConstitutiveSearch.NativeMechanism.reconstructCircuit
#print axioms ConstitutiveSearch.NativeMechanism.reconstructed_member_to_path
#print axioms ConstitutiveSearch.NativeMechanism.reconstructed_path_to_member
#print axioms ConstitutiveSearch.NativeMechanism.CircuitContainsEdge
#print axioms ConstitutiveSearch.NativeMechanism.MechanismOccurrence
#print axioms ConstitutiveSearch.NativeMechanism.membersOf
#print axioms ConstitutiveSearch.NativeMechanism.ComposesWith
/- AXIOM_AUDIT_END -/
