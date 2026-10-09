import RelationalPerimeter.Constitution.BoundaryTransport
import RelationalPerimeter.Constitution.CircularPresentationBridge

/-!
# Separating models for positive circularity and boundary transport

The same positive chain accepts identified endpoint readings or a separated,
obstructed enrichment. Closing-fibre equivalence can exchange its two witnesses
while all three selected index values remain unchanged.
-/

namespace RelationalPerimeter.Constitution.Examples

open StrongPerimetralTurning

def node : LocalNode Unit Unit (fun _ _ => Bool) Unit (fun _ => Bool) :=
  { explicit := ()
    implicit := ()
    difference := ()
    provenance := true
    internallyCompatible := true }

def positive : PositiveCircularPresentation :=
  { Explicit := Unit
    Implicit := Unit
    Compatible := fun _ _ => Bool
    Difference := Unit
    Provenance := fun _ => Bool
    initialNode := node
    perimeter := .advance false (.boundary node)
    perimeterPositive := .here
    finalJunction := false }

def identifiedBoundary : EndpointBoundary positive :=
  { Endpoint := Unit
    leftEndpoint := ()
    rightEndpoint := ()
    leftPole := fun _ => ()
    rightPole := fun _ => ()
    initialLeftPole := rfl
    initialRightPole := rfl }

theorem identifiedBoundary_eq :
    identifiedBoundary.leftEndpoint = identifiedBoundary.rightEndpoint := rfl

theorem identifiedBoundary_no_obstruction :
    CircularClosureObstruction positive identifiedBoundary → False :=
  CircularClosureObstruction.noObstructionOfIdentifiedEndpoints identifiedBoundary_eq

def separatedBoundary : EndpointBoundary positive :=
  { Endpoint := Bool
    leftEndpoint := false
    rightEndpoint := true
    leftPole := fun _ => false
    rightPole := fun _ => true
    initialLeftPole := rfl
    initialRightPole := rfl }

def obstruction : CircularClosureObstruction positive separatedBoundary :=
  { TotalLoop := PLift (false = true)
    closeFromIdentification := fun equality => ⟨equality⟩
    loopContractsInitialDifference := fun loop => loop.down
    rejectInitialContraction := fun _ equality => by cases equality }

def obstructed : CircularPresentation :=
  CircularPresentation.ofPositive positive separatedBoundary obstruction

theorem same_positive_data : obstructed.toPositiveCircularPresentation = positive := rfl

/- A raw witnessed chain can repeat its node values. This does not identify
   occurrences or generated cursors in the historical free execution. -/
theorem raw_node_return : positive.perimeter.finalNode = positive.initialNode := rfl

def boundary : ConstitutiveBoundary := closingBoundary positive

def boolFlip : ExactTypeTransport Bool Bool :=
  { forward := fun witness => !witness
    backward := fun witness => !witness
    forwardBackward := fun witness => by cases witness <;> rfl
    backwardForward := fun witness => by cases witness <;> rfl }

def closingSwap : BoundaryCarrierTransport boundary boundary :=
  { explicit := ExactTypeTransport.reflexive _
    implicit := ExactTypeTransport.reflexive _
    difference := ExactTypeTransport.reflexive _
    junction := boolFlip
    provenance := ExactTypeTransport.reflexive _ }

theorem closingSwap_preserves_indices :
    closingSwap.implicit.forward boundary.source = boundary.source ∧
    closingSwap.explicit.forward boundary.target = boundary.target ∧
    closingSwap.difference.forward boundary.difference = boundary.difference :=
  ⟨rfl, rfl, rfl⟩

theorem closingSwap_does_not_preserve_witness :
    closingSwap.junction.forward boundary.junction ≠ boundary.junction := by
  intro equality
  cases equality

theorem closingSwap_cannot_lift
    (rich : BoundaryTransport boundary boundary)
    (sameCarriers : rich.toBoundaryCarrierTransport = closingSwap) : False := by
  have agreement := congrArg
    (fun carrier : BoundaryCarrierTransport boundary boundary =>
      carrier.junction.forward boundary.junction) sameCarriers
  exact closingSwap_does_not_preserve_witness
    (agreement.symm.trans rich.junctionExact)

def exampleEquippedFinalRole : EquippedFinalRole boundary :=
  EquippedFinalRole.canonical boundary

theorem exampleRole_provenance : exampleEquippedFinalRole.provenance = true := rfl

theorem historicalExample_recovered :
    CircularPresentation.ofPositive
      StrongPerimetralTurning.Example.examplePresentation.toPositiveCircularPresentation
      StrongPerimetralTurning.Example.examplePresentation.endpointBoundary
      StrongPerimetralTurning.Example.examplePresentation.closureObstruction =
        StrongPerimetralTurning.Example.examplePresentation :=
  CircularPresentation.historical_roundTrip _

end RelationalPerimeter.Constitution.Examples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Examples.node
#print axioms RelationalPerimeter.Constitution.Examples.positive
#print axioms RelationalPerimeter.Constitution.Examples.identifiedBoundary
#print axioms RelationalPerimeter.Constitution.Examples.identifiedBoundary_eq
#print axioms RelationalPerimeter.Constitution.Examples.identifiedBoundary_no_obstruction
#print axioms RelationalPerimeter.Constitution.Examples.separatedBoundary
#print axioms RelationalPerimeter.Constitution.Examples.obstruction
#print axioms RelationalPerimeter.Constitution.Examples.obstructed
#print axioms RelationalPerimeter.Constitution.Examples.same_positive_data
#print axioms RelationalPerimeter.Constitution.Examples.raw_node_return
#print axioms RelationalPerimeter.Constitution.Examples.boundary
#print axioms RelationalPerimeter.Constitution.Examples.boolFlip
#print axioms RelationalPerimeter.Constitution.Examples.closingSwap
#print axioms RelationalPerimeter.Constitution.Examples.closingSwap_preserves_indices
#print axioms RelationalPerimeter.Constitution.Examples.closingSwap_does_not_preserve_witness
#print axioms RelationalPerimeter.Constitution.Examples.closingSwap_cannot_lift
#print axioms RelationalPerimeter.Constitution.Examples.exampleEquippedFinalRole
#print axioms RelationalPerimeter.Constitution.Examples.exampleRole_provenance
#print axioms RelationalPerimeter.Constitution.Examples.historicalExample_recovered
/- AXIOM_AUDIT_END -/
