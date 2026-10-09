import StrongPerimetralTurning

/-!
# Exact bridge to the historical obstructed presentation

The positive parent is authoritative for the successive data. The legacy
interface is recovered from that same parent, its endpoint readings and a
separately supplied obstruction, without choosing another spine or junction.
-/

namespace StrongPerimetralTurning.CircularPresentation

def endpointBoundary (P : CircularPresentation) :
    EndpointBoundary P.toPositiveCircularPresentation :=
  { Endpoint := P.Endpoint
    leftEndpoint := P.leftEndpoint
    rightEndpoint := P.rightEndpoint
    leftPole := P.leftPole
    rightPole := P.rightPole
    initialLeftPole := P.initialLeftPole
    initialRightPole := P.initialRightPole }

def closureObstruction (P : CircularPresentation) :
    CircularClosureObstruction P.toPositiveCircularPresentation P.endpointBoundary :=
  { TotalLoop := P.TotalLoop
    closeFromIdentification := P.closeFromIdentification
    loopContractsInitialDifference := P.loopContractsInitialDifference
    rejectInitialContraction := P.rejectInitialContraction }

def ofPositive
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    CircularPresentation :=
  { toPositiveCircularPresentation := positive
    Endpoint := boundary.Endpoint
    leftEndpoint := boundary.leftEndpoint
    rightEndpoint := boundary.rightEndpoint
    leftPole := boundary.leftPole
    rightPole := boundary.rightPole
    initialLeftPole := boundary.initialLeftPole
    initialRightPole := boundary.initialRightPole
    TotalLoop := obstruction.TotalLoop
    closeFromIdentification := obstruction.closeFromIdentification
    loopContractsInitialDifference := obstruction.loopContractsInitialDifference
    rejectInitialContraction := obstruction.rejectInitialContraction }

theorem positive_roundTrip
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    (ofPositive positive boundary obstruction).toPositiveCircularPresentation = positive :=
  rfl

theorem boundary_roundTrip
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    (ofPositive positive boundary obstruction).endpointBoundary = boundary := by
  cases boundary
  rfl

theorem obstruction_roundTrip
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    (ofPositive positive boundary obstruction).closureObstruction = obstruction := by
  cases boundary
  cases obstruction
  rfl

theorem historical_roundTrip (P : CircularPresentation) :
    ofPositive P.toPositiveCircularPresentation P.endpointBoundary P.closureObstruction = P := by
  cases P
  rfl

end StrongPerimetralTurning.CircularPresentation

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.CircularPresentation.endpointBoundary
#print axioms StrongPerimetralTurning.CircularPresentation.closureObstruction
#print axioms StrongPerimetralTurning.CircularPresentation.ofPositive
#print axioms StrongPerimetralTurning.CircularPresentation.positive_roundTrip
#print axioms StrongPerimetralTurning.CircularPresentation.boundary_roundTrip
#print axioms StrongPerimetralTurning.CircularPresentation.obstruction_roundTrip
#print axioms StrongPerimetralTurning.CircularPresentation.historical_roundTrip
/- AXIOM_AUDIT_END -/
