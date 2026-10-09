import RelationalPerimeter.Constitution.PositiveGeneration
import RelationalPerimeter.Constitution.CircularPresentationBridge

/-!
# Historical enrichment of generated positive presentations

This bridge alone imports the historical obstruction machinery. Generation and
deployment do not consume the endpoint readings or the rejection of contraction.
-/

namespace RelationalPerimeter.Constitution.PositiveHistory

open StrongPerimetralTurning

variable {F : PositiveFormation} {source target : F.State}

def toHistorical (history : PositiveHistory F source target) (positive : Occurrence history)
    (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    CircularPresentation :=
  CircularPresentation.ofPositive (history.toCircular positive junction) endpoints obstruction

theorem historical_positive (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).toPositiveCircularPresentation =
      history.toCircular positive junction :=
  CircularPresentation.positive_roundTrip _ _ _

theorem historical_endpoints (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).endpointBoundary = endpoints :=
  CircularPresentation.boundary_roundTrip _ _ _

theorem historical_obstruction (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).closureObstruction = obstruction :=
  CircularPresentation.obstruction_roundTrip _ _ _

theorem historical_deployment (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).perimeter = history.deploy := rfl

end RelationalPerimeter.Constitution.PositiveHistory

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toHistorical
#print axioms RelationalPerimeter.Constitution.PositiveHistory.historical_positive
#print axioms RelationalPerimeter.Constitution.PositiveHistory.historical_endpoints
#print axioms RelationalPerimeter.Constitution.PositiveHistory.historical_obstruction
#print axioms RelationalPerimeter.Constitution.PositiveHistory.historical_deployment
/- AXIOM_AUDIT_END -/
