import RelationalPerimeter.Constitution.FormationTransport

namespace RelationalPerimeter.Constitution

open StrongPerimetralTurning

namespace PositiveHistory

variable {F : PositiveFormation} {T : ConstitutiveSignature}

theorem transport_closing_source (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    map.implicit.forward history.boundaryShape.source =
      (history.transportSignature map).boundaryShape.source := by
  exact ((congrArg LocalNode.implicit (congrArg PerimeterSpine.finalNode (history.transport_deploy map))).trans
    (congrArg LocalNode.implicit (map.mapSpine_final history.deploy))).symm

def closingSignatureTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    ExactTypeTransport (ClosingWitness history.boundaryShape)
      (ClosingWitness (history.transportSignature map).boundaryShape) :=
  map.compatibilityAt (history.transport_closing_source map) rfl

theorem transport_closing_return (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (junction : ClosingWitness history.boundaryShape) :
    (history.closingSignatureTransport map).backward
      ((history.closingSignatureTransport map).forward junction) = junction :=
  (history.closingSignatureTransport map).forwardBackward junction

theorem transport_closing_return_target (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (junction : ClosingWitness (history.transportSignature map).boundaryShape) :
    (history.closingSignatureTransport map).forward
      ((history.closingSignatureTransport map).backward junction) = junction :=
  (history.closingSignatureTransport map).backwardForward junction

def transportedCircular (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    PositiveCircularPresentation :=
  (history.transportSignature map).toCircular (history.transportOccurrence map positive)
    ((history.closingSignatureTransport map).forward junction)

def circularBoundaryTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    BoundaryTransport (closingBoundary (history.toCircular positive junction))
      (closingBoundary (history.transportedCircular map positive junction)) :=
  map.restrict
    (B := closingBoundary (history.toCircular positive junction))
    (C := closingBoundary (history.transportedCircular map positive junction))
    (history.transport_closing_source map) rfl rfl rfl rfl

theorem circular_junction_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.circularBoundaryTransport map positive junction).junction.forward junction =
      (history.transportedCircular map positive junction).finalJunction :=
  (history.circularBoundaryTransport map positive junction).junctionExact

theorem circular_provenance_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.circularBoundaryTransport map positive junction).provenance.forward (F.node source).provenance =
      (history.transportedCircular map positive junction).initialNode.provenance :=
  (history.circularBoundaryTransport map positive junction).provenanceExact

end PositiveHistory
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_closing_source
#print axioms RelationalPerimeter.Constitution.PositiveHistory.closingSignatureTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_closing_return
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_closing_return_target
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transportedCircular
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circularBoundaryTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_junction_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_provenance_preserved
/- AXIOM_AUDIT_END -/
