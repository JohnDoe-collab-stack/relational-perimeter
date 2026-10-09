import RelationalPerimeter.Constitution.ClosingTransport
import RelationalPerimeter.Constitution.FormationTransportExamples

namespace RelationalPerimeter.Constitution.ClosingTransportExamples

open FormationTransportExamples

def circular := firstHistory.toCircular .here true

def movedCircular := firstHistory.transportedCircular witnessFlip .here true

theorem junction_flipped : movedCircular.finalJunction = false := rfl

theorem provenance_flipped : movedCircular.initialNode.provenance = false := rfl

def boundaryMap : BoundaryTransport (closingBoundary circular) (closingBoundary movedCircular) :=
  PositiveHistory.circularBoundaryTransport (F := formation) (T := signature)
    witnessFlip firstHistory .here true

theorem boundary_junction_return : boundaryMap.junction.backward movedCircular.finalJunction =
    circular.finalJunction := rfl

theorem final_role_preserved :
    ((EquippedFinalRole.canonical (closingBoundary circular)).transport boundaryMap).witness =
      movedCircular.finalJunction := rfl

end RelationalPerimeter.Constitution.ClosingTransportExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.circular
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.movedCircular
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.junction_flipped
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.provenance_flipped
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.boundaryMap
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.boundary_junction_return
#print axioms RelationalPerimeter.Constitution.ClosingTransportExamples.final_role_preserved
/- AXIOM_AUDIT_END -/
