import RelationalPerimeter.Constitution.CircularRoles
import RelationalPerimeter.Constitution.ClosingTransport

set_option linter.checkUnivs false

/-! Role transport between a supplied history and its signature reconstruction.
The state and full step data remain the same. Structural positions and complete
successive links are preserved; the final role uses the selected closing data. -/

namespace RelationalPerimeter.Constitution

open StrongPerimetralTurning

namespace PositionReindex

def exactTransport {S : ConstitutiveSignature} {node : S.Node}
    {first second : PerimeterSpine S.Compatible node} (exactSpine : first = second) :
    ExactTypeTransport (NonClosingPosition first) (NonClosingPosition second) := by
  cases exactSpine
  exact ExactTypeTransport.reflexive _

theorem forward_exact {S : ConstitutiveSignature} {node : S.Node}
    {first second : PerimeterSpine S.Compatible node} (exactSpine : first = second)
    (position : NonClosingPosition first) :
    (exactTransport exactSpine).forward position = exactSpine ▸ position := by
  cases exactSpine
  rfl

theorem reverse_forward_exact {S : ConstitutiveSignature} {node : S.Node}
    {first second : PerimeterSpine S.Compatible node} (exactSpine : first = second)
    (position : NonClosingPosition second) :
    exactSpine ▸ (exactTransport exactSpine.symm).forward position = position := by
  cases exactSpine
  rfl

theorem link_cast {S : ConstitutiveSignature} {node : S.Node}
    {first second : PerimeterSpine S.Compatible node} (exactSpine : first = second)
    (position : NonClosingPosition first) :
    second.linkAt (exactSpine ▸ position) = first.linkAt position := by
  cases exactSpine
  rfl

end PositionReindex

namespace PositiveHistory

variable {F : PositiveFormation} {T : ConstitutiveSignature}

def circularPositionTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    ExactTypeTransport (NonClosingPosition history.deploy)
      (NonClosingPosition (history.transportSignature map).deploy) :=
  (map.positionTransport history.deploy).compose
    (PositionReindex.exactTransport (history.transport_deploy map).symm)

theorem circular_position_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (position : NonClosingPosition history.deploy) :
    history.transport_deploy map ▸
        (history.circularPositionTransport map).forward position =
      map.mapPosition history.deploy position :=
  PositionReindex.reverse_forward_exact (history.transport_deploy map) _

def interiorRoleTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (EquippedInteriorRole (history.toCircular positive junction))
      (EquippedInteriorRole (history.transportedCircular map positive junction)) :=
  ((EquippedInteriorRole.positionTransport (history.toCircular positive junction)).reverse.compose
    (history.circularPositionTransport map)).compose
    (EquippedInteriorRole.positionTransport (history.transportedCircular map positive junction))

theorem interior_position_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    history.transport_deploy map ▸
        ((history.interiorRoleTransport map positive junction).forward role).position =
      map.mapPosition history.deploy role.position :=
  history.circular_position_preserved map role.position

theorem interior_link_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    ((history.interiorRoleTransport map positive junction).forward role).link =
      map.mapLink role.link := by
  let transported := (history.interiorRoleTransport map positive junction).forward role
  have castLink : (history.transportSignature map).deploy.linkAt transported.position =
      (map.mapSpine history.deploy).linkAt
        (history.transport_deploy map ▸ transported.position) :=
    (PositionReindex.link_cast (S := T) (history.transport_deploy map) transported.position).symm
  have positionLink : (map.mapSpine history.deploy).linkAt
        (history.transport_deploy map ▸ transported.position) =
      (map.mapSpine history.deploy).linkAt (map.mapPosition history.deploy role.position) :=
    congrArg ((map.mapSpine history.deploy).linkAt)
      (history.interior_position_preserved map positive junction role)
  exact transported.linkExact.trans (castLink.trans (positionLink.trans
    ((map.mapSpine_link history.deploy role.position).trans
      (congrArg map.mapLink role.linkExact.symm))))

theorem interior_source_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    ((history.interiorRoleTransport map positive junction).forward role).link.source =
      map.mapNode role.link.source :=
  congrArg SuccessiveLink.source (history.interior_link_preserved map positive junction role)

theorem interior_target_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    ((history.interiorRoleTransport map positive junction).forward role).link.target =
      map.mapNode role.link.target :=
  congrArg SuccessiveLink.target (history.interior_link_preserved map positive junction role)

theorem interior_return (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    (history.interiorRoleTransport map positive junction).backward
      ((history.interiorRoleTransport map positive junction).forward role) = role :=
  (history.interiorRoleTransport map positive junction).forwardBackward role

theorem interior_return_target (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.transportedCircular map positive junction)) :
    (history.interiorRoleTransport map positive junction).forward
      ((history.interiorRoleTransport map positive junction).backward role) = role :=
  (history.interiorRoleTransport map positive junction).backwardForward role

def finalRoleTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (EquippedFinalRole (closingBoundary (history.toCircular positive junction)))
      (EquippedFinalRole (closingBoundary (history.transportedCircular map positive junction))) :=
  EquippedFinalRole.exactTransport (history.circularBoundaryTransport map positive junction)

theorem final_witness_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    ((history.finalRoleTransport map positive junction).forward role).witness =
      (history.circularBoundaryTransport map positive junction).junction.forward role.witness := rfl

theorem final_source_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    map.implicit.forward role.source =
      ((history.finalRoleTransport map positive junction).forward role).source :=
  EquippedFinalRole.source_preserved (history.circularBoundaryTransport map positive junction) role

theorem final_target_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    map.explicit.forward role.target =
      ((history.finalRoleTransport map positive junction).forward role).target :=
  EquippedFinalRole.target_preserved (history.circularBoundaryTransport map positive junction) role

theorem final_difference_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    map.difference.forward (closingBoundary (history.toCircular positive junction)).difference =
      (closingBoundary (history.transportedCircular map positive junction)).difference :=
  (history.circularBoundaryTransport map positive junction).differenceExact

theorem final_provenance_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    (history.circularBoundaryTransport map positive junction).provenance.forward role.provenance =
      ((history.finalRoleTransport map positive junction).forward role).provenance :=
  EquippedFinalRole.provenance_preserved (history.circularBoundaryTransport map positive junction) role

def circularRoleTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (CircularRole (history.toCircular positive junction))
      (CircularRole (history.transportedCircular map positive junction)) :=
  { forward := fun role => match role with
      | .interior role => .interior ((history.interiorRoleTransport map positive junction).forward role)
      | .final role => .final ((history.finalRoleTransport map positive junction).forward role)
    backward := fun role => match role with
      | .interior role => .interior ((history.interiorRoleTransport map positive junction).backward role)
      | .final role => .final ((history.finalRoleTransport map positive junction).backward role)
    forwardBackward := by
      intro role
      cases role with
      | interior role =>
          exact congrArg CircularRole.interior
            ((history.interiorRoleTransport map positive junction).forwardBackward role)
      | final role =>
          exact congrArg CircularRole.final
            ((history.finalRoleTransport map positive junction).forwardBackward role)
    backwardForward := by
      intro role
      cases role with
      | interior role =>
          exact congrArg CircularRole.interior
            ((history.interiorRoleTransport map positive junction).backwardForward role)
      | final role =>
          exact congrArg CircularRole.final
            ((history.finalRoleTransport map positive junction).backwardForward role) }

theorem circular_interior_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    (history.circularRoleTransport map positive junction).forward (.interior role) =
      .interior ((history.interiorRoleTransport map positive junction).forward role) := rfl

theorem circular_final_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    (history.circularRoleTransport map positive junction).forward (.final role) =
      .final ((history.finalRoleTransport map positive junction).forward role) := rfl

theorem circular_return (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : CircularRole (history.toCircular positive junction)) :
    (history.circularRoleTransport map positive junction).backward
      ((history.circularRoleTransport map positive junction).forward role) = role :=
  (history.circularRoleTransport map positive junction).forwardBackward role

theorem circular_return_target (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : CircularRole (history.transportedCircular map positive junction)) :
    (history.circularRoleTransport map positive junction).forward
      ((history.circularRoleTransport map positive junction).backward role) = role :=
  (history.circularRoleTransport map positive junction).backwardForward role

theorem circular_classification_commutes (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : CircularRole (history.toCircular positive junction)) :
    CircularRole.classify ((history.circularRoleTransport map positive junction).forward role) =
      Sum.map (history.circularPositionTransport map).forward id
        (CircularRole.classify role) := by
  cases role <;> rfl

theorem circular_generated_position_commutes (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : CircularRole (history.toCircular positive junction)) :
    CircularRole.generatedPosition ((history.circularRoleTransport map positive junction).forward role) =
      Option.map (history.circularPositionTransport map).forward
        (CircularRole.generatedPosition role) := by
  cases role <;> rfl

end PositiveHistory
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.PositionReindex.exactTransport
#print axioms RelationalPerimeter.Constitution.PositionReindex.forward_exact
#print axioms RelationalPerimeter.Constitution.PositionReindex.reverse_forward_exact
#print axioms RelationalPerimeter.Constitution.PositionReindex.link_cast
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circularPositionTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_position_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interiorRoleTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interior_position_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interior_link_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interior_source_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interior_target_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interior_return
#print axioms RelationalPerimeter.Constitution.PositiveHistory.interior_return_target
#print axioms RelationalPerimeter.Constitution.PositiveHistory.finalRoleTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.final_witness_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.final_source_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.final_target_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.final_difference_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.final_provenance_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circularRoleTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_interior_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_final_preserved
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_return
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_return_target
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_classification_commutes
#print axioms RelationalPerimeter.Constitution.PositiveHistory.circular_generated_position_commutes
/- AXIOM_AUDIT_END -/
