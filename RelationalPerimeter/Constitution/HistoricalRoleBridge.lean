import RelationalPerimeter.Constitution.CircularRoles
import RelationalPerimeter.Constitution.CircularPresentationBridge

namespace RelationalPerimeter.Constitution.HistoricalRoleBridge

open StrongPerimetralTurning

def finalRequirementTransport (P : CircularPresentation) :
    ExactTypeTransport (FinalRequirement P)
      (EquippedFinalRole (closingBoundary P.toPositiveCircularPresentation)) :=
  { forward := fun _ => EquippedFinalRole.canonical _
    backward := fun _ => .distinguished
    forwardBackward := fun marker => by cases marker; rfl
    backwardForward := fun role => EquippedFinalRole.unique _ role }

theorem marker_junction_readout (P : CircularPresentation) (marker : FinalRequirement P) :
    ((finalRequirementTransport P).forward marker).witness = P.finalJunction := rfl

def requirementTransport (P : CircularPresentation) :
    ExactTypeTransport (CircularRequirement P) (CircularRole P.toPositiveCircularPresentation) :=
  { forward := fun requirement => match requirement with
      | .inl position => .interior (EquippedInteriorRole.canonical _ position)
      | .inr marker => .final ((finalRequirementTransport P).forward marker)
    backward := fun role => match role with
      | .interior role => .inl role.position
      | .final role => .inr ((finalRequirementTransport P).backward role)
    forwardBackward := fun requirement => by
      cases requirement with
      | inl => rfl
      | inr marker => exact congrArg Sum.inr ((finalRequirementTransport P).forwardBackward marker)
    backwardForward := fun role => by
      cases role with
      | interior role => exact congrArg CircularRole.interior role.canonical_return
      | final role => exact congrArg CircularRole.final ((finalRequirementTransport P).backwardForward role) }

def realizeInterior {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (role : EquippedInteriorRole P.toPositiveCircularPresentation) : History.Occurrence history.history :=
  realization.realize role.position

def realization_readout {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (role : EquippedInteriorRole P.toPositiveCircularPresentation) :
    RequirementOccurrenceAgreement P history role.position (realizeInterior realization role) :=
  realization.agreement role.position

theorem realization_injective {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : EquippedInteriorRole P.toPositiveCircularPresentation}
    (sameOccurrence : realizeInterior realization first = realizeInterior realization second) :
    first = second := EquippedInteriorRole.ext (realization.realize_injective sameOccurrence)

def realizeRole {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    CircularRole P.toPositiveCircularPresentation → Option (History.Occurrence history.history)
  | .interior role => .some (realizeInterior realization role)
  | .final _ => .none

theorem final_not_realized {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (role : EquippedFinalRole (closingBoundary P.toPositiveCircularPresentation)) :
    realizeRole realization (.final role) = .none := rfl

end RelationalPerimeter.Constitution.HistoricalRoleBridge

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.finalRequirementTransport
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.marker_junction_readout
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.requirementTransport
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.realizeInterior
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.realization_readout
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.realization_injective
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.realizeRole
#print axioms RelationalPerimeter.Constitution.HistoricalRoleBridge.final_not_realized
/- AXIOM_AUDIT_END -/
