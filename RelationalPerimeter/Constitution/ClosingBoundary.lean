import RelationalPerimeter.Constitution.BoundaryTransport

/- Primitive sorts keep their separate universe parameters. -/
set_option linter.checkUnivs false

/-!
# Closing boundary before a junction is chosen

The shape retains the selected source, target, difference and initial provenance.
Only the closing witness is omitted. Its fibre can therefore be empty. An indexed
pointing supplies a witness in Type; the existence statements below stay in Prop.
The existing constitutive boundary is reconstructed without changing its fields.
-/

namespace RelationalPerimeter.Constitution

universe uE uI uK uD uP

structure ClosingBoundaryShape where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  source : Implicit
  target : Explicit
  Difference : Type uD
  Provenance : Difference → Type uP
  difference : Difference
  provenance : Provenance difference

def ClosingWitness (B : ClosingBoundaryShape) : Type uK :=
  B.Compatible B.source B.target

structure PointedClosingBoundary (B : ClosingBoundaryShape) where
  junction : ClosingWitness B

namespace ClosingBoundaryShape

def point (B : ClosingBoundaryShape) (junction : ClosingWitness B) :
    PointedClosingBoundary B := ⟨junction⟩

def pointingTransport (B : ClosingBoundaryShape) :
    ExactTypeTransport (ClosingWitness B) (PointedClosingBoundary B) :=
  { forward := B.point
    backward := fun pointed => pointed.junction
    forwardBackward := fun _ => rfl
    backwardForward := fun pointed => by cases pointed; rfl }

theorem nonempty_pointed_iff (B : ClosingBoundaryShape) :
    Nonempty (PointedClosingBoundary B) ↔ Nonempty (ClosingWitness B) :=
  ⟨fun ⟨pointed⟩ => ⟨pointed.junction⟩, fun ⟨junction⟩ => ⟨B.point junction⟩⟩

theorem noPointingOfEmpty (B : ClosingBoundaryShape)
    (empty : ClosingWitness B → False) : Nonempty (PointedClosingBoundary B) → False :=
  fun inhabited => by
    obtain ⟨pointed⟩ := inhabited
    exact empty pointed.junction

end ClosingBoundaryShape

namespace ConstitutiveBoundary

def toClosingBoundaryShape (B : ConstitutiveBoundary) : ClosingBoundaryShape :=
  { Explicit := B.Explicit
    Implicit := B.Implicit
    Compatible := B.Compatible
    source := B.source
    target := B.target
    Difference := B.Difference
    Provenance := B.Provenance
    difference := B.difference
    provenance := B.provenance }

def toPointedClosingBoundary (B : ConstitutiveBoundary) :
    PointedClosingBoundary B.toClosingBoundaryShape := ⟨B.junction⟩

theorem shape_fibre_nonempty (B : ConstitutiveBoundary) :
    Nonempty (ClosingWitness B.toClosingBoundaryShape) := ⟨B.junction⟩

end ConstitutiveBoundary

namespace PointedClosingBoundary

def toConstitutiveBoundary {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    ConstitutiveBoundary :=
  { Explicit := B.Explicit
    Implicit := B.Implicit
    Compatible := B.Compatible
    source := B.source
    target := B.target
    junction := pointed.junction
    Difference := B.Difference
    Provenance := B.Provenance
    difference := B.difference
    provenance := B.provenance }

theorem shape_roundTrip {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    pointed.toConstitutiveBoundary.toClosingBoundaryShape = B := rfl

theorem pointing_roundTrip {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    pointed.toConstitutiveBoundary.toPointedClosingBoundary = pointed := by
  cases pointed
  rfl

/- The role remains an inhabited singleton over each fixed pointing. These views
   do not identify two pointings with different closing witnesses. -/
abbrev FinalRole {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :=
  EquippedFinalRole pointed.toConstitutiveBoundary

def finalRole {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    pointed.FinalRole := EquippedFinalRole.canonical _

theorem finalRole_unique {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B)
    (first second : pointed.FinalRole) : first = second :=
  EquippedFinalRole.unique first second

theorem finalRole_junction {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B)
    (role : pointed.FinalRole) : role.witness = pointed.junction := role.witnessExact

end PointedClosingBoundary

namespace ConstitutiveBoundary

theorem boundary_roundTrip (B : ConstitutiveBoundary) :
    B.toPointedClosingBoundary.toConstitutiveBoundary = B := rfl

end ConstitutiveBoundary

namespace ClosingBoundaryShape

theorem nonempty_finalRole_iff (B : ClosingBoundaryShape) :
    (∃ pointed : PointedClosingBoundary B, Nonempty pointed.FinalRole) ↔
      Nonempty (ClosingWitness B) :=
  ⟨fun ⟨pointed, _⟩ => ⟨pointed.junction⟩,
    fun ⟨junction⟩ => ⟨B.point junction, ⟨(B.point junction).finalRole⟩⟩⟩

theorem noFinalRoleOfEmpty (B : ClosingBoundaryShape)
    (empty : ClosingWitness B → False) :
    (∃ pointed : PointedClosingBoundary B, Nonempty pointed.FinalRole) → False :=
  fun inhabited => by
    obtain ⟨junction⟩ := B.nonempty_finalRole_iff.mp inhabited
    exact empty junction

end ClosingBoundaryShape
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape
#print axioms RelationalPerimeter.Constitution.ClosingWitness
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape.point
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape.pointingTransport
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape.nonempty_pointed_iff
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape.noPointingOfEmpty
#print axioms RelationalPerimeter.Constitution.ConstitutiveBoundary.toClosingBoundaryShape
#print axioms RelationalPerimeter.Constitution.ConstitutiveBoundary.toPointedClosingBoundary
#print axioms RelationalPerimeter.Constitution.ConstitutiveBoundary.shape_fibre_nonempty
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.toConstitutiveBoundary
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.shape_roundTrip
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.pointing_roundTrip
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.FinalRole
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole_unique
#print axioms RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole_junction
#print axioms RelationalPerimeter.Constitution.ConstitutiveBoundary.boundary_roundTrip
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape.nonempty_finalRole_iff
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryShape.noFinalRoleOfEmpty
/- AXIOM_AUDIT_END -/
