import RelationalPerimeter.Constitution.ClosingBoundary

/-!
# Empty, unique and multiple closing-witness fibres

The empty shape is constructed directly. It is not the forgetting of a boundary
that already contains a junction. The Bool shape distinguishes the uniqueness of
the role over each pointing from the multiplicity of pointings over one shape.
-/

namespace RelationalPerimeter.Constitution.ClosingBoundaryExamples

universe uW

def fibreShape (Witness : Type uW) : ClosingBoundaryShape :=
  { Explicit := Unit
    Implicit := Unit
    Compatible := fun _ _ => Witness
    source := ()
    target := ()
    Difference := Unit
    Provenance := fun _ => Unit
    difference := ()
    provenance := () }

def emptyShape : ClosingBoundaryShape := fibreShape Empty

theorem empty_has_no_junction : ClosingWitness emptyShape → False :=
  fun witness => nomatch witness

theorem empty_no_pointing : Nonempty (PointedClosingBoundary emptyShape) → False :=
  emptyShape.noPointingOfEmpty empty_has_no_junction

theorem empty_no_final_role :
    (∃ pointed : PointedClosingBoundary emptyShape, Nonempty pointed.FinalRole) → False :=
  emptyShape.noFinalRoleOfEmpty empty_has_no_junction

theorem empty_not_from_constitutive
    (boundary : ConstitutiveBoundary.{0, 0, 0, 0, 0})
    (sameShape : boundary.toClosingBoundaryShape = emptyShape) : False := by
  have inhabited := boundary.shape_fibre_nonempty
  rw [sameShape] at inhabited
  obtain ⟨junction⟩ := inhabited
  exact empty_has_no_junction junction

def unitShape : ClosingBoundaryShape := fibreShape Unit

def unitPointing : PointedClosingBoundary unitShape := unitShape.point ()

theorem unit_fibre_unique (first second : ClosingWitness unitShape) : first = second := by
  cases first
  cases second
  rfl

def unitRole : unitPointing.FinalRole := unitPointing.finalRole

theorem unit_role_unique (role : unitPointing.FinalRole) : role = unitRole :=
  unitPointing.finalRole_unique role unitRole

def boolShape : ClosingBoundaryShape := fibreShape Bool

def falsePointing : PointedClosingBoundary boolShape := boolShape.point false

def truePointing : PointedClosingBoundary boolShape := boolShape.point true

theorem bool_witnesses_distinct :
    (false : ClosingWitness boolShape) ≠ (true : ClosingWitness boolShape) :=
  fun equality => Bool.noConfusion equality

theorem bool_pointings_distinct : falsePointing ≠ truePointing := by
  intro equality
  have witnesses := congrArg (fun pointed : PointedClosingBoundary boolShape =>
    pointed.junction) equality
  exact bool_witnesses_distinct witnesses

theorem bool_same_shape :
    falsePointing.toConstitutiveBoundary.toClosingBoundaryShape =
      truePointing.toConstitutiveBoundary.toClosingBoundaryShape := rfl

def falseRole : falsePointing.FinalRole := falsePointing.finalRole

def trueRole : truePointing.FinalRole := truePointing.finalRole

theorem bool_per_choice_role_unique (pointed : PointedClosingBoundary boolShape)
    (first second : pointed.FinalRole) : first = second :=
  pointed.finalRole_unique first second

theorem bool_role_witnesses_distinct : falseRole.witness ≠ trueRole.witness :=
  bool_witnesses_distinct

theorem bool_pointing_fibre_not_unique :
    (∀ first second : PointedClosingBoundary boolShape, first = second) → False :=
  fun unique => bool_pointings_distinct (unique falsePointing truePointing)

theorem bool_closing_fibre_not_unique :
    (∀ first second : ClosingWitness boolShape, first = second) → False :=
  fun unique => bool_witnesses_distinct (unique false true)

end RelationalPerimeter.Constitution.ClosingBoundaryExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.fibreShape
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.emptyShape
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_has_no_junction
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_no_pointing
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_no_final_role
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_not_from_constitutive
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.unitShape
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.unitPointing
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.unit_fibre_unique
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.unitRole
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.unit_role_unique
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.boolShape
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.falsePointing
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.truePointing
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_witnesses_distinct
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_pointings_distinct
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_same_shape
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.falseRole
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.trueRole
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_per_choice_role_unique
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_role_witnesses_distinct
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_pointing_fibre_not_unique
#print axioms RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_closing_fibre_not_unique
/- AXIOM_AUDIT_END -/
