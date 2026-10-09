import RelationalPerimeter.Constitution.CircularRoles
import RelationalPerimeter.Constitution.HistoricalRoleBridge
import RelationalPerimeter.Constitution.ClosingBoundaryExamples
import RelationalPerimeter.Constitution.FormationTransportExamples
import RelationalPerimeter.Constitution.PositiveGenerationExamples

namespace RelationalPerimeter.Constitution.CircularRolesExamples

open StrongPerimetralTurning FormationTransportExamples

def falsePresentation := firstHistory.toCircular .here false

def truePresentation := firstHistory.toCircular .here true

def falseFinal : EquippedFinalRole (closingBoundary falsePresentation) := .canonical _

def trueFinal : EquippedFinalRole (closingBoundary truePresentation) := .canonical _

theorem same_shape : (closingBoundary falsePresentation).toClosingBoundaryShape =
    (closingBoundary truePresentation).toClosingBoundaryShape := rfl

theorem chosen_witnesses_distinct : falseFinal.witness ≠ trueFinal.witness := by
  intro equality
  cases equality

theorem false_choice_role_unique (first second : EquippedFinalRole (closingBoundary falsePresentation)) :
    first = second := EquippedFinalRole.unique first second

theorem true_choice_role_unique (first second : EquippedFinalRole (closingBoundary truePresentation)) :
    first = second := EquippedFinalRole.unique first second

theorem unpointed_empty_no_final :
    (∃ pointing : PointedClosingBoundary ClosingBoundaryExamples.emptyShape,
      Nonempty pointing.FinalRole) → False := ClosingBoundaryExamples.empty_no_final_role

def interior : EquippedInteriorRole falsePresentation :=
  EquippedInteriorRole.ofOccurrence firstHistory .here false .here

theorem interior_step_witness : interior.link.compatibility = true := rfl

theorem closing_witness : falseFinal.witness = false := rfl

theorem interior_final_separate : (CircularRole.interior interior : CircularRole falsePresentation) ≠
    .final falseFinal := CircularRole.branches_distinct _ _

theorem final_not_generated : CircularRole.generatedPosition (.final falseFinal) = .none :=
  CircularRole.final_no_generated_position _

theorem interior_generated : CircularRole.generatedPosition (.interior interior) = .some interior.position := rfl

def ExtendedRole (P : PositiveCircularPresentation) := CircularRole P ⊕ Unit

def exterior : ExtendedRole falsePresentation := .inr ()

theorem exterior_outside_declared_grammar (role : CircularRole falsePresentation) :
    (Sum.inl role : ExtendedRole falsePresentation) ≠ exterior := by
  intro equality
  cases equality

theorem declared_grammar_still_exhaustive (role : CircularRole falsePresentation) :
    (∃ position, role = .interior (EquippedInteriorRole.canonical falsePresentation position)) ∨
      role = .final falseFinal := CircularRole.exhaustive role

theorem no_exhaustiveness_of_larger_type :
    (∀ extended : ExtendedRole falsePresentation, ∃ role : CircularRole falsePresentation,
      extended = .inl role) → False := by
  intro exhaustive
  obtain ⟨role, equality⟩ := exhaustive exterior
  exact exterior_outside_declared_grammar role equality.symm

def legacyMarkerRole := (HistoricalRoleBridge.finalRequirementTransport
  PositiveGenerationExamples.unitHistorical).forward .distinguished

theorem legacy_marker_retains_junction : legacyMarkerRole.witness =
    PositiveGenerationExamples.unitHistorical.finalJunction := rfl

theorem legacy_marker_return : (HistoricalRoleBridge.finalRequirementTransport
    PositiveGenerationExamples.unitHistorical).backward legacyMarkerRole = .distinguished := rfl

end RelationalPerimeter.Constitution.CircularRolesExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.falsePresentation
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.truePresentation
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.falseFinal
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.trueFinal
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.same_shape
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.chosen_witnesses_distinct
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.false_choice_role_unique
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.true_choice_role_unique
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.unpointed_empty_no_final
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.interior
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.interior_step_witness
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.closing_witness
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.interior_final_separate
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.final_not_generated
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.interior_generated
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.ExtendedRole
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.exterior
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.exterior_outside_declared_grammar
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.declared_grammar_still_exhaustive
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.no_exhaustiveness_of_larger_type
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.legacyMarkerRole
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.legacy_marker_retains_junction
#print axioms RelationalPerimeter.Constitution.CircularRolesExamples.legacy_marker_return
/- AXIOM_AUDIT_END -/
