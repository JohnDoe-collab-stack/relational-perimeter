import RelationalPerimeter.Computation.StructuralOpening
import RelationalPerimeter.Computation.RelationalAction

/-!
# Operational reduction after exact opening

A discovered relation from the left alternative to the right alternative
allows every parent continuation to be represented on the right.  The
reduction does not identify the alternatives and does not assert that the left
continuation carrier is empty.
-/

namespace RelationalPerimeter.Computation

universe uRelation

namespace OperationalReduction

/-- Absorb the left alternative into the right after splitting the parent. -/
def absorbLeft
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (action : RelationalContinuationAction system Relation)
    {parent left right : system.State}
    (opening : ExactStructuralOpening system parent left right)
    (relation : Relation left right) :
    system.Continuation parent → system.Continuation right :=
  fun continuation =>
    match opening.split continuation with
    | .inl leftContinuation => action.act relation leftContinuation
    | .inr rightContinuation => rightContinuation

/--
Criterion preservation for left absorption.  This theorem consumes both the
criterion compatibility of the opening and the separate preservation proof of
the relational action.
-/
theorem absorbLeft_preserves
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {action : RelationalContinuationAction system Relation}
    (preserving : CriterionPreservingAction system Relation action)
    {parent left right : system.State}
    {opening : ExactStructuralOpening system parent left right}
    (compatible : CriterionExactOpening system opening)
    (relation : Relation left right)
    (continuation : system.Continuation parent)
    (accepted : system.Criterion parent continuation) :
    system.Criterion right
      (absorbLeft action opening relation continuation) := by
  have splitAccepted := compatible.split_preserves continuation accepted
  cases splitResult : opening.split continuation with
  | inl leftContinuation =>
      rw [absorbLeft, splitResult]
      rw [splitResult] at splitAccepted
      exact preserving.preserves relation leftContinuation splitAccepted
  | inr rightContinuation =>
      rw [absorbLeft, splitResult]
      rw [splitResult] at splitAccepted
      exact splitAccepted

/-- The retained right branch always embeds back into the parent carrier. -/
def retainRight
    {system : SearchSystem}
    {parent left right : system.State}
    (opening : ExactStructuralOpening system parent left right) :
    system.Continuation right → system.Continuation parent :=
  fun continuation => opening.merge (.inr continuation)

/-- Embedding the retained branch back into the parent preserves the criterion. -/
theorem retainRight_preserves
    {system : SearchSystem}
    {parent left right : system.State}
    {opening : ExactStructuralOpening system parent left right}
    (compatible : CriterionExactOpening system opening)
    (continuation : system.Continuation right)
    (accepted : system.Criterion right continuation) :
    system.Criterion parent (retainRight opening continuation) :=
  compatible.merge_right_preserves continuation accepted

/--
The operational reduction preserves viability in both directions, without
claiming an isomorphism of continuation carriers.
-/
theorem viable_iff_after_absorbLeft
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {action : RelationalContinuationAction system Relation}
    (preserving : CriterionPreservingAction system Relation action)
    {parent left right : system.State}
    {opening : ExactStructuralOpening system parent left right}
    (compatible : CriterionExactOpening system opening)
    (relation : Relation left right) :
    system.Viable parent ↔ system.Viable right := by
  constructor
  · intro viable
    rcases viable with ⟨continuation, accepted⟩
    exact
      ⟨absorbLeft action opening relation continuation,
        absorbLeft_preserves
          preserving compatible relation continuation accepted⟩
  · intro viable
    rcases viable with ⟨continuation, accepted⟩
    exact
      ⟨retainRight opening continuation,
        retainRight_preserves compatible continuation accepted⟩

end OperationalReduction
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.OperationalReduction.absorbLeft
#print axioms RelationalPerimeter.Computation.OperationalReduction.absorbLeft_preserves
#print axioms RelationalPerimeter.Computation.OperationalReduction.retainRight
#print axioms RelationalPerimeter.Computation.OperationalReduction.retainRight_preserves
#print axioms RelationalPerimeter.Computation.OperationalReduction.viable_iff_after_absorbLeft
/- AXIOM_AUDIT_END -/
