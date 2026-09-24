import RelationalPerimeter.Computation.SearchSystem

/-!
# Exact structural opening

An opening decomposes the continuation carrier of one parent into the sum of
the continuation carriers of two alternatives.  The decomposition is exact
and reversible, but it makes no choice between the alternatives.
-/

namespace RelationalPerimeter.Computation

/-- Exact constructive opening of a parent continuation carrier. -/
structure ExactStructuralOpening
    (system : SearchSystem)
    (parent left right : system.State) where
  split :
    system.Continuation parent →
      system.Continuation left ⊕ system.Continuation right
  merge :
    system.Continuation left ⊕ system.Continuation right →
      system.Continuation parent
  split_merge :
    (branch : system.Continuation left ⊕ system.Continuation right) →
      split (merge branch) = branch
  merge_split :
    (continuation : system.Continuation parent) →
      merge (split continuation) = continuation

namespace ExactStructuralOpening

/-- The left injection, read back through the exact opening, stays left. -/
theorem split_left
    {system : SearchSystem}
    {parent left right : system.State}
    (opening : ExactStructuralOpening system parent left right)
    (continuation : system.Continuation left) :
    opening.split (opening.merge (.inl continuation)) =
      .inl continuation :=
  opening.split_merge (.inl continuation)

/-- The right injection, read back through the exact opening, stays right. -/
theorem split_right
    {system : SearchSystem}
    {parent left right : system.State}
    (opening : ExactStructuralOpening system parent left right)
    (continuation : system.Continuation right) :
    opening.split (opening.merge (.inr continuation)) =
      .inr continuation :=
  opening.split_merge (.inr continuation)

end ExactStructuralOpening

/--
Compatibility of an exact opening with the criterion.  This is separate from
the structural opening: the carrier equivalence alone does not preserve a
criterion.
-/
structure CriterionExactOpening
    (system : SearchSystem)
    {parent left right : system.State}
    (opening : ExactStructuralOpening system parent left right) where
  split_preserves :
    (continuation : system.Continuation parent) →
      system.Criterion parent continuation →
        match opening.split continuation with
        | .inl leftContinuation =>
            system.Criterion left leftContinuation
        | .inr rightContinuation =>
            system.Criterion right rightContinuation
  merge_preserves :
    (branch : system.Continuation left ⊕ system.Continuation right) →
      (match branch with
       | .inl leftContinuation =>
           system.Criterion left leftContinuation
       | .inr rightContinuation =>
           system.Criterion right rightContinuation) →
      system.Criterion parent (opening.merge branch)

namespace CriterionExactOpening

/-- Criterion-preserving inclusion of the left alternative into the parent. -/
theorem merge_left_preserves
    {system : SearchSystem}
    {parent left right : system.State}
    {opening : ExactStructuralOpening system parent left right}
    (compatible : CriterionExactOpening system opening)
    (continuation : system.Continuation left)
    (accepted : system.Criterion left continuation) :
    system.Criterion parent (opening.merge (.inl continuation)) :=
  compatible.merge_preserves (.inl continuation) accepted

/-- Criterion-preserving inclusion of the right alternative into the parent. -/
theorem merge_right_preserves
    {system : SearchSystem}
    {parent left right : system.State}
    {opening : ExactStructuralOpening system parent left right}
    (compatible : CriterionExactOpening system opening)
    (continuation : system.Continuation right)
    (accepted : system.Criterion right continuation) :
    system.Criterion parent (opening.merge (.inr continuation)) :=
  compatible.merge_preserves (.inr continuation) accepted

end CriterionExactOpening
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.ExactStructuralOpening
#print axioms RelationalPerimeter.Computation.ExactStructuralOpening.split_left
#print axioms RelationalPerimeter.Computation.ExactStructuralOpening.split_right
#print axioms RelationalPerimeter.Computation.CriterionExactOpening
#print axioms RelationalPerimeter.Computation.CriterionExactOpening.merge_left_preserves
#print axioms RelationalPerimeter.Computation.CriterionExactOpening.merge_right_preserves
/- AXIOM_AUDIT_END -/
