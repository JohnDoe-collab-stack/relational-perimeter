import RelationalPerimeter.Computation.SearchSystem

/-!
# Primitive relations acting on continuations

A relation witness and its action are kept distinct.  The action is total on
the structural continuation carrier.  Preservation of the criterion is a
further proof, not part of the action's computational definition.
-/

namespace RelationalPerimeter.Computation

universe uRelation

/-- A witness of a primitive relation acts on every source continuation. -/
structure RelationalContinuationAction
    (system : SearchSystem)
    (Relation : system.State → system.State → Type uRelation) where
  act :
    {source target : system.State} →
      Relation source target →
      system.Continuation source →
      system.Continuation target

/-- A relational action equipped with a separate criterion-preservation law. -/
structure CriterionPreservingAction
    (system : SearchSystem)
    (Relation : system.State → system.State → Type uRelation)
    (action : RelationalContinuationAction system Relation) where
  preserves :
    {source target : system.State} →
      (relation : Relation source target) →
      (continuation : system.Continuation source) →
      system.Criterion source continuation →
      system.Criterion target (action.act relation continuation)

namespace CriterionPreservingAction

/-- A criterion-preserving action transports viability directionally. -/
theorem preserves_viable
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {action : RelationalContinuationAction system Relation}
    (preserving : CriterionPreservingAction system Relation action)
    {source target : system.State}
    (relation : Relation source target) :
    system.Viable source → system.Viable target := by
  intro viable
  rcases viable with ⟨continuation, accepted⟩
  exact
    ⟨action.act relation continuation,
      preserving.preserves relation continuation accepted⟩

end CriterionPreservingAction
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.RelationalContinuationAction
#print axioms RelationalPerimeter.Computation.CriterionPreservingAction
#print axioms RelationalPerimeter.Computation.CriterionPreservingAction.preserves_viable
/- AXIOM_AUDIT_END -/
