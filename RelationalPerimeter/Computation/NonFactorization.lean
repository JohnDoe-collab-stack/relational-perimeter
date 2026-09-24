import Init

/-!
# Constructive non-factorization through an information-forgetting projection

Two inputs with the same projection and different observed outputs refute any
claim that the observation can be recovered from that projection alone.
-/

namespace RelationalPerimeter.Computation

/-- A value-valued observation is recoverable from a projection alone. -/
def ValueFactorsThrough
    {Input Projected Output : Type}
    (project : Input → Projected)
    (observe : Input → Output) : Prop :=
  ∃ projectedObservation : Projected → Output,
    ∀ input : Input,
      projectedObservation (project input) = observe input

/--
Equal projections with unequal observations constructively refute value
factorization.
-/
theorem value_not_factors_of_same_projection
    {Input Projected Output : Type}
    (project : Input → Projected)
    (observe : Input → Output)
    (first second : Input)
    (sameProjection : project first = project second)
    (differentObservation : observe first ≠ observe second) :
    ¬ ValueFactorsThrough project observe := by
  intro factors
  rcases factors with ⟨projectedObservation, exactFactor⟩
  apply differentObservation
  calc
    observe first = projectedObservation (project first) :=
      (exactFactor first).symm
    _ = projectedObservation (project second) := by
      rw [sameProjection]
    _ = observe second := exactFactor second

end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.ValueFactorsThrough
#print axioms RelationalPerimeter.Computation.value_not_factors_of_same_projection
/- AXIOM_AUDIT_END -/
