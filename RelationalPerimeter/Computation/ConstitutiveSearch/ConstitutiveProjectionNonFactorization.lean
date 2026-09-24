/-!
# Constructive non-factorization through information-forgetting projections

The closure program needs a precise notion of information loss.

A property factors through a projection when it can be recovered solely from
the projected value.  A numeric observation factors through a projection when
one function of the projected value reproduces that observation exactly.

The two generic separator theorems below are constructive:
* equal projections with opposite predicate truth values refute predicate
  factorization;
* equal projections with distinct observed values refute value factorization.
-/

namespace ConstitutiveSearch

/-- A predicate is recoverable from a projection alone. -/
def PredicateFactorsThrough
    {A B : Type}
    (project : A → B)
    (predicate : A → Prop) : Prop :=
  ∃ projectedPredicate : B → Prop,
    ∀ value : A,
      predicate value ↔
        projectedPredicate
          (project value)

/-- A value-valued observation is recoverable from a projection alone. -/
def ValueFactorsThrough
    {A B C : Type}
    (project : A → B)
    (observe : A → C) : Prop :=
  ∃ projectedObservation : B → C,
    ∀ value : A,
      projectedObservation
          (project value) =
        observe value

/--
Two states with the same projection but different predicate truth values
constructively refute predicate factorization.
-/
theorem predicate_not_factors_of_same_projection
    {A B : Type}
    (project : A → B)
    (predicate : A → Prop)
    (first second : A)
    (sameProjection :
      project first =
        project second)
    (firstFalse :
      ¬ predicate first)
    (secondTrue :
      predicate second) :
    ¬
      PredicateFactorsThrough
        project
        predicate := by
  intro factors
  rcases factors with
    ⟨projectedPredicate, exactFactor⟩
  have secondProjected :
      projectedPredicate
        (project second) :=
    (exactFactor second).1
      secondTrue
  have firstProjected :
      projectedPredicate
        (project first) := by
    rw [sameProjection]
    exact secondProjected
  exact
    firstFalse
      ((exactFactor first).2
        firstProjected)

/--
Two states with the same projection but unequal observations constructively
refute value factorization.
-/
theorem value_not_factors_of_same_projection
    {A B C : Type}
    (project : A → B)
    (observe : A → C)
    (first second : A)
    (sameProjection :
      project first =
        project second)
    (different :
      observe first ≠
        observe second) :
    ¬
      ValueFactorsThrough
        project
        observe := by
  intro factors
  rcases factors with
    ⟨projectedObservation, exactFactor⟩
  apply different
  calc
    observe first
        =
      projectedObservation
        (project first) :=
          (exactFactor first).symm
    _ =
      projectedObservation
        (project second) := by
          rw [sameProjection]
    _ =
      observe second :=
        exactFactor second

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PredicateFactorsThrough
#print axioms ConstitutiveSearch.ValueFactorsThrough
#print axioms ConstitutiveSearch.predicate_not_factors_of_same_projection
#print axioms ConstitutiveSearch.value_not_factors_of_same_projection
/- AXIOM_AUDIT_END -/
