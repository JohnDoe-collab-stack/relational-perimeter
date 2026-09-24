import RelationalPerimeter.Computation.ConstitutiveSearch.SearchableTransportCode
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

/-!
# Executable validation of searchable transport codes

SearchableBy is a code-local proposition saying that every primitive atom of a
constituted TransportCode can be rediscovered by one announced RelationSearch.

This module turns that proposition into an executable validator.

The validator traverses the complete code syntax:
* identity performs no primitive query;
* every atom performs exactly one primitive.find query;
* composition validates both subcodes.

It records:
* a Boolean success flag;
* the exact number of primitive relation-search queries.

The central theorems show:
* validation performs exactly code.size primitive queries;
* validation succeeds exactly when SearchableBy holds.

Thus SearchableBy is no longer treated as a cost-free side condition when
complexity accounting needs an executable validation phase.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Result of executable validation of one constituted transport code. -/
structure SearchableCodeValidationRun where
  success : Bool
  primitiveQueries : Nat
  validatedAtoms : Nat

namespace SearchableCodeValidationRun

/-- Combine validation outcomes without short-circuiting either subcode. -/
def combine
    (first second : SearchableCodeValidationRun) :
    SearchableCodeValidationRun :=
  { success :=
      first.success &&
        second.success
    primitiveQueries :=
      first.primitiveQueries +
        second.primitiveQueries
    validatedAtoms := first.validatedAtoms + second.validatedAtoms }

end SearchableCodeValidationRun

/--
Validate every primitive atom of a constituted code against one announced
primitive RelationSearch.
-/
def validateSearchableCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    {source target : State} →
      TransportCode
        Generator
        source
        target →
      SearchableCodeValidationRun
  | _, _, .identity _ =>
      { success := true
        primitiveQueries := 0
        validatedAtoms := 0 }
  | source, target, .atom _ =>
      match
        primitive.find source target with
      | some _ =>
          { success := true
            primitiveQueries := 1
            validatedAtoms := 1 }
      | none =>
          { success := false
            primitiveQueries := 1
            validatedAtoms := 1 }
  | _, _, .compose first second =>
      SearchableCodeValidationRun.combine
        (validateSearchableCode
          primitive
          first)
        (validateSearchableCode
          primitive
          second)

/-- Validation executes exactly one primitive query per code atom. -/
theorem validateSearchableCode_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) :
    (validateSearchableCode
      primitive
      code).primitiveQueries =
        code.size := by
  induction code with
  | identity state =>
      rfl
  | @atom source target witness =>
      cases found :
          primitive.find source target with
      | none =>
          rw [
            validateSearchableCode,
            found
          ]
          rfl
      | some executableWitness =>
          rw [
            validateSearchableCode,
            found
          ]
          rfl
  | compose first second firstHypothesis secondHypothesis =>
      change
        (validateSearchableCode
              primitive
              first).primitiveQueries +
            (validateSearchableCode
              primitive
              second).primitiveQueries =
          first.size +
            second.size
      calc
        (validateSearchableCode
              primitive
              first).primitiveQueries +
            (validateSearchableCode
              primitive
              second).primitiveQueries =
            first.size +
              (validateSearchableCode
                primitive
                second).primitiveQueries :=
          congrArg
            (fun value =>
              value +
                (validateSearchableCode
                  primitive
                  second).primitiveQueries)
            firstHypothesis
        _ = first.size + second.size :=
          congrArg
            (Nat.add first.size)
            secondHypothesis

/-- The validation recursion emits one validated-atom unit per code atom. -/
theorem validateSearchableCode_validatedAtoms
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code : TransportCode Generator source target) :
    (validateSearchableCode primitive code).validatedAtoms = code.size := by
  induction code with
  | identity state => rfl
  | @atom source target witness =>
      cases found : primitive.find source target <;>
        rw [validateSearchableCode, found] <;> rfl
  | compose first second firstHypothesis secondHypothesis =>
      change
        (validateSearchableCode primitive first).validatedAtoms +
            (validateSearchableCode primitive second).validatedAtoms =
          first.size + second.size
      rw [firstHypothesis, secondHypothesis]

/-- Executable validation succeeds exactly for SearchableBy codes. -/
theorem validateSearchableCode_success_iff
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) :
    (validateSearchableCode
        primitive
        code).success =
        true ↔
      code.SearchableBy primitive := by
  induction code with
  | identity state =>
      exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | @atom source target witness =>
      cases found :
          primitive.find source target with
      | none =>
          constructor
          · intro impossible
            rw [
              validateSearchableCode,
              found
            ] at impossible
            cases impossible
          · intro searchable
            exact False.elim (searchable found)
      | some executableWitness =>
          constructor
          · intro _ impossible
            rw [found] at impossible
            cases impossible
          · intro _
            rw [
              validateSearchableCode,
              found
            ]
  | compose first second firstHypothesis secondHypothesis =>
      change
        (((validateSearchableCode primitive first).success &&
            (validateSearchableCode primitive second).success) = true) ↔
          (first.SearchableBy primitive ∧
            second.SearchableBy primitive)
      constructor
      · intro combined
        have successes :=
          (Constructive.bool_and_eq_true_iff
            (validateSearchableCode primitive first).success
            (validateSearchableCode primitive second).success).mp
            combined
        exact
          ⟨firstHypothesis.mp successes.1,
            secondHypothesis.mp successes.2⟩
      · intro searchable
        exact
          (Constructive.bool_and_eq_true_iff
            (validateSearchableCode primitive first).success
            (validateSearchableCode primitive second).success).mpr
            ⟨firstHypothesis.mpr searchable.1,
              secondHypothesis.mpr searchable.2⟩

/-- SearchableBy evidence implies executable validator success. -/
theorem validateSearchableCode_success_of_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive) :
    (validateSearchableCode
        primitive
        code).success =
      true :=
  (validateSearchableCode_success_iff
    primitive
    code).2
    searchable

/-- Validator success reconstructs the code-local SearchableBy proposition. -/
theorem searchable_of_validateSearchableCode_success
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target)
    (success :
      (validateSearchableCode
          primitive
          code).success =
        true) :
    code.SearchableBy primitive :=
  (validateSearchableCode_success_iff
    primitive
    code).1
    success

/-- Primitive-query validation cost for a dependent code family. -/
def searchableCodeValidationPrimitiveBudget
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (n : Nat) : Nat :=
  (validateSearchableCode
    (primitive n)
    (code n)).primitiveQueries

/--
If constituted code size is input-polynomial, executable SearchableBy
validation cost is input-polynomial with the same envelope.
-/
theorem searchableCodeValidationPrimitiveBudget_inputPolynomiallyBounded
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (inputBits : Nat → Nat)
    (codeSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (code n).size)) :
    InputPolynomiallyBounded
      inputBits
      (searchableCodeValidationPrimitiveBudget
        primitive
        code) := by
  rcases codeSizeBounded with
    ⟨envelope, codeLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  change
    (validateSearchableCode
        (primitive n)
        (code n)).primitiveQueries ≤
      envelope.eval
        (inputBits n)
  rw [
    validateSearchableCode_primitiveQueries
  ]
  exact
    codeLe n

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SearchableCodeValidationRun
#print axioms ConstitutiveSearch.SearchableCodeValidationRun.combine
#print axioms ConstitutiveSearch.validateSearchableCode_validatedAtoms
#print axioms ConstitutiveSearch.validateSearchableCode
#print axioms ConstitutiveSearch.validateSearchableCode_primitiveQueries
#print axioms ConstitutiveSearch.validateSearchableCode_success_iff
#print axioms ConstitutiveSearch.validateSearchableCode_success_of_searchable
#print axioms ConstitutiveSearch.searchable_of_validateSearchableCode_success
#print axioms ConstitutiveSearch.searchableCodeValidationPrimitiveBudget
#print axioms ConstitutiveSearch.searchableCodeValidationPrimitiveBudget_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
