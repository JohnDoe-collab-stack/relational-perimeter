import RelationalPerimeter.Constitution.HeytingArithmetic.ArithmeticFormulaTools
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveComparison
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveEvaluation

/-!
# Primitive-recursive structural Euclidean division

The semantic arithmetic layer already computes quotient and remainder by
structural recursion on the dividend.  This file realizes that same algorithm
inside the positive `PRFunction` language.

The remainder is compiled first.  The quotient then reuses the compiled
remainder at the current recursion counter.  No minimization, bounded-search
oracle, classical choice, or arbitrary Lean function is inserted into the
program tree.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Small evaluator equations -/

private theorem PRFunction.run_lessBit_division (left right : Nat) :
    PRFunction.lessBit.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      natLessBit left right :=
  (PRFunction.lessBit_evaluates left right).symm

private theorem PRFunction.run_ifZero_division
    (selector whenZero whenPositive : Nat) :
    PRFunction.ifZero.run
        (NatVector.cons selector
          (NatVector.cons whenZero
            (NatVector.cons whenPositive NatVector.nil))) =
      natIfZero selector whenZero whenPositive :=
  (PRFunction.ifZero_evaluates selector whenZero whenPositive).symm

private theorem natLessBit_one_of_lt
    {left right : Nat}
    (strict : left < right) :
    natLessBit left right = 1 := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => exact (Nat.not_lt_zero 0 strict).elim
      | succ right => rfl
  | succ left inductionHypothesis =>
      cases right with
      | zero => exact (Nat.not_lt_zero (Nat.succ left) strict).elim
      | succ right =>
          unfold natLessBit
          repeat rw [Nat.add_one]
          rw [Nat.succ_sub_succ_eq_sub]
          exact inductionHypothesis (Nat.lt_of_succ_lt_succ strict)

private theorem natLessBit_zero_of_not_lt
    {left right : Nat}
    (notStrict : left < right -> False) :
    natLessBit left right = 0 := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ right => exact (notStrict (Nat.zero_lt_succ right)).elim
  | succ left inductionHypothesis =>
      cases right with
      | zero =>
          unfold natLessBit
          rw [Nat.zero_sub]
          rfl
      | succ right =>
          unfold natLessBit
          repeat rw [Nat.add_one]
          rw [Nat.succ_sub_succ_eq_sub]
          exact inductionHypothesis fun strict =>
            notStrict (Nat.succ_lt_succ strict)

/-! ## Compiled remainder -/

/-- Successor of the previous remainder in a division step. -/
def PRFunction.divisionRemainderCandidate : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

/-- Whether the candidate remainder is still strictly below the modulus. -/
def PRFunction.divisionRemainderSelector : PRFunction 3 :=
  PRFunction.composition
    PRFunction.lessBit
    (PRFunctionVector.cons
      PRFunction.divisionRemainderCandidate
      (PRFunctionVector.singleton
        (PRFunction.projection 3 2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))

/-- Grow the remainder below the modulus and reset it to zero at the modulus. -/
def PRFunction.divisionRemainderStep : PRFunction 3 :=
  PRFunction.composition
    PRFunction.ifZero
    (PRFunctionVector.cons
      PRFunction.divisionRemainderSelector
      (PRFunctionVector.cons
        PRFunction.zero
        (PRFunctionVector.singleton
          PRFunction.divisionRemainderCandidate)))

/-- Primitive-recursive remainder, recursing on the dividend. -/
def PRFunction.constructiveRemainder : PRFunction 2 :=
  PRFunction.primitiveRecursion
    (PRFunction.zero : PRFunction 1)
    PRFunction.divisionRemainderStep

@[simp] theorem PRFunction.run_divisionRemainderCandidate
    (counter previous modulus : Nat) :
    PRFunction.divisionRemainderCandidate.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      Nat.succ previous := by
  unfold PRFunction.divisionRemainderCandidate
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton]
  rw [PRFunction.run_projection, PRFunction.run_successor]
  rfl

@[simp] theorem PRFunction.run_divisionRemainderSelector
    (counter previous modulus : Nat) :
    PRFunction.divisionRemainderSelector.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      natLessBit (Nat.succ previous) modulus := by
  unfold PRFunction.divisionRemainderSelector
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_divisionRemainderCandidate,
    PRFunction.run_projection,
    PRFunction.run_lessBit_division]
  rfl

@[simp] theorem PRFunction.run_divisionRemainderStep
    (counter previous modulus : Nat) :
    PRFunction.divisionRemainderStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      natIfZero
        (natLessBit (Nat.succ previous) modulus)
        0
        (Nat.succ previous) := by
  unfold PRFunction.divisionRemainderStep
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_divisionRemainderSelector, PRFunction.run_zero,
    PRFunction.run_divisionRemainderCandidate,
    PRFunction.run_ifZero_division]

/-- The positive remainder program computes the existing structural remainder. -/
theorem PRFunction.constructiveRemainder_run
    (dividend modulus : Nat) :
    PRFunction.constructiveRemainder.run
        (NatVector.cons dividend
          (NatVector.cons modulus NatVector.nil)) =
      HeytingArithmetic.constructiveRemainder dividend modulus := by
  induction dividend with
  | zero =>
      unfold PRFunction.constructiveRemainder
      rw [PRFunction.run_primitive_zero, PRFunction.run_zero]
      rfl
  | succ dividend inductionHypothesis =>
      unfold PRFunction.constructiveRemainder
      rw [PRFunction.run_primitive_succ,
        PRFunction.run_divisionRemainderStep]
      change
        natIfZero
            (natLessBit
              (Nat.succ
                (PRFunction.constructiveRemainder.run
                  (NatVector.cons dividend
                    (NatVector.cons modulus NatVector.nil))))
              modulus)
            0
            (Nat.succ
              (PRFunction.constructiveRemainder.run
                (NatVector.cons dividend
                  (NatVector.cons modulus NatVector.nil)))) =
          HeytingArithmetic.constructiveRemainder
            (Nat.succ dividend) modulus
      rw [inductionHypothesis]
      by_cases grows :
          Nat.succ
              (HeytingArithmetic.constructiveRemainder dividend modulus) <
            modulus
      · rw [natLessBit_one_of_lt grows]
        change Nat.succ
            (HeytingArithmetic.constructiveRemainder dividend modulus) =
          HeytingArithmetic.constructiveRemainder
            (Nat.succ dividend) modulus
        unfold HeytingArithmetic.constructiveRemainder
        rw [constructiveDivMod_succ_of_lt dividend modulus grows]
      · rw [natLessBit_zero_of_not_lt grows]
        change 0 = HeytingArithmetic.constructiveRemainder
          (Nat.succ dividend) modulus
        unfold HeytingArithmetic.constructiveRemainder
        rw [constructiveDivMod_succ_of_not_lt dividend modulus grows]

/-- Positive execution certificate for the structural remainder. -/
theorem PRFunction.constructiveRemainder_evaluates
    (dividend modulus : Nat) :
    PRFunction.Evaluates
      PRFunction.constructiveRemainder
      (NatVector.cons dividend
        (NatVector.cons modulus NatVector.nil))
      (HeytingArithmetic.constructiveRemainder dividend modulus) := by
  unfold PRFunction.Evaluates
  exact (PRFunction.constructiveRemainder_run dividend modulus).symm

/-! ## Compiled quotient -/

/-- Recompute the remainder at the current quotient recursion counter. -/
def PRFunction.divisionRemainderAtCounter : PRFunction 3 :=
  PRFunction.composition
    PRFunction.constructiveRemainder
    (PRFunctionVector.cons
      (PRFunction.projection 3 0 (Nat.zero_lt_succ 2))
      (PRFunctionVector.singleton
        (PRFunction.projection 3 2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))

/-- Candidate remainder for deciding the next quotient step. -/
def PRFunction.divisionCounterCandidate : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton PRFunction.divisionRemainderAtCounter)

/-- Whether the next dividend stays inside the current quotient block. -/
def PRFunction.divisionQuotientSelector : PRFunction 3 :=
  PRFunction.composition
    PRFunction.lessBit
    (PRFunctionVector.cons
      PRFunction.divisionCounterCandidate
      (PRFunctionVector.singleton
        (PRFunction.projection 3 2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))

/-- Successor of the previous quotient. -/
def PRFunction.divisionQuotientCandidate : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

/-- Preserve the quotient inside a block and increment it at a full modulus. -/
def PRFunction.divisionQuotientStep : PRFunction 3 :=
  PRFunction.composition
    PRFunction.ifZero
    (PRFunctionVector.cons
      PRFunction.divisionQuotientSelector
      (PRFunctionVector.cons
        PRFunction.divisionQuotientCandidate
        (PRFunctionVector.singleton
          (PRFunction.projection 3 1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))))

/-- Primitive-recursive quotient, recursing on the dividend. -/
def PRFunction.constructiveQuotient : PRFunction 2 :=
  PRFunction.primitiveRecursion
    (PRFunction.zero : PRFunction 1)
    PRFunction.divisionQuotientStep

@[simp] theorem PRFunction.run_divisionRemainderAtCounter
    (counter previous modulus : Nat) :
    PRFunction.divisionRemainderAtCounter.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      HeytingArithmetic.constructiveRemainder counter modulus := by
  unfold PRFunction.divisionRemainderAtCounter
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_projection,
    PRFunction.run_projection,
    PRFunction.constructiveRemainder_run]
  rfl

@[simp] theorem PRFunction.run_divisionCounterCandidate
    (counter previous modulus : Nat) :
    PRFunction.divisionCounterCandidate.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      Nat.succ (HeytingArithmetic.constructiveRemainder counter modulus) := by
  unfold PRFunction.divisionCounterCandidate
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_divisionRemainderAtCounter, PRFunction.run_successor]

@[simp] theorem PRFunction.run_divisionQuotientSelector
    (counter previous modulus : Nat) :
    PRFunction.divisionQuotientSelector.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      natLessBit
        (Nat.succ (HeytingArithmetic.constructiveRemainder counter modulus))
        modulus := by
  unfold PRFunction.divisionQuotientSelector
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_divisionCounterCandidate, PRFunction.run_projection,
    PRFunction.run_lessBit_division]
  rfl

@[simp] theorem PRFunction.run_divisionQuotientCandidate
    (counter previous modulus : Nat) :
    PRFunction.divisionQuotientCandidate.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      Nat.succ previous := by
  unfold PRFunction.divisionQuotientCandidate
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_projection, PRFunction.run_successor]
  rfl

@[simp] theorem PRFunction.run_divisionQuotientStep
    (counter previous modulus : Nat) :
    PRFunction.divisionQuotientStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons modulus NatVector.nil))) =
      natIfZero
        (natLessBit
          (Nat.succ
            (HeytingArithmetic.constructiveRemainder counter modulus))
          modulus)
        (Nat.succ previous)
        previous := by
  unfold PRFunction.divisionQuotientStep
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_divisionQuotientSelector,
    PRFunction.run_divisionQuotientCandidate,
    PRFunction.run_projection, PRFunction.run_ifZero_division]
  rfl

/-- The positive quotient program computes the existing structural quotient. -/
theorem PRFunction.constructiveQuotient_run
    (dividend modulus : Nat) :
    PRFunction.constructiveQuotient.run
        (NatVector.cons dividend
          (NatVector.cons modulus NatVector.nil)) =
      HeytingArithmetic.constructiveQuotient dividend modulus := by
  induction dividend with
  | zero =>
      unfold PRFunction.constructiveQuotient
      rw [PRFunction.run_primitive_zero, PRFunction.run_zero]
      rfl
  | succ dividend inductionHypothesis =>
      unfold PRFunction.constructiveQuotient
      rw [PRFunction.run_primitive_succ,
        PRFunction.run_divisionQuotientStep]
      change
        natIfZero
            (natLessBit
              (Nat.succ
                (HeytingArithmetic.constructiveRemainder
                  dividend modulus))
              modulus)
            (Nat.succ
              (PRFunction.constructiveQuotient.run
                (NatVector.cons dividend
                  (NatVector.cons modulus NatVector.nil))))
            (PRFunction.constructiveQuotient.run
              (NatVector.cons dividend
                (NatVector.cons modulus NatVector.nil))) =
          HeytingArithmetic.constructiveQuotient
            (Nat.succ dividend) modulus
      rw [inductionHypothesis]
      by_cases grows :
          Nat.succ
              (HeytingArithmetic.constructiveRemainder dividend modulus) <
            modulus
      · rw [natLessBit_one_of_lt grows]
        change HeytingArithmetic.constructiveQuotient dividend modulus =
          HeytingArithmetic.constructiveQuotient
            (Nat.succ dividend) modulus
        unfold HeytingArithmetic.constructiveQuotient
        rw [constructiveDivMod_succ_of_lt dividend modulus grows]
      · rw [natLessBit_zero_of_not_lt grows]
        change Nat.succ
            (HeytingArithmetic.constructiveQuotient dividend modulus) =
          HeytingArithmetic.constructiveQuotient
            (Nat.succ dividend) modulus
        unfold HeytingArithmetic.constructiveQuotient
        rw [constructiveDivMod_succ_of_not_lt dividend modulus grows]

/-- Positive execution certificate for the structural quotient. -/
theorem PRFunction.constructiveQuotient_evaluates
    (dividend modulus : Nat) :
    PRFunction.Evaluates
      PRFunction.constructiveQuotient
      (NatVector.cons dividend
        (NatVector.cons modulus NatVector.nil))
      (HeytingArithmetic.constructiveQuotient dividend modulus) := by
  unfold PRFunction.Evaluates
  exact (PRFunction.constructiveQuotient_run dividend modulus).symm

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.constructiveRemainder_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.constructiveQuotient_evaluates
/- AXIOM_AUDIT_END -/
