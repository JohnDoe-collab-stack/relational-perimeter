import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveControl

/-!
# Primitive-recursive constants, products, differences, and comparisons

These explicit program trees provide the arithmetic control needed to index a
bounded trace of syntax-code transformations.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- A constant program at any arity. -/
def PRFunction.constant (arity : Nat) : Nat -> PRFunction arity
  | 0 => PRFunction.zero
  | Nat.succ value =>
      PRFunction.composition
        PRFunction.successor
        (PRFunctionVector.singleton (PRFunction.constant arity value))

/-- Explicit constant programs return their stated value. -/
theorem PRFunction.constant_evaluates
    (arity value : Nat)
    (inputs : NatVector arity) :
    PRFunction.Evaluates
      (PRFunction.constant arity value)
      inputs
      value := by
  induction value with
  | zero =>
      exact PRFunction.Evaluates.zero inputs
  | succ value inductionHypothesis =>
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact inductionHypothesis
        · exact PRFunctionVector.Evaluates.nil inputs
      · exact PRFunction.Evaluates.successor
          (NatVector.cons value NatVector.nil)

/-- Multiplication step: add the fixed right input to the previous result. -/
def PRFunction.multiplyStep : PRFunction 3 :=
  PRFunction.composition
    PRFunction.add
    (PRFunctionVector.cons
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
      (PRFunctionVector.singleton
        (PRFunction.projection 3 2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))

/-- Primitive-recursive multiplication, recursing on the left input. -/
def PRFunction.multiply : PRFunction 2 :=
  PRFunction.primitiveRecursion
    PRFunction.zero
    PRFunction.multiplyStep

/-- The explicit multiplication program computes natural multiplication. -/
theorem PRFunction.multiply_evaluates (left right : Nat) :
    PRFunction.Evaluates
      PRFunction.multiply
      (NatVector.cons left
        (NatVector.cons right NatVector.nil))
      (left * right) := by
  induction left with
  | zero =>
      rw [Nat.zero_mul]
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.zero
          (NatVector.cons right NatVector.nil))
  | succ left inductionHypothesis =>
      rw [Nat.succ_mul]
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
            (NatVector.cons left
              (NatVector.cons (left * right)
                (NatVector.cons right NatVector.nil)))
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              2
              (Nat.succ_lt_succ
                (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
              (NatVector.cons left
                (NatVector.cons (left * right)
                  (NatVector.cons right NatVector.nil)))
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons left
                (NatVector.cons (left * right)
                  (NatVector.cons right NatVector.nil)))
      · exact PRFunction.add_evaluates (left * right) right

/-- Subtraction step: take the predecessor of the previous result. -/
def PRFunction.subtractReversedStep : PRFunction 3 :=
  PRFunction.composition
    PRFunction.predecessor
    (PRFunctionVector.singleton
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

/-- Truncated subtraction with inputs ordered `(amount, value)`. -/
def PRFunction.subtractReversed : PRFunction 2 :=
  PRFunction.primitiveRecursion
    PRFunction.identity
    PRFunction.subtractReversedStep

/-- The reversed subtraction program computes `value - amount`. -/
theorem PRFunction.subtractReversed_evaluates (amount value : Nat) :
    PRFunction.Evaluates
      PRFunction.subtractReversed
      (NatVector.cons amount
        (NatVector.cons value NatVector.nil))
      (value - amount) := by
  induction amount with
  | zero =>
      rw [Nat.sub_zero]
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.projection
          0
          (Nat.zero_lt_succ 0)
          (NatVector.cons value NatVector.nil))
  | succ amount inductionHypothesis =>
      rw [Nat.sub_succ]
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
            (NatVector.cons amount
              (NatVector.cons (value - amount)
                (NatVector.cons value NatVector.nil)))
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons amount
              (NatVector.cons (value - amount)
                (NatVector.cons value NatVector.nil)))
      · exact PRFunction.predecessor_evaluates (value - amount)

/-- Truncated subtraction with conventional inputs `(value, amount)`. -/
def PRFunction.subtract : PRFunction 2 :=
  PRFunction.composition
    PRFunction.subtractReversed
    (PRFunctionVector.cons
      (PRFunction.projection 2 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
      (PRFunctionVector.singleton
        (PRFunction.projection 2 0 (Nat.zero_lt_succ 1))))

/-- The explicit subtraction program computes truncated subtraction. -/
theorem PRFunction.subtract_evaluates (value amount : Nat) :
    PRFunction.Evaluates
      PRFunction.subtract
      (NatVector.cons value
        (NatVector.cons amount NatVector.nil))
      (value - amount) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact PRFunction.Evaluates.projection
        1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
        (NatVector.cons value
          (NatVector.cons amount NatVector.nil))
    · apply PRFunctionVector.Evaluates.cons
      · exact PRFunction.Evaluates.projection
          0
          (Nat.zero_lt_succ 1)
          (NatVector.cons value
            (NatVector.cons amount NatVector.nil))
      · exact PRFunctionVector.Evaluates.nil
          (NatVector.cons value
            (NatVector.cons amount NatVector.nil))
  · exact PRFunction.subtractReversed_evaluates amount value

/-- Numeric zero characteristic: one exactly at zero. -/
def natIsZero : Nat -> Nat
  | 0 => 1
  | Nat.succ _value => 0

/-- Primitive-recursive numeric zero characteristic. -/
def PRFunction.isZero : PRFunction 1 :=
  PRFunction.primitiveRecursion
    (PRFunction.constant 0 1)
    PRFunction.zero

/-- The explicit zero characteristic computes `natIsZero`. -/
theorem PRFunction.isZero_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.isZero
      (NatVector.cons value NatVector.nil)
      (natIsZero value) := by
  induction value with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.constant_evaluates 0 1 NatVector.nil)
  | succ value inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      exact PRFunction.Evaluates.zero
        (NatVector.cons value
          (NatVector.cons (natIsZero value) NatVector.nil))

/-- Numeric positivity characteristic: zero at zero and one above zero. -/
def natPositiveBit (value : Nat) : Nat :=
  natIfZero value 0 1

/-- Primitive-recursive numeric positivity characteristic. -/
def PRFunction.positiveBit : PRFunction 1 :=
  PRFunction.composition
    PRFunction.ifZero
    (PRFunctionVector.cons
      PRFunction.identity
      (PRFunctionVector.cons
        PRFunction.zero
        (PRFunctionVector.singleton (PRFunction.constant 1 1))))

/-- The explicit positivity characteristic computes `natPositiveBit`. -/
theorem PRFunction.positiveBit_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.positiveBit
      (NatVector.cons value NatVector.nil)
      (natPositiveBit value) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact PRFunction.Evaluates.projection
        0
        (Nat.zero_lt_succ 0)
        (NatVector.cons value NatVector.nil)
    · apply PRFunctionVector.Evaluates.cons
      · exact PRFunction.Evaluates.zero
          (NatVector.cons value NatVector.nil)
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.constant_evaluates 1 1
            (NatVector.cons value NatVector.nil)
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons value NatVector.nil)
  · exact PRFunction.ifZero_evaluates value 0 1

/-- Numeric strict-order characteristic. -/
def natLessBit (left right : Nat) : Nat :=
  natPositiveBit (right - left)

/-- Positivity of the numeric strict-order bit is exactly strict order. -/
theorem natLessBit_pos_iff (left right : Nat) :
    0 < natLessBit left right ↔ left < right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero =>
          constructor
          · intro impossible
            exact (Nat.not_lt_zero 0 impossible).elim
          · intro impossible
            exact (Nat.not_lt_zero 0 impossible).elim
      | succ right =>
          constructor
          · intro _positive
            exact Nat.zero_lt_succ right
          · intro _strict
            exact Nat.zero_lt_succ 0
  | succ left inductionHypothesis =>
      cases right with
      | zero =>
          constructor
          · intro impossible
            unfold natLessBit natPositiveBit at impossible
            rw [Nat.zero_sub] at impossible
            exact (Nat.not_lt_zero 0 impossible).elim
          · intro impossible
            exact (Nat.not_lt_zero (Nat.succ left) impossible).elim
      | succ right =>
          constructor
          · intro positive
            unfold natLessBit at positive
            rw [Nat.succ_sub_succ_eq_sub] at positive
            exact Nat.succ_lt_succ ((inductionHypothesis right).mp positive)
          · intro strict
            have positive :=
              (inductionHypothesis right).mpr
                (Nat.lt_of_succ_lt_succ strict)
            unfold natLessBit at positive ⊢
            rw [Nat.succ_sub_succ_eq_sub]
            exact positive

/-- Difference `right - left` in conventional two-input order. -/
def PRFunction.rightMinusLeft : PRFunction 2 :=
  PRFunction.composition
    PRFunction.subtract
    (PRFunctionVector.cons
      (PRFunction.projection 2 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
      (PRFunctionVector.singleton
        (PRFunction.projection 2 0 (Nat.zero_lt_succ 1))))

/-- Primitive-recursive numeric strict-order characteristic. -/
def PRFunction.lessBit : PRFunction 2 :=
  PRFunction.composition
    PRFunction.positiveBit
    (PRFunctionVector.singleton PRFunction.rightMinusLeft)

/-- The explicit strict-order characteristic computes `natLessBit`. -/
theorem PRFunction.lessBit_evaluates (left right : Nat) :
    PRFunction.Evaluates
      PRFunction.lessBit
      (NatVector.cons left
        (NatVector.cons right NatVector.nil))
      (natLessBit left right) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
            (NatVector.cons left
              (NatVector.cons right NatVector.nil))
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              0
              (Nat.zero_lt_succ 1)
              (NatVector.cons left
                (NatVector.cons right NatVector.nil))
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons left
                (NatVector.cons right NatVector.nil))
      · exact PRFunction.subtract_evaluates right left
    · exact PRFunctionVector.Evaluates.nil
        (NatVector.cons left
          (NatVector.cons right NatVector.nil))
  · exact PRFunction.positiveBit_evaluates (right - left)

/-- Numeric equality characteristic. -/
def natEqualBit (left right : Nat) : Nat :=
  natIsZero ((left - right) + (right - left))

/-- Sum of both directed truncated differences. -/
def PRFunction.symmetricDifference : PRFunction 2 :=
  PRFunction.composition
    PRFunction.add
    (PRFunctionVector.cons
      PRFunction.subtract
      (PRFunctionVector.singleton PRFunction.rightMinusLeft))

/-- Primitive-recursive numeric equality characteristic. -/
def PRFunction.equalBit : PRFunction 2 :=
  PRFunction.composition
    PRFunction.isZero
    (PRFunctionVector.singleton PRFunction.symmetricDifference)

/-- The explicit equality characteristic computes `natEqualBit`. -/
theorem PRFunction.equalBit_evaluates (left right : Nat) :
    PRFunction.Evaluates
      PRFunction.equalBit
      (NatVector.cons left
        (NatVector.cons right NatVector.nil))
      (natEqualBit left right) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.subtract_evaluates left right
        · apply PRFunctionVector.Evaluates.cons
          · apply PRFunction.Evaluates.composition
            · apply PRFunctionVector.Evaluates.cons
              · exact PRFunction.Evaluates.projection
                  1
                  (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
                  (NatVector.cons left
                    (NatVector.cons right NatVector.nil))
              · apply PRFunctionVector.Evaluates.cons
                · exact PRFunction.Evaluates.projection
                    0
                    (Nat.zero_lt_succ 1)
                    (NatVector.cons left
                      (NatVector.cons right NatVector.nil))
                · exact PRFunctionVector.Evaluates.nil
                    (NatVector.cons left
                      (NatVector.cons right NatVector.nil))
            · exact PRFunction.subtract_evaluates right left
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons left
                (NatVector.cons right NatVector.nil))
      · exact PRFunction.add_evaluates
          (left - right)
          (right - left)
    · exact PRFunctionVector.Evaluates.nil
        (NatVector.cons left
          (NatVector.cons right NatVector.nil))
  · exact PRFunction.isZero_evaluates
      ((left - right) + (right - left))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.constant_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.multiply_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.subtract_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isZero_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.positiveBit_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.natLessBit_pos_iff
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.lessBit_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.equalBit_evaluates
/- AXIOM_AUDIT_END -/
