import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveArithmetic

/-!
# Primitive-recursive control and binary decomposition

This module builds the control operations needed by the inverse of the local
Goedel pairing.  Programs remain explicit trees in the positive
`PRFunction` language; their specifications are witnessed by executions.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- The constant-one program at any input arity. -/
def PRFunction.constantOne (arity : Nat) : PRFunction arity :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton PRFunction.zero)

/-- The explicit constant-one program always returns one. -/
theorem PRFunction.constantOne_evaluates
    (arity : Nat)
    (inputs : NatVector arity) :
    PRFunction.Evaluates
      (PRFunction.constantOne arity)
      inputs
      1 := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact PRFunction.Evaluates.zero inputs
    · exact PRFunctionVector.Evaluates.nil inputs
  · exact PRFunction.Evaluates.successor
      (NatVector.cons 0 NatVector.nil)

/-- Primitive-recursive predecessor. -/
def PRFunction.predecessor : PRFunction 1 :=
  PRFunction.primitiveRecursion
    PRFunction.zero
    (PRFunction.projection 2 0 (Nat.zero_lt_succ 1))

/-- The explicit predecessor program computes `Nat.pred`. -/
theorem PRFunction.predecessor_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.predecessor
      (NatVector.cons value NatVector.nil)
      value.pred := by
  induction value with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.zero NatVector.nil)
  | succ value inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc
        inductionHypothesis
      exact PRFunction.Evaluates.projection
        0
        (Nat.zero_lt_succ 1)
        (NatVector.cons value
          (NatVector.cons value.pred NatVector.nil))

/-- Numeric zero test with two result branches. -/
def natIfZero : Nat -> Nat -> Nat -> Nat
  | 0, whenZero, _whenPositive => whenZero
  | Nat.succ _value, _whenZero, whenPositive => whenPositive

/-- Primitive-recursive zero test with branches in the second and third slots. -/
def PRFunction.ifZero : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 (Nat.zero_lt_succ 1))
    (PRFunction.projection 4 3
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))))

/-- The explicit zero-test program selects the specified branch. -/
theorem PRFunction.ifZero_evaluates
    (selector whenZero whenPositive : Nat) :
    PRFunction.Evaluates
      PRFunction.ifZero
      (NatVector.cons selector
        (NatVector.cons whenZero
          (NatVector.cons whenPositive NatVector.nil)))
      (natIfZero selector whenZero whenPositive) := by
  induction selector with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.projection
          0
          (Nat.zero_lt_succ 1)
          (NatVector.cons whenZero
            (NatVector.cons whenPositive NatVector.nil)))
  | succ selector inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc
        inductionHypothesis
      exact PRFunction.Evaluates.projection
        3
        (Nat.succ_lt_succ
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))
        (NatVector.cons selector
          (NatVector.cons (natIfZero selector whenZero whenPositive)
            (NatVector.cons whenZero
              (NatVector.cons whenPositive NatVector.nil))))

/-- Numeric parity bit: zero for even values and one for odd values. -/
def natParityBit : Nat -> Nat
  | 0 => 0
  | Nat.succ value => natIfZero (natParityBit value) 1 0

/-- One parity-toggle step, using the previous result. -/
def PRFunction.parityStep : PRFunction 2 :=
  PRFunction.composition
    PRFunction.ifZero
    (PRFunctionVector.cons
      (PRFunction.projection 2 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
      (PRFunctionVector.cons
        (PRFunction.constantOne 2)
        (PRFunctionVector.singleton PRFunction.zero)))

/-- Primitive-recursive numeric parity. -/
def PRFunction.parityBit : PRFunction 1 :=
  PRFunction.primitiveRecursion
    PRFunction.zero
    PRFunction.parityStep

/-- The explicit parity program computes `natParityBit`. -/
theorem PRFunction.parityBit_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.parityBit
      (NatVector.cons value NatVector.nil)
      (natParityBit value) := by
  induction value with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.zero NatVector.nil)
  | succ value inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
            (NatVector.cons value
              (NatVector.cons (natParityBit value) NatVector.nil))
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.constantOne_evaluates 2
              (NatVector.cons value
                (NatVector.cons (natParityBit value) NatVector.nil))
          · apply PRFunctionVector.Evaluates.cons
            · exact PRFunction.Evaluates.zero
                (NatVector.cons value
                  (NatVector.cons (natParityBit value) NatVector.nil))
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons value
                  (NatVector.cons (natParityBit value) NatVector.nil))
      · exact PRFunction.ifZero_evaluates (natParityBit value) 1 0

/-- Structural floor division by two, driven by the preceding parity bit. -/
def natHalf : Nat -> Nat
  | 0 => 0
  | Nat.succ value =>
      natIfZero
        (natParityBit value)
        (natHalf value)
        (Nat.succ (natHalf value))

/-- Parity of the recursion counter in the two-input step context. -/
def PRFunction.parityOfCounter : PRFunction 2 :=
  PRFunction.composition
    PRFunction.parityBit
    (PRFunctionVector.singleton
      (PRFunction.projection 2 0 (Nat.zero_lt_succ 1)))

/-- Successor of the previous result in the two-input step context. -/
def PRFunction.successorOfPrevious : PRFunction 2 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.projection 2 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

/-- One floor-halving step. -/
def PRFunction.halfStep : PRFunction 2 :=
  PRFunction.composition
    PRFunction.ifZero
    (PRFunctionVector.cons
      PRFunction.parityOfCounter
      (PRFunctionVector.cons
        (PRFunction.projection 2 1
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
        (PRFunctionVector.singleton PRFunction.successorOfPrevious)))

/-- Primitive-recursive structural floor division by two. -/
def PRFunction.half : PRFunction 1 :=
  PRFunction.primitiveRecursion
    PRFunction.zero
    PRFunction.halfStep

/-- The explicit halving program computes `natHalf`. -/
theorem PRFunction.half_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.half
      (NatVector.cons value NatVector.nil)
      (natHalf value) := by
  induction value with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.zero NatVector.nil)
  | succ value inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · apply PRFunction.Evaluates.composition
          · apply PRFunctionVector.Evaluates.cons
            · exact PRFunction.Evaluates.projection
                0
                (Nat.zero_lt_succ 1)
                (NatVector.cons value
                  (NatVector.cons (natHalf value) NatVector.nil))
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons value
                  (NatVector.cons (natHalf value) NatVector.nil))
          · exact PRFunction.parityBit_evaluates value
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              1
              (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
              (NatVector.cons value
                (NatVector.cons (natHalf value) NatVector.nil))
          · apply PRFunctionVector.Evaluates.cons
            · apply PRFunction.Evaluates.composition
              · apply PRFunctionVector.Evaluates.cons
                · exact PRFunction.Evaluates.projection
                    1
                    (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
                    (NatVector.cons value
                      (NatVector.cons (natHalf value) NatVector.nil))
                · exact PRFunctionVector.Evaluates.nil
                    (NatVector.cons value
                      (NatVector.cons (natHalf value) NatVector.nil))
              · exact PRFunction.Evaluates.successor
                  (NatVector.cons (natHalf value) NatVector.nil)
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons value
                  (NatVector.cons (natHalf value) NatVector.nil))
      · exact PRFunction.ifZero_evaluates
          (natParityBit value)
          (natHalf value)
          (Nat.succ (natHalf value))

/-- Even structural doubles have parity bit zero. -/
theorem natParityBit_natDouble (value : Nat) :
    natParityBit (natDouble value) = 0 := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change
        natIfZero
          (natIfZero (natParityBit (natDouble value)) 1 0)
          1
          0 = 0
      rw [inductionHypothesis]
      rfl

/-- Odd successors of structural doubles have parity bit one. -/
theorem natParityBit_succ_natDouble (value : Nat) :
    natParityBit (Nat.succ (natDouble value)) = 1 := by
  change natIfZero (natParityBit (natDouble value)) 1 0 = 1
  rw [natParityBit_natDouble]
  rfl

/-- Halving a structural double recovers its payload. -/
theorem natHalf_natDouble (value : Nat) :
    natHalf (natDouble value) = value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change
        natIfZero
          (natParityBit (Nat.succ (natDouble value)))
          (natHalf (Nat.succ (natDouble value)))
          (Nat.succ (natHalf (Nat.succ (natDouble value)))) =
            Nat.succ value
      rw [natParityBit_succ_natDouble]
      change
        Nat.succ
          (natIfZero
            (natParityBit (natDouble value))
            (natHalf (natDouble value))
            (Nat.succ (natHalf (natDouble value)))) =
          Nat.succ value
      rw [natParityBit_natDouble, inductionHypothesis]
      rfl

/-- Halving an odd successor of a structural double also recovers its payload. -/
theorem natHalf_succ_natDouble (value : Nat) :
    natHalf (Nat.succ (natDouble value)) = value := by
  change
    natIfZero
      (natParityBit (natDouble value))
      (natHalf (natDouble value))
      (Nat.succ (natHalf (natDouble value))) = value
  rw [natParityBit_natDouble, natHalf_natDouble]
  rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.predecessor_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.ifZero_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.parityBit_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.half_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.natParityBit_natDouble
#print axioms RelationalPerimeter.HeytingArithmetic.natParityBit_succ_natDouble
#print axioms RelationalPerimeter.HeytingArithmetic.natHalf_natDouble
#print axioms RelationalPerimeter.HeytingArithmetic.natHalf_succ_natDouble
/- AXIOM_AUDIT_END -/
