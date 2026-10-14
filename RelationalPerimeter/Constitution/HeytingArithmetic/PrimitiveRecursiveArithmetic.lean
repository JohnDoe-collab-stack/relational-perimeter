import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursive

/-!
# Derived primitive-recursive arithmetic programs

Every function in this file is an explicit `PRFunction` tree.  Correctness is
expressed by positive execution evidence, not by adding a semantic oracle to
the primitive-recursive language.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- A singleton vector of programs. -/
def PRFunctionVector.singleton
    {inputArity : Nat}
    (program : PRFunction inputArity) :
    PRFunctionVector inputArity 1 :=
  PRFunctionVector.cons program PRFunctionVector.nil

/-- Primitive-recursive addition, recursing on the first input. -/
def PRFunction.add : PRFunction 2 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 1 0 (Nat.zero_lt_succ 0))
    (PRFunction.composition
      PRFunction.successor
      (PRFunctionVector.singleton
        (PRFunction.projection 3 1
          (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))))

/-- The explicit addition program computes natural addition. -/
theorem PRFunction.add_evaluates (left right : Nat) :
    PRFunction.Evaluates
      PRFunction.add
      (NatVector.cons left
        (NatVector.cons right NatVector.nil))
      (left + right) := by
  induction left with
  | zero =>
      rw [Nat.zero_add]
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.projection
          0 (Nat.zero_lt_succ 0)
          (NatVector.cons right NatVector.nil))
  | succ left inductionHypothesis =>
      rw [Nat.succ_add]
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
            (NatVector.cons left
              (NatVector.cons (left + right)
                (NatVector.cons right NatVector.nil)))
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons left
              (NatVector.cons (left + right)
                (NatVector.cons right NatVector.nil)))
      · exact PRFunction.Evaluates.successor
          (NatVector.cons (left + right) NatVector.nil)

/-- Structural doubling agrees with adding a natural to itself. -/
theorem nat_add_self_eq_natDouble (value : Nat) :
    value + value = natDouble value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.succ_add, Nat.add_succ, inductionHypothesis]
      change
        Nat.succ (Nat.succ (natDouble value)) =
          Nat.succ (Nat.succ (natDouble value))
      rfl

/-- Primitive-recursive doubling by composition with addition. -/
def PRFunction.double : PRFunction 1 :=
  PRFunction.composition
    PRFunction.add
    (PRFunctionVector.cons PRFunction.identity
      (PRFunctionVector.singleton PRFunction.identity))

/-- The explicit doubling program computes the local structural double. -/
theorem PRFunction.double_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.double
      (NatVector.cons value NatVector.nil)
      (natDouble value) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact PRFunction.Evaluates.projection
        0 (Nat.zero_lt_succ 0)
        (NatVector.cons value NatVector.nil)
    · apply PRFunctionVector.Evaluates.cons
      · exact PRFunction.Evaluates.projection
          0 (Nat.zero_lt_succ 0)
          (NatVector.cons value NatVector.nil)
      · exact PRFunctionVector.Evaluates.nil
          (NatVector.cons value NatVector.nil)
  · have addition := PRFunction.add_evaluates value value
    rw [← nat_add_self_eq_natDouble value]
    exact addition

/-- The step `p |-> S(double p)` used by prefix pairing. -/
def PRFunction.pairStep : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.composition
        PRFunction.double
        (PRFunctionVector.singleton
          (PRFunction.projection 3 1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))))

/-- Primitive-recursive implementation of the local prefix pair. -/
def PRFunction.pair : PRFunction 2 :=
  PRFunction.primitiveRecursion
    PRFunction.double
    PRFunction.pairStep

/-- The explicit prefix-pair program computes `natPair`. -/
theorem PRFunction.pair_evaluates (tag payload : Nat) :
    PRFunction.Evaluates
      PRFunction.pair
      (NatVector.cons tag
        (NatVector.cons payload NatVector.nil))
      (natPair tag payload) := by
  induction tag with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.double_evaluates payload)
  | succ tag inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · apply PRFunction.Evaluates.composition
          · apply PRFunctionVector.Evaluates.cons
            · exact PRFunction.Evaluates.projection
                1
                (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
                (NatVector.cons tag
                  (NatVector.cons (natPair tag payload)
                    (NatVector.cons payload NatVector.nil)))
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons tag
                  (NatVector.cons (natPair tag payload)
                    (NatVector.cons payload NatVector.nil)))
          · exact PRFunction.double_evaluates (natPair tag payload)
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons tag
              (NatVector.cons (natPair tag payload)
                (NatVector.cons payload NatVector.nil)))
      · exact PRFunction.Evaluates.successor
          (NatVector.cons (natDouble (natPair tag payload)) NatVector.nil)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.add
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.add_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.nat_add_self_eq_natDouble
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.double
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.double_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.pair
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.pair_evaluates
/- AXIOM_AUDIT_END -/
