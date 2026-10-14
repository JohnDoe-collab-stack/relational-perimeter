import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveDivision
import RelationalPerimeter.Constitution.HeytingArithmetic.Representability

/-!
# Primitive-recursive Goedel beta lookup

This file closes the numeric dependency needed by encoded proof archives.  It
builds the ordinary beta component

`dividend mod (((index + 1) * coefficient) + 1)`

as an explicit positive `PRFunction` tree, using the structural remainder
compiled in `PrimitiveRecursiveDivision`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem PRFunction.run_multiply_beta (left right : Nat) :
    PRFunction.multiply.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      left * right :=
  (PRFunction.multiply_evaluates left right).symm

/-! ## Modulus construction -/

/-- The successor of the beta index. -/
def PRFunction.betaIndexSuccessor : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.projection 3 2
        (Nat.succ_lt_succ
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))))

/-- Product `(index + 1) * coefficient`. -/
def PRFunction.betaScaledIndex : PRFunction 3 :=
  PRFunction.composition
    PRFunction.multiply
    (PRFunctionVector.cons
      PRFunction.betaIndexSuccessor
      (PRFunctionVector.singleton
        (PRFunction.projection 3 1
          (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))))

/-- Positive beta modulus `((index + 1) * coefficient) + 1`. -/
def PRFunction.betaModulus : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton PRFunction.betaScaledIndex)

/-- Primitive-recursive lookup in a beta-coded archive. -/
def PRFunction.betaLookup : PRFunction 3 :=
  PRFunction.composition
    PRFunction.constructiveRemainder
    (PRFunctionVector.cons
      (PRFunction.projection 3 0 (Nat.zero_lt_succ 2))
      (PRFunctionVector.singleton PRFunction.betaModulus))

@[simp] theorem PRFunction.run_betaIndexSuccessor
    (dividend coefficient index : Nat) :
    PRFunction.betaIndexSuccessor.run
        (NatVector.cons dividend
          (NatVector.cons coefficient
            (NatVector.cons index NatVector.nil))) =
      Nat.succ index := by
  unfold PRFunction.betaIndexSuccessor
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_projection, PRFunction.run_successor]
  rfl

@[simp] theorem PRFunction.run_betaScaledIndex
    (dividend coefficient index : Nat) :
    PRFunction.betaScaledIndex.run
        (NatVector.cons dividend
          (NatVector.cons coefficient
            (NatVector.cons index NatVector.nil))) =
      Nat.succ index * coefficient := by
  unfold PRFunction.betaScaledIndex
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_betaIndexSuccessor,
    PRFunction.run_projection, PRFunction.run_multiply_beta]
  rfl

@[simp] theorem PRFunction.run_betaModulus
    (dividend coefficient index : Nat) :
    PRFunction.betaModulus.run
        (NatVector.cons dividend
          (NatVector.cons coefficient
            (NatVector.cons index NatVector.nil))) =
      Nat.succ (Nat.succ index * coefficient) := by
  unfold PRFunction.betaModulus
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_betaScaledIndex, PRFunction.run_successor]

/-- The compiled lookup computes the numeric beta component exactly. -/
theorem PRFunction.betaLookup_run
    (dividend coefficient index : Nat) :
    PRFunction.betaLookup.run
        (NatVector.cons dividend
          (NatVector.cons coefficient
            (NatVector.cons index NatVector.nil))) =
      betaComponent dividend coefficient index := by
  unfold PRFunction.betaLookup betaComponent
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_projection,
    PRFunction.run_betaModulus,
    PRFunction.constructiveRemainder_run]
  rfl

/-- Positive execution certificate for beta archive lookup. -/
theorem PRFunction.betaLookup_evaluates
    (dividend coefficient index : Nat) :
    PRFunction.Evaluates
      PRFunction.betaLookup
      (NatVector.cons dividend
        (NatVector.cons coefficient
          (NatVector.cons index NatVector.nil)))
      (betaComponent dividend coefficient index) := by
  unfold PRFunction.Evaluates
  exact (PRFunction.betaLookup_run dividend coefficient index).symm

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.betaLookup_run
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.betaLookup_evaluates
/- AXIOM_AUDIT_END -/
