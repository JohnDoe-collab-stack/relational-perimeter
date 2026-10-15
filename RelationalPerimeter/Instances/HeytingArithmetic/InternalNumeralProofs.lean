import RelationalPerimeter.Instances.HeytingArithmetic.ProofTheoryTransport

/-!
# Object-level HA proofs for concrete numerals

These are proof-producing computations.  Meta-level equality or inequality of
natural numbers is consumed to build an explicit `Derivation` in the object
calculus; semantic truth is never used as a proof rule.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def numeralEqualityFormula (bound left right : Nat) : ScopedFormula bound :=
  ScopedFormula.equal
    (ScopedTerm.numeral bound left)
    (ScopedTerm.numeral bound right)

def numeralEqualityProof
    (bound left right : Nat)
    (same : left = right) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (numeralEqualityFormula bound left right) := by
  subst right
  exact Derivation.equalityReflexivity (ScopedTerm.numeral bound left)

def numeralInequalityProof :
    (bound left right : Nat) ->
    (different : left = right -> False) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.neg (numeralEqualityFormula bound left right))
  | bound, 0, 0, different => (different rfl).elim
  | bound, 0, Nat.succ right, _different => by
      let equality := numeralEqualityFormula bound 0 (Nat.succ right)
      let reverseEquality :=
        numeralEqualityFormula bound (Nat.succ right) 0
      let assumed : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil) equality :=
        Derivation.hypothesis ContextMember.here
      let reversed : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil) reverseEquality :=
        Derivation.equalitySymmetry assumed
      let nonzero : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil)
          (ScopedFormula.neg reverseEquality) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.successorNotZero
            (ScopedTerm.numeral bound right))
      exact Derivation.implicationIntroduction
        (Derivation.implicationElimination nonzero reversed)
  | bound, Nat.succ left, 0, _different =>
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.successorNotZero
          (ScopedTerm.numeral bound left))
  | bound, Nat.succ left, Nat.succ right, different => by
      let equality :=
        numeralEqualityFormula bound (Nat.succ left) (Nat.succ right)
      let predecessorEquality := numeralEqualityFormula bound left right
      have predecessorDifferent : left = right -> False := by
        intro same
        exact different (congrArg Nat.succ same)
      let assumed : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil) equality :=
        Derivation.hypothesis ContextMember.here
      let injective : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil)
          (ScopedFormula.impl equality predecessorEquality) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.successorInjective
            (ScopedTerm.numeral bound left)
            (ScopedTerm.numeral bound right))
      let predecessors : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil)
          predecessorEquality :=
        Derivation.implicationElimination injective assumed
      let predecessorsDiffer : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons equality FormulaContext.nil)
          (ScopedFormula.neg predecessorEquality) :=
        Derivation.weaken equality
          (numeralInequalityProof bound left right predecessorDifferent)
      exact Derivation.implicationIntroduction
        (Derivation.implicationElimination predecessorsDiffer predecessors)

theorem numeralEqualityFormula_raw
    (bound left right : Nat) :
    (numeralEqualityFormula bound left right).raw =
      RawFormula.equal (RawTerm.numeral left) (RawTerm.numeral right) := rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.numeralEqualityProof
#print axioms RelationalPerimeter.HeytingArithmetic.numeralInequalityProof
/- AXIOM_AUDIT_END -/
