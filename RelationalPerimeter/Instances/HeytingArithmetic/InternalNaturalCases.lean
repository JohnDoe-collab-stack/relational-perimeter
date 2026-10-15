import RelationalPerimeter.Instances.HeytingArithmetic.InternalConcreteArithmetic

/-!
# Internal decomposition of natural-number variables
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def zeroOrSuccessorBody : ScopedFormula 1 :=
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  let predecessorBody : ScopedFormula 2 :=
    ScopedFormula.equal
      (ScopedTerm.bvar 1 (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
      (ScopedTerm.succ (ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)))
  ScopedFormula.disj
    (ScopedFormula.equal value (ScopedTerm.zero 1))
    (ScopedFormula.ex predecessorBody)

def zeroOrSuccessorBaseProof :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (zeroOrSuccessorBody.instantiate (ScopedTerm.zero 0)) := by
  let predecessorBody : ScopedFormula 1 :=
    ScopedFormula.equal
      (ScopedTerm.zero 0).lift
      (ScopedTerm.succ (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.zero 0) (ScopedTerm.zero 0)) :=
    Derivation.equalityReflexivity (ScopedTerm.zero 0)
  let result := Derivation.disjunctionIntroductionLeft
    (right := ScopedFormula.ex predecessorBody) reflexive
  have baseExact :
      zeroOrSuccessorBody.instantiate (ScopedTerm.zero 0) =
        ScopedFormula.disj
          (ScopedFormula.equal (ScopedTerm.zero 0) (ScopedTerm.zero 0))
          (ScopedFormula.ex predecessorBody) := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  rw [baseExact]
  exact result

def zeroOrSuccessorStepProof :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl zeroOrSuccessorBody
          (zeroOrSuccessorBody.successorInstance))) := by
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  let predecessorBody : ScopedFormula 2 :=
    ScopedFormula.equal
      (ScopedTerm.succ
        (ScopedTerm.bvar 1 (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))
      (ScopedTerm.succ (ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)))
  have reflexive : Derivation LogicMode.intuitionistic haTheory
      (FormulaContext.cons zeroOrSuccessorBody FormulaContext.nil.lift)
      (ScopedFormula.equal value.succ value.succ) :=
    Derivation.equalityReflexivity value.succ
  have predecessorAtValue :
      predecessorBody.instantiate value =
        ScopedFormula.equal value.succ value.succ := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  have predecessorProof : Derivation LogicMode.intuitionistic haTheory
      (FormulaContext.cons zeroOrSuccessorBody FormulaContext.nil.lift)
      (predecessorBody.instantiate value) := by
    rw [predecessorAtValue]
    exact reflexive
  let introduced := Derivation.existentialIntroduction
    (body := predecessorBody) value predecessorProof
  let result := Derivation.disjunctionIntroductionRight
    (left := ScopedFormula.equal value.succ (ScopedTerm.zero 1)) introduced
  have successorExact : zeroOrSuccessorBody.successorInstance =
      ScopedFormula.disj
        (ScopedFormula.equal value.succ (ScopedTerm.zero 1))
        (ScopedFormula.ex predecessorBody) := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  rw [successorExact]
  exact result

def zeroOrSuccessorProof :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all zeroOrSuccessorBody) := by
  let inductionAxiom : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil (ScopedFormula.induction zeroOrSuccessorBody) :=
    Derivation.theoryAxiom
      (StandardArithmeticAxiom.induction zeroOrSuccessorBody)
  let premises : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.conj
        (zeroOrSuccessorBody.instantiate (ScopedTerm.zero 0))
        (ScopedFormula.all
          (ScopedFormula.impl zeroOrSuccessorBody
            zeroOrSuccessorBody.successorInstance))) :=
    Derivation.conjunctionIntroduction zeroOrSuccessorBaseProof
      zeroOrSuccessorStepProof
  exact Derivation.implicationElimination inductionAxiom premises

def zeroOrSuccessorAt
    (term : ScopedTerm 0) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (zeroOrSuccessorBody.instantiate term) :=
  Derivation.universalElimination term zeroOrSuccessorProof

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.zeroOrSuccessorProof
#print axioms RelationalPerimeter.HeytingArithmetic.zeroOrSuccessorAt
/- AXIOM_AUDIT_END -/
