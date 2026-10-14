import RelationalPerimeter.Constitution.HeytingArithmetic.InternalTermNormalization

/-!
# Internal HA certificates for concrete order and beta computations
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem natAddComputedGapEq
    {smaller larger : Nat}
    (strict : smaller < larger) :
    smaller + Nat.succ (larger - Nat.succ smaller) = larger := by
  induction smaller generalizing larger with
  | zero =>
      cases larger with
      | zero => exact (Nat.not_lt_zero 0 strict).elim
      | succ larger =>
          rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.zero_add]
  | succ smaller inductionHypothesis =>
      cases larger with
      | zero => exact (Nat.not_lt_zero (Nat.succ smaller) strict).elim
      | succ larger =>
          have earlier : smaller < larger :=
            Nat.lt_of_succ_lt_succ strict
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_add]
          exact congrArg Nat.succ (inductionHypothesis earlier)

private def castDerivationConclusion
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {source target : ScopedFormula bound}
    (sameConclusion : source = target)
    (proof : Derivation mode theory context source) :
    Derivation mode theory context target := by
  cases sameConclusion
  exact proof

private theorem RawFormula.instantiate_shifted_add_succ_equation
    (left right replacement : RawTerm) :
    (RawFormula.equal
        (RawTerm.add left.shift (RawTerm.succ (RawTerm.bvar 0)))
        right.shift).instantiateTerm replacement =
      RawFormula.equal
        (RawTerm.add left (RawTerm.succ replacement)) right := by
  apply congrArgTwo RawFormula.equal
  · apply congrArgTwo RawTerm.add
    · exact RawTerm.renameSucc_substituteSingle left replacement
    · rfl
  · exact RawTerm.renameSucc_substituteSingle right replacement

private theorem RawFormula.instantiate_shifted_mul_add_equation
    (dividend modulus remainder replacement : RawTerm) :
    (RawFormula.equal dividend.shift
        (RawTerm.add
          (RawTerm.mul (RawTerm.bvar 0) modulus.shift)
          remainder.shift)).instantiateTerm replacement =
      RawFormula.equal dividend
        (RawTerm.add (RawTerm.mul replacement modulus) remainder) := by
  apply congrArgTwo RawFormula.equal
  · exact RawTerm.renameSucc_substituteSingle dividend replacement
  · apply congrArgTwo RawTerm.add
    · apply congrArgTwo RawTerm.mul
      · rfl
      · exact RawTerm.renameSucc_substituteSingle modulus replacement
    · exact RawTerm.renameSucc_substituteSingle remainder replacement

def scopedLessThanFormula
    (left right : ScopedTerm 0) : ScopedFormula 0 :=
  { raw := lessThanFormula left.raw right.raw
    isScoped := lessThanFormula_wellScoped left.raw right.raw
      left.isScoped right.isScoped }

def lessThanClosedProof
    (left right : ScopedTerm 0)
    (strict : left.raw.evaluate emptyEnvironment <
      right.raw.evaluate emptyEnvironment) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedLessThanFormula left right) := by
  let gap := right.raw.evaluate emptyEnvironment -
    Nat.succ (left.raw.evaluate emptyEnvironment)
  have exactSum : left.raw.evaluate emptyEnvironment + Nat.succ gap =
      right.raw.evaluate emptyEnvironment :=
    natAddComputedGapEq strict
  let body : ScopedFormula 1 :=
    { raw := RawFormula.equal
        (RawTerm.add left.raw.shift
          (RawTerm.succ (RawTerm.bvar 0)))
        right.raw.shift
      isScoped := And.intro
        (And.intro
          (left.raw.shift_wellScoped left.isScoped)
          (Nat.zero_lt_succ 0))
        (right.raw.shift_wellScoped right.isScoped) }
  let instantiatedLeft : ScopedTerm 0 :=
    ScopedTerm.add left (ScopedTerm.numeral 0 (Nat.succ gap))
  have instantiatedEquality :
      Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
        (ScopedFormula.equal instantiatedLeft right) :=
    closedTermEqualityProof instantiatedLeft right (by
      change left.raw.evaluate emptyEnvironment +
          (RawTerm.numeral (Nat.succ gap)).evaluate emptyEnvironment =
        right.raw.evaluate emptyEnvironment
      rw [RawTerm.evaluate_numeral]
      exact exactSum)
  have instantiatedBody : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      (body.instantiate (ScopedTerm.numeral 0 gap)) := by
    refine castDerivationConclusion ?_ instantiatedEquality
    apply ScopedFormula.eq_of_raw_eq
    exact (RawFormula.instantiate_shifted_add_succ_equation
      left.raw right.raw (RawTerm.numeral gap)).symm
  let introduced := Derivation.existentialIntroduction
    (body := body) (ScopedTerm.numeral 0 gap) instantiatedBody
  refine castDerivationConclusion ?_ introduced
  apply ScopedFormula.eq_of_raw_eq
  rfl

def scopedRemainderFormula
    (dividend modulus remainder : ScopedTerm 0) : ScopedFormula 0 :=
  { raw := remainderFormula dividend.raw modulus.raw remainder.raw
    isScoped := remainderFormula_wellScoped
      dividend.raw modulus.raw remainder.raw
      dividend.isScoped modulus.isScoped remainder.isScoped }

def remainderClosedProof
    (dividend modulus remainder : ScopedTerm 0)
    (modulusPositive : 0 < modulus.raw.evaluate emptyEnvironment)
    (correct : remainder.raw.evaluate emptyEnvironment =
      constructiveRemainder
        (dividend.raw.evaluate emptyEnvironment)
        (modulus.raw.evaluate emptyEnvironment)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedRemainderFormula dividend modulus remainder) := by
  let dividendValue := dividend.raw.evaluate emptyEnvironment
  let modulusValue := modulus.raw.evaluate emptyEnvironment
  let remainderValue := remainder.raw.evaluate emptyEnvironment
  have division := constructiveDivMod_spec dividendValue modulusValue
    modulusPositive
  have remainderBound : remainderValue < modulusValue := by
    change remainder.raw.evaluate emptyEnvironment <
      modulus.raw.evaluate emptyEnvironment
    rw [correct]
    exact division.2
  let boundedProof := lessThanClosedProof remainder modulus remainderBound
  let quotient := constructiveQuotient dividendValue modulusValue
  let quotientTerm := ScopedTerm.numeral 0 quotient
  let sumTerm := ScopedTerm.add (ScopedTerm.mul quotientTerm modulus) remainder
  have quotientEquation : dividendValue = sumTerm.raw.evaluate emptyEnvironment := by
    change dividendValue =
      (RawTerm.numeral quotient).evaluate emptyEnvironment *
        modulusValue + remainderValue
    rw [RawTerm.evaluate_numeral]
    change dividend.raw.evaluate emptyEnvironment =
      quotient * modulus.raw.evaluate emptyEnvironment +
        remainder.raw.evaluate emptyEnvironment
    rw [correct]
    exact division.1
  let equationProof := closedTermEqualityProof dividend sumTerm quotientEquation
  let equationBody : ScopedFormula 1 :=
    { raw := RawFormula.equal dividend.raw.shift
        (RawTerm.add
          (RawTerm.mul (RawTerm.bvar 0) modulus.raw.shift)
          remainder.raw.shift)
      isScoped := And.intro
        (dividend.raw.shift_wellScoped dividend.isScoped)
        (And.intro
          (And.intro
            (Nat.zero_lt_succ 0)
            (modulus.raw.shift_wellScoped modulus.isScoped))
          (remainder.raw.shift_wellScoped remainder.isScoped)) }
  have instantiatedEquation : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil (equationBody.instantiate quotientTerm) := by
    refine castDerivationConclusion ?_ equationProof
    apply ScopedFormula.eq_of_raw_eq
    exact (RawFormula.instantiate_shifted_mul_add_equation
      dividend.raw modulus.raw remainder.raw
      (RawTerm.numeral quotient)).symm
  let quotientWitness := Derivation.existentialIntroduction
    (body := equationBody) quotientTerm instantiatedEquation
  have normalizedWitness : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      { raw := RawFormula.ex
          (RawFormula.equal dividend.raw.shift
            (RawTerm.add
              (RawTerm.mul (RawTerm.bvar 0) modulus.raw.shift)
              remainder.raw.shift))
        isScoped := equationBody.isScoped } := by
    refine castDerivationConclusion ?_ quotientWitness
    apply ScopedFormula.eq_of_raw_eq
    rfl
  exact Derivation.conjunctionIntroduction boundedProof normalizedWitness

def scopedBetaValueFormula
    {bound : Nat}
    (dividend coefficient index value : ScopedTerm bound) : ScopedFormula bound :=
  { raw := betaValueFormula dividend.raw coefficient.raw index.raw value.raw
    isScoped := betaValueFormula_wellScoped
      dividend.raw coefficient.raw index.raw value.raw
      dividend.isScoped coefficient.isScoped index.isScoped value.isScoped }

def betaValueClosedProof
    (dividend coefficient index value : ScopedTerm 0)
    (correct : value.raw.evaluate emptyEnvironment =
      constructiveRemainder
        (dividend.raw.evaluate emptyEnvironment)
        ((index.raw.evaluate emptyEnvironment + 1) *
          coefficient.raw.evaluate emptyEnvironment + 1)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedBetaValueFormula dividend coefficient index value) := by
  let modulus := ScopedTerm.succ
    (ScopedTerm.mul (ScopedTerm.succ index) coefficient)
  have modulusPositive : 0 < modulus.raw.evaluate emptyEnvironment :=
    Nat.zero_lt_succ _
  have normalizedCorrect : value.raw.evaluate emptyEnvironment =
      constructiveRemainder
        (dividend.raw.evaluate emptyEnvironment)
        (modulus.raw.evaluate emptyEnvironment) := correct
  refine castDerivationConclusion ?_
    (remainderClosedProof dividend modulus value modulusPositive
      normalizedCorrect)
  apply ScopedFormula.eq_of_raw_eq
  rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanClosedProof
#print axioms RelationalPerimeter.HeytingArithmetic.remainderClosedProof
#print axioms RelationalPerimeter.HeytingArithmetic.betaValueClosedProof
/- AXIOM_AUDIT_END -/
