import RelationalPerimeter

/-! Public clients of the numerical prerequisites; these are not physical
scenarios and do not certify a geometry or gravitational field equation. -/
set_option genInjectivity false
namespace Tests.Relativity.NumericalChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Arithmetic
open RelationalPerimeter.Relativity.Analysis

theorem halves_agree : Rational.ofParts 1 0 1 = Rational.ofParts 2 0 3 :=
  Rational.normalize_congr (by decide)

theorem halves_sum : Rational.add (Rational.ofParts 1 0 1) (Rational.ofParts 1 0 1) = Rational.one := by
  apply Rational.normalize_congr
  apply Fraction.trans (Fraction.add_congr (Rational.normalize_agrees _) (Rational.normalize_agrees _))
  exact of_decide_eq_true rfl

theorem distributivity (a b c : Rational) :
    Rational.mul a (Rational.add b c) = Rational.add (Rational.mul a b) (Rational.mul a c) :=
  Rational.mul_add a b c

theorem rational_reflection (a b : Rational)
    (agreement : Agreement (CauchyRepresentation.constant a) (CauchyRepresentation.constant b)) : a = b :=
  constant_agreement_reflects_equality a b agreement

def different_encodings_same_reading : Agreement vanishingRepresentation (CauchyRepresentation.constant Rational.zero) :=
  vanishingAgreement

theorem encodings_remain_distinct : vanishingRepresentation ≠ CauchyRepresentation.constant Rational.zero :=
  vanishing_encoding_distinct

theorem no_false_constant_agreement :
    Agreement (CauchyRepresentation.constant Rational.one) (CauchyRepresentation.constant Rational.zero) → False :=
  fun h => Rational.one_ne_zero (constant_agreement_reflects_equality _ _ h)

def product_respects_reading :
    Agreement (CauchyRepresentation.mul vanishingRepresentation (CauchyRepresentation.constant Rational.one))
      (CauchyRepresentation.constant Rational.zero) :=
  Agreement.compose
    (CauchyRepresentation.mulAgreement vanishingAgreement
      (Agreement.reflexive (CauchyRepresentation.constant Rational.one)))
    (Agreement.compose (CauchyRepresentation.constantProduct Rational.zero Rational.one)
      (constant_agreement_of_equality _ _ (Rational.zero_mul _)))

theorem shared_jet_exact {dimension : Nat} (point : Fin dimension → Rational) (axis : Fin dimension)
    (polynomial : Polynomial dimension) :
    (Polynomial.evaluateJet point axis polynomial).value = Polynomial.evaluate point polynomial ∧
    (Polynomial.evaluateJet point axis polynomial).slope =
      Polynomial.evaluate point (Polynomial.formalDerivative axis polynomial) :=
  Polynomial.jet_exact point axis polynomial

theorem formal_primitive_exact (coefficients : List Rational) :
    UnivariateSeries.formalDerivative (UnivariateSeries.primitive coefficients) = coefficients :=
  UnivariateSeries.derivative_primitive coefficients

def polynomial_rational_reading {dimension : Nat} (point : Fin dimension → Rational) (polynomial : Polynomial dimension) :=
  Polynomial.rationalReading point polynomial

def sumSmoke : Nat := (Rational.add (Rational.ofParts 1 0 1) (Rational.ofParts 1 0 1)).index
theorem sumSmoke_exact : sumSmoke = Rational.one.index := congrArg Rational.index halves_sum

-- Executability check only, not a confirmatory experiment or cost claim.
#eval sumSmoke

end Tests.Relativity.NumericalChecks

/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.NumericalChecks.halves_agree
#print axioms Tests.Relativity.NumericalChecks.halves_sum
#print axioms Tests.Relativity.NumericalChecks.distributivity
#print axioms Tests.Relativity.NumericalChecks.rational_reflection
#print axioms Tests.Relativity.NumericalChecks.different_encodings_same_reading
#print axioms Tests.Relativity.NumericalChecks.encodings_remain_distinct
#print axioms Tests.Relativity.NumericalChecks.no_false_constant_agreement
#print axioms Tests.Relativity.NumericalChecks.product_respects_reading
#print axioms Tests.Relativity.NumericalChecks.shared_jet_exact
#print axioms Tests.Relativity.NumericalChecks.formal_primitive_exact
#print axioms Tests.Relativity.NumericalChecks.polynomial_rational_reading
#print axioms Tests.Relativity.NumericalChecks.sumSmoke
#print axioms Tests.Relativity.NumericalChecks.sumSmoke_exact
/- AXIOM_AUDIT_END -/
