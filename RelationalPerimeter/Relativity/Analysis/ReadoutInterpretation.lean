import RelationalPerimeter.Relativity.Analysis.ConstructiveContinuum

/-!
The rational injection into Cauchy representations is faithful: positive
analytic agreement of constant exact readings reflects their numerical
equality. This does not identify source occurrences or arbitrary encodings.
Multiplicative and differential interpretation remain separate obligations.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Analysis
open Arithmetic

private theorem gap_positive {a b : Nat} (h : a < b) : 0 < b - a := by
  apply Nat.pos_of_ne_zero
  intro zero
  have same := Natural.sub_add_of_le (Nat.le_of_lt h)
  rw [zero, Nat.zero_add] at same
  rw [same] at h
  exact Nat.lt_irrefl _ h

private theorem doubled_gap_exceeds {a b d : Nat} (h : a < b) (hd : 0 < d) :
    ¬ b * (2 * d) ≤ (b - a) * d + a * (2 * d) := by
  intro bound
  have left : b * (2 * d) = (b * 2) * d := by exact_natural
  have right : (b - a) * d + a * (2 * d) = ((b - a) + a * 2) * d := by exact_natural
  rw [left, right] at bound
  have reduced := Nat.le_of_mul_le_mul_right bound hd
  have rebuild := Natural.sub_add_of_le (Nat.le_of_lt h)
  conv at reduced => lhs; rw [← rebuild]
  rw [Natural.add_mul] at reduced
  have tooSmall := Natural.le_cancel_right (a * 2) reduced
  rw [Nat.mul_succ, Nat.mul_one] at tooSmall
  have zeroBound : b - a ≤ 0 := by
    apply Natural.le_cancel_left (b - a)
    rw [Nat.add_zero]
    exact tooSmall
  exact Nat.not_le_of_gt (gap_positive h) zeroBound

private def crossLeft (a b : Fraction) : Nat :=
  a.numerator.positive * b.denominator + b.numerator.negative * a.denominator

private def crossRight (a b : Fraction) : Nat :=
  b.numerator.positive * a.denominator + a.numerator.negative * b.denominator

private def separationPrecision (a b : Fraction) (h : crossLeft a b < crossRight a b) : Precision :=
  ⟨crossRight a b - crossLeft a b, 2 * (a.denominator * b.denominator), gap_positive h,
   Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.mul_pos a.positive b.positive)⟩

private theorem precision_separates (a b : Fraction) (h : crossLeft a b < crossRight a b) :
    ¬ Fraction.Le (Fraction.sub b a) (separationPrecision a b h).fraction := by
  intro bound
  unfold Fraction.Le Fraction.sub Fraction.add Fraction.neg
    Balance.Le Balance.add Balance.neg Balance.scale Precision.fraction separationPrecision at bound
  have numerical : crossRight a b * (2 * (a.denominator * b.denominator)) ≤
      (crossRight a b - crossLeft a b) * (a.denominator * b.denominator) +
        crossLeft a b * (2 * (a.denominator * b.denominator)) := by
    calc
      _ = _ := by unfold crossRight; exact_natural
      _ ≤ _ := bound
      _ = _ := by unfold crossLeft; exact_natural
  exact doubled_gap_exceeds h (Nat.mul_pos a.positive b.positive) numerical

theorem constant_agreement_reflects_equality (a b : Rational)
    (agreement : Agreement (CauchyRepresentation.constant a) (CauchyRepresentation.constant b)) : a = b := by
  apply Rational.equal_of_agree
  by_cases same : Fraction.Agree a.representation b.representation
  · exact same
  · have different : crossLeft a.representation b.representation ≠ crossRight a.representation b.representation := same
    cases Nat.le_total (crossLeft a.representation b.representation) (crossRight a.representation b.representation) with
    | inl lower =>
      cases Nat.lt_or_eq_of_le lower with
      | inr equal => exact False.elim (different equal)
      | inl strict =>
        let e := separationPrecision a.representation b.representation strict
        have close := agreement.close e (agreement.modulus e) (agreement.modulus e)
          (Nat.le_refl _) (Nat.le_refl _)
        have raw := (Fraction.le_congr (Rational.sub_representation_agrees b a)
          (Rational.normalize_agrees e.fraction)).mp close.2
        exact False.elim (precision_separates _ _ strict raw)
    | inr upper =>
      cases Nat.lt_or_eq_of_le upper with
      | inr equal => exact False.elim (different equal.symm)
      | inl strict =>
        have reverseStrict : crossLeft b.representation a.representation < crossRight b.representation a.representation := strict
        let e := separationPrecision b.representation a.representation reverseStrict
        have close := agreement.close e (agreement.modulus e) (agreement.modulus e)
          (Nat.le_refl _) (Nat.le_refl _)
        have raw := (Fraction.le_congr (Rational.sub_representation_agrees a b)
          (Rational.normalize_agrees e.fraction)).mp close.1
        exact False.elim (precision_separates _ _ reverseStrict raw)

def constant_agreement_of_equality (a b : Rational) (h : a = b) :
    Agreement (CauchyRepresentation.constant a) (CauchyRepresentation.constant b) :=
  h ▸ Agreement.reflexive (CauchyRepresentation.constant a)

theorem constant_agreement_iff_equality (a b : Rational) :
    Nonempty (Agreement (CauchyRepresentation.constant a) (CauchyRepresentation.constant b)) ↔ a = b :=
  ⟨fun ⟨agreement⟩ => constant_agreement_reflects_equality a b agreement,
   fun h => ⟨constant_agreement_of_equality a b h⟩⟩

private theorem reciprocal_nonnegative (n : Nat) : Rational.Le Rational.zero (Rational.inverseNatSucc n) := by
  apply (Rational.normalize_le_iff _ _).mpr
  unfold Fraction.Le Fraction.zero Fraction.ofParts Balance.Le Balance.scale Balance.zero
  dsimp only
  conv => lhs; simp only [Nat.zero_mul, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  conv => rhs; simp only [Nat.zero_mul, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  exact Nat.zero_le _

private theorem reciprocal_le_precision (e : Precision) (n : Nat) (hn : e.denominator ≤ n) :
    Rational.Le (Rational.inverseNatSucc n) e.value := by
  apply (Rational.normalize_le_iff _ _).mpr
  unfold Fraction.Le Fraction.ofParts Precision.fraction Balance.Le Balance.scale
  dsimp only
  conv => lhs; simp only [Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  conv => rhs; simp only [Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  have unit : n + 1 ≤ e.numerator * (n + 1) := by
    have positive := Nat.mul_le_mul_right (n + 1) e.numeratorPositive
    rw [Nat.one_mul] at positive
    exact positive
  exact Nat.le_trans hn (Nat.le_trans (Nat.le_succ n) unit)

private theorem bounded_nonnegative_difference {a b bound : Rational}
    (ha : Rational.Le a bound) (hb : Rational.Le Rational.zero b) : Rational.Le (Rational.sub a b) bound := by
  have negative := Rational.neg_le_neg hb
  rw [Rational.neg_zero] at negative
  have combined := Rational.add_le ha negative
  rw [Rational.add_zero] at combined
  exact combined

/-- A genuinely nonconstant rational sequence with a constructed Cauchy
modulus; its agreement with zero is proved below without identifying it. -/
def vanishingRepresentation : CauchyRepresentation where
  approximate := Rational.inverseNatSucc
  modulus e := e.denominator
  cauchy e n m hn hm :=
    ⟨bounded_nonnegative_difference (reciprocal_le_precision e n hn) (reciprocal_nonnegative m),
     bounded_nonnegative_difference (reciprocal_le_precision e m hm) (reciprocal_nonnegative n)⟩

def vanishingAgreement : Agreement vanishingRepresentation (CauchyRepresentation.constant Rational.zero) where
  modulus e := e.denominator
  close e n _ hn _ := by
    change Close (Rational.inverseNatSucc n) Rational.zero e.value
    constructor
    · rw [Rational.sub_zero]
      exact reciprocal_le_precision e n hn
    · rw [Rational.zero_sub]
      have nonpositive := Rational.neg_le_neg (reciprocal_nonnegative n)
      rw [Rational.neg_zero] at nonpositive
      exact Rational.le_trans nonpositive e.zero_le_value

theorem vanishing_encoding_distinct : vanishingRepresentation ≠ CauchyRepresentation.constant Rational.zero := by
  intro same
  have initial := congrArg (fun representation : CauchyRepresentation => representation.approximate 0) same
  exact Rational.one_ne_zero initial

end RelationalPerimeter.Relativity.Analysis

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Analysis.constant_agreement_reflects_equality
#print axioms RelationalPerimeter.Relativity.Analysis.constant_agreement_of_equality
#print axioms RelationalPerimeter.Relativity.Analysis.constant_agreement_iff_equality
#print axioms RelationalPerimeter.Relativity.Analysis.vanishingRepresentation
#print axioms RelationalPerimeter.Relativity.Analysis.vanishingAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.vanishing_encoding_distinct
/- AXIOM_AUDIT_END -/
