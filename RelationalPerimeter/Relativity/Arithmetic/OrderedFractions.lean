import RelationalPerimeter.Relativity.ExactArithmetic

/-!
Executable rational comparisons and their representation laws. Comparisons
apply to exact rational data, not to arbitrary analytic encodings.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Arithmetic

namespace Balance

def Le (a b : Balance) : Prop := a.positive + b.negative ≤ b.positive + a.negative
instance (a b : Balance) : Decidable (Le a b) := inferInstanceAs (Decidable (_ ≤ _))

theorem le_refl (a : Balance) : Le a a := Nat.le_refl _
theorem agree_le {a b : Balance} (h : Agree a b) : Le a b := by
  unfold Le
  rw [h]
  exact Nat.le_refl _

theorem le_trans {a b c : Balance} (hab : Le a b) (hbc : Le b c) : Le a c := by
  apply Natural.le_cancel_right b.negative
  calc
    (a.positive + c.negative) + b.negative = (a.positive + b.negative) + c.negative := by exact_natural
    _ ≤ (b.positive + a.negative) + c.negative := Nat.add_le_add_right hab _
    _ = (b.positive + c.negative) + a.negative := by exact_natural
    _ ≤ (c.positive + b.negative) + a.negative := Nat.add_le_add_right hbc _
    _ = (c.positive + a.negative) + b.negative := by exact_natural

theorem le_antisymm {a b : Balance} (hab : Le a b) (hba : Le b a) : Agree a b :=
  Nat.le_antisymm hab hba

theorem le_total (a b : Balance) : Le a b ∨ Le b a := Nat.le_total _ _

theorem le_congr {a b c d : Balance} (hab : Agree a b) (hcd : Agree c d) :
    Le a c ↔ Le b d :=
  ⟨fun h => le_trans (agree_le (symm hab)) (le_trans h (agree_le hcd)),
   fun h => le_trans (agree_le hab) (le_trans h (agree_le (symm hcd)))⟩

theorem scale_le {a b : Balance} (h : Le a b) (n : Nat) : Le (scale a n) (scale b n) := by
  unfold Le scale
  rw [← Natural.add_mul, ← Natural.add_mul]
  exact Nat.mul_le_mul_right n h

theorem scale_le_reflect {a b : Balance} {n : Nat} (hn : 0 < n)
    (h : Le (scale a n) (scale b n)) : Le a b := by
  unfold Le scale at h
  rw [← Natural.add_mul, ← Natural.add_mul,
    Nat.mul_comm (a.positive + b.negative) n,
    Nat.mul_comm (b.positive + a.negative) n] at h
  exact Nat.le_of_mul_le_mul_left h hn

theorem add_le_left {a b : Balance} (h : Le a b) (c : Balance) : Le (add a c) (add b c) := by
  unfold Le add
  calc
    (a.positive + c.positive) + (b.negative + c.negative) =
        (a.positive + b.negative) + (c.positive + c.negative) := by exact_natural
    _ ≤ (b.positive + a.negative) + (c.positive + c.negative) := Nat.add_le_add_right h _
    _ = (b.positive + c.positive) + (a.negative + c.negative) := by exact_natural

end Balance

namespace Fraction

def Le (a b : Fraction) : Prop :=
  Balance.Le (a.numerator.scale b.denominator) (b.numerator.scale a.denominator)

instance (a b : Fraction) : Decidable (Le a b) := inferInstanceAs (Decidable (Balance.Le _ _))

theorem le_refl (a : Fraction) : Le a a := Nat.le_refl _
theorem agree_le {a b : Fraction} (h : Agree a b) : Le a b := Balance.agree_le h
theorem le_antisymm {a b : Fraction} (hab : Le a b) (hba : Le b a) : Agree a b :=
  Nat.le_antisymm hab hba
theorem le_total (a b : Fraction) : Le a b ∨ Le b a := Nat.le_total _ _

theorem le_trans {a b c : Fraction} (hab : Le a b) (hbc : Le b c) : Le a c := by
  have first := Balance.scale_le hab c.denominator
  have second := Balance.scale_le hbc a.denominator
  have midpoint : (b.numerator.scale a.denominator).scale c.denominator =
      (b.numerator.scale c.denominator).scale a.denominator := by
    unfold Balance.scale
    apply Balance.ext <;> exact_natural
  rw [midpoint] at first
  have combined := Balance.le_trans first second
  have start : (a.numerator.scale b.denominator).scale c.denominator =
      (a.numerator.scale c.denominator).scale b.denominator := by
    unfold Balance.scale
    apply Balance.ext <;> exact_natural
  have finish : (c.numerator.scale b.denominator).scale a.denominator =
      (c.numerator.scale a.denominator).scale b.denominator := by
    unfold Balance.scale
    apply Balance.ext <;> exact_natural
  rw [start, finish] at combined
  exact Balance.scale_le_reflect b.positive combined

theorem le_congr {a b c d : Fraction} (hab : Agree a b) (hcd : Agree c d) :
    Le a c ↔ Le b d :=
  ⟨fun h => le_trans (agree_le (symm hab)) (le_trans h (agree_le hcd)),
   fun h => le_trans (agree_le hab) (le_trans h (agree_le (symm hcd)))⟩

theorem neg_le_neg {a b : Fraction} (h : Le a b) : Le (neg b) (neg a) := by
  unfold Le neg Balance.Le Balance.scale Balance.neg
  calc
    b.numerator.negative * a.denominator + a.numerator.positive * b.denominator =
        a.numerator.positive * b.denominator + b.numerator.negative * a.denominator := Nat.add_comm ..
    _ ≤ b.numerator.positive * a.denominator + a.numerator.negative * b.denominator := h
    _ = a.numerator.negative * b.denominator + b.numerator.positive * a.denominator := Nat.add_comm ..

theorem add_le_left {a b : Fraction} (h : Le a b) (c : Fraction) : Le (add a c) (add b c) := by
  unfold Le Balance.Le Balance.scale at h
  have scaled := Nat.mul_le_mul_right (c.denominator * c.denominator) h
  unfold Le add Balance.Le Balance.scale Balance.add
  calc
    _ = (a.numerator.positive * b.denominator + b.numerator.negative * a.denominator) *
          (c.denominator * c.denominator) +
        (c.numerator.positive + c.numerator.negative) *
          (a.denominator * b.denominator * c.denominator) := by exact_natural
    _ ≤ (b.numerator.positive * a.denominator + a.numerator.negative * b.denominator) *
          (c.denominator * c.denominator) +
        (c.numerator.positive + c.numerator.negative) *
          (a.denominator * b.denominator * c.denominator) := Nat.add_le_add_right scaled _
    _ = _ := by exact_natural

theorem zero_le_iff (a : Fraction) : Le zero a ↔ a.numerator.negative ≤ a.numerator.positive := by
  change (0 * a.denominator + a.numerator.negative * 1 ≤
    a.numerator.positive * 1 + 0 * a.denominator) ↔ _
  have left : 0 * a.denominator + a.numerator.negative * 1 = a.numerator.negative := by
    rw [Nat.zero_mul, Nat.zero_add, Nat.mul_one]
  have right : a.numerator.positive * 1 + 0 * a.denominator = a.numerator.positive := by
    rw [Nat.zero_mul, Nat.add_zero, Nat.mul_one]
  rw [left, right]

theorem zero_le_mul {a b : Fraction} (ha : Le zero a) (hb : Le zero b) : Le zero (mul a b) := by
  apply (zero_le_iff _).mpr
  have first := (zero_le_iff a).mp ha
  have second := (zero_le_iff b).mp hb
  have ea := Natural.sub_add_of_le first
  have eb := Natural.sub_add_of_le second
  change a.numerator.positive * b.numerator.negative + a.numerator.negative * b.numerator.positive ≤
    a.numerator.positive * b.numerator.positive + a.numerator.negative * b.numerator.negative
  conv => lhs; rw [← ea, ← eb]
  conv => rhs; rw [← ea, ← eb]
  calc
    _ = a.numerator.negative * (b.numerator.positive - b.numerator.negative) +
        (a.numerator.positive - a.numerator.negative) * b.numerator.negative +
        (a.numerator.negative * b.numerator.negative + a.numerator.negative * b.numerator.negative) := by exact_natural
    _ ≤ _ + (a.numerator.positive - a.numerator.negative) *
        (b.numerator.positive - b.numerator.negative) := Nat.le_add_right ..
    _ = _ := by exact_natural

theorem magnitude_upper (a : Fraction) : Le a (nat (a.numerator.positive + a.numerator.negative)) := by
  change a.numerator.positive * 1 + 0 * a.denominator ≤
    (a.numerator.positive + a.numerator.negative) * a.denominator + a.numerator.negative * 1
  rw [Nat.mul_one, Nat.zero_mul, Nat.add_zero, Nat.mul_one]
  have denominatorBound := Nat.mul_le_mul_left (a.numerator.positive + a.numerator.negative) a.positive
  rw [Nat.mul_one] at denominatorBound
  exact Nat.le_trans (Nat.le_add_right ..)
    (Nat.le_trans denominatorBound (Nat.le_add_right ..))

end Fraction
end RelationalPerimeter.Relativity.Arithmetic

namespace RelationalPerimeter.Relativity.Rational
open Arithmetic

def Le (a b : Rational) : Prop := Fraction.Le a.representation b.representation
instance (a b : Rational) : Decidable (Le a b) := inferInstanceAs (Decidable (Fraction.Le _ _))

theorem le_refl (a : Rational) : Le a a := Fraction.le_refl _
theorem le_trans {a b c : Rational} (hab : Le a b) (hbc : Le b c) : Le a c := Fraction.le_trans hab hbc
theorem le_antisymm {a b : Rational} (hab : Le a b) (hba : Le b a) : a = b :=
  equal_of_agree (Fraction.le_antisymm hab hba)
theorem le_total (a b : Rational) : Le a b ∨ Le b a := Fraction.le_total _ _

theorem normalize_le_iff (a b : Fraction) : Le (normalize a) (normalize b) ↔ Fraction.Le a b :=
  Fraction.le_congr (normalize_agrees a) (normalize_agrees b)

theorem add_le_left {a b : Rational} (h : Le a b) (c : Rational) : Le (add a c) (add b c) :=
  (normalize_le_iff _ _).mpr (Fraction.add_le_left h c.representation)

theorem add_le {a b c d : Rational} (hab : Le a b) (hcd : Le c d) : Le (add a c) (add b d) := by
  have first := add_le_left hab c
  have second := add_le_left hcd b
  rw [add_comm c b, add_comm d b] at second
  exact le_trans first second

theorem neg_le_neg {a b : Rational} (h : Le a b) : Le (neg b) (neg a) :=
  (normalize_le_iff _ _).mpr (Fraction.neg_le_neg h)

theorem add_le_cancel_right {a b c : Rational} (h : Le (add a c) (add b c)) : Le a b := by
  have moved := add_le_left h (neg c)
  rw [add_assoc, add_assoc, add_neg, add_zero, add_zero] at moved
  exact moved

theorem zero_le_sub_iff (a b : Rational) : Le zero (sub b a) ↔ Le a b := by
  constructor
  · intro h
    have moved := add_le_left h a
    rw [zero_add, sub, add_assoc, neg_add_cancel, add_zero] at moved
    exact moved
  · intro h
    have moved := add_le_left h (neg a)
    rw [add_neg] at moved
    exact moved

theorem zero_le_mul {a b : Rational} (ha : Le zero a) (hb : Le zero b) : Le zero (mul a b) := by
  have first := (Fraction.le_congr (normalize_agrees Fraction.zero) (Fraction.refl a.representation)).mp ha
  have second := (Fraction.le_congr (normalize_agrees Fraction.zero) (Fraction.refl b.representation)).mp hb
  exact (normalize_le_iff _ _).mpr (Fraction.zero_le_mul first second)

theorem mul_le_right {a b c : Rational} (hab : Le a b) (hc : Le zero c) : Le (mul a c) (mul b c) := by
  have nonnegative := zero_le_mul ((zero_le_sub_iff a b).mpr hab) hc
  rw [sub_mul] at nonnegative
  exact (zero_le_sub_iff _ _).mp nonnegative

theorem mul_le_left {a b c : Rational} (hab : Le a b) (hc : Le zero c) : Le (mul c a) (mul c b) := by
  have h := mul_le_right hab hc
  rw [mul_comm a c, mul_comm b c] at h
  exact h

theorem nat_nonnegative (n : Nat) : Le zero (ofNat n) :=
  (normalize_le_iff _ _).mpr ((Fraction.zero_le_iff _).mpr (Nat.zero_le n))

theorem nat_le {n m : Nat} (h : n ≤ m) : Le (ofNat n) (ofNat m) := by
  apply (normalize_le_iff _ _).mpr
  change n * 1 + 0 ≤ m * 1 + 0
  rw [Nat.mul_one, Nat.mul_one, Nat.add_zero, Nat.add_zero]
  exact h

def magnitudeBound (a : Rational) : Nat :=
  a.representation.numerator.positive + a.representation.numerator.negative

theorem magnitude_bounds (a : Rational) :
    Le a (ofNat (magnitudeBound a)) ∧ Le (neg a) (ofNat (magnitudeBound a)) := by
  constructor
  · exact (Fraction.le_congr (Fraction.refl _) (normalize_agrees _)).mpr (Fraction.magnitude_upper _)
  · apply (normalize_le_iff _ _).mpr
    have h := Fraction.magnitude_upper (Fraction.neg a.representation)
    change Fraction.Le (Fraction.neg a.representation)
      (Fraction.nat (a.representation.numerator.negative + a.representation.numerator.positive)) at h
    rw [Nat.add_comm] at h
    exact h

end RelationalPerimeter.Relativity.Rational

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.Le
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.le_trans
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.le_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.scale_le_reflect
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.Le
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.le_trans
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.le_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.neg_le_neg
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add_le_left
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.zero_le_iff
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.zero_le_mul
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.magnitude_upper
#print axioms RelationalPerimeter.Relativity.Rational.Le
#print axioms RelationalPerimeter.Relativity.Rational.le_trans
#print axioms RelationalPerimeter.Relativity.Rational.le_antisymm
#print axioms RelationalPerimeter.Relativity.Rational.le_total
#print axioms RelationalPerimeter.Relativity.Rational.normalize_le_iff
#print axioms RelationalPerimeter.Relativity.Rational.add_le_left
#print axioms RelationalPerimeter.Relativity.Rational.add_le
#print axioms RelationalPerimeter.Relativity.Rational.neg_le_neg
#print axioms RelationalPerimeter.Relativity.Rational.add_le_cancel_right
#print axioms RelationalPerimeter.Relativity.Rational.zero_le_sub_iff
#print axioms RelationalPerimeter.Relativity.Rational.zero_le_mul
#print axioms RelationalPerimeter.Relativity.Rational.mul_le_right
#print axioms RelationalPerimeter.Relativity.Rational.mul_le_left
#print axioms RelationalPerimeter.Relativity.Rational.nat_nonnegative
#print axioms RelationalPerimeter.Relativity.Rational.nat_le
#print axioms RelationalPerimeter.Relativity.Rational.magnitudeBound
#print axioms RelationalPerimeter.Relativity.Rational.magnitude_bounds
/- AXIOM_AUDIT_END -/
