import RelationalPerimeter.Relativity.Arithmetic.FractionRepresentation
import RelationalPerimeter.Relativity.Arithmetic.PairEnumeration

/-!
Canonical, executable rational data, constructed by a finite search whose
coverage is proved. Numerical equality reflects cross-multiplication, so it
is not an assumed quotient. This first backend prioritizes constructive
correctness: the enumeration cost is not claimed to be efficient, and is
not a physical or computational complexity result.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity
open Arithmetic

namespace RationalRepresentation

def decode (index : Nat) : Fraction :=
  let (p, rest) := Enumeration.pair index
  let (n, d) := Enumeration.pair rest
  Fraction.ofParts p n d

def encode (a : Fraction) : Nat :=
  Enumeration.code a.numerator.positive
    (Enumeration.code a.numerator.negative (a.denominator - 1))

theorem decode_encode (a : Fraction) : decode (encode a) = a := by
  unfold decode encode
  rw [Enumeration.pair_code]
  dsimp only
  rw [Enumeration.pair_code]
  dsimp only
  cases a with
  | mk numerator denominator positive =>
    cases denominator with
    | zero => exact False.elim (Nat.not_lt_zero 0 positive)
    | succ d =>
      cases numerator
      rw [Nat.succ_sub_succ, Nat.sub_zero]
      rfl

structure First (start : Nat) (target : Fraction) where
  index : Nat
  above : start ≤ index
  agrees : Fraction.Agree (decode index) target
  least : ∀ i, start ≤ i → i < index → Fraction.Agree (decode i) target → False

/-- Forward, short-circuiting search. All failed candidates supply the
negative evidence needed to establish the first accepted representative. -/
def search (target : Fraction) : (fuel start : Nat) →
    PSum (First start target)
      (∀ i, start ≤ i → i < start + fuel → Fraction.Agree (decode i) target → False)
  | 0, start => .inr fun i above below _ =>
    Nat.not_lt_of_ge above below
  | fuel + 1, start =>
    if h : Fraction.Agree (decode start) target then
      .inl ⟨start, Nat.le_refl start, h, fun i above below =>
        False.elim (Nat.not_lt_of_ge above below)⟩
    else
      match search target fuel (start + 1) with
      | .inl found => .inl
        ⟨found.index, Nat.le_trans (Nat.le_succ start) found.above, found.agrees,
         fun i above below agreement =>
           match Nat.lt_or_eq_of_le above with
           | .inl strictlyAbove => found.least i strictlyAbove below agreement
           | .inr same => h (same ▸ agreement)⟩
      | .inr absent => .inr fun i above below agreement =>
        match Nat.lt_or_eq_of_le above with
        | .inl strictlyAbove =>
          absent i strictlyAbove
            (by rw [Nat.succ_add, ← Nat.add_succ]; exact below) agreement
        | .inr same => h (same ▸ agreement)

def first (target : Fraction) : First 0 target :=
  match search target (encode target + 1) 0 with
  | .inl found => found
  | .inr absent => False.elim
    (absent (encode target) (Nat.zero_le _)
      (by rw [Nat.zero_add]; exact Nat.lt_succ_self _)
      (by rw [decode_encode]; exact Fraction.refl target))

end RationalRepresentation

/-- One index, with an intrinsic proof that earlier encodings do not denote
the same rational value. Proofs carry no additional numerical data. -/
structure Rational where
  index : Nat
  least : ∀ i, i < index →
    Fraction.Agree (RationalRepresentation.decode i) (RationalRepresentation.decode index) → False

namespace Rational

def representation (a : Rational) : Fraction := RationalRepresentation.decode a.index

theorem ext {a b : Rational} (h : a.index = b.index) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance (a b : Rational) : Decidable (a = b) :=
  if h : a.index = b.index then .isTrue (ext h)
  else .isFalse fun same => h (congrArg Rational.index same)

def normalize (target : Fraction) : Rational :=
  let found := RationalRepresentation.first target
  ⟨found.index, fun i below agreement =>
    found.least i (Nat.zero_le _) below (Fraction.trans agreement found.agrees)⟩

theorem normalize_agrees (target : Fraction) : Fraction.Agree (normalize target).representation target :=
  (RationalRepresentation.first target).agrees

theorem equal_of_agree {a b : Rational} (h : Fraction.Agree a.representation b.representation) : a = b := by
  apply ext
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro less
    exact a.least b.index less (Fraction.symm h)
  · apply Nat.le_of_not_gt
    intro less
    exact b.least a.index less h

theorem equal_iff_agree (a b : Rational) : a = b ↔ Fraction.Agree a.representation b.representation :=
  ⟨fun h => h ▸ Fraction.refl a.representation, equal_of_agree⟩

theorem normalize_congr {a b : Fraction} (h : Fraction.Agree a b) : normalize a = normalize b :=
  equal_of_agree (Fraction.trans (normalize_agrees a)
    (Fraction.trans h (Fraction.symm (normalize_agrees b))))

theorem normalize_representation (a : Rational) : normalize a.representation = a :=
  equal_of_agree (normalize_agrees a.representation)

def zero : Rational := normalize Fraction.zero
def one : Rational := normalize Fraction.one
def ofNat (n : Nat) : Rational := normalize (Fraction.nat n)
def ofParts (positive negative denominatorMinusOne : Nat) : Rational :=
  normalize (Fraction.ofParts positive negative denominatorMinusOne)
def add (a b : Rational) : Rational := normalize (Fraction.add a.representation b.representation)
def neg (a : Rational) : Rational := normalize (Fraction.neg a.representation)
def sub (a b : Rational) : Rational := add a (neg b)
def mul (a b : Rational) : Rational := normalize (Fraction.mul a.representation b.representation)

theorem add_comm (a b : Rational) : add a b = add b a := normalize_congr (Fraction.add_comm ..)
theorem mul_comm (a b : Rational) : mul a b = mul b a := normalize_congr (Fraction.mul_comm ..)

theorem add_assoc (a b c : Rational) : add (add a b) c = add a (add b c) :=
  normalize_congr (Fraction.trans
    (Fraction.add_congr (normalize_agrees _) (Fraction.refl _))
    (Fraction.trans (Fraction.add_assoc ..)
      (Fraction.symm (Fraction.add_congr (Fraction.refl _) (normalize_agrees _)))))

theorem mul_assoc (a b c : Rational) : mul (mul a b) c = mul a (mul b c) :=
  normalize_congr (Fraction.trans
    (Fraction.mul_congr (normalize_agrees _) (Fraction.refl _))
    (Fraction.trans (Fraction.mul_assoc ..)
      (Fraction.symm (Fraction.mul_congr (Fraction.refl _) (normalize_agrees _)))))

theorem mul_add (a b c : Rational) : mul a (add b c) = add (mul a b) (mul a c) :=
  normalize_congr (Fraction.trans
    (Fraction.mul_congr (Fraction.refl _) (normalize_agrees _))
    (Fraction.trans (Fraction.mul_add ..)
      (Fraction.symm (Fraction.add_congr (normalize_agrees _) (normalize_agrees _)))))

theorem add_zero (a : Rational) : add a zero = a := by
  have agreement := Fraction.trans (Fraction.add_congr (Fraction.refl a.representation)
    (normalize_agrees Fraction.zero)) (Fraction.add_zero a.representation)
  exact (normalize_congr agreement).trans (normalize_representation a)

theorem mul_one (a : Rational) : mul a one = a := by
  have agreement := Fraction.trans (Fraction.mul_congr (Fraction.refl a.representation)
    (normalize_agrees Fraction.one)) (Fraction.mul_one a.representation)
  exact (normalize_congr agreement).trans (normalize_representation a)

theorem mul_zero (a : Rational) : mul a zero = zero :=
  normalize_congr (Fraction.trans (Fraction.mul_congr (Fraction.refl _) (normalize_agrees _))
    (Fraction.mul_zero _))

theorem add_neg (a : Rational) : add a (neg a) = zero :=
  normalize_congr (Fraction.trans (Fraction.add_congr (Fraction.refl _) (normalize_agrees _))
    (Fraction.add_neg _))

theorem neg_neg (a : Rational) : neg (neg a) = a := by
  have agreement := Fraction.neg_congr (normalize_agrees (Fraction.neg a.representation))
  rw [Fraction.neg_neg] at agreement
  exact (normalize_congr agreement).trans (normalize_representation a)

theorem neg_zero : neg zero = zero :=
  normalize_congr (Fraction.trans (Fraction.neg_congr (normalize_agrees Fraction.zero)) (Fraction.refl Fraction.zero))

theorem zero_add (a : Rational) : add zero a = a := (add_comm _ _).trans (add_zero a)
theorem one_mul (a : Rational) : mul one a = a := (mul_comm _ _).trans (mul_one a)
theorem zero_mul (a : Rational) : mul zero a = zero := (mul_comm _ _).trans (mul_zero a)
theorem neg_add_cancel (a : Rational) : add (neg a) a = zero := (add_comm _ _).trans (add_neg a)

theorem add_left_comm (a b c : Rational) : add a (add b c) = add b (add a c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem neg_add (a b : Rational) : neg (add a b) = add (neg a) (neg b) :=
  normalize_congr (Fraction.trans
    (Fraction.neg_congr (normalize_agrees _))
    (Fraction.trans (Fraction.neg_add ..)
      (Fraction.symm (Fraction.add_congr (normalize_agrees _) (normalize_agrees _)))))

theorem sub_self (a : Rational) : sub a a = zero := add_neg a

theorem sub_zero (a : Rational) : sub a zero = a := by
  unfold sub
  rw [neg_zero, add_zero]

theorem zero_sub (a : Rational) : sub zero a = neg a := zero_add _

theorem sub_representation_agrees (a b : Rational) :
    Fraction.Agree (sub a b).representation (Fraction.sub a.representation b.representation) :=
  Fraction.trans (normalize_agrees _) (Fraction.add_congr (Fraction.refl _) (normalize_agrees _))

theorem sub_compose (a b c : Rational) : add (sub a b) (sub b c) = sub a c := by
  unfold sub
  rw [add_assoc, ← add_assoc (neg b) b (neg c), neg_add_cancel, zero_add]

theorem neg_mul (a b : Rational) : mul (neg a) b = neg (mul a b) :=
  normalize_congr (Fraction.trans
    (Fraction.mul_congr (normalize_agrees _) (Fraction.refl _))
    (Fraction.trans (Fraction.neg_mul ..)
      (Fraction.symm (Fraction.neg_congr (normalize_agrees _)))))

theorem mul_neg (a b : Rational) : mul a (neg b) = neg (mul a b) := by
  rw [mul_comm a (neg b), neg_mul, mul_comm b a]

theorem mul_sub (a b c : Rational) : mul a (sub b c) = sub (mul a b) (mul a c) := by
  unfold sub
  rw [mul_add, mul_neg]

theorem add_mul (a b c : Rational) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm (add a b) c, mul_add, mul_comm c a, mul_comm c b]

theorem sub_mul (a b c : Rational) : mul (sub a b) c = sub (mul a c) (mul b c) := by
  rw [mul_comm (sub a b) c, mul_sub, mul_comm c a, mul_comm c b]

theorem neg_sub (a b : Rational) : neg (sub a b) = sub b a := by
  unfold sub
  rw [neg_add, neg_neg, add_comm]

theorem nat_add (a b : Nat) : add (ofNat a) (ofNat b) = ofNat (a + b) := by
  apply normalize_congr
  apply Fraction.trans (Fraction.add_congr (normalize_agrees _) (normalize_agrees _))
  unfold Fraction.Agree Fraction.add Fraction.nat Balance.Agree Balance.scale Balance.add Balance.nat
  exact_natural

theorem nat_mul (a b : Nat) : mul (ofNat a) (ofNat b) = ofNat (a * b) := by
  apply normalize_congr
  apply Fraction.trans (Fraction.mul_congr (normalize_agrees _) (normalize_agrees _))
  change (a * b + 0 * 0) * 1 + 0 * (1 * 1) = (a * b) * (1 * 1) + (a * 0 + 0 * b) * 1
  exact_natural

def inverseNatSucc (n : Nat) : Rational := ofParts 1 0 n

theorem nat_succ_inverse (n : Nat) : mul (ofNat (n + 1)) (inverseNatSucc n) = one := by
  apply normalize_congr
  apply Fraction.trans (Fraction.mul_congr (normalize_agrees _) (normalize_agrees _))
  unfold Fraction.Agree Fraction.mul Fraction.nat Fraction.ofParts Fraction.one
    Balance.Agree Balance.mul Balance.nat Balance.scale Balance.one
  exact_natural

theorem one_ne_zero : one ≠ zero := by
  intro same
  have representatives := (equal_iff_agree one zero).mp same
  have values := Fraction.trans (Fraction.symm (normalize_agrees Fraction.one))
    (Fraction.trans representatives (normalize_agrees Fraction.zero))
  exact Nat.noConfusion values

end Rational
end RelationalPerimeter.Relativity

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.RationalRepresentation.decode
#print axioms RelationalPerimeter.Relativity.RationalRepresentation.decode_encode
#print axioms RelationalPerimeter.Relativity.RationalRepresentation.search
#print axioms RelationalPerimeter.Relativity.RationalRepresentation.first
#print axioms RelationalPerimeter.Relativity.Rational
#print axioms RelationalPerimeter.Relativity.Rational.ext
#print axioms RelationalPerimeter.Relativity.Rational.normalize
#print axioms RelationalPerimeter.Relativity.Rational.normalize_agrees
#print axioms RelationalPerimeter.Relativity.Rational.equal_of_agree
#print axioms RelationalPerimeter.Relativity.Rational.equal_iff_agree
#print axioms RelationalPerimeter.Relativity.Rational.normalize_congr
#print axioms RelationalPerimeter.Relativity.Rational.normalize_representation
#print axioms RelationalPerimeter.Relativity.Rational.add
#print axioms RelationalPerimeter.Relativity.Rational.neg
#print axioms RelationalPerimeter.Relativity.Rational.mul
#print axioms RelationalPerimeter.Relativity.Rational.add_comm
#print axioms RelationalPerimeter.Relativity.Rational.mul_comm
#print axioms RelationalPerimeter.Relativity.Rational.add_assoc
#print axioms RelationalPerimeter.Relativity.Rational.mul_assoc
#print axioms RelationalPerimeter.Relativity.Rational.mul_add
#print axioms RelationalPerimeter.Relativity.Rational.add_zero
#print axioms RelationalPerimeter.Relativity.Rational.mul_one
#print axioms RelationalPerimeter.Relativity.Rational.mul_zero
#print axioms RelationalPerimeter.Relativity.Rational.add_neg
#print axioms RelationalPerimeter.Relativity.Rational.neg_neg
#print axioms RelationalPerimeter.Relativity.Rational.neg_zero
#print axioms RelationalPerimeter.Relativity.Rational.zero_add
#print axioms RelationalPerimeter.Relativity.Rational.one_mul
#print axioms RelationalPerimeter.Relativity.Rational.zero_mul
#print axioms RelationalPerimeter.Relativity.Rational.neg_add_cancel
#print axioms RelationalPerimeter.Relativity.Rational.add_left_comm
#print axioms RelationalPerimeter.Relativity.Rational.neg_add
#print axioms RelationalPerimeter.Relativity.Rational.sub_self
#print axioms RelationalPerimeter.Relativity.Rational.sub_zero
#print axioms RelationalPerimeter.Relativity.Rational.zero_sub
#print axioms RelationalPerimeter.Relativity.Rational.sub_representation_agrees
#print axioms RelationalPerimeter.Relativity.Rational.sub_compose
#print axioms RelationalPerimeter.Relativity.Rational.neg_mul
#print axioms RelationalPerimeter.Relativity.Rational.mul_neg
#print axioms RelationalPerimeter.Relativity.Rational.mul_sub
#print axioms RelationalPerimeter.Relativity.Rational.add_mul
#print axioms RelationalPerimeter.Relativity.Rational.sub_mul
#print axioms RelationalPerimeter.Relativity.Rational.neg_sub
#print axioms RelationalPerimeter.Relativity.Rational.nat_add
#print axioms RelationalPerimeter.Relativity.Rational.nat_mul
#print axioms RelationalPerimeter.Relativity.Rational.inverseNatSucc
#print axioms RelationalPerimeter.Relativity.Rational.nat_succ_inverse
#print axioms RelationalPerimeter.Relativity.Rational.one_ne_zero
/- AXIOM_AUDIT_END -/
