import RelationalPerimeter.Relativity.Arithmetic.SignedBalance

/-!
Exact, intermediate fraction data with a positive denominator. `Agree` is
cross-multiplication of signed balances, not equality of encodings. This
module proves the representation laws before any canonical encoding or
analytic interpretation is used.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace RelationalPerimeter.Relativity.Arithmetic

structure Fraction where
  numerator : Balance
  denominator : Nat
  positive : 0 < denominator

namespace Fraction

def Agree (a b : Fraction) : Prop :=
  Balance.Agree (a.numerator.scale b.denominator) (b.numerator.scale a.denominator)

instance (a b : Fraction) : Decidable (Agree a b) := inferInstanceAs (Decidable (Balance.Agree _ _))

def zero : Fraction := ⟨Balance.zero, 1, Nat.zero_lt_succ 0⟩
def one : Fraction := ⟨Balance.one, 1, Nat.zero_lt_succ 0⟩
def nat (n : Nat) : Fraction := ⟨Balance.nat n, 1, Nat.zero_lt_succ 0⟩
def ofParts (p n d : Nat) : Fraction := ⟨⟨p, n⟩, d + 1, Nat.zero_lt_succ d⟩

def add (a b : Fraction) : Fraction :=
  ⟨Balance.add (a.numerator.scale b.denominator) (b.numerator.scale a.denominator),
   a.denominator * b.denominator, Nat.mul_pos a.positive b.positive⟩
def neg (a : Fraction) : Fraction := ⟨a.numerator.neg, a.denominator, a.positive⟩
def sub (a b : Fraction) : Fraction := add a (neg b)
def mul (a b : Fraction) : Fraction :=
  ⟨a.numerator.mul b.numerator, a.denominator * b.denominator, Nat.mul_pos a.positive b.positive⟩

theorem refl (a : Fraction) : Agree a a := rfl
theorem symm {a b : Fraction} (h : Agree a b) : Agree b a := h.symm

theorem trans {a b c : Fraction} (hab : Agree a b) (hbc : Agree b c) : Agree a c := by
  have first := Balance.scale_congr hab c.denominator
  have second := Balance.scale_congr hbc a.denominator
  have midpoint : (b.numerator.scale a.denominator).scale c.denominator =
      (b.numerator.scale c.denominator).scale a.denominator := by
    unfold Balance.scale
    apply Balance.ext <;> exact_natural
  rw [midpoint] at first
  have combined := Balance.trans first second
  have start : (a.numerator.scale b.denominator).scale c.denominator =
      (a.numerator.scale c.denominator).scale b.denominator := by
    unfold Balance.scale
    apply Balance.ext <;> exact_natural
  have finish : (c.numerator.scale b.denominator).scale a.denominator =
      (c.numerator.scale a.denominator).scale b.denominator := by
    unfold Balance.scale
    apply Balance.ext <;> exact_natural
  rw [start, finish] at combined
  exact Balance.scale_reflect b.positive combined

theorem add_congr_left {a b : Fraction} (h : Agree a b) (c : Fraction) :
    Agree (add a c) (add b c) := by
  have hs := congrArg (· * (c.denominator * c.denominator)) h
  unfold Agree Balance.Agree Balance.scale at h
  unfold Agree add Balance.Agree Balance.scale Balance.add
  calc
    _ = (a.numerator.positive * b.denominator + b.numerator.negative * a.denominator) *
          (c.denominator * c.denominator) +
        (c.numerator.positive + c.numerator.negative) *
          (a.denominator * b.denominator * c.denominator) := by exact_natural
    _ = (b.numerator.positive * a.denominator + a.numerator.negative * b.denominator) *
          (c.denominator * c.denominator) +
        (c.numerator.positive + c.numerator.negative) *
          (a.denominator * b.denominator * c.denominator) :=
      congrArg (· + (c.numerator.positive + c.numerator.negative) *
        (a.denominator * b.denominator * c.denominator)) hs
    _ = _ := by exact_natural

theorem add_comm (a b : Fraction) : Agree (add a b) (add b a) := by
  unfold Agree add Balance.Agree Balance.scale Balance.add
  exact_natural

theorem add_congr {a b c d : Fraction} (hab : Agree a b) (hcd : Agree c d) :
    Agree (add a c) (add b d) :=
  trans (add_congr_left hab c)
    (trans (add_comm b c) (trans (add_congr_left hcd b) (add_comm d b)))

theorem neg_congr {a b : Fraction} (h : Agree a b) : Agree (neg a) (neg b) := by
  unfold Agree Balance.Agree Balance.scale neg Balance.neg
  calc
    a.numerator.negative * b.denominator + b.numerator.positive * a.denominator =
        b.numerator.positive * a.denominator + a.numerator.negative * b.denominator := Nat.add_comm ..
    _ = a.numerator.positive * b.denominator + b.numerator.negative * a.denominator := h.symm
    _ = b.numerator.negative * a.denominator + a.numerator.positive * b.denominator := Nat.add_comm ..

theorem mul_congr_left {a b : Fraction} (h : Agree a b) (c : Fraction) :
    Agree (mul a c) (mul b c) := by
  unfold Agree Balance.Agree Balance.scale at h
  have hp := congrArg (· * (c.numerator.positive * c.denominator)) h
  have hn := congrArg (· * (c.numerator.negative * c.denominator)) h.symm
  unfold Agree mul Balance.Agree Balance.scale Balance.mul
  calc
    _ = (a.numerator.positive * b.denominator + b.numerator.negative * a.denominator) *
          (c.numerator.positive * c.denominator) +
        (b.numerator.positive * a.denominator + a.numerator.negative * b.denominator) *
          (c.numerator.negative * c.denominator) := by exact_natural
    _ = (b.numerator.positive * a.denominator + a.numerator.negative * b.denominator) *
          (c.numerator.positive * c.denominator) +
        (a.numerator.positive * b.denominator + b.numerator.negative * a.denominator) *
          (c.numerator.negative * c.denominator) := by rw [hp, hn]
    _ = _ := by exact_natural

theorem mul_comm (a b : Fraction) : Agree (mul a b) (mul b a) := by
  unfold Agree mul Balance.Agree Balance.scale Balance.mul
  exact_natural

theorem mul_congr {a b c d : Fraction} (hab : Agree a b) (hcd : Agree c d) :
    Agree (mul a c) (mul b d) :=
  trans (mul_congr_left hab c)
    (trans (mul_comm b c) (trans (mul_congr_left hcd b) (mul_comm d b)))

theorem add_assoc (a b c : Fraction) : Agree (add (add a b) c) (add a (add b c)) := by
  unfold Agree add Balance.Agree Balance.scale Balance.add
  exact_natural

theorem mul_assoc (a b c : Fraction) : Agree (mul (mul a b) c) (mul a (mul b c)) := by
  unfold Agree mul Balance.Agree Balance.scale Balance.mul
  exact_natural

theorem mul_add (a b c : Fraction) : Agree (mul a (add b c)) (add (mul a b) (mul a c)) := by
  unfold Agree add mul Balance.Agree Balance.scale Balance.add Balance.mul
  exact_natural

theorem add_zero (a : Fraction) : Agree (add a zero) a := by
  unfold Agree add zero Balance.Agree Balance.scale Balance.add Balance.zero
  exact_natural

theorem mul_one (a : Fraction) : Agree (mul a one) a := by
  unfold Agree mul one Balance.Agree Balance.scale Balance.mul Balance.one
  exact_natural

theorem mul_zero (a : Fraction) : Agree (mul a zero) zero := by
  unfold Agree mul zero Balance.Agree Balance.scale Balance.mul Balance.zero
  exact_natural

theorem add_neg (a : Fraction) : Agree (add a (neg a)) zero := by
  unfold Agree add neg zero Balance.Agree Balance.scale Balance.add Balance.neg Balance.zero
  exact_natural

theorem neg_neg (a : Fraction) : neg (neg a) = a := rfl

theorem neg_mul (a b : Fraction) : Agree (mul (neg a) b) (neg (mul a b)) := by
  unfold Agree mul neg Balance.Agree Balance.scale Balance.mul Balance.neg
  exact_natural

theorem neg_add (a b : Fraction) : Agree (neg (add a b)) (add (neg a) (neg b)) := by
  unfold Agree add neg Balance.Agree Balance.scale Balance.add Balance.neg
  exact_natural

end Fraction
end RelationalPerimeter.Relativity.Arithmetic

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.Agree
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.neg
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.trans
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.neg_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add_comm
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul_comm
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add_assoc
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul_assoc
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul_add
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add_zero
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul_one
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.mul_zero
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.add_neg
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.neg_neg
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.neg_mul
#print axioms RelationalPerimeter.Relativity.Arithmetic.Fraction.neg_add
/- AXIOM_AUDIT_END -/
