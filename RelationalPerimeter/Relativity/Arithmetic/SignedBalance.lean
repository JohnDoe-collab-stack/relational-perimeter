import RelationalPerimeter.Relativity.Arithmetic.NaturalLaws

/-!
An intermediate signed representation. The two natural numbers are not
identified as data: `Agree` is the explicit equality of their differences.
Canonical rational data are constructed in the numerical layer above this
representation. No equality of physical occurrences follows from `Agree`.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Arithmetic

local instance : Std.Associative (α := Nat) (· * ·) := ⟨Natural.mul_assoc⟩

structure Balance where
  positive : Nat
  negative : Nat

namespace Balance

theorem ext {a b : Balance} (hp : a.positive = b.positive) (hn : a.negative = b.negative) : a = b := by
  cases a
  cases b
  cases hp
  cases hn
  rfl

def Agree (a b : Balance) : Prop := a.positive + b.negative = b.positive + a.negative

instance (a b : Balance) : Decidable (Agree a b) :=
  inferInstanceAs (Decidable (a.positive + b.negative = b.positive + a.negative))

def zero : Balance := ⟨0, 0⟩
def one : Balance := ⟨1, 0⟩
def nat (n : Nat) : Balance := ⟨n, 0⟩
def add (a b : Balance) : Balance := ⟨a.positive + b.positive, a.negative + b.negative⟩
def neg (a : Balance) : Balance := ⟨a.negative, a.positive⟩
def mul (a b : Balance) : Balance :=
  ⟨a.positive * b.positive + a.negative * b.negative,
   a.positive * b.negative + a.negative * b.positive⟩
def scale (a : Balance) (n : Nat) : Balance := ⟨a.positive * n, a.negative * n⟩

theorem refl (a : Balance) : Agree a a := rfl
theorem symm {a b : Balance} (h : Agree a b) : Agree b a := h.symm

theorem trans {a b c : Balance} (hab : Agree a b) (hbc : Agree b c) : Agree a c := by
  apply Natural.add_cancel_right b.negative
  calc
    (a.positive + c.negative) + b.negative = (a.positive + b.negative) + c.negative := by exact_natural
    _ = (b.positive + a.negative) + c.negative := congrArg (· + c.negative) hab
    _ = (b.positive + c.negative) + a.negative := by exact_natural
    _ = (c.positive + b.negative) + a.negative := congrArg (· + a.negative) hbc
    _ = (c.positive + a.negative) + b.negative := by exact_natural

theorem scale_congr {a b : Balance} (h : Agree a b) (n : Nat) : Agree (scale a n) (scale b n) := by
  unfold Agree scale
  rw [← Natural.add_mul, ← Natural.add_mul]
  exact congrArg (· * n) h

theorem scale_reflect {a b : Balance} {n : Nat} (hn : 0 < n)
    (h : Agree (scale a n) (scale b n)) : Agree a b := by
  unfold Agree scale at h
  rw [← Natural.add_mul, ← Natural.add_mul] at h
  exact Natural.mul_cancel_right hn h

theorem scale_scale (a : Balance) (m n : Nat) : scale (scale a m) n = scale a (m * n) := by
  cases a
  unfold scale
  rw [Natural.mul_assoc, Natural.mul_assoc]

theorem add_congr_left {a b : Balance} (h : Agree a b) (c : Balance) : Agree (add a c) (add b c) := by
  unfold Agree add
  calc
    (a.positive + c.positive) + (b.negative + c.negative) =
        (a.positive + b.negative) + (c.positive + c.negative) := by exact_natural
    _ = (b.positive + a.negative) + (c.positive + c.negative) :=
      congrArg (· + (c.positive + c.negative)) h
    _ = (b.positive + c.positive) + (a.negative + c.negative) := by exact_natural

theorem add_comm (a b : Balance) : add a b = add b a := by
  unfold add
  rw [Nat.add_comm a.positive, Nat.add_comm a.negative]

theorem add_assoc (a b c : Balance) : add (add a b) c = add a (add b c) := by
  unfold add
  rw [Nat.add_assoc, Nat.add_assoc]

theorem add_congr {a b c d : Balance} (hab : Agree a b) (hcd : Agree c d) :
    Agree (add a c) (add b d) := by
  have first := add_congr_left hab c
  have second := add_congr_left hcd b
  rw [add_comm c b, add_comm d b] at second
  exact trans first second

theorem neg_congr {a b : Balance} (h : Agree a b) : Agree (neg a) (neg b) := by
  unfold Agree neg
  rw [Nat.add_comm a.negative, Nat.add_comm b.negative]
  exact h.symm

theorem mul_congr_left {a b : Balance} (h : Agree a b) (c : Balance) :
    Agree (mul a c) (mul b c) := by
  have reverse : a.negative + b.positive = b.negative + a.positive := by
    rw [Nat.add_comm a.negative, Nat.add_comm b.negative]
    exact h.symm
  unfold Agree mul
  calc
    (a.positive * c.positive + a.negative * c.negative) +
        (b.positive * c.negative + b.negative * c.positive) =
        (a.positive + b.negative) * c.positive +
          (a.negative + b.positive) * c.negative := by
      rw [Natural.add_mul, Natural.add_mul]
      exact_natural
    _ = (b.positive + a.negative) * c.positive +
          (b.negative + a.positive) * c.negative := by rw [h, reverse]
    _ = (b.positive * c.positive + b.negative * c.negative) +
        (a.positive * c.negative + a.negative * c.positive) := by
      rw [Natural.add_mul, Natural.add_mul]
      exact_natural

theorem mul_comm (a b : Balance) : mul a b = mul b a := by
  unfold mul
  rw [Nat.mul_comm a.positive b.positive, Nat.mul_comm a.negative b.negative,
    Nat.mul_comm a.positive b.negative, Nat.mul_comm a.negative b.positive,
    Nat.add_comm (b.negative * a.positive)]

theorem mul_congr {a b c d : Balance} (hab : Agree a b) (hcd : Agree c d) :
    Agree (mul a c) (mul b d) := by
  have first := mul_congr_left hab c
  have second := mul_congr_left hcd b
  rw [mul_comm c b, mul_comm d b] at second
  exact trans first second

theorem mul_assoc (a b c : Balance) : mul (mul a b) c = mul a (mul b c) := by
  unfold mul
  rw [Natural.add_mul, Natural.add_mul, Natural.add_mul, Natural.add_mul,
    Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  apply ext <;> exact_natural

theorem mul_add (a b c : Balance) : mul a (add b c) = add (mul a b) (mul a c) := by
  unfold mul add
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  apply ext <;> exact_natural

theorem scale_add (a b : Balance) (n : Nat) : scale (add a b) n = add (scale a n) (scale b n) := by
  unfold scale add
  rw [Natural.add_mul, Natural.add_mul]

theorem scale_mul (a b : Balance) (m n : Nat) :
    mul (scale a m) (scale b n) = scale (mul a b) (m * n) := by
  unfold mul scale
  rw [Natural.add_mul, Natural.add_mul]
  apply ext <;> exact_natural

theorem add_zero (a : Balance) : add a zero = a := by
  cases a
  rfl

theorem mul_one (a : Balance) : mul a one = a := by
  unfold mul one
  rw [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.mul_zero, Nat.mul_one, Nat.zero_add]

theorem mul_zero (a : Balance) : mul a zero = zero := by
  unfold mul zero
  rw [Nat.mul_zero, Nat.mul_zero]

theorem add_neg (a : Balance) : Agree (add a (neg a)) zero := by
  unfold Agree add neg zero
  rw [Nat.add_zero, Nat.zero_add, Nat.add_comm]

end Balance
end RelationalPerimeter.Relativity.Arithmetic

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.Agree
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.trans
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.scale_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.scale_reflect
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.scale_scale
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.add_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.neg_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.mul_congr
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.mul_comm
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.mul_assoc
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.mul_add
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.scale_add
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.scale_mul
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.add_zero
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.mul_one
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.mul_zero
#print axioms RelationalPerimeter.Relativity.Arithmetic.Balance.add_neg
/- AXIOM_AUDIT_END -/
