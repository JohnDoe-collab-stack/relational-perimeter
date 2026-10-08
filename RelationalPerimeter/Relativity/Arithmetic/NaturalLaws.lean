import Init

/-!
Constructive arithmetic lemmas used by the numerical interpretation layer.
These lemmas deliberately use induction and equality elimination. They do
not borrow stronger dependency chains from the toolchain's algebra library.
This numerical layer does not constitute physical events.
-/
set_option genInjectivity false

namespace RelationalPerimeter.Relativity.Arithmetic.Natural

theorem add_cancel_left (a : Nat) {b c : Nat} (h : a + b = a + c) : b = c := by
  induction a with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.succ.inj h)

theorem add_cancel_right (c : Nat) {a b : Nat} (h : a + c = b + c) : a = b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact add_cancel_left c h

theorem le_cancel_left (a : Nat) {b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  induction a with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.le_of_succ_le_succ h)

theorem le_cancel_right (c : Nat) {a b : Nat} (h : a + c ≤ b + c) : a ≤ b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact le_cancel_left c h

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
    rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, ih]

theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, Nat.mul_comm a b, mul_assoc]

theorem mul_cancel_left {a b c : Nat} (ha : 0 < a) (h : a * b = a * c) : b = c :=
  Nat.eq_of_mul_eq_mul_left ha h

theorem mul_cancel_right {a b c : Nat} (hc : 0 < c) (h : a * c = b * c) : a = b := by
  rw [Nat.mul_comm a c, Nat.mul_comm b c] at h
  exact mul_cancel_left hc h

theorem sub_add_of_le {a b : Nat} (h : b ≤ a) : a - b + b = a := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    cases a with
    | zero => exact False.elim (Nat.not_succ_le_zero _ h)
    | succ a =>
      have lower := ih (Nat.le_of_succ_le_succ h)
      rw [Nat.succ_sub_succ]
      rw [← Nat.add_assoc, lower]

theorem sub_balance (a b : Nat) : (a - b) + b = (b - a) + a := by
  induction a generalizing b with
  | zero => rw [Nat.zero_sub, Nat.zero_add, Nat.sub_zero, Nat.add_zero]
  | succ a ih =>
    cases b with
    | zero => rw [Nat.zero_sub, Nat.zero_add, Nat.sub_zero, Nat.add_zero]
    | succ b =>
      rw [Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.add_succ, Nat.add_succ, ih b]

theorem positive_product (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  Nat.mul_pos ha hb

def join (a b : Nat) : Nat := if a ≤ b then b else a

theorem le_join_left (a b : Nat) : a ≤ join a b := by
  unfold join
  split
  · assumption
  · exact Nat.le_refl _

theorem le_join_right (a b : Nat) : b ≤ join a b := by
  unfold join
  split
  · exact Nat.le_refl _
  · next h => exact Nat.le_of_lt (Nat.lt_of_not_le h)

end RelationalPerimeter.Relativity.Arithmetic.Natural

/-- Normalize natural-number expressions with equality proofs on the two
terms separately, rather than replacing the proposition by an equivalent one. -/
macro "exact_natural" : tactic => `(tactic| (
  conv => lhs; simp only [RelationalPerimeter.Relativity.Arithmetic.Natural.add_mul,
    Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    RelationalPerimeter.Relativity.Arithmetic.Natural.mul_assoc, Nat.mul_comm,
    RelationalPerimeter.Relativity.Arithmetic.Natural.mul_left_comm,
    Nat.mul_succ, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add]
  all_goals conv => rhs; simp only [RelationalPerimeter.Relativity.Arithmetic.Natural.add_mul,
    Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    RelationalPerimeter.Relativity.Arithmetic.Natural.mul_assoc, Nat.mul_comm,
    RelationalPerimeter.Relativity.Arithmetic.Natural.mul_left_comm,
    Nat.mul_succ, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add]))

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.add_cancel_left
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.add_cancel_right
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.le_cancel_left
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.le_cancel_right
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.add_mul
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.mul_assoc
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.mul_left_comm
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.mul_cancel_left
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.mul_cancel_right
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.sub_add_of_le
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.sub_balance
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.positive_product
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.join
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.le_join_left
#print axioms RelationalPerimeter.Relativity.Arithmetic.Natural.le_join_right
/- AXIOM_AUDIT_END -/
