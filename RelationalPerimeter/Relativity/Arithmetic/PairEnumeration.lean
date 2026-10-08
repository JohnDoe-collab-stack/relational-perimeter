import RelationalPerimeter.Relativity.Arithmetic.NaturalLaws

/-!
A constructive enumeration of pairs, used to construct canonical numerical
representatives by finite search. The inverse law is proved, not assumed.
This is a correctness-oriented normalization tool, not a cost bound.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Arithmetic.Enumeration

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n + 1

def code (a b : Nat) : Nat := triangle (a + b) + b

def pair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    match pair n with
    | (0, b) => (b + 1, 0)
    | (a + 1, b) => (a, b + 1)

theorem code_start (n : Nat) : code (n + 1) 0 = code 0 n + 1 := by
  unfold code
  rw [Nat.add_zero, Nat.zero_add]
  rfl

theorem code_next (a b : Nat) : code a (b + 1) = code (a + 1) b + 1 := by
  unfold code
  rw [Nat.add_succ, Nat.succ_add, Nat.add_succ]

theorem diagonal (n : Nat) : ∀ a b, a + b = n → pair (code a b) = (a, b) := by
  induction n with
  | zero =>
    intro a b h
    cases a with
    | zero =>
      rw [Nat.zero_add] at h
      cases h
      rfl
    | succ a =>
      rw [Nat.succ_add] at h
      exact False.elim (Nat.noConfusion h)
  | succ n ih =>
    have start : pair (code (n + 1) 0) = (n + 1, 0) := by
      rw [code_start, pair, ih 0 n (Nat.zero_add n)]
    intro a b h
    induction b generalizing a with
    | zero =>
      rw [Nat.add_zero] at h
      cases h
      exact start
    | succ b ihb =>
      have predecessor : (a + 1) + b = n + 1 := by
        rw [Nat.succ_add, ← Nat.add_succ]
        exact h
      rw [code_next, pair, ihb (a + 1) predecessor]

theorem pair_code (a b : Nat) : pair (code a b) = (a, b) := diagonal (a + b) a b rfl

end RelationalPerimeter.Relativity.Arithmetic.Enumeration

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.triangle
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.code
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.pair
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.code_start
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.code_next
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.diagonal
#print axioms RelationalPerimeter.Relativity.Arithmetic.Enumeration.pair_code
/- AXIOM_AUDIT_END -/
