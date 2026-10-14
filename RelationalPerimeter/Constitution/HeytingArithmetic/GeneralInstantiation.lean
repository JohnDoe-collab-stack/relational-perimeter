import RelationalPerimeter.Constitution.HeytingArithmetic.Substitution

/-!
# General capture-avoiding term instantiation

Numeral substitution is sufficient for the semantic Tarski diagonal, but a
proof calculus needs the genuine first-order operation that removes the newest
free variable and replaces it by an arbitrary term.  This file defines that
operation on raw syntax and states its exact De Bruijn and semantic laws.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Raise every free variable of a term through `depth` new binders. -/
def RawTerm.raise : RawTerm -> Nat -> RawTerm
  | term, 0 => term
  | term, Nat.succ depth => (term.raise depth).rename Nat.succ

/-- Substitute the newest free variable and lower every later variable. -/
def singleTermSubstitution (replacement : RawTerm) : Substitution
  | 0 => replacement
  | Nat.succ index => RawTerm.bvar index

/-- The single-term substitution lifted through an explicit binder depth. -/
def termSubstitutionAtDepth (replacement : RawTerm) : Nat -> Substitution
  | 0 => singleTermSubstitution replacement
  | Nat.succ depth => liftSubstitution (termSubstitutionAtDepth replacement depth)

/-- Instantiate the newest free variable in a raw term. -/
def RawTerm.instantiateTerm
    (body replacement : RawTerm) : RawTerm :=
  body.substitute (singleTermSubstitution replacement)

/-- Instantiate the newest free variable in a raw formula. -/
def RawFormula.instantiateTerm
    (body : RawFormula)
    (replacement : RawTerm) : RawFormula :=
  body.substitute (singleTermSubstitution replacement)

/-- Lifting preserves variables strictly below the current binder depth. -/
theorem termSubstitutionAtDepth_of_lt
    (replacement : RawTerm)
    (depth index : Nat)
    (bounded : index < depth) :
    termSubstitutionAtDepth replacement depth index =
      RawTerm.bvar index := by
  induction depth generalizing index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            (termSubstitutionAtDepth replacement depth index).rename Nat.succ =
              RawTerm.bvar (Nat.succ index)
          rw [inductionHypothesis index (Nat.lt_of_succ_lt_succ bounded)]
          rfl

/-- At the removed variable, lifting inserts the equally raised replacement. -/
theorem termSubstitutionAtDepth_at
    (replacement : RawTerm)
    (depth : Nat) :
    termSubstitutionAtDepth replacement depth depth =
      replacement.raise depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        (termSubstitutionAtDepth replacement depth depth).rename Nat.succ =
          (replacement.raise depth).rename Nat.succ
      rw [inductionHypothesis]

/-- Variables after the removed variable are lowered by one. -/
theorem termSubstitutionAtDepth_after
    (replacement : RawTerm)
    (depth offset : Nat) :
    termSubstitutionAtDepth replacement depth
        (depth + Nat.succ offset) =
      RawTerm.bvar (depth + offset) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [Nat.succ_add]
      change
        (termSubstitutionAtDepth replacement depth
          (depth + Nat.succ offset)).rename Nat.succ =
          RawTerm.bvar (Nat.succ (depth + offset))
      rw [inductionHypothesis]
      rfl

/-- Raising a scoped term moves it through the requested number of binders. -/
theorem RawTerm.raise_wellScoped
    (term : RawTerm)
    (source depth : Nat)
    (isScoped : term.WellScoped source) :
    (term.raise depth).WellScoped (depth + source) := by
  induction depth with
  | zero => simpa only [RawTerm.raise, Nat.zero_add] using isScoped
  | succ depth inductionHypothesis =>
      rw [Nat.succ_add]
      exact (term.raise depth).wellScoped_rename
        inductionHypothesis
        Nat.succ
        (fun _index bounded => Nat.succ_lt_succ bounded)

/-- Single-term instantiation removes exactly one variable from term scope. -/
theorem RawTerm.instantiateTerm_wellScoped
    (body replacement : RawTerm)
    (bound : Nat)
    (bodyScoped : body.WellScoped (Nat.succ bound))
    (replacementScoped : replacement.WellScoped bound) :
    (body.instantiateTerm replacement).WellScoped bound := by
  exact body.wellScoped_substitute
    bodyScoped
    (singleTermSubstitution replacement)
    (fun index bounded => by
      cases index with
      | zero => exact replacementScoped
      | succ index => exact Nat.lt_of_succ_lt_succ bounded)

/-- Single-term instantiation removes exactly one variable from formula scope. -/
theorem RawFormula.instantiateTerm_wellScoped
    (body : RawFormula)
    (replacement : RawTerm)
    (bound : Nat)
    (bodyScoped : body.WellScoped (Nat.succ bound))
    (replacementScoped : replacement.WellScoped bound) :
    (body.instantiateTerm replacement).WellScoped bound := by
  exact body.wellScoped_substitute
    bodyScoped
    (singleTermSubstitution replacement)
    (fun index bounded => by
      cases index with
      | zero => exact replacementScoped
      | succ index => exact Nat.lt_of_succ_lt_succ bounded)

/-- Term instantiation has the expected pushed-environment semantics. -/
theorem RawTerm.evaluate_instantiateTerm
    (body replacement : RawTerm)
    (environment : Environment) :
    (body.instantiateTerm replacement).evaluate environment =
      body.evaluate
        (pushEnvironment environment (replacement.evaluate environment)) := by
  rw [RawTerm.instantiateTerm, RawTerm.evaluate_substitute]
  apply body.evaluate_congr
  intro index
  cases index <;> rfl

/-- Formula instantiation has the expected pushed-environment semantics. -/
theorem RawFormula.holds_instantiateTerm
    (body : RawFormula)
    (replacement : RawTerm)
    (environment : Environment) :
    (body.instantiateTerm replacement).Holds environment ↔
      body.Holds
        (pushEnvironment environment (replacement.evaluate environment)) := by
  apply Iff.trans
    (body.holds_substitute
      (singleTermSubstitution replacement)
      environment)
  apply body.holds_congr
  intro index
  cases index <;> rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.instantiateTerm
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.instantiateTerm
#print axioms RelationalPerimeter.HeytingArithmetic.termSubstitutionAtDepth_at
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.instantiateTerm_wellScoped
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.holds_instantiateTerm
/- AXIOM_AUDIT_END -/
