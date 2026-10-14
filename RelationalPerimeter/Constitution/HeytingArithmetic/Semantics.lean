import RelationalPerimeter.Constitution.HeytingArithmetic.Scoping

/-!
# Standard natural-number semantics

Evaluation is structural and cannot inspect syntax codes.  Environment
independence for sentences is proved pointwise, without function or
proposition extensionality.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- A De Bruijn environment in the standard natural-number structure. -/
abbrev Environment := Nat -> Nat

/-- The canonical environment used to evaluate closed sentences. -/
def emptyEnvironment : Environment := fun _index => 0

/-- Insert the value of a freshly bound variable at index zero. -/
def pushEnvironment
    (environment : Environment)
    (value : Nat) :
    Environment
  | 0 => value
  | Nat.succ index => environment index

/-- Standard evaluation of bare arithmetic terms. -/
def RawTerm.evaluate : RawTerm -> Environment -> Nat
  | RawTerm.bvar index, environment => environment index
  | RawTerm.zero, _environment => 0
  | RawTerm.succ term, environment => Nat.succ (term.evaluate environment)
  | RawTerm.add left right, environment =>
      left.evaluate environment + right.evaluate environment
  | RawTerm.mul left right, environment =>
      left.evaluate environment * right.evaluate environment

/-- Constructive standard-`Nat` semantics of bare formulas. -/
def RawFormula.Holds : RawFormula -> Environment -> Prop
  | RawFormula.falsum, _environment => False
  | RawFormula.equal left right, environment =>
      left.evaluate environment = right.evaluate environment
  | RawFormula.conj left right, environment =>
      left.Holds environment ∧ right.Holds environment
  | RawFormula.disj left right, environment =>
      left.Holds environment ∨ right.Holds environment
  | RawFormula.impl left right, environment =>
      left.Holds environment -> right.Holds environment
  | RawFormula.all body, environment =>
      (value : Nat) -> body.Holds (pushEnvironment environment value)
  | RawFormula.ex body, environment =>
      Exists fun value : Nat => body.Holds (pushEnvironment environment value)

/-- A numeral evaluates to the natural number it denotes. -/
theorem RawTerm.evaluate_numeral
    (value : Nat)
    (environment : Environment) :
    (RawTerm.numeral value).evaluate environment = value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change Nat.succ ((RawTerm.numeral value).evaluate environment) =
        Nat.succ value
      rw [inductionHypothesis]

/-- Pointwise equal environments give equal term evaluations. -/
theorem RawTerm.evaluate_congr
    (term : RawTerm)
    (left right : Environment)
    (agree : (index : Nat) -> left index = right index) :
    term.evaluate left = term.evaluate right := by
  induction term with
  | bvar index => exact agree index
  | zero => rfl
  | succ term inductionHypothesis => exact congrArg Nat.succ inductionHypothesis
  | add first second firstHypothesis secondHypothesis =>
      change
        first.evaluate left + second.evaluate left =
          first.evaluate right + second.evaluate right
      rw [firstHypothesis, secondHypothesis]
  | mul first second firstHypothesis secondHypothesis =>
      change
        first.evaluate left * second.evaluate left =
          first.evaluate right * second.evaluate right
      rw [firstHypothesis, secondHypothesis]

/-- Pointwise agreement on used variables gives equal term evaluations. -/
theorem RawTerm.evaluate_eq_of_scoped_agreement
    {bound : Nat}
    (term : RawTerm)
    (isScoped : term.WellScoped bound)
    (left right : Environment)
    (agree : (index : Nat) -> index < bound -> left index = right index) :
    term.evaluate left = term.evaluate right := by
  induction term with
  | bvar index => exact agree index isScoped
  | zero => rfl
  | succ term inductionHypothesis =>
      exact congrArg Nat.succ (inductionHypothesis isScoped)
  | add leftTerm rightTerm leftHypothesis rightHypothesis =>
      change
        leftTerm.evaluate left + rightTerm.evaluate left =
          leftTerm.evaluate right + rightTerm.evaluate right
      rw [leftHypothesis isScoped.1, rightHypothesis isScoped.2]
  | mul leftTerm rightTerm leftHypothesis rightHypothesis =>
      change
        leftTerm.evaluate left * rightTerm.evaluate left =
          leftTerm.evaluate right * rightTerm.evaluate right
      rw [leftHypothesis isScoped.1, rightHypothesis isScoped.2]

/-- Pointwise agreement on all variables preserves formula semantics. -/
theorem RawFormula.holds_congr
    (formula : RawFormula)
    (left right : Environment)
    (agree : (index : Nat) -> left index = right index) :
    formula.Holds left ↔ formula.Holds right := by
  induction formula generalizing left right with
  | falsum => exact Iff.rfl
  | equal leftTerm rightTerm =>
      change
        leftTerm.evaluate left = rightTerm.evaluate left ↔
          leftTerm.evaluate right = rightTerm.evaluate right
      rw [leftTerm.evaluate_congr left right agree]
      rw [rightTerm.evaluate_congr left right agree]
  | conj leftFormula rightFormula leftHypothesis rightHypothesis =>
      exact and_congr
        (leftHypothesis left right agree)
        (rightHypothesis left right agree)
  | disj leftFormula rightFormula leftHypothesis rightHypothesis =>
      exact or_congr
        (leftHypothesis left right agree)
        (rightHypothesis left right agree)
  | impl leftFormula rightFormula leftHypothesis rightHypothesis =>
      constructor
      · intro implication leftHolds
        exact (rightHypothesis left right agree).mp
          (implication ((leftHypothesis left right agree).mpr leftHolds))
      · intro implication leftHolds
        exact (rightHypothesis left right agree).mpr
          (implication ((leftHypothesis left right agree).mp leftHolds))
  | all body inductionHypothesis =>
      constructor
      · intro universal value
        apply (inductionHypothesis
          (pushEnvironment left value)
          (pushEnvironment right value)
          ?_).mp
        · exact universal value
        · intro index
          cases index with
          | zero => rfl
          | succ index => exact agree index
      · intro universal value
        apply (inductionHypothesis
          (pushEnvironment left value)
          (pushEnvironment right value)
          ?_).mpr
        · exact universal value
        · intro index
          cases index with
          | zero => rfl
          | succ index => exact agree index
  | ex body inductionHypothesis =>
      constructor
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            exact Exists.intro value
              ((inductionHypothesis
                (pushEnvironment left value)
                (pushEnvironment right value)
                (fun index => by
                  cases index with
                  | zero => rfl
                  | succ index => exact agree index)).mp bodyHolds)
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            exact Exists.intro value
              ((inductionHypothesis
                (pushEnvironment left value)
                (pushEnvironment right value)
                (fun index => by
                  cases index with
                  | zero => rfl
                  | succ index => exact agree index)).mpr bodyHolds)

/-- Scoped agreement suffices for formula semantics. -/
theorem RawFormula.holds_iff_of_scoped_agreement
    {bound : Nat}
    (formula : RawFormula)
    (isScoped : formula.WellScoped bound)
    (left right : Environment)
    (agree : (index : Nat) -> index < bound -> left index = right index) :
    formula.Holds left ↔ formula.Holds right := by
  induction formula generalizing bound left right with
  | falsum => exact Iff.rfl
  | equal leftTerm rightTerm =>
      change
        leftTerm.evaluate left = rightTerm.evaluate left ↔
          leftTerm.evaluate right = rightTerm.evaluate right
      rw [leftTerm.evaluate_eq_of_scoped_agreement
        isScoped.1 left right agree]
      rw [rightTerm.evaluate_eq_of_scoped_agreement
        isScoped.2 left right agree]
  | conj leftFormula rightFormula leftHypothesis rightHypothesis =>
      exact and_congr
        (leftHypothesis isScoped.1 left right agree)
        (rightHypothesis isScoped.2 left right agree)
  | disj leftFormula rightFormula leftHypothesis rightHypothesis =>
      exact or_congr
        (leftHypothesis isScoped.1 left right agree)
        (rightHypothesis isScoped.2 left right agree)
  | impl leftFormula rightFormula leftHypothesis rightHypothesis =>
      constructor
      · intro implication leftHolds
        exact (rightHypothesis isScoped.2 left right agree).mp
          (implication ((leftHypothesis isScoped.1 left right agree).mpr leftHolds))
      · intro implication leftHolds
        exact (rightHypothesis isScoped.2 left right agree).mpr
          (implication ((leftHypothesis isScoped.1 left right agree).mp leftHolds))
  | all body inductionHypothesis =>
      constructor
      · intro universal value
        exact (inductionHypothesis isScoped
          (pushEnvironment left value)
          (pushEnvironment right value)
          (fun index bounded => by
            cases index with
            | zero => rfl
            | succ index =>
                exact agree index (Nat.lt_of_succ_lt_succ bounded))).mp
          (universal value)
      · intro universal value
        exact (inductionHypothesis isScoped
          (pushEnvironment left value)
          (pushEnvironment right value)
          (fun index bounded => by
            cases index with
            | zero => rfl
            | succ index =>
                exact agree index (Nat.lt_of_succ_lt_succ bounded))).mpr
          (universal value)
  | ex body inductionHypothesis =>
      constructor
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            exact Exists.intro value
              ((inductionHypothesis isScoped
                (pushEnvironment left value)
                (pushEnvironment right value)
                (fun index bounded => by
                  cases index with
                  | zero => rfl
                  | succ index =>
                      exact agree index
                        (Nat.lt_of_succ_lt_succ bounded))).mp bodyHolds)
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            exact Exists.intro value
              ((inductionHypothesis isScoped
                (pushEnvironment left value)
                (pushEnvironment right value)
                (fun index bounded => by
                  cases index with
                  | zero => rfl
                  | succ index =>
                      exact agree index
                        (Nat.lt_of_succ_lt_succ bounded))).mpr bodyHolds)

/-- Standard truth of a closed arithmetic sentence. -/
def Sentence.models (sentence : Sentence) : Prop :=
  sentence.raw.Holds emptyEnvironment

/-- A sentence has the same truth value in every environment. -/
theorem Sentence.holds_environment_independent
    (sentence : Sentence)
    (left right : Environment) :
    sentence.raw.Holds left ↔ sentence.raw.Holds right :=
  sentence.raw.holds_iff_of_scoped_agreement
    sentence.isScoped left right
    (fun index impossible => (Nat.not_lt_zero index impossible).elim)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.evaluate
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.Holds
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.holds_iff_of_scoped_agreement
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence.models
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence.holds_environment_independent
/- AXIOM_AUDIT_END -/
