import RelationalPerimeter.Instances.HeytingArithmetic.Semantics

/-!
# Renaming and simultaneous substitution

All operations are capture avoiding by construction.  The semantic lemmas are
proved through pointwise environment agreement; no function extensionality is
used.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

abbrev Renaming := Nat -> Nat
abbrev Substitution := Nat -> RawTerm

/-- Lift a rho through one binder. -/
def liftRenaming (rho : Renaming) : Renaming
  | 0 => 0
  | Nat.succ index => Nat.succ (rho index)

/-- Rename every variable of a term. -/
def RawTerm.rename (term : RawTerm) (rho : Renaming) : RawTerm :=
  match term with
  | RawTerm.bvar index => RawTerm.bvar (rho index)
  | RawTerm.zero => RawTerm.zero
  | RawTerm.succ body => RawTerm.succ (body.rename rho)
  | RawTerm.add left right =>
      RawTerm.add (left.rename rho) (right.rename rho)
  | RawTerm.mul left right =>
      RawTerm.mul (left.rename rho) (right.rename rho)

/-- Capture-avoiding rho of formulas. -/
def RawFormula.rename
    (formula : RawFormula)
    (rho : Renaming) :
    RawFormula :=
  match formula with
  | RawFormula.falsum => RawFormula.falsum
  | RawFormula.equal left right =>
      RawFormula.equal (left.rename rho) (right.rename rho)
  | RawFormula.conj left right =>
      RawFormula.conj (left.rename rho) (right.rename rho)
  | RawFormula.disj left right =>
      RawFormula.disj (left.rename rho) (right.rename rho)
  | RawFormula.impl left right =>
      RawFormula.impl (left.rename rho) (right.rename rho)
  | RawFormula.all body =>
      RawFormula.all (body.rename (liftRenaming rho))
  | RawFormula.ex body =>
      RawFormula.ex (body.rename (liftRenaming rho))

/-- Lift a simultaneous substitution through one binder. -/
def liftSubstitution (substitution : Substitution) : Substitution
  | 0 => RawTerm.bvar 0
  | Nat.succ index =>
      (substitution index).rename Nat.succ

/-- Simultaneous substitution in terms. -/
def RawTerm.substitute
    (term : RawTerm)
    (substitution : Substitution) :
    RawTerm :=
  match term with
  | RawTerm.bvar index => substitution index
  | RawTerm.zero => RawTerm.zero
  | RawTerm.succ body => RawTerm.succ (body.substitute substitution)
  | RawTerm.add left right =>
      RawTerm.add
        (left.substitute substitution)
        (right.substitute substitution)
  | RawTerm.mul left right =>
      RawTerm.mul
        (left.substitute substitution)
        (right.substitute substitution)

/-- Capture-avoiding simultaneous substitution in formulas. -/
def RawFormula.substitute
    (formula : RawFormula)
    (substitution : Substitution) :
    RawFormula :=
  match formula with
  | RawFormula.falsum => RawFormula.falsum
  | RawFormula.equal left right =>
      RawFormula.equal
        (left.substitute substitution)
        (right.substitute substitution)
  | RawFormula.conj left right =>
      RawFormula.conj
        (left.substitute substitution)
        (right.substitute substitution)
  | RawFormula.disj left right =>
      RawFormula.disj
        (left.substitute substitution)
        (right.substitute substitution)
  | RawFormula.impl left right =>
      RawFormula.impl
        (left.substitute substitution)
        (right.substitute substitution)
  | RawFormula.all body =>
      RawFormula.all (body.substitute (liftSubstitution substitution))
  | RawFormula.ex body =>
      RawFormula.ex (body.substitute (liftSubstitution substitution))

/-- Lifted rhos preserve the corresponding successor contexts. -/
theorem liftRenaming_lt
    {source target : Nat}
    (rho : Renaming)
    (maps : (index : Nat) -> index < source -> rho index < target)
    (index : Nat)
    (bounded : index < Nat.succ source) :
    liftRenaming rho index < Nat.succ target := by
  cases index with
  | zero => exact Nat.zero_lt_succ target
  | succ index =>
      exact Nat.succ_lt_succ
        (maps index (Nat.lt_of_succ_lt_succ bounded))

/-- Renaming preserves term scoping under a bounded variable map. -/
theorem RawTerm.wellScoped_rename
    {source target : Nat}
    (term : RawTerm)
    (isScoped : term.WellScoped source)
    (rho : Renaming)
    (maps : (index : Nat) -> index < source -> rho index < target) :
    (term.rename rho).WellScoped target := by
  induction term with
  | bvar index => exact maps index isScoped
  | zero => exact trivial
  | succ body inductionHypothesis => exact inductionHypothesis isScoped
  | add left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1)
        (rightHypothesis isScoped.2)
  | mul left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1)
        (rightHypothesis isScoped.2)

/-- Renaming preserves formula scoping. -/
theorem RawFormula.wellScoped_rename
    {source target : Nat}
    (formula : RawFormula)
    (isScoped : formula.WellScoped source)
    (rho : Renaming)
    (maps : (index : Nat) -> index < source -> rho index < target) :
    (formula.rename rho).WellScoped target := by
  induction formula generalizing source target rho with
  | falsum => exact trivial
  | equal left right =>
      exact And.intro
        (left.wellScoped_rename isScoped.1 rho maps)
        (right.wellScoped_rename isScoped.2 rho maps)
  | conj left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1 rho maps)
        (rightHypothesis isScoped.2 rho maps)
  | disj left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1 rho maps)
        (rightHypothesis isScoped.2 rho maps)
  | impl left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1 rho maps)
        (rightHypothesis isScoped.2 rho maps)
  | all body inductionHypothesis =>
      exact inductionHypothesis isScoped (liftRenaming rho)
        (liftRenaming_lt rho maps)
  | ex body inductionHypothesis =>
      exact inductionHypothesis isScoped (liftRenaming rho)
        (liftRenaming_lt rho maps)

/-- A lifted substitution is scoped in the lifted target context. -/
theorem liftSubstitution_wellScoped
    {source target : Nat}
    (substitution : Substitution)
    (maps :
      (index : Nat) ->
        index < source ->
          (substitution index).WellScoped target)
    (index : Nat)
    (bounded : index < Nat.succ source) :
    (liftSubstitution substitution index).WellScoped (Nat.succ target) := by
  cases index with
  | zero => exact Nat.zero_lt_succ target
  | succ index =>
      exact (substitution index).wellScoped_rename
        (maps index (Nat.lt_of_succ_lt_succ bounded))
        Nat.succ
        (fun inner innerBound => Nat.succ_lt_succ innerBound)

/-- Simultaneous substitution preserves term scoping. -/
theorem RawTerm.wellScoped_substitute
    {source target : Nat}
    (term : RawTerm)
    (isScoped : term.WellScoped source)
    (substitution : Substitution)
    (maps :
      (index : Nat) ->
        index < source ->
          (substitution index).WellScoped target) :
    (term.substitute substitution).WellScoped target := by
  induction term with
  | bvar index => exact maps index isScoped
  | zero => exact trivial
  | succ body inductionHypothesis => exact inductionHypothesis isScoped
  | add left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1)
        (rightHypothesis isScoped.2)
  | mul left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1)
        (rightHypothesis isScoped.2)

/-- Simultaneous substitution preserves formula scoping. -/
theorem RawFormula.wellScoped_substitute
    {source target : Nat}
    (formula : RawFormula)
    (isScoped : formula.WellScoped source)
    (substitution : Substitution)
    (maps :
      (index : Nat) ->
        index < source ->
          (substitution index).WellScoped target) :
    (formula.substitute substitution).WellScoped target := by
  induction formula generalizing source target substitution with
  | falsum => exact trivial
  | equal left right =>
      exact And.intro
        (left.wellScoped_substitute isScoped.1 substitution maps)
        (right.wellScoped_substitute isScoped.2 substitution maps)
  | conj left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1 substitution maps)
        (rightHypothesis isScoped.2 substitution maps)
  | disj left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1 substitution maps)
        (rightHypothesis isScoped.2 substitution maps)
  | impl left right leftHypothesis rightHypothesis =>
      exact And.intro
        (leftHypothesis isScoped.1 substitution maps)
        (rightHypothesis isScoped.2 substitution maps)
  | all body inductionHypothesis =>
      exact inductionHypothesis isScoped (liftSubstitution substitution)
        (liftSubstitution_wellScoped substitution maps)
  | ex body inductionHypothesis =>
      exact inductionHypothesis isScoped (liftSubstitution substitution)
        (liftSubstitution_wellScoped substitution maps)

/-- Renaming is interpreted by precomposition of the environment. -/
theorem RawTerm.evaluate_rename
    (term : RawTerm)
    (rho : Renaming)
    (environment : Environment) :
    (term.rename rho).evaluate environment =
      term.evaluate (fun index => environment (rho index)) := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      change Nat.succ ((body.rename rho).evaluate environment) =
        Nat.succ (body.evaluate (fun index => environment (rho index)))
      rw [inductionHypothesis]
  | add left right leftHypothesis rightHypothesis =>
      change
        (left.rename rho).evaluate environment +
            (right.rename rho).evaluate environment =
          left.evaluate (fun index => environment (rho index)) +
            right.evaluate (fun index => environment (rho index))
      rw [leftHypothesis, rightHypothesis]
  | mul left right leftHypothesis rightHypothesis =>
      change
        (left.rename rho).evaluate environment *
            (right.rename rho).evaluate environment =
          left.evaluate (fun index => environment (rho index)) *
            right.evaluate (fun index => environment (rho index))
      rw [leftHypothesis, rightHypothesis]

/-- Term substitution is interpreted by evaluating the substituted terms. -/
theorem RawTerm.evaluate_substitute
    (term : RawTerm)
    (substitution : Substitution)
    (environment : Environment) :
    (term.substitute substitution).evaluate environment =
      term.evaluate (fun index => (substitution index).evaluate environment) := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      change
        Nat.succ ((body.substitute substitution).evaluate environment) =
          Nat.succ
            (body.evaluate
              (fun index => (substitution index).evaluate environment))
      rw [inductionHypothesis]
  | add left right leftHypothesis rightHypothesis =>
      change
        (left.substitute substitution).evaluate environment +
            (right.substitute substitution).evaluate environment =
          left.evaluate
              (fun index => (substitution index).evaluate environment) +
            right.evaluate
              (fun index => (substitution index).evaluate environment)
      rw [leftHypothesis, rightHypothesis]
  | mul left right leftHypothesis rightHypothesis =>
      change
        (left.substitute substitution).evaluate environment *
            (right.substitute substitution).evaluate environment =
          left.evaluate
              (fun index => (substitution index).evaluate environment) *
            right.evaluate
              (fun index => (substitution index).evaluate environment)
      rw [leftHypothesis, rightHypothesis]

/-- Formula rho has the expected pointwise semantics. -/
theorem RawFormula.holds_rename
    (formula : RawFormula)
    (rho : Renaming)
    (environment : Environment) :
    (formula.rename rho).Holds environment ↔
      formula.Holds (fun index => environment (rho index)) := by
  induction formula generalizing rho environment with
  | falsum => exact Iff.rfl
  | equal left right =>
      change
        (left.rename rho).evaluate environment =
            (right.rename rho).evaluate environment ↔
          left.evaluate (fun index => environment (rho index)) =
            right.evaluate (fun index => environment (rho index))
      rw [left.evaluate_rename, right.evaluate_rename]
  | conj left right leftHypothesis rightHypothesis =>
      exact and_congr
        (leftHypothesis rho environment)
        (rightHypothesis rho environment)
  | disj left right leftHypothesis rightHypothesis =>
      exact or_congr
        (leftHypothesis rho environment)
        (rightHypothesis rho environment)
  | impl left right leftHypothesis rightHypothesis =>
      constructor
      · intro implication leftHolds
        exact (rightHypothesis rho environment).mp
          (implication ((leftHypothesis rho environment).mpr leftHolds))
      · intro implication leftHolds
        exact (rightHypothesis rho environment).mpr
          (implication ((leftHypothesis rho environment).mp leftHolds))
  | all body inductionHypothesis =>
      constructor
      · intro universal value
        have renamed :=
          (inductionHypothesis
            (liftRenaming rho)
            (pushEnvironment environment value)).mp
            (universal value)
        exact (body.holds_congr
          (fun index =>
            pushEnvironment environment value (liftRenaming rho index))
          (pushEnvironment
            (fun index => environment (rho index)) value)
          (fun index => by cases index <;> rfl)).mp renamed
      · intro universal value
        apply (inductionHypothesis
          (liftRenaming rho)
          (pushEnvironment environment value)).mpr
        exact (body.holds_congr
          (fun index =>
            pushEnvironment environment value (liftRenaming rho index))
          (pushEnvironment
            (fun index => environment (rho index)) value)
          (fun index => by cases index <;> rfl)).mpr
          (universal value)
  | ex body inductionHypothesis =>
      constructor
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            have renamed :=
              (inductionHypothesis
                (liftRenaming rho)
                (pushEnvironment environment value)).mp bodyHolds
            exact Exists.intro value
              ((body.holds_congr
                (fun index =>
                  pushEnvironment environment value
                    (liftRenaming rho index))
                (pushEnvironment
                  (fun index => environment (rho index)) value)
                (fun index => by cases index <;> rfl)).mp renamed)
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            refine Exists.intro value ?_
            apply (inductionHypothesis
              (liftRenaming rho)
              (pushEnvironment environment value)).mpr
            exact (body.holds_congr
              (fun index =>
                pushEnvironment environment value
                  (liftRenaming rho index))
              (pushEnvironment
                (fun index => environment (rho index)) value)
              (fun index => by cases index <;> rfl)).mpr bodyHolds

/-- Formula substitution has the expected pointwise semantics. -/
theorem RawFormula.holds_substitute
    (formula : RawFormula)
    (substitution : Substitution)
    (environment : Environment) :
    (formula.substitute substitution).Holds environment ↔
      formula.Holds
        (fun index => (substitution index).evaluate environment) := by
  induction formula generalizing substitution environment with
  | falsum => exact Iff.rfl
  | equal left right =>
      change
        (left.substitute substitution).evaluate environment =
            (right.substitute substitution).evaluate environment ↔
          left.evaluate
              (fun index => (substitution index).evaluate environment) =
            right.evaluate
              (fun index => (substitution index).evaluate environment)
      rw [left.evaluate_substitute, right.evaluate_substitute]
  | conj left right leftHypothesis rightHypothesis =>
      exact and_congr
        (leftHypothesis substitution environment)
        (rightHypothesis substitution environment)
  | disj left right leftHypothesis rightHypothesis =>
      exact or_congr
        (leftHypothesis substitution environment)
        (rightHypothesis substitution environment)
  | impl left right leftHypothesis rightHypothesis =>
      constructor
      · intro implication leftHolds
        exact (rightHypothesis substitution environment).mp
          (implication
            ((leftHypothesis substitution environment).mpr leftHolds))
      · intro implication leftHolds
        exact (rightHypothesis substitution environment).mpr
          (implication
            ((leftHypothesis substitution environment).mp leftHolds))
  | all body inductionHypothesis =>
      constructor
      · intro universal value
        have substituted :=
          (inductionHypothesis
            (liftSubstitution substitution)
            (pushEnvironment environment value)).mp
            (universal value)
        exact (body.holds_congr
          (fun index =>
            (liftSubstitution substitution index).evaluate
              (pushEnvironment environment value))
          (pushEnvironment
            (fun index => (substitution index).evaluate environment)
            value)
          (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                exact (substitution index).evaluate_rename
                  Nat.succ (pushEnvironment environment value))).mp
          substituted
      · intro universal value
        apply (inductionHypothesis
          (liftSubstitution substitution)
          (pushEnvironment environment value)).mpr
        exact (body.holds_congr
          (fun index =>
            (liftSubstitution substitution index).evaluate
              (pushEnvironment environment value))
          (pushEnvironment
            (fun index => (substitution index).evaluate environment)
            value)
          (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                exact (substitution index).evaluate_rename
                  Nat.succ (pushEnvironment environment value))).mpr
          (universal value)
  | ex body inductionHypothesis =>
      constructor
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            have substituted :=
              (inductionHypothesis
                (liftSubstitution substitution)
                (pushEnvironment environment value)).mp bodyHolds
            exact Exists.intro value
              ((body.holds_congr
                (fun index =>
                  (liftSubstitution substitution index).evaluate
                    (pushEnvironment environment value))
                (pushEnvironment
                  (fun index => (substitution index).evaluate environment)
                  value)
                (fun index => by
                  cases index with
                  | zero => rfl
                  | succ index =>
                      exact (substitution index).evaluate_rename
                        Nat.succ
                        (pushEnvironment environment value))).mp substituted)
      · intro existential
        cases existential with
        | intro value bodyHolds =>
            refine Exists.intro value ?_
            apply (inductionHypothesis
              (liftSubstitution substitution)
              (pushEnvironment environment value)).mpr
            exact (body.holds_congr
              (fun index =>
                (liftSubstitution substitution index).evaluate
                  (pushEnvironment environment value))
              (pushEnvironment
                (fun index => (substitution index).evaluate environment)
                value)
              (fun index => by
                cases index with
                | zero => rfl
                | succ index =>
                    exact (substitution index).evaluate_rename
                      Nat.succ
                      (pushEnvironment environment value))).mpr bodyHolds

/-- Replace all free variables by one closed numeral. -/
def RawFormula.instantiateNumeral
    (formula : RawFormula)
    (value : Nat) :
    RawFormula :=
  formula.substitute (fun _index => RawTerm.numeral value)

/-- Apply a unary predicate to a numeral and obtain a closed sentence. -/
def Predicate.applyNumeral
    (predicate : Predicate)
    (value : Nat) :
    Sentence where
  raw := predicate.raw.instantiateNumeral value
  isScoped := predicate.raw.wellScoped_substitute
    predicate.isScoped
    (fun _index => RawTerm.numeral value)
    (fun _index _bounded => RawTerm.numeral_wellScoped value 0)

/-- Applying a predicate to a numeral evaluates it at that natural number. -/
theorem Predicate.models_applyNumeral
    (predicate : Predicate)
    (value : Nat) :
    (predicate.applyNumeral value).models ↔
      predicate.raw.Holds (pushEnvironment emptyEnvironment value) := by
  apply Iff.trans
    (predicate.raw.holds_substitute
      (fun _index => RawTerm.numeral value)
      emptyEnvironment)
  apply predicate.raw.holds_iff_of_scoped_agreement predicate.isScoped
  intro index bounded
  cases index with
  | zero => exact RawTerm.evaluate_numeral value emptyEnvironment
  | succ index =>
      exact (Nat.not_lt_zero index
        (Nat.lt_of_succ_lt_succ bounded)).elim

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.rename
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitute
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.wellScoped_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.holds_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.Predicate.applyNumeral
#print axioms RelationalPerimeter.HeytingArithmetic.Predicate.models_applyNumeral
/- AXIOM_AUDIT_END -/
