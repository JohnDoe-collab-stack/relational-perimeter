import RelationalPerimeter.Constitution.HeytingArithmetic.HASoundness

/-!
# Informative standard semantics for Heyting arithmetic

This module interprets HA formulas in `Type`. Existential realizers retain
their numerical witness, so accepted derivations can feed interfaces whose
truth notion is computational rather than merely propositional.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Computational realizers for raw arithmetic formulas. -/
def RawFormula.Realizes : RawFormula -> Environment -> Type
  | RawFormula.falsum, _environment => Empty
  | RawFormula.equal left right, environment =>
      PLift (left.evaluate environment = right.evaluate environment)
  | RawFormula.conj left right, environment =>
      left.Realizes environment × right.Realizes environment
  | RawFormula.disj left right, environment =>
      Sum (left.Realizes environment) (right.Realizes environment)
  | RawFormula.impl left right, environment =>
      left.Realizes environment -> right.Realizes environment
  | RawFormula.all body, environment =>
      (value : Nat) -> body.Realizes (pushEnvironment environment value)
  | RawFormula.ex body, environment =>
      Sigma fun value : Nat => body.Realizes (pushEnvironment environment value)

/-- An indexed presentation of the same informative semantics. Unlike the
recursive family above, this family stays opaque when its formula index is a
large compiled graph, so clients do not have to normalize that graph merely
to type-check a witness transport. -/
inductive RawFormula.InformativeWitness :
    Environment -> RawFormula -> Type where
  | equal {environment : Environment} {left right : RawTerm} :
      PLift (left.evaluate environment = right.evaluate environment) ->
        InformativeWitness environment (RawFormula.equal left right)
  | conj {environment : Environment} {left right : RawFormula} :
      InformativeWitness environment left ->
      InformativeWitness environment right ->
        InformativeWitness environment (RawFormula.conj left right)
  | disjLeft {environment : Environment} {left right : RawFormula} :
      InformativeWitness environment left ->
        InformativeWitness environment (RawFormula.disj left right)
  | disjRight {environment : Environment} {left right : RawFormula} :
      InformativeWitness environment right ->
        InformativeWitness environment (RawFormula.disj left right)
  | impl {environment : Environment} {left right : RawFormula} :
      (left.Realizes environment ->
        InformativeWitness environment right) ->
      InformativeWitness environment (RawFormula.impl left right)
  | all {environment : Environment} {body : RawFormula} :
      ((value : Nat) ->
        InformativeWitness (pushEnvironment environment value) body) ->
      InformativeWitness environment (RawFormula.all body)
  | ex {environment : Environment} {body : RawFormula} (value : Nat) :
      InformativeWitness (pushEnvironment environment value) body ->
      InformativeWitness environment (RawFormula.ex body)

mutual

def RawFormula.realizesToInformativeWitness
    (formula : RawFormula) (environment : Environment) :
    formula.Realizes environment ->
      InformativeWitness environment formula :=
  match formula with
  | .falsum => fun impossible => impossible.elim
  | .equal _left _right => fun equality => .equal equality
  | .conj left right => fun pair =>
      .conj
        (left.realizesToInformativeWitness environment pair.1)
        (right.realizesToInformativeWitness environment pair.2)
  | .disj left right => fun alternative =>
      match alternative with
      | Sum.inl leftRealizer =>
          .disjLeft (left.realizesToInformativeWitness environment leftRealizer)
      | Sum.inr rightRealizer =>
          .disjRight
            (right.realizesToInformativeWitness environment rightRealizer)
  | .impl _left right => fun implication =>
      .impl (fun leftRealizer =>
        right.realizesToInformativeWitness environment
          (implication leftRealizer))
  | .all body => fun universal =>
      .all (fun value => body.realizesToInformativeWitness
        (pushEnvironment environment value) (universal value))
  | .ex body => fun existential =>
      .ex existential.1
        (body.realizesToInformativeWitness
          (pushEnvironment environment existential.1) existential.2)

def RawFormula.informativeWitnessToRealizes
    (formula : RawFormula) (environment : Environment) :
    InformativeWitness environment formula -> formula.Realizes environment :=
  match formula with
  | .falsum => fun witness => nomatch witness
  | .equal _left _right => fun witness =>
      match witness with
      | .equal equality => equality
  | .conj left right => fun witness =>
      match witness with
      | .conj leftWitness rightWitness =>
          (left.informativeWitnessToRealizes environment leftWitness,
            right.informativeWitnessToRealizes environment rightWitness)
  | .disj left right => fun witness =>
      match witness with
      | .disjLeft leftWitness =>
          Sum.inl (left.informativeWitnessToRealizes environment leftWitness)
      | .disjRight rightWitness =>
          Sum.inr (right.informativeWitnessToRealizes environment rightWitness)
  | .impl _left right => fun witness =>
      match witness with
      | .impl implication => fun leftRealizer =>
          right.informativeWitnessToRealizes environment
            (implication leftRealizer)
  | .all body => fun witness =>
      match witness with
      | .all universal => fun value =>
          body.informativeWitnessToRealizes
            (pushEnvironment environment value) (universal value)
  | .ex body => fun witness =>
      match witness with
      | .ex value bodyWitness =>
          ⟨value, body.informativeWitnessToRealizes
            (pushEnvironment environment value) bodyWitness⟩

end

/-- A computationally usable equivalence between two realizer types. -/
structure RealizerEquivalence (left right : Type) : Type where
  forward : left -> right
  backward : right -> left

/-- Computational realizers for every member of a local context. -/
def FormulaContext.Realizes
    {bound : Nat} : FormulaContext bound -> Environment -> Type
  | FormulaContext.nil, _environment => Unit
  | FormulaContext.cons head tail, environment =>
      head.raw.Realizes environment × tail.Realizes environment

/-- Pointwise equal environments preserve informative realizers. -/
def RawFormula.realizes_congr
    (formula : RawFormula)
    (left right : Environment)
    (agree : (index : Nat) -> left index = right index) :
    RealizerEquivalence (formula.Realizes left) (formula.Realizes right) :=
  match formula with
  | RawFormula.falsum =>
      { forward := fun impossible => impossible.elim
        backward := fun impossible => impossible.elim }
  | RawFormula.equal leftTerm rightTerm =>
      { forward := fun equality => ⟨by
          rw [← leftTerm.evaluate_congr left right agree]
          rw [← rightTerm.evaluate_congr left right agree]
          exact equality.down⟩
        backward := fun equality => ⟨by
          rw [leftTerm.evaluate_congr left right agree]
          rw [rightTerm.evaluate_congr left right agree]
          exact equality.down⟩ }
  | RawFormula.conj first second =>
      let firstEquivalence := first.realizes_congr left right agree
      let secondEquivalence := second.realizes_congr left right agree
      { forward := fun pair =>
          (firstEquivalence.forward pair.1,
            secondEquivalence.forward pair.2)
        backward := fun pair =>
          (firstEquivalence.backward pair.1,
            secondEquivalence.backward pair.2) }
  | RawFormula.disj first second =>
      let firstEquivalence := first.realizes_congr left right agree
      let secondEquivalence := second.realizes_congr left right agree
      { forward := fun alternative =>
          match alternative with
          | Sum.inl firstRealizer =>
              Sum.inl (firstEquivalence.forward firstRealizer)
          | Sum.inr secondRealizer =>
              Sum.inr (secondEquivalence.forward secondRealizer)
        backward := fun alternative =>
          match alternative with
          | Sum.inl firstRealizer =>
              Sum.inl (firstEquivalence.backward firstRealizer)
          | Sum.inr secondRealizer =>
              Sum.inr (secondEquivalence.backward secondRealizer) }
  | RawFormula.impl antecedent consequent =>
      let antecedentEquivalence := antecedent.realizes_congr left right agree
      let consequentEquivalence := consequent.realizes_congr left right agree
      { forward := fun implication antecedentAtRight =>
          consequentEquivalence.forward
            (implication (antecedentEquivalence.backward antecedentAtRight))
        backward := fun implication antecedentAtLeft =>
          consequentEquivalence.backward
            (implication (antecedentEquivalence.forward antecedentAtLeft)) }
  | RawFormula.all body =>
      { forward := fun universal value =>
          (body.realizes_congr
            (pushEnvironment left value)
            (pushEnvironment right value)
            (fun index => by
              cases index with
              | zero => rfl
              | succ index => exact agree index)).forward (universal value)
        backward := fun universal value =>
          (body.realizes_congr
            (pushEnvironment left value)
            (pushEnvironment right value)
            (fun index => by
              cases index with
              | zero => rfl
              | succ index => exact agree index)).backward (universal value) }
  | RawFormula.ex body =>
      { forward := fun existential =>
          ⟨existential.1,
            (body.realizes_congr
              (pushEnvironment left existential.1)
              (pushEnvironment right existential.1)
              (fun index => by
                cases index with
                | zero => rfl
                | succ index => exact agree index)).forward existential.2⟩
        backward := fun existential =>
          ⟨existential.1,
            (body.realizes_congr
              (pushEnvironment left existential.1)
              (pushEnvironment right existential.1)
              (fun index => by
                cases index with
                | zero => rfl
                | succ index => exact agree index)).backward existential.2⟩ }

/-- Agreement on the variables allowed by a scoping certificate suffices. -/
def RawFormula.realizes_congrScoped
    {bound : Nat}
    (formula : RawFormula)
    (isScoped : formula.WellScoped bound)
    (left right : Environment)
    (agree : (index : Nat) -> index < bound -> left index = right index) :
    RealizerEquivalence (formula.Realizes left) (formula.Realizes right) :=
  match formula with
  | RawFormula.falsum =>
      { forward := fun impossible => impossible.elim
        backward := fun impossible => impossible.elim }
  | RawFormula.equal leftTerm rightTerm =>
      { forward := fun equality => ⟨by
          rw [← leftTerm.evaluate_eq_of_scoped_agreement
            isScoped.1 left right agree]
          rw [← rightTerm.evaluate_eq_of_scoped_agreement
            isScoped.2 left right agree]
          exact equality.down⟩
        backward := fun equality => ⟨by
          rw [leftTerm.evaluate_eq_of_scoped_agreement
            isScoped.1 left right agree]
          rw [rightTerm.evaluate_eq_of_scoped_agreement
            isScoped.2 left right agree]
          exact equality.down⟩ }
  | RawFormula.conj first second =>
      let firstEquivalence :=
        first.realizes_congrScoped isScoped.1 left right agree
      let secondEquivalence :=
        second.realizes_congrScoped isScoped.2 left right agree
      { forward := fun pair =>
          (firstEquivalence.forward pair.1, secondEquivalence.forward pair.2)
        backward := fun pair =>
          (firstEquivalence.backward pair.1, secondEquivalence.backward pair.2) }
  | RawFormula.disj first second =>
      let firstEquivalence :=
        first.realizes_congrScoped isScoped.1 left right agree
      let secondEquivalence :=
        second.realizes_congrScoped isScoped.2 left right agree
      { forward := fun alternative =>
          match alternative with
          | Sum.inl realizer => Sum.inl (firstEquivalence.forward realizer)
          | Sum.inr realizer => Sum.inr (secondEquivalence.forward realizer)
        backward := fun alternative =>
          match alternative with
          | Sum.inl realizer => Sum.inl (firstEquivalence.backward realizer)
          | Sum.inr realizer => Sum.inr (secondEquivalence.backward realizer) }
  | RawFormula.impl antecedent consequent =>
      let antecedentEquivalence :=
        antecedent.realizes_congrScoped isScoped.1 left right agree
      let consequentEquivalence :=
        consequent.realizes_congrScoped isScoped.2 left right agree
      { forward := fun implication antecedentAtRight =>
          consequentEquivalence.forward
            (implication (antecedentEquivalence.backward antecedentAtRight))
        backward := fun implication antecedentAtLeft =>
          consequentEquivalence.backward
            (implication (antecedentEquivalence.forward antecedentAtLeft)) }
  | RawFormula.all body =>
      { forward := fun universal value =>
          (body.realizes_congrScoped isScoped
            (pushEnvironment left value)
            (pushEnvironment right value)
            (fun index bounded => by
              cases index with
              | zero => rfl
              | succ index =>
                  exact agree index (Nat.lt_of_succ_lt_succ bounded))).forward
            (universal value)
        backward := fun universal value =>
          (body.realizes_congrScoped isScoped
            (pushEnvironment left value)
            (pushEnvironment right value)
            (fun index bounded => by
              cases index with
              | zero => rfl
              | succ index =>
                  exact agree index (Nat.lt_of_succ_lt_succ bounded))).backward
            (universal value) }
  | RawFormula.ex body =>
      { forward := fun existential =>
          ⟨existential.1,
            (body.realizes_congrScoped isScoped
              (pushEnvironment left existential.1)
              (pushEnvironment right existential.1)
              (fun index bounded => by
                cases index with
                | zero => rfl
                | succ index =>
                    exact agree index
                      (Nat.lt_of_succ_lt_succ bounded))).forward existential.2⟩
        backward := fun existential =>
          ⟨existential.1,
            (body.realizes_congrScoped isScoped
              (pushEnvironment left existential.1)
              (pushEnvironment right existential.1)
              (fun index bounded => by
                cases index with
                | zero => rfl
                | succ index =>
                    exact agree index
                      (Nat.lt_of_succ_lt_succ bounded))).backward existential.2⟩ }

/-- Renaming and environment precomposition preserve informative realizers. -/
def RawFormula.realizes_rename
    (formula : RawFormula)
    (rho : Renaming)
    (environment : Environment) :
    RealizerEquivalence
      ((formula.rename rho).Realizes environment)
      (formula.Realizes (fun index => environment (rho index))) :=
  match formula with
  | RawFormula.falsum =>
      { forward := fun impossible => impossible.elim
        backward := fun impossible => impossible.elim }
  | RawFormula.equal left right =>
      { forward := fun equality => ⟨by
          rw [← left.evaluate_rename rho environment]
          rw [← right.evaluate_rename rho environment]
          exact equality.down⟩
        backward := fun equality => ⟨by
          rw [left.evaluate_rename rho environment]
          rw [right.evaluate_rename rho environment]
          exact equality.down⟩ }
  | RawFormula.conj left right =>
      let leftEquivalence := left.realizes_rename rho environment
      let rightEquivalence := right.realizes_rename rho environment
      { forward := fun pair =>
          (leftEquivalence.forward pair.1, rightEquivalence.forward pair.2)
        backward := fun pair =>
          (leftEquivalence.backward pair.1, rightEquivalence.backward pair.2) }
  | RawFormula.disj left right =>
      let leftEquivalence := left.realizes_rename rho environment
      let rightEquivalence := right.realizes_rename rho environment
      { forward := fun alternative =>
          match alternative with
          | Sum.inl realizer => Sum.inl (leftEquivalence.forward realizer)
          | Sum.inr realizer => Sum.inr (rightEquivalence.forward realizer)
        backward := fun alternative =>
          match alternative with
          | Sum.inl realizer => Sum.inl (leftEquivalence.backward realizer)
          | Sum.inr realizer => Sum.inr (rightEquivalence.backward realizer) }
  | RawFormula.impl left right =>
      let leftEquivalence := left.realizes_rename rho environment
      let rightEquivalence := right.realizes_rename rho environment
      { forward := fun implication leftAtTarget =>
          rightEquivalence.forward
            (implication (leftEquivalence.backward leftAtTarget))
        backward := fun implication leftAtSource =>
          rightEquivalence.backward
            (implication (leftEquivalence.forward leftAtSource)) }
  | RawFormula.all body =>
      { forward := fun universal value =>
          let recursive := body.realizes_rename (liftRenaming rho)
            (pushEnvironment environment value)
          let congruence := body.realizes_congr
            (fun index =>
              pushEnvironment environment value (liftRenaming rho index))
            (pushEnvironment (fun index => environment (rho index)) value)
            (fun index => by cases index <;> rfl)
          congruence.forward (recursive.forward (universal value))
        backward := fun universal value =>
          let recursive := body.realizes_rename (liftRenaming rho)
            (pushEnvironment environment value)
          let congruence := body.realizes_congr
            (fun index =>
              pushEnvironment environment value (liftRenaming rho index))
            (pushEnvironment (fun index => environment (rho index)) value)
            (fun index => by cases index <;> rfl)
          recursive.backward (congruence.backward (universal value)) }
  | RawFormula.ex body =>
      { forward := fun existential =>
          let recursive := body.realizes_rename (liftRenaming rho)
            (pushEnvironment environment existential.1)
          let congruence := body.realizes_congr
            (fun index => pushEnvironment environment existential.1
              (liftRenaming rho index))
            (pushEnvironment (fun index => environment (rho index))
              existential.1)
            (fun index => by cases index <;> rfl)
          ⟨existential.1,
            congruence.forward (recursive.forward existential.2)⟩
        backward := fun existential =>
          let recursive := body.realizes_rename (liftRenaming rho)
            (pushEnvironment environment existential.1)
          let congruence := body.realizes_congr
            (fun index => pushEnvironment environment existential.1
              (liftRenaming rho index))
            (pushEnvironment (fun index => environment (rho index))
              existential.1)
            (fun index => by cases index <;> rfl)
          ⟨existential.1,
            recursive.backward (congruence.backward existential.2)⟩ }

/-- Substitution and evaluation preserve informative realizers. -/
def RawFormula.realizes_substitute
    (formula : RawFormula)
    (substitution : Substitution)
    (environment : Environment) :
    RealizerEquivalence
      ((formula.substitute substitution).Realizes environment)
      (formula.Realizes
        (fun index => (substitution index).evaluate environment)) :=
  match formula with
  | RawFormula.falsum =>
      { forward := fun impossible => impossible.elim
        backward := fun impossible => impossible.elim }
  | RawFormula.equal left right =>
      { forward := fun equality => ⟨by
          rw [← left.evaluate_substitute substitution environment]
          rw [← right.evaluate_substitute substitution environment]
          exact equality.down⟩
        backward := fun equality => ⟨by
          rw [left.evaluate_substitute substitution environment]
          rw [right.evaluate_substitute substitution environment]
          exact equality.down⟩ }
  | RawFormula.conj left right =>
      let leftEquivalence := left.realizes_substitute substitution environment
      let rightEquivalence := right.realizes_substitute substitution environment
      { forward := fun pair =>
          (leftEquivalence.forward pair.1, rightEquivalence.forward pair.2)
        backward := fun pair =>
          (leftEquivalence.backward pair.1, rightEquivalence.backward pair.2) }
  | RawFormula.disj left right =>
      let leftEquivalence := left.realizes_substitute substitution environment
      let rightEquivalence := right.realizes_substitute substitution environment
      { forward := fun alternative =>
          match alternative with
          | Sum.inl realizer => Sum.inl (leftEquivalence.forward realizer)
          | Sum.inr realizer => Sum.inr (rightEquivalence.forward realizer)
        backward := fun alternative =>
          match alternative with
          | Sum.inl realizer => Sum.inl (leftEquivalence.backward realizer)
          | Sum.inr realizer => Sum.inr (rightEquivalence.backward realizer) }
  | RawFormula.impl left right =>
      let leftEquivalence := left.realizes_substitute substitution environment
      let rightEquivalence := right.realizes_substitute substitution environment
      { forward := fun implication leftAtTarget =>
          rightEquivalence.forward
            (implication (leftEquivalence.backward leftAtTarget))
        backward := fun implication leftAtSource =>
          rightEquivalence.backward
            (implication (leftEquivalence.forward leftAtSource)) }
  | RawFormula.all body =>
      { forward := fun universal value =>
          let recursive := body.realizes_substitute
            (liftSubstitution substitution)
            (pushEnvironment environment value)
          let congruence := body.realizes_congr
            (fun index => (liftSubstitution substitution index).evaluate
              (pushEnvironment environment value))
            (pushEnvironment
              (fun index => (substitution index).evaluate environment) value)
            (fun index => by
              cases index with
              | zero => rfl
              | succ index =>
                  exact (substitution index).evaluate_rename Nat.succ
                    (pushEnvironment environment value))
          congruence.forward (recursive.forward (universal value))
        backward := fun universal value =>
          let recursive := body.realizes_substitute
            (liftSubstitution substitution)
            (pushEnvironment environment value)
          let congruence := body.realizes_congr
            (fun index => (liftSubstitution substitution index).evaluate
              (pushEnvironment environment value))
            (pushEnvironment
              (fun index => (substitution index).evaluate environment) value)
            (fun index => by
              cases index with
              | zero => rfl
              | succ index =>
                  exact (substitution index).evaluate_rename Nat.succ
                    (pushEnvironment environment value))
          recursive.backward (congruence.backward (universal value)) }
  | RawFormula.ex body =>
      { forward := fun existential =>
          let recursive := body.realizes_substitute
            (liftSubstitution substitution)
            (pushEnvironment environment existential.1)
          let congruence := body.realizes_congr
            (fun index => (liftSubstitution substitution index).evaluate
              (pushEnvironment environment existential.1))
            (pushEnvironment
              (fun index => (substitution index).evaluate environment)
              existential.1)
            (fun index => by
              cases index with
              | zero => rfl
              | succ index =>
                  exact (substitution index).evaluate_rename Nat.succ
                    (pushEnvironment environment existential.1))
          ⟨existential.1,
            congruence.forward (recursive.forward existential.2)⟩
        backward := fun existential =>
          let recursive := body.realizes_substitute
            (liftSubstitution substitution)
            (pushEnvironment environment existential.1)
          let congruence := body.realizes_congr
            (fun index => (liftSubstitution substitution index).evaluate
              (pushEnvironment environment existential.1))
            (pushEnvironment
              (fun index => (substitution index).evaluate environment)
              existential.1)
            (fun index => by
              cases index with
              | zero => rfl
              | succ index =>
                  exact (substitution index).evaluate_rename Nat.succ
                    (pushEnvironment environment existential.1))
          ⟨existential.1,
            recursive.backward (congruence.backward existential.2)⟩ }

def ScopedFormula.realizes_lift
    {bound : Nat}
    (formula : ScopedFormula bound)
    (environment : Environment)
    (value : Nat) :
    RealizerEquivalence
      (formula.lift.raw.Realizes (pushEnvironment environment value))
      (formula.raw.Realizes environment) :=
  let renamed := formula.raw.realizes_rename Nat.succ
    (pushEnvironment environment value)
  let congruence := formula.raw.realizes_congr
    (fun index => pushEnvironment environment value (Nat.succ index))
    environment (fun _index => rfl)
  { forward := fun realizer => congruence.forward (renamed.forward realizer)
    backward := fun realizer => renamed.backward (congruence.backward realizer) }

def ScopedFormula.realizes_instantiate
    {bound : Nat}
    (formula : ScopedFormula (Nat.succ bound))
    (term : ScopedTerm bound)
    (environment : Environment) :
    RealizerEquivalence
      ((formula.instantiate term).raw.Realizes environment)
      (formula.raw.Realizes
        (pushEnvironment environment (term.raw.evaluate environment))) :=
  let substituted := formula.raw.realizes_substitute
    (singleTermSubstitution term.raw) environment
  let congruence := formula.raw.realizes_congr
    (fun index => (singleTermSubstitution term.raw index).evaluate environment)
    (pushEnvironment environment (term.raw.evaluate environment))
    (fun index => by cases index <;> rfl)
  { forward := fun realizer => congruence.forward (substituted.forward realizer)
    backward := fun realizer => substituted.backward (congruence.backward realizer) }

def ScopedFormula.informativeWitness_instantiate
    {bound : Nat}
    (formula : ScopedFormula (Nat.succ bound))
    (term : ScopedTerm bound)
    (environment : Environment) :
    RealizerEquivalence
      (RawFormula.InformativeWitness environment
        (formula.instantiate term).raw)
      (RawFormula.InformativeWitness
        (pushEnvironment environment (term.raw.evaluate environment))
        formula.raw) :=
  let direct := formula.realizes_instantiate term environment
  { forward := fun witness =>
      formula.raw.realizesToInformativeWitness
        (pushEnvironment environment (term.raw.evaluate environment))
        (direct.forward
          ((formula.instantiate term).raw.informativeWitnessToRealizes
            environment witness))
    backward := fun witness =>
      (formula.instantiate term).raw.realizesToInformativeWitness environment
        (direct.backward
          (formula.raw.informativeWitnessToRealizes
            (pushEnvironment environment (term.raw.evaluate environment))
            witness)) }

def FormulaContext.realizes_lift
    {bound : Nat}
    (context : FormulaContext bound)
    (environment : Environment)
    (value : Nat) :
    context.Realizes environment ->
      context.lift.Realizes (pushEnvironment environment value) :=
  match context with
  | FormulaContext.nil => fun _unit => Unit.unit
  | FormulaContext.cons head tail => fun pair =>
      ((head.realizes_lift environment value).backward pair.1,
        tail.realizes_lift environment value pair.2)

def FormulaContext.realizes_congr
    {bound : Nat}
    (context : FormulaContext bound)
    (left right : Environment)
    (agree : (index : Nat) -> left index = right index) :
    RealizerEquivalence
      (context.Realizes left) (context.Realizes right) :=
  match context with
  | FormulaContext.nil =>
      { forward := fun _unit => Unit.unit
        backward := fun _unit => Unit.unit }
  | FormulaContext.cons head tail =>
      let headEquivalence := head.raw.realizes_congr left right agree
      let tailEquivalence := tail.realizes_congr left right agree
      { forward := fun pair =>
          (headEquivalence.forward pair.1, tailEquivalence.forward pair.2)
        backward := fun pair =>
          (headEquivalence.backward pair.1, tailEquivalence.backward pair.2) }

def FormulaContext.realizes_liftForward
    {bound : Nat}
    (context : FormulaContext bound)
    (environment : Environment)
    (value : Nat) :
    context.lift.Realizes (pushEnvironment environment value) ->
      context.Realizes environment :=
  match context with
  | FormulaContext.nil => fun _unit => Unit.unit
  | FormulaContext.cons head tail => fun pair =>
      ((head.realizes_lift environment value).forward pair.1,
        tail.realizes_liftForward environment value pair.2)

def FormulaContext.realizes_instantiate
    {bound : Nat}
    (context : FormulaContext (Nat.succ bound))
    (term : ScopedTerm bound)
    (environment : Environment) :
    (context.instantiate term).Realizes environment ->
      context.Realizes
        (pushEnvironment environment (term.raw.evaluate environment)) :=
  match context with
  | FormulaContext.nil => fun _unit => Unit.unit
  | FormulaContext.cons head tail => fun pair =>
      ((head.realizes_instantiate term environment).forward pair.1,
        tail.realizes_instantiate term environment pair.2)

def ContextMember.realizes
    {bound : Nat}
    {formula : ScopedFormula bound}
    {context : FormulaContext bound}
    (member : ContextMember formula context)
    (environment : Environment) :
    context.Realizes environment -> formula.raw.Realizes environment :=
  match member with
  | ContextMember.here => fun pair => pair.1
  | ContextMember.there earlier => fun pair => earlier.realizes environment pair.2

def ScopedFormula.realizes_successorInstance
    {bound : Nat}
    (formula : ScopedFormula (Nat.succ bound))
    (environment : Environment)
    (value : Nat) :
    formula.successorInstance.raw.Realizes
        (pushEnvironment environment value) ->
      formula.raw.Realizes
        (pushEnvironment environment (Nat.succ value)) :=
  let substituted := formula.raw.realizes_substitute
    ScopedFormula.replaceNewestKeepingScopeSubstitution
    (pushEnvironment environment value)
  let congruence := formula.raw.realizes_congr
    (fun index =>
      (ScopedFormula.replaceNewestKeepingScopeSubstitution index).evaluate
        (pushEnvironment environment value))
    (pushEnvironment environment (Nat.succ value))
    (fun index => by cases index <;> rfl)
  fun realizer => congruence.forward (substituted.forward realizer)

/-- Each positive HA arithmetic scheme has an informative realizer. -/
def standardArithmeticAxiom_realizes
    {bound : Nat}
    {formula : ScopedFormula bound}
    (axiomWitness : StandardArithmeticAxiom formula)
    (environment : Environment) :
    formula.raw.Realizes environment :=
  match axiomWitness with
  | StandardArithmeticAxiom.successorNotZero term =>
      fun impossible => Nat.noConfusion impossible.down
  | StandardArithmeticAxiom.successorInjective left right =>
      fun equality => ⟨Nat.succ.inj equality.down⟩
  | StandardArithmeticAxiom.addZero term => ⟨Nat.add_zero _⟩
  | StandardArithmeticAxiom.addSuccessor left right => ⟨Nat.add_succ _ _⟩
  | StandardArithmeticAxiom.multiplyZero term => ⟨Nat.mul_zero _⟩
  | StandardArithmeticAxiom.multiplySuccessor left right => ⟨Nat.mul_succ _ _⟩
  | @StandardArithmeticAxiom.induction bound body => fun premises value =>
      let base := (body.realizes_instantiate (ScopedTerm.zero bound)
        environment).forward premises.1
      let step := fun index atIndex =>
        body.realizes_successorInstance environment index
          (premises.2 index atIndex)
      Nat.rec base (fun index earlier => step index earlier) value

/-- Constructive Type-valued soundness of every intuitionistic HA derivation. -/
def haDerivation_realizes
    {bound : Nat}
    {sourceContext : FormulaContext bound}
    {sourceConclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic haTheory
      sourceContext sourceConclusion)
    (environment : Environment) :
    sourceContext.Realizes environment ->
      sourceConclusion.raw.Realizes environment :=
  match proof with
  | Derivation.theoryAxiom witness =>
      fun _context => standardArithmeticAxiom_realizes witness environment
  | Derivation.hypothesis member => member.realizes environment
  | Derivation.weaken extra premise =>
      fun context => haDerivation_realizes premise environment context.2
  | Derivation.implicationIntroduction premise =>
      fun context leftRealizer =>
        haDerivation_realizes premise environment (leftRealizer, context)
  | Derivation.implicationElimination implication argument =>
      fun context =>
        haDerivation_realizes implication environment context
          (haDerivation_realizes argument environment context)
  | Derivation.conjunctionIntroduction left right =>
      fun context =>
        (haDerivation_realizes left environment context,
          haDerivation_realizes right environment context)
  | Derivation.conjunctionEliminationLeft premise =>
      fun context => (haDerivation_realizes premise environment context).1
  | Derivation.conjunctionEliminationRight premise =>
      fun context => (haDerivation_realizes premise environment context).2
  | Derivation.disjunctionIntroductionLeft premise =>
      fun context => Sum.inl (haDerivation_realizes premise environment context)
  | Derivation.disjunctionIntroductionRight premise =>
      fun context => Sum.inr (haDerivation_realizes premise environment context)
  | Derivation.disjunctionElimination disjunction leftBranch rightBranch =>
      fun context =>
        match haDerivation_realizes disjunction environment context with
        | Sum.inl leftRealizer =>
            haDerivation_realizes leftBranch environment (leftRealizer, context)
        | Sum.inr rightRealizer =>
            haDerivation_realizes rightBranch environment (rightRealizer, context)
  | Derivation.falsumElimination premise =>
      fun context => (haDerivation_realizes premise environment context).elim
  | @Derivation.universalIntroduction _ _ _ context body premise =>
      fun contextRealizer value =>
        haDerivation_realizes premise (pushEnvironment environment value)
          (context.realizes_lift environment value contextRealizer)
  | @Derivation.universalElimination _ _ _ context body term premise =>
      fun contextRealizer =>
        (body.realizes_instantiate term environment).backward
          (haDerivation_realizes premise environment contextRealizer
            (term.raw.evaluate environment))
  | @Derivation.existentialIntroduction _ _ _ context body term premise =>
      fun contextRealizer =>
        ⟨term.raw.evaluate environment,
          (body.realizes_instantiate term environment).forward
            (haDerivation_realizes premise environment contextRealizer)⟩
  | @Derivation.existentialElimination _ _ _ context body conclusion
      existential branch =>
      fun contextRealizer =>
        let existentialRealizer :=
          haDerivation_realizes existential environment contextRealizer
        let branchResult := haDerivation_realizes branch
          (pushEnvironment environment existentialRealizer.1)
          (existentialRealizer.2,
            context.realizes_lift environment existentialRealizer.1
              contextRealizer)
        (conclusion.realizes_lift environment existentialRealizer.1).forward
          branchResult
  | Derivation.equalityReflexivity term => fun _context => ⟨rfl⟩
  | Derivation.equalitySymmetry premise =>
      fun context =>
        ⟨(haDerivation_realizes premise environment context).down.symm⟩
  | Derivation.equalityTransitivity first second =>
      fun context =>
        ⟨(haDerivation_realizes first environment context).down.trans
          (haDerivation_realizes second environment context).down⟩
  | @Derivation.equalitySubstitution _ _ _ context left right body
      equality premise =>
      fun contextRealizer =>
        let termEquality :=
          (haDerivation_realizes equality environment contextRealizer).down
        let atLeft := (body.realizes_instantiate left environment).forward
          (haDerivation_realizes premise environment contextRealizer)
        let atRight := (body.raw.realizes_congr
          (pushEnvironment environment (left.raw.evaluate environment))
          (pushEnvironment environment (right.raw.evaluate environment))
          (fun index => by
            cases index with
            | zero => exact termEquality
            | succ index => rfl)).forward atLeft
        (body.realizes_instantiate right environment).backward atRight
  | @Derivation.liftVariables _ _ _ context conclusion premise =>
      fun contextRealizer =>
        let tailEnvironment : Environment := fun index =>
          environment (Nat.succ index)
        let canonicalEnvironment :=
          pushEnvironment tailEnvironment (environment 0)
        let canonicalContext :=
          (context.lift.realizes_congr environment canonicalEnvironment
            (fun index => by cases index <;> rfl)).forward contextRealizer
        let earlierContext := context.realizes_liftForward tailEnvironment
          (environment 0) canonicalContext
        let canonicalConclusion :=
          (conclusion.realizes_lift tailEnvironment
            (environment 0)).backward
            (haDerivation_realizes premise tailEnvironment earlierContext)
        (conclusion.lift.raw.realizes_congr canonicalEnvironment environment
          (fun index => by cases index <;> rfl)).forward canonicalConclusion
  | @Derivation.freeInstantiation _ _ _ context conclusion replacement premise =>
      fun contextRealizer =>
        (conclusion.realizes_instantiate replacement environment).backward
          (haDerivation_realizes premise
            (pushEnvironment environment (replacement.raw.evaluate environment))
            (context.realizes_instantiate replacement environment contextRealizer))
  | Derivation.doubleNegationElimination permission premise =>
      nomatch permission

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.Realizes
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.InformativeWitness
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.realizesToInformativeWitness
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.informativeWitnessToRealizes
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.realizes_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.ScopedFormula.informativeWitness_instantiate
#print axioms RelationalPerimeter.HeytingArithmetic.standardArithmeticAxiom_realizes
#print axioms RelationalPerimeter.HeytingArithmetic.haDerivation_realizes
/- AXIOM_AUDIT_END -/
