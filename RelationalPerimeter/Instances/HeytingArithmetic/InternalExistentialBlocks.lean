import RelationalPerimeter.Instances.HeytingArithmetic.InternalNumeralProofs

/-!
# Constructive proof introduction for finite existential blocks

The witness vector is substituted into the free De Bruijn variables and then
reintroduced in exactly the binder order used by `RawFormula.existsMany`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem existentialBinaryCongr
    {alpha beta gamma : Type}
    (operation : alpha -> beta -> gamma)
    {left₁ left₂ : alpha}
    {right₁ right₂ : beta}
    (leftEqual : left₁ = left₂)
    (rightEqual : right₁ = right₂) :
    operation left₁ right₁ = operation left₂ right₂ := by
  cases leftEqual
  cases rightEqual
  rfl

theorem RawTerm.renameSucc_substituteLift_local
    (term : RawTerm)
    (substitution : Substitution) :
    (term.rename Nat.succ).substitute (liftSubstitution substitution) =
      (term.substitute substitution).rename Nat.succ := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawTerm.add
        leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawTerm.mul
        leftHypothesis rightHypothesis

theorem RawTerm.substitute_eq_self_of_scoped_agreement
    {bound : Nat}
    (term : RawTerm)
    (scopeEvidence : term.WellScoped bound)
    (substitution : Substitution)
    (agrees : (index : Nat) -> index < bound ->
      substitution index = RawTerm.bvar index) :
    term.substitute substitution = term := by
  induction term with
  | bvar index => exact agrees index scopeEvidence
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ (inductionHypothesis scopeEvidence)
  | add left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawTerm.add
        (leftHypothesis scopeEvidence.1)
        (rightHypothesis scopeEvidence.2)
  | mul left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawTerm.mul
        (leftHypothesis scopeEvidence.1)
        (rightHypothesis scopeEvidence.2)

theorem RawFormula.substitute_eq_self_of_scoped_agreement
    {bound : Nat}
    (formula : RawFormula)
    (scopeEvidence : formula.WellScoped bound)
    (substitution : Substitution)
    (agrees : (index : Nat) -> index < bound ->
      substitution index = RawTerm.bvar index) :
    formula.substitute substitution = formula := by
  induction formula generalizing bound substitution with
  | falsum => rfl
  | equal left right =>
      exact existentialBinaryCongr RawFormula.equal
        (left.substitute_eq_self_of_scoped_agreement
          scopeEvidence.1 substitution agrees)
        (right.substitute_eq_self_of_scoped_agreement
          scopeEvidence.2 substitution agrees)
  | conj left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawFormula.conj
        (leftHypothesis scopeEvidence.1 substitution agrees)
        (rightHypothesis scopeEvidence.2 substitution agrees)
  | disj left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawFormula.disj
        (leftHypothesis scopeEvidence.1 substitution agrees)
        (rightHypothesis scopeEvidence.2 substitution agrees)
  | impl left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawFormula.impl
        (leftHypothesis scopeEvidence.1 substitution agrees)
        (rightHypothesis scopeEvidence.2 substitution agrees)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis scopeEvidence
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          rw [liftSubstitution, agrees index
            (Nat.lt_of_succ_lt_succ bounded)]
          rfl
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis scopeEvidence
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          rw [liftSubstitution, agrees index
            (Nat.lt_of_succ_lt_succ bounded)]
          rfl

def numeralClosingSubstitution
    {count : Nat}
    (values : NatVector count) : Substitution :=
  fun index => RawTerm.numeral (values.getD index)

def numeralClosingSubstitutionAtDepth
    {count : Nat}
    (values : NatVector count) : Nat -> Substitution
  | 0 => numeralClosingSubstitution values
  | Nat.succ depth =>
      liftSubstitution (numeralClosingSubstitutionAtDepth values depth)

@[simp] theorem numeralClosingSubstitutionAtDepth_zero
    {count : Nat}
    (values : NatVector count) :
    numeralClosingSubstitutionAtDepth values 0 =
      numeralClosingSubstitution values := rfl

@[simp] theorem numeralClosingSubstitutionAtDepth_succ
    {count : Nat}
    (values : NatVector count)
    (depth : Nat) :
    numeralClosingSubstitutionAtDepth values (Nat.succ depth) =
      liftSubstitution (numeralClosingSubstitutionAtDepth values depth) := rfl

theorem numeralClosing_cons_composition
    {count : Nat}
    (head : Nat)
    (tail : NatVector count)
    (depth index : Nat) :
    ((numeralClosingSubstitutionAtDepth tail (Nat.succ depth) index).substitute
      (termSubstitutionAtDepth (RawTerm.numeral head) depth)) =
    numeralClosingSubstitutionAtDepth
      (NatVector.cons head tail) depth index := by
  induction depth generalizing index with
  | zero =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            ((RawTerm.numeral (tail.getD index)).rename Nat.succ).substitute
                (singleTermSubstitution (RawTerm.numeral head)) =
              RawTerm.numeral (tail.getD index)
          induction tail.getD index with
          | zero => rfl
          | succ value inductionHypothesis =>
              exact congrArg RawTerm.succ inductionHypothesis
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            ((numeralClosingSubstitutionAtDepth tail
                (Nat.succ depth) index).rename Nat.succ).substitute
                (liftSubstitution
                  (termSubstitutionAtDepth (RawTerm.numeral head) depth)) =
              (numeralClosingSubstitutionAtDepth
                (NatVector.cons head tail) depth index).rename Nat.succ
          rw [RawTerm.renameSucc_substituteLift_local,
            inductionHypothesis index]

theorem RawTerm.substitute_closeCons
    {count : Nat}
    (term : RawTerm)
    (head : Nat)
    (tail : NatVector count)
    (depth : Nat) :
    (term.substitute
        (numeralClosingSubstitutionAtDepth tail (Nat.succ depth))).substitute
          (termSubstitutionAtDepth (RawTerm.numeral head) depth) =
      term.substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons head tail) depth) := by
  induction term with
  | bvar index => exact numeralClosing_cons_composition head tail depth index
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawTerm.add
        leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawTerm.mul
        leftHypothesis rightHypothesis

theorem RawFormula.substitute_closeCons
    {count : Nat}
    (formula : RawFormula)
    (head : Nat)
    (tail : NatVector count)
    (depth : Nat) :
    (formula.substitute
        (numeralClosingSubstitutionAtDepth tail (Nat.succ depth))).substitute
          (termSubstitutionAtDepth (RawTerm.numeral head) depth) =
      formula.substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons head tail) depth) := by
  induction formula generalizing depth with
  | falsum => rfl
  | equal left right =>
      exact existentialBinaryCongr RawFormula.equal
        (left.substitute_closeCons head tail depth)
        (right.substitute_closeCons head tail depth)
  | conj left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawFormula.conj
        (leftHypothesis depth) (rightHypothesis depth)
  | disj left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawFormula.disj
        (leftHypothesis depth) (rightHypothesis depth)
  | impl left right leftHypothesis rightHypothesis =>
      exact existentialBinaryCongr RawFormula.impl
        (leftHypothesis depth) (rightHypothesis depth)
  | all body inductionHypothesis =>
      exact congrArg RawFormula.all
        (inductionHypothesis (Nat.succ depth))
  | ex body inductionHypothesis =>
      exact congrArg RawFormula.ex
        (inductionHypothesis (Nat.succ depth))

def ScopedFormula.closeWithNumerals
    {count : Nat}
    (formula : ScopedFormula count)
    (values : NatVector count) : ScopedFormula 0 :=
  { raw := formula.raw.substitute (numeralClosingSubstitution values)
    isScoped := formula.raw.wellScoped_substitute formula.isScoped
      (numeralClosingSubstitution values)
      (fun index _bounded => RawTerm.numeral_wellScoped (values.getD index) 0) }

def ScopedFormula.closeTailWithNumerals
    {count : Nat}
    (formula : ScopedFormula (Nat.succ count))
    (tail : NatVector count) : ScopedFormula 1 :=
  { raw := formula.raw.substitute
      (numeralClosingSubstitutionAtDepth tail 1)
    isScoped := formula.raw.wellScoped_substitute formula.isScoped
      (numeralClosingSubstitutionAtDepth tail 1)
      (fun index bounded => by
        cases index with
        | zero => exact Nat.zero_lt_succ 0
        | succ index =>
            change ((RawTerm.numeral (tail.getD index)).rename Nat.succ).WellScoped 1
            exact RawTerm.wellScoped_rename
              (RawTerm.numeral (tail.getD index))
              (RawTerm.numeral_wellScoped (tail.getD index) 0)
              Nat.succ
              (fun variableIndex impossible =>
                (Nat.not_lt_zero variableIndex impossible).elim)) }

theorem ScopedFormula.closeWithNumerals_cons
    {count : Nat}
    (formula : ScopedFormula (Nat.succ count))
    (head : Nat)
    (tail : NatVector count) :
    (formula.closeTailWithNumerals tail).instantiate
        (ScopedTerm.numeral 0 head) =
      formula.closeWithNumerals (NatVector.cons head tail) := by
  apply ScopedFormula.eq_of_raw_eq
  exact formula.raw.substitute_closeCons head tail 0

theorem ScopedFormula.ex_closeWithNumerals
    {count : Nat}
    (formula : ScopedFormula (Nat.succ count))
    (tail : NatVector count) :
    (ScopedFormula.ex formula).closeWithNumerals tail =
      ScopedFormula.ex (formula.closeTailWithNumerals tail) := by
  rfl

def ScopedFormula.existsManyBlock
    {count : Nat}
    (body : ScopedFormula count) : ScopedFormula 0 :=
  { raw := body.raw.existsMany count
    isScoped := RawFormula.existsMany_wellScoped count 0 body.raw
      (Eq.mpr
        (congrArg (fun available => body.raw.WellScoped available)
          (Nat.add_zero count))
        body.isScoped) }

def ExistsManyIntroductionAt (count : Nat) : Type :=
    (body : ScopedFormula count) ->
    (values : NatVector count) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.closeWithNumerals values) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      body.existsManyBlock

def Derivation.introduceExistsManyByCount :
    (count : Nat) -> ExistsManyIntroductionAt count :=
  Nat.rec
    (fun body values proof =>
      by
        have unchanged : body.raw.substitute
            (numeralClosingSubstitution values) = body.raw :=
          body.raw.substitute_eq_self_of_scoped_agreement body.isScoped
            (numeralClosingSubstitution values)
            (fun index impossible =>
              (Nat.not_lt_zero index impossible).elim)
        have closedEquals : body.closeWithNumerals values = body :=
          ScopedFormula.eq_of_raw_eq unchanged
        have targetEquals : body.existsManyBlock = body := by
          apply ScopedFormula.eq_of_raw_eq
          rfl
        exact Eq.mpr (congrArg
          (fun formula => Derivation LogicMode.intuitionistic haTheory
            FormulaContext.nil formula)
          targetEquals)
          (Eq.mp (congrArg
            (fun formula => Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil formula)
            closedEquals)
            proof))
    (fun count previous body values proof =>
      by
        let head := values.getD 0
        let tail := values.tailD
        have rebuilt : NatVector.cons head tail = values :=
          values.rebuildD
        have rebuiltClosed :
            body.closeWithNumerals (NatVector.cons head tail) =
              body.closeWithNumerals values :=
          congrArg body.closeWithNumerals rebuilt
        have rebuiltProof : Derivation LogicMode.intuitionistic haTheory
            FormulaContext.nil
            (body.closeWithNumerals (NatVector.cons head tail)) :=
          Eq.mpr (congrArg
            (fun formula => Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil formula)
            rebuiltClosed)
            proof
        let partialFormula := body.closeTailWithNumerals tail
        have instantiated : Derivation LogicMode.intuitionistic haTheory
            FormulaContext.nil
            (partialFormula.instantiate (ScopedTerm.numeral 0 head)) :=
          Eq.mp (congrArg
            (fun formula => Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil formula)
            (body.closeWithNumerals_cons head tail).symm)
            rebuiltProof
        let existential : Derivation LogicMode.intuitionistic haTheory
            FormulaContext.nil (ScopedFormula.ex partialFormula) :=
          Derivation.existentialIntroduction (ScopedTerm.numeral 0 head)
            instantiated
        have closedExistential :
            (ScopedFormula.ex body).closeWithNumerals tail =
              ScopedFormula.ex partialFormula :=
          body.ex_closeWithNumerals tail
        have recursiveInput : Derivation LogicMode.intuitionistic haTheory
            FormulaContext.nil
            ((ScopedFormula.ex body).closeWithNumerals tail) :=
          Eq.mpr (congrArg
            (fun formula => Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil formula)
            closedExistential)
            existential
        exact previous (ScopedFormula.ex body) tail recursiveInput)

def Derivation.introduceExistsMany
    {count : Nat}
    (body : ScopedFormula count)
    (values : NatVector count)
    (proof : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.closeWithNumerals values)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      body.existsManyBlock :=
  Derivation.introduceExistsManyByCount count body values proof

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitute_closeCons
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.introduceExistsMany
/- AXIOM_AUDIT_END -/
