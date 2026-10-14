import RelationalPerimeter.Constitution.HeytingArithmetic.InternalBoundedCases

/-!
# Proof-producing finite bounded universal reasoning
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem RawTerm.rename_eq_self_of_wellScoped
    (term : RawTerm)
    (bound : Nat)
    (isScoped : term.WellScoped bound)
    (renameMap : Renaming)
    (fixed : (index : Nat) -> index < bound -> renameMap index = index) :
    term.rename renameMap = term := by
  induction term with
  | bvar index => exact congrArg RawTerm.bvar (fixed index isScoped)
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ (inductionHypothesis isScoped)
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add
        (leftHypothesis isScoped.1) (rightHypothesis isScoped.2)
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul
        (leftHypothesis isScoped.1) (rightHypothesis isScoped.2)

private theorem RawFormula.rename_eq_self_of_wellScoped
    (formula : RawFormula)
    (bound : Nat)
    (isScoped : formula.WellScoped bound)
    (renameMap : Renaming)
    (fixed : (index : Nat) -> index < bound -> renameMap index = index) :
    formula.rename renameMap = formula := by
  induction formula generalizing bound renameMap with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.rename_eq_self_of_wellScoped bound isScoped.1 renameMap fixed)
        (right.rename_eq_self_of_wellScoped bound isScoped.2 renameMap fixed)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis bound isScoped.1 renameMap fixed)
        (rightHypothesis bound isScoped.2 renameMap fixed)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis bound isScoped.1 renameMap fixed)
        (rightHypothesis bound isScoped.2 renameMap fixed)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis bound isScoped.1 renameMap fixed)
        (rightHypothesis bound isScoped.2 renameMap fixed)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftRenaming renameMap)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg Nat.succ
            (fixed index (Nat.lt_of_succ_lt_succ bounded))
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftRenaming renameMap)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg Nat.succ
            (fixed index (Nat.lt_of_succ_lt_succ bounded))

private theorem RawTerm.substitute_eq_self_of_wellScoped
    (term : RawTerm)
    (bound : Nat)
    (isScoped : term.WellScoped bound)
    (substitution : Substitution)
    (fixed : (index : Nat) -> index < bound ->
      substitution index = RawTerm.bvar index) :
    term.substitute substitution = term := by
  induction term with
  | bvar index => exact fixed index isScoped
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ (inductionHypothesis isScoped)
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add
        (leftHypothesis isScoped.1) (rightHypothesis isScoped.2)
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul
        (leftHypothesis isScoped.1) (rightHypothesis isScoped.2)

private theorem RawFormula.substitute_eq_self_of_wellScoped
    (formula : RawFormula)
    (bound : Nat)
    (isScoped : formula.WellScoped bound)
    (substitution : Substitution)
    (fixed : (index : Nat) -> index < bound ->
      substitution index = RawTerm.bvar index) :
    formula.substitute substitution = formula := by
  induction formula generalizing bound substitution with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.substitute_eq_self_of_wellScoped bound isScoped.1
          substitution fixed)
        (right.substitute_eq_self_of_wellScoped bound isScoped.2
          substitution fixed)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis bound isScoped.1 substitution fixed)
        (rightHypothesis bound isScoped.2 substitution fixed)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis bound isScoped.1 substitution fixed)
        (rightHypothesis bound isScoped.2 substitution fixed)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis bound isScoped.1 substitution fixed)
        (rightHypothesis bound isScoped.2 substitution fixed)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftSubstitution substitution)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (fixed index (Nat.lt_of_succ_lt_succ bounded))
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftSubstitution substitution)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (fixed index (Nat.lt_of_succ_lt_succ bounded))

def ScopedFormula.asNewestTemplate
    (formula : ScopedFormula 1) : ScopedFormula 2 :=
  { raw := formula.raw
    isScoped := formula.raw.wellScoped_mono (Nat.succ_le_succ (Nat.zero_le 1))
      formula.isScoped }

def consumeBoundedCases
    (body : ScopedFormula 1) :
    (bound : Nat) ->
    ((index : Nat) -> index < bound ->
      Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
        (body.instantiate (ScopedTerm.numeral 0 index))) ->
    (context : FormulaContext 1) ->
    Derivation LogicMode.intuitionistic haTheory context (boundedCasesBody bound) ->
      Derivation LogicMode.intuitionistic haTheory context body
  | 0, _instances, context, impossible =>
      Derivation.falsumElimination impossible
  | Nat.succ bound, instances, context, casesProof => by
      let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
      let equality := ScopedFormula.equal value
        (ScopedTerm.numeral 1 bound)
      let leftContext := FormulaContext.cons equality context
      let equalityProof : Derivation LogicMode.intuitionistic haTheory leftContext
          equality := Derivation.hypothesis ContextMember.here
      let atNumeralClosed := instances bound (Nat.lt_succ_self bound)
      have atNumeral : Derivation LogicMode.intuitionistic haTheory leftContext
          ((body.asNewestTemplate).instantiate
            (ScopedTerm.numeral 1 bound)) := by
        have lifted := atNumeralClosed.liftVariables
        have liftedClosed : Derivation LogicMode.intuitionistic haTheory
            FormulaContext.nil
            (body.instantiate (ScopedTerm.numeral 0 bound)).lift := by
          simpa [FormulaContext.lift] using lifted
        have sameConclusion :
            (body.instantiate (ScopedTerm.numeral 0 bound)).lift =
              (body.asNewestTemplate).instantiate
                (ScopedTerm.numeral 1 bound) := by
          apply ScopedFormula.eq_of_raw_eq
          change
            (body.raw.substitute
              (singleTermSubstitution (RawTerm.numeral bound))).rename
                Nat.succ =
              body.raw.substitute
                (singleTermSubstitution (RawTerm.numeral bound))
          apply RawFormula.rename_eq_self_of_wellScoped _ 0
          · exact (body.instantiate
              (ScopedTerm.numeral 0 bound)).isScoped
          · intro index bounded
            exact (Nat.not_lt_zero index bounded).elim
        exact (Derivation.castConclusion sameConclusion liftedClosed)
          |>.weakenClosedTo leftContext
      have leftBranch : Derivation LogicMode.intuitionistic haTheory leftContext
          body := by
        have transported := transportFormulaAlongEquality
          body.asNewestTemplate (Derivation.equalitySymmetry equalityProof)
          atNumeral
        have sameConclusion :
            body.asNewestTemplate.instantiate value = body := by
          apply ScopedFormula.eq_of_raw_eq
          apply RawFormula.substitute_eq_self_of_wellScoped
            body.raw 1 body.isScoped
          intro index bounded
          cases index with
          | zero => rfl
          | succ index =>
              exact (Nat.not_lt_of_ge
                (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim
        exact Derivation.castConclusion sameConclusion transported
      let rightContext := FormulaContext.cons (boundedCasesBody bound) context
      let earlierCases : Derivation LogicMode.intuitionistic haTheory rightContext
          (boundedCasesBody bound) :=
        Derivation.hypothesis ContextMember.here
      let earlierInstances := fun index bounded =>
        instances index (Nat.lt_trans bounded (Nat.lt_succ_self bound))
      let rightBranch := consumeBoundedCases body bound earlierInstances
        rightContext earlierCases
      exact Derivation.disjunctionElimination casesProof leftBranch rightBranch

def proveBoundedUniversal
    (body : ScopedFormula 1)
    (bound : Nat)
    (instances : (index : Nat) -> index < bound ->
      Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
        (body.instantiate (ScopedTerm.numeral 0 index))) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl (lessThanNumeralBody bound) body)) := by
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let context := FormulaContext.cons (lessThanNumeralBody bound)
    FormulaContext.nil
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  let lessProof : Derivation LogicMode.intuitionistic haTheory context
      (lessThanNumeralBody bound) :=
    Derivation.hypothesis ContextMember.here
  let casesBody := ScopedFormula.impl (lessThanNumeralBody bound)
    (boundedCasesBody bound)
  let liftedCasesBody : ScopedFormula 2 :=
    { raw := casesBody.raw
      isScoped := casesBody.raw.wellScoped_mono
        (Nat.succ_le_succ (Nat.zero_le 1)) casesBody.isScoped }
  let liftedCasesSource := (boundedCasesProof bound).liftVariables
  have liftedCasesExact :
      (boundedCasesStatement bound).lift =
        ScopedFormula.all liftedCasesBody := by
    apply ScopedFormula.eq_of_raw_eq
    apply congrArg RawFormula.all
    apply RawFormula.rename_eq_self_of_wellScoped casesBody.raw 1
      casesBody.isScoped (liftRenaming Nat.succ)
    intro index bounded
    cases index with
    | zero => rfl
    | succ index =>
        exact (Nat.not_lt_of_ge
          (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim
  have liftedCases : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil (ScopedFormula.all liftedCasesBody) := by
    simpa [FormulaContext.lift] using
      Derivation.castConclusion liftedCasesExact liftedCasesSource
  let casesImplicationRaw := Derivation.universalElimination value liftedCases
  have casesInstantiationExact :
      liftedCasesBody.instantiate value = casesBody := by
    apply ScopedFormula.eq_of_raw_eq
    apply RawFormula.substitute_eq_self_of_wellScoped
      casesBody.raw 1 casesBody.isScoped
    intro index bounded
    cases index with
    | zero => rfl
    | succ index =>
        exact (Nat.not_lt_of_ge
          (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim
  let casesImplicationClosed := Derivation.castConclusion
    casesInstantiationExact casesImplicationRaw
  have casesImplication : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.impl (lessThanNumeralBody bound)
        (boundedCasesBody bound)) := by
    apply Derivation.weakenClosedTo context
    exact casesImplicationClosed
  let casesProof := Derivation.implicationElimination casesImplication lessProof
  exact consumeBoundedCases body bound instances context casesProof

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.consumeBoundedCases
#print axioms RelationalPerimeter.HeytingArithmetic.proveBoundedUniversal
/- AXIOM_AUDIT_END -/
