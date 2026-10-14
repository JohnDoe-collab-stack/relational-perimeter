import RelationalPerimeter.Constitution.HeytingArithmetic.InternalDerivationTools

/-!
# Finite internal case analysis below a concrete numeral
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem RawTerm.numeral_substitute_any
    (value : Nat) (substitution : Substitution) :
    (RawTerm.numeral value).substitute substitution =
      RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change RawTerm.succ
          ((RawTerm.numeral value).substitute substitution) =
        RawTerm.succ (RawTerm.numeral value)
      rw [inductionHypothesis]

private theorem RawTerm.numeral_rename_any
    (value : Nat) (rho : Renaming) :
    (RawTerm.numeral value).rename rho = RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change RawTerm.succ ((RawTerm.numeral value).rename rho) =
        RawTerm.succ (RawTerm.numeral value)
      rw [inductionHypothesis]

private theorem RawFormula.instantiate_shifted_add_succ_equation
    (left right replacement : RawTerm) :
    (RawFormula.equal
        (RawTerm.add left.shift (RawTerm.succ (RawTerm.bvar 0)))
        right.shift).instantiateTerm replacement =
      RawFormula.equal
        (RawTerm.add left (RawTerm.succ replacement)) right := by
  apply congrArgTwo RawFormula.equal
  · apply congrArgTwo RawTerm.add
    · exact RawTerm.renameSucc_substituteSingle left replacement
    · rfl
  · exact RawTerm.renameSucc_substituteSingle right replacement

private theorem RawFormula.instantiate_shifted_add_succ_numeral_equation
    (left replacement : RawTerm) (value : Nat) :
    (RawFormula.equal
        (RawTerm.add left.shift (RawTerm.succ (RawTerm.bvar 0)))
        (RawTerm.numeral value)).instantiateTerm replacement =
      RawFormula.equal
        (RawTerm.add left (RawTerm.succ replacement))
        (RawTerm.numeral value) := by
  apply congrArgTwo RawFormula.equal
  · apply congrArgTwo RawTerm.add
    · exact RawTerm.renameSucc_substituteSingle left replacement
    · rfl
  · exact RawTerm.numeral_substitute_any value
      (singleTermSubstitution replacement)

private def ScopedFormula.liftBinder
    {bound : Nat}
    (formula : ScopedFormula (Nat.succ bound)) :
    ScopedFormula (Nat.succ (Nat.succ bound)) :=
  { raw := formula.raw.rename (liftRenaming Nat.succ)
    isScoped := formula.raw.wellScoped_rename formula.isScoped
      (liftRenaming Nat.succ)
      (liftRenaming_lt Nat.succ
        (fun _index bounded => Nat.succ_lt_succ bounded)) }

private theorem RawTerm.rename_congr_pointwise
    (term : RawTerm)
    (first second : Renaming)
    (same : (index : Nat) -> first index = second index) :
    term.rename first = term.rename second := by
  induction term with
  | bvar index => exact congrArg RawTerm.bvar (same index)
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

private theorem RawFormula.rename_congr_pointwise
    (formula : RawFormula)
    (first second : Renaming)
    (same : (index : Nat) -> first index = second index) :
    formula.rename first = formula.rename second := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.rename_congr_pointwise first second same)
        (right.rename_congr_pointwise first second same)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second same)
        (rightHypothesis first second same)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second same)
        (rightHypothesis first second same)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second same)
        (rightHypothesis first second same)
  | all body inductionHypothesis =>
      exact congrArg RawFormula.all
        (inductionHypothesis (liftRenaming first) (liftRenaming second)
          (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                exact congrArg Nat.succ (same index)))
  | ex body inductionHypothesis =>
      exact congrArg RawFormula.ex
        (inductionHypothesis (liftRenaming first) (liftRenaming second)
          (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                exact congrArg Nat.succ (same index)))

private theorem RawTerm.rename_compose_pointwise
    (term : RawTerm)
    (first second : Renaming) :
    (term.rename first).rename second =
      term.rename (fun index => second (first index)) := by
  induction term with
  | bvar _index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

private theorem RawFormula.rename_compose_pointwise
    (formula : RawFormula)
    (first second : Renaming) :
    (formula.rename first).rename second =
      formula.rename (fun index => second (first index)) := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.rename_compose_pointwise first second)
        (right.rename_compose_pointwise first second)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second)
        (rightHypothesis first second)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second)
        (rightHypothesis first second)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second)
        (rightHypothesis first second)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      exact (inductionHypothesis (liftRenaming first)
        (liftRenaming second)).trans
        (body.rename_congr_pointwise
          (fun index => liftRenaming second (liftRenaming first index))
          (liftRenaming (fun index => second (first index)))
          (fun index => by cases index <;> rfl))
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      exact (inductionHypothesis (liftRenaming first)
        (liftRenaming second)).trans
        (body.rename_congr_pointwise
          (fun index => liftRenaming second (liftRenaming first index))
          (liftRenaming (fun index => second (first index)))
          (fun index => by cases index <;> rfl))

private theorem RawTerm.substitute_eq_rename_of_wellScoped
    (term : RawTerm)
    (bound : Nat)
    (isScoped : term.WellScoped bound)
    (substitution : Substitution)
    (rho : Renaming)
    (same : (index : Nat) -> index < bound ->
      substitution index = RawTerm.bvar (rho index)) :
    term.substitute substitution = term.rename rho := by
  induction term generalizing bound substitution rho with
  | bvar index => exact same index isScoped
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ
        (inductionHypothesis bound isScoped substitution rho same)
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add
        (leftHypothesis bound isScoped.1 substitution rho same)
        (rightHypothesis bound isScoped.2 substitution rho same)
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul
        (leftHypothesis bound isScoped.1 substitution rho same)
        (rightHypothesis bound isScoped.2 substitution rho same)

private theorem RawFormula.substitute_eq_rename_of_wellScoped
    (formula : RawFormula)
    (bound : Nat)
    (isScoped : formula.WellScoped bound)
    (substitution : Substitution)
    (rho : Renaming)
    (same : (index : Nat) -> index < bound ->
      substitution index = RawTerm.bvar (rho index)) :
    formula.substitute substitution = formula.rename rho := by
  induction formula generalizing bound substitution rho with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.substitute_eq_rename_of_wellScoped bound isScoped.1
          substitution rho same)
        (right.substitute_eq_rename_of_wellScoped bound isScoped.2
          substitution rho same)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis bound isScoped.1 substitution rho same)
        (rightHypothesis bound isScoped.2 substitution rho same)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis bound isScoped.1 substitution rho same)
        (rightHypothesis bound isScoped.2 substitution rho same)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis bound isScoped.1 substitution rho same)
        (rightHypothesis bound isScoped.2 substitution rho same)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftSubstitution substitution) (liftRenaming rho)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (same index (Nat.lt_of_succ_lt_succ bounded))
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftSubstitution substitution) (liftRenaming rho)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (same index (Nat.lt_of_succ_lt_succ bounded))

private theorem RawTerm.rename_eq_self_of_wellScoped_local
    (term : RawTerm)
    (bound : Nat)
    (isScoped : term.WellScoped bound)
    (rho : Renaming)
    (fixed : (index : Nat) -> index < bound -> rho index = index) :
    term.rename rho = term := by
  induction term generalizing bound rho with
  | bvar index => exact congrArg RawTerm.bvar (fixed index isScoped)
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ
        (inductionHypothesis bound isScoped rho fixed)
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add
        (leftHypothesis bound isScoped.1 rho fixed)
        (rightHypothesis bound isScoped.2 rho fixed)
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul
        (leftHypothesis bound isScoped.1 rho fixed)
        (rightHypothesis bound isScoped.2 rho fixed)

private theorem RawFormula.rename_eq_self_of_wellScoped_local
    (formula : RawFormula)
    (bound : Nat)
    (isScoped : formula.WellScoped bound)
    (rho : Renaming)
    (fixed : (index : Nat) -> index < bound -> rho index = index) :
    formula.rename rho = formula := by
  induction formula generalizing bound rho with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.rename_eq_self_of_wellScoped_local bound isScoped.1 rho fixed)
        (right.rename_eq_self_of_wellScoped_local bound isScoped.2 rho fixed)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis bound isScoped.1 rho fixed)
        (rightHypothesis bound isScoped.2 rho fixed)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis bound isScoped.1 rho fixed)
        (rightHypothesis bound isScoped.2 rho fixed)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis bound isScoped.1 rho fixed)
        (rightHypothesis bound isScoped.2 rho fixed)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftRenaming rho)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg Nat.succ
            (fixed index (Nat.lt_of_succ_lt_succ bounded))
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis (Nat.succ bound) isScoped
        (liftRenaming rho)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg Nat.succ
            (fixed index (Nat.lt_of_succ_lt_succ bounded))

private theorem ScopedFormula.transport_raw_mpr
    {source target : Nat}
    (sameBound : source = target)
    (formula : ScopedFormula target) :
    (Eq.mpr (congrArg ScopedFormula sameBound) formula).raw = formula.raw := by
  cases sameBound
  rfl

private theorem ScopedFormula.liftMany_raw
    {bound : Nat}
    (count : Nat)
    (formula : ScopedFormula bound) :
    (ScopedFormula.liftMany count formula).raw =
      Nat.rec formula.raw
        (fun _previousCount previousRaw =>
          previousRaw.rename Nat.succ) count := by
  induction count with
  | zero =>
      exact ScopedFormula.transport_raw_mpr (Nat.zero_add bound) formula
  | succ count inductionHypothesis =>
      change
        (Eq.mpr (congrArg ScopedFormula (Nat.succ_add count bound))
          (ScopedFormula.lift (ScopedFormula.liftMany count formula))).raw = _
      rw [ScopedFormula.transport_raw_mpr (Nat.succ_add count bound)]
      change (ScopedFormula.liftMany count formula).raw.rename Nat.succ = _
      rw [inductionHypothesis]

def boundedCasesBody : Nat -> ScopedFormula 1
  | 0 => ScopedFormula.falsum 1
  | Nat.succ bound =>
      let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
      ScopedFormula.disj
        (ScopedFormula.equal value (ScopedTerm.numeral 1 bound))
        (boundedCasesBody bound)

def lessThanNumeralBody (bound : Nat) : ScopedFormula 1 :=
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  { raw := lessThanFormula value.raw (RawTerm.numeral bound)
    isScoped := lessThanFormula_wellScoped value.raw
      (RawTerm.numeral bound) value.isScoped
      (RawTerm.numeral_wellScoped bound 1) }

def boundedCasesStatement (bound : Nat) : ScopedFormula 0 :=
  ScopedFormula.all
    (ScopedFormula.impl (lessThanNumeralBody bound)
      (boundedCasesBody bound))

def boundedCasesZeroProof :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (boundedCasesStatement 0) := by
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  let gap := ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)
  let liftedValue := ScopedTerm.bvar 1
    (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
  let equationBody : ScopedFormula 2 :=
    ScopedFormula.equal
      (ScopedTerm.add liftedValue gap.succ)
      (ScopedTerm.zero 2)
  let lessHypothesis : Derivation LogicMode.intuitionistic haTheory
      (FormulaContext.cons (lessThanNumeralBody 0) FormulaContext.nil)
      (lessThanNumeralBody 0) :=
    Derivation.hypothesis ContextMember.here
  let branchContext := FormulaContext.cons equationBody
    (FormulaContext.cons (lessThanNumeralBody 0).lift FormulaContext.nil)
  let equation : Derivation LogicMode.intuitionistic haTheory branchContext
      equationBody := Derivation.hypothesis ContextMember.here
  let addSuccessor : Derivation LogicMode.intuitionistic haTheory branchContext
      (ScopedFormula.equal
        (ScopedTerm.add liftedValue gap.succ)
        (ScopedTerm.succ (ScopedTerm.add liftedValue gap))) :=
    Derivation.theoryAxiom
      (StandardArithmeticAxiom.addSuccessor liftedValue gap)
  let successorZero : Derivation LogicMode.intuitionistic haTheory branchContext
      (ScopedFormula.equal
        (ScopedTerm.succ (ScopedTerm.add liftedValue gap))
        (ScopedTerm.zero 2)) :=
    Derivation.equalityTransitivity
      (Derivation.equalitySymmetry addSuccessor) equation
  let nonzero : Derivation LogicMode.intuitionistic haTheory branchContext
      (ScopedFormula.neg
        (ScopedFormula.equal
          (ScopedTerm.succ (ScopedTerm.add liftedValue gap))
          (ScopedTerm.zero 2))) :=
    Derivation.theoryAxiom
      (StandardArithmeticAxiom.successorNotZero
        (ScopedTerm.add liftedValue gap))
  let contradiction : Derivation LogicMode.intuitionistic haTheory branchContext
      (ScopedFormula.falsum 1).lift := by
    simpa [ScopedFormula.lift, ScopedFormula.falsum,
      RawFormula.rename] using
      Derivation.implicationElimination nonzero successorZero
  have lessExact : lessThanNumeralBody 0 =
      ScopedFormula.ex equationBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedLess := Derivation.castConclusion lessExact lessHypothesis
  let eliminated := Derivation.existentialElimination
    (body := equationBody)
    (conclusion := ScopedFormula.falsum 1)
    normalizedLess contradiction
  simpa [boundedCasesStatement, boundedCasesBody, lessThanNumeralBody,
    scopedLessThanFormula, lessThanFormula, equationBody, value,
    liftedValue, gap, branchContext, ScopedFormula.lift,
    ScopedTerm.lift, FormulaContext.lift,
    RawFormula.rename, RawTerm.rename] using eliminated

def boundedCasesProof : (bound : Nat) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (boundedCasesStatement bound)
  | 0 => boundedCasesZeroProof
  | Nat.succ bound => by
      apply Derivation.universalIntroduction
      apply Derivation.implicationIntroduction
      let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
      let gap := ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)
      let liftedValue := ScopedTerm.bvar 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
      let equationBody : ScopedFormula 2 :=
        ScopedFormula.equal
          (ScopedTerm.add liftedValue gap.succ)
          (ScopedTerm.numeral 2 (Nat.succ bound))
      let lessHypothesis : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons (lessThanNumeralBody (Nat.succ bound))
            FormulaContext.nil)
          (lessThanNumeralBody (Nat.succ bound)) :=
        Derivation.hypothesis ContextMember.here
      let branchContext := FormulaContext.cons equationBody
        (FormulaContext.cons
          (lessThanNumeralBody (Nat.succ bound)).lift FormulaContext.nil)
      let gapZero := ScopedFormula.equal gap (ScopedTerm.zero 2)
      let predecessorBody : ScopedFormula 3 :=
        ScopedFormula.equal
          (ScopedTerm.bvar 1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
          (ScopedTerm.succ
            (ScopedTerm.bvar 0 (Nat.zero_lt_succ 2)))
      let gapCasesFormula := ScopedFormula.disj gapZero
        (ScopedFormula.ex predecessorBody)
      let liftedNaturalCasesBody : ScopedFormula 3 :=
        { raw := zeroOrSuccessorBody.raw
          isScoped := zeroOrSuccessorBody.raw.wellScoped_mono
            (Nat.succ_le_succ (Nat.zero_le 2))
            zeroOrSuccessorBody.isScoped }
      let liftedNaturalCases :=
        Derivation.liftVariables
          (Derivation.liftVariables zeroOrSuccessorProof)
      have liftedNaturalCasesExact :
          (ScopedFormula.all zeroOrSuccessorBody).lift.lift =
            ScopedFormula.all liftedNaturalCasesBody := by
        apply ScopedFormula.eq_of_raw_eq
        rfl
      let normalizedNaturalCases := Derivation.castConclusion
        liftedNaturalCasesExact liftedNaturalCases
      let gapCasesClosed := Derivation.universalElimination gap
        normalizedNaturalCases
      have gapCasesAtBranch : Derivation LogicMode.intuitionistic haTheory
          branchContext gapCasesFormula := by
        apply Derivation.weakenClosedTo branchContext
        simpa [gapCasesFormula, gapZero, gap, predecessorBody,
          zeroOrSuccessorBody, liftedNaturalCasesBody,
          ScopedFormula.instantiate,
          ScopedFormula.equal, ScopedFormula.disj, ScopedFormula.ex,
          ScopedTerm.instantiate,
          ScopedTerm.bvar, ScopedTerm.zero, ScopedTerm.succ,
          RawFormula.instantiateTerm, RawTerm.instantiateTerm,
          RawFormula.substitute, RawTerm.substitute,
          singleTermSubstitution, liftSubstitution,
          RawTerm.rename, RawTerm.raise,
          FormulaContext.lift]
          using gapCasesClosed
      let zeroContext := FormulaContext.cons gapZero branchContext
      let gapZeroProof : Derivation LogicMode.intuitionistic haTheory zeroContext
          gapZero := Derivation.hypothesis ContextMember.here
      let equationAtZeroContext : Derivation LogicMode.intuitionistic haTheory
          zeroContext equationBody :=
        Derivation.hypothesis (ContextMember.there ContextMember.here)
      let varyingGapBody : ScopedFormula 3 :=
        ScopedFormula.equal
          (ScopedTerm.add liftedValue.lift
            (ScopedTerm.succ
              (ScopedTerm.bvar 0 (Nat.zero_lt_succ 2))))
          (ScopedTerm.numeral 3 (Nat.succ bound))
      have equationWithZero : Derivation LogicMode.intuitionistic haTheory
          zeroContext
          (ScopedFormula.equal
            (ScopedTerm.add liftedValue (ScopedTerm.zero 2).succ)
            (ScopedTerm.numeral 2 (Nat.succ bound))) := by
        have atGapExact : varyingGapBody.instantiate gap = equationBody := by
          apply ScopedFormula.eq_of_raw_eq
          change
            (RawFormula.equal
                (RawTerm.add liftedValue.raw.shift
                  (RawTerm.succ (RawTerm.bvar 0)))
                (RawTerm.numeral (Nat.succ bound))).instantiateTerm
                gap.raw =
              RawFormula.equal
                (RawTerm.add liftedValue.raw (RawTerm.succ gap.raw))
                (RawTerm.numeral (Nat.succ bound))
          exact RawFormula.instantiate_shifted_add_succ_numeral_equation
            liftedValue.raw gap.raw (Nat.succ bound)
        let equationAtGap := Derivation.castConclusion atGapExact.symm
          equationAtZeroContext
        let transported := transportFormulaAlongEquality varyingGapBody
          gapZeroProof equationAtGap
        have atZeroExact :
            varyingGapBody.instantiate (ScopedTerm.zero 2) =
              ScopedFormula.equal
                (ScopedTerm.add liftedValue (ScopedTerm.zero 2).succ)
                (ScopedTerm.numeral 2 (Nat.succ bound)) := by
          apply ScopedFormula.eq_of_raw_eq
          change
            (RawFormula.equal
                (RawTerm.add liftedValue.raw.shift
                  (RawTerm.succ (RawTerm.bvar 0)))
                (RawTerm.numeral (Nat.succ bound))).instantiateTerm
                RawTerm.zero =
              RawFormula.equal
                (RawTerm.add liftedValue.raw (RawTerm.succ RawTerm.zero))
                (RawTerm.numeral (Nat.succ bound))
          exact RawFormula.instantiate_shifted_add_succ_numeral_equation
            liftedValue.raw RawTerm.zero (Nat.succ bound)
        exact Derivation.castConclusion atZeroExact transported
      let addOne : Derivation LogicMode.intuitionistic haTheory zeroContext
          (ScopedFormula.equal
            (ScopedTerm.add liftedValue (ScopedTerm.zero 2).succ)
            (ScopedTerm.succ
              (ScopedTerm.add liftedValue (ScopedTerm.zero 2)))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addSuccessor liftedValue
            (ScopedTerm.zero 2))
      let addZero : Derivation LogicMode.intuitionistic haTheory zeroContext
          (ScopedFormula.equal
            (ScopedTerm.add liftedValue (ScopedTerm.zero 2)) liftedValue) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addZero liftedValue)
      let successorAddZero := successorCongruenceAt addZero
      let successorEquation : Derivation LogicMode.intuitionistic haTheory
          zeroContext
          (ScopedFormula.equal liftedValue.succ
            (ScopedTerm.numeral 2 (Nat.succ bound))) :=
        Derivation.equalityTransitivity
          (Derivation.equalitySymmetry successorAddZero)
          (Derivation.equalityTransitivity
            (Derivation.equalitySymmetry addOne) equationWithZero)
      let predecessorEquality : Derivation LogicMode.intuitionistic haTheory
          zeroContext
          (ScopedFormula.equal liftedValue
            (ScopedTerm.numeral 2 bound)) :=
        Derivation.implicationElimination
          (Derivation.theoryAxiom
            (StandardArithmeticAxiom.successorInjective liftedValue
              (ScopedTerm.numeral 2 bound)))
          successorEquation
      let zeroBranch :=
        Derivation.disjunctionIntroductionLeft
          (right := (boundedCasesBody bound).lift) predecessorEquality
      let successorExistential := ScopedFormula.ex predecessorBody
      let successorContext := FormulaContext.cons successorExistential
        branchContext
      let successorHypothesis : Derivation LogicMode.intuitionistic haTheory
          successorContext successorExistential :=
        Derivation.hypothesis ContextMember.here
      let predecessor := ScopedTerm.bvar 0 (Nat.zero_lt_succ 2)
      let liftedGap := ScopedTerm.bvar 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
      let twiceLiftedValue := ScopedTerm.bvar 2
        (Nat.succ_lt_succ
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
      let predecessorEquation : ScopedFormula 3 := predecessorBody
      let predecessorContext := FormulaContext.cons predecessorEquation
        (FormulaContext.cons successorExistential.lift branchContext.lift)
      let predecessorEquationProof : Derivation LogicMode.intuitionistic haTheory
          predecessorContext predecessorEquation :=
        Derivation.hypothesis ContextMember.here
      let liftedEquation : ScopedFormula 3 := equationBody.lift
      let equationInPredecessorContext : Derivation LogicMode.intuitionistic haTheory
          predecessorContext liftedEquation :=
        Derivation.hypothesis
          (ContextMember.there
            (ContextMember.there ContextMember.here))
      let varyingLiftedGapBody : ScopedFormula 4 :=
        ScopedFormula.equal
          (ScopedTerm.add twiceLiftedValue.lift
            (ScopedTerm.succ
              (ScopedTerm.bvar 0 (Nat.zero_lt_succ 3))))
          (ScopedTerm.numeral 4 (Nat.succ bound))
      let explicitLiftedEquation : ScopedFormula 3 :=
        ScopedFormula.equal
          (ScopedTerm.add twiceLiftedValue liftedGap.succ)
          (ScopedTerm.numeral 3 (Nat.succ bound))
      have equationWithSuccessor : Derivation LogicMode.intuitionistic haTheory
          predecessorContext
          (ScopedFormula.equal
            (ScopedTerm.add twiceLiftedValue predecessor.succ.succ)
            (ScopedTerm.numeral 3 (Nat.succ bound))) := by
        have liftedEquationExact : liftedEquation =
            explicitLiftedEquation := by
          apply ScopedFormula.eq_of_raw_eq
          apply congrArgTwo RawFormula.equal
          · rfl
          · exact RawTerm.numeral_rename_any (Nat.succ bound) Nat.succ
        let explicitEquation := Derivation.castConclusion liftedEquationExact
          equationInPredecessorContext
        have atGapExact : varyingLiftedGapBody.instantiate liftedGap =
            explicitLiftedEquation := by
          apply ScopedFormula.eq_of_raw_eq
          change
            (RawFormula.equal
                (RawTerm.add twiceLiftedValue.raw.shift
                  (RawTerm.succ (RawTerm.bvar 0)))
                (RawTerm.numeral (Nat.succ bound))).instantiateTerm
                liftedGap.raw =
              RawFormula.equal
                (RawTerm.add twiceLiftedValue.raw
                  (RawTerm.succ liftedGap.raw))
                (RawTerm.numeral (Nat.succ bound))
          exact RawFormula.instantiate_shifted_add_succ_numeral_equation
            twiceLiftedValue.raw liftedGap.raw (Nat.succ bound)
        let equationAtGap := Derivation.castConclusion atGapExact.symm
          explicitEquation
        let transported := transportFormulaAlongEquality varyingLiftedGapBody
          predecessorEquationProof equationAtGap
        have atSuccessorExact :
            varyingLiftedGapBody.instantiate predecessor.succ =
              ScopedFormula.equal
                (ScopedTerm.add twiceLiftedValue predecessor.succ.succ)
                (ScopedTerm.numeral 3 (Nat.succ bound)) := by
          apply ScopedFormula.eq_of_raw_eq
          change
            (RawFormula.equal
                (RawTerm.add twiceLiftedValue.raw.shift
                  (RawTerm.succ (RawTerm.bvar 0)))
                (RawTerm.numeral (Nat.succ bound))).instantiateTerm
                predecessor.succ.raw =
              RawFormula.equal
                (RawTerm.add twiceLiftedValue.raw
                  (RawTerm.succ predecessor.succ.raw))
                (RawTerm.numeral (Nat.succ bound))
          exact RawFormula.instantiate_shifted_add_succ_numeral_equation
            twiceLiftedValue.raw predecessor.succ.raw (Nat.succ bound)
        exact Derivation.castConclusion atSuccessorExact transported
      let unfoldSecondSuccessor : Derivation LogicMode.intuitionistic haTheory
          predecessorContext
          (ScopedFormula.equal
            (ScopedTerm.add twiceLiftedValue predecessor.succ.succ)
            (ScopedTerm.succ
              (ScopedTerm.add twiceLiftedValue predecessor.succ))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addSuccessor twiceLiftedValue
            predecessor.succ)
      let successorReduced : Derivation LogicMode.intuitionistic haTheory
          predecessorContext
          (ScopedFormula.equal
            (ScopedTerm.succ
              (ScopedTerm.add twiceLiftedValue predecessor.succ))
            (ScopedTerm.numeral 3 (Nat.succ bound))) :=
        Derivation.equalityTransitivity
          (Derivation.equalitySymmetry unfoldSecondSuccessor)
          equationWithSuccessor
      let reducedEquation : Derivation LogicMode.intuitionistic haTheory
          predecessorContext
          (ScopedFormula.equal
            (ScopedTerm.add twiceLiftedValue predecessor.succ)
            (ScopedTerm.numeral 3 bound)) :=
        Derivation.implicationElimination
          (Derivation.theoryAxiom
            (StandardArithmeticAxiom.successorInjective
              (ScopedTerm.add twiceLiftedValue predecessor.succ)
              (ScopedTerm.numeral 3 bound)))
          successorReduced
      let lessAtValue : ScopedFormula 3 :=
        { raw := (lessThanNumeralBody bound).raw.substitute
            (singleTermSubstitution twiceLiftedValue.raw)
          isScoped := (lessThanNumeralBody bound).raw.wellScoped_substitute
            (lessThanNumeralBody bound).isScoped
            (singleTermSubstitution twiceLiftedValue.raw)
            (fun index bounded => by
              cases index with
              | zero => exact twiceLiftedValue.isScoped
              | succ index =>
                  exact (Nat.not_lt_of_ge
                    (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim) }
      let lessWitnessBody : ScopedFormula 4 :=
        { raw := RawFormula.equal
            (RawTerm.add twiceLiftedValue.raw.shift
              (RawTerm.succ (RawTerm.bvar 0)))
            (RawTerm.numeral bound).shift
          isScoped := (lessThanFormula_wellScoped twiceLiftedValue.raw
            (RawTerm.numeral bound) twiceLiftedValue.isScoped
            (RawTerm.numeral_wellScoped bound 3)) }
      have witnessExact : lessWitnessBody.instantiate predecessor =
          ScopedFormula.equal
            (ScopedTerm.add twiceLiftedValue predecessor.succ)
            (ScopedTerm.numeral 3 bound) := by
        apply ScopedFormula.eq_of_raw_eq
        exact RawFormula.instantiate_shifted_add_succ_equation
          twiceLiftedValue.raw (RawTerm.numeral bound) predecessor.raw
      let normalizedEquation := Derivation.castConclusion witnessExact.symm
        reducedEquation
      let lessWitness := Derivation.existentialIntroduction
        (body := lessWitnessBody) predecessor normalizedEquation
      have lessWitnessExact : lessWitnessBody.ex = lessAtValue := by
        apply ScopedFormula.eq_of_raw_eq
        apply congrArg RawFormula.ex
        apply congrArgTwo RawFormula.equal
        · apply congrArgTwo RawTerm.add
          · rfl
          · rfl
        · change (RawTerm.numeral bound).rename Nat.succ =
            ((RawTerm.numeral bound).rename Nat.succ).substitute
              (liftSubstitution
                (singleTermSubstitution twiceLiftedValue.raw))
          rw [RawTerm.numeral_rename_any]
          rw [RawTerm.numeral_substitute_any]
      have normalizedLess : Derivation LogicMode.intuitionistic haTheory
          predecessorContext lessAtValue := by
        exact Derivation.castConclusion lessWitnessExact lessWitness
      let recursiveCore := ScopedFormula.impl
        (lessThanNumeralBody bound) (boundedCasesBody bound)
      let recursiveUniversalBody :=
        recursiveCore.liftBinder.liftBinder.liftBinder
      let liftedRecursiveSource := (boundedCasesProof bound).liftMany 3
      have normalizedRecursiveSource : Derivation LogicMode.intuitionistic haTheory
          FormulaContext.nil
          (ScopedFormula.liftMany 3 (boundedCasesStatement bound)) := by
        simpa [FormulaContext.liftMany, FormulaContext.lift] using
          liftedRecursiveSource
      have liftedRecursiveExact :
          ScopedFormula.liftMany 3 (boundedCasesStatement bound) =
            ScopedFormula.all recursiveUniversalBody := by
        apply ScopedFormula.eq_of_raw_eq
        rfl
      let liftedRecursive := Derivation.castConclusion liftedRecursiveExact
        normalizedRecursiveSource
      let recursiveAtValueRaw := Derivation.universalElimination
        twiceLiftedValue liftedRecursive
      have recursiveAtValueExact :
          recursiveUniversalBody.instantiate twiceLiftedValue =
            ScopedFormula.impl lessAtValue
              (ScopedFormula.liftMany 2 (boundedCasesBody bound)) := by
        apply ScopedFormula.eq_of_raw_eq
        have binderStable :
            recursiveCore.raw.rename (liftRenaming Nat.succ) =
              recursiveCore.raw := by
          apply RawFormula.rename_eq_self_of_wellScoped_local
            recursiveCore.raw 1 recursiveCore.isScoped
          intro index bounded
          cases index with
          | zero => rfl
          | succ index =>
              exact (Nat.not_lt_of_ge
                (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim
        have liftedRaw : recursiveUniversalBody.raw =
            recursiveCore.raw := by
          change (((recursiveCore.raw.rename (liftRenaming Nat.succ)).rename
            (liftRenaming Nat.succ)).rename (liftRenaming Nat.succ)) =
              recursiveCore.raw
          rw [binderStable, binderStable, binderStable]
        let doubleSucc : Renaming := fun index => Nat.succ (Nat.succ index)
        have substitutionAsRename :
            recursiveCore.raw.substitute
                (singleTermSubstitution twiceLiftedValue.raw) =
              recursiveCore.raw.rename doubleSucc := by
          apply RawFormula.substitute_eq_rename_of_wellScoped
            recursiveCore.raw 1 recursiveCore.isScoped
          intro index bounded
          cases index with
          | zero => rfl
          | succ index =>
              exact (Nat.not_lt_of_ge
                (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim
        have doubleRename :
            (recursiveCore.raw.rename Nat.succ).rename Nat.succ =
              recursiveCore.raw.rename doubleSucc := by
          exact recursiveCore.raw.rename_compose_pointwise
            Nat.succ Nat.succ
        have renamedCoreExact :
            (recursiveCore.raw.rename Nat.succ).rename Nat.succ =
              (ScopedFormula.impl lessAtValue
                (ScopedFormula.liftMany 2
                  (boundedCasesBody bound))).raw := by
          have lessSubstitutionAsRename :
              (lessThanNumeralBody bound).raw.substitute
                  (singleTermSubstitution twiceLiftedValue.raw) =
                (lessThanNumeralBody bound).raw.rename doubleSucc := by
            apply RawFormula.substitute_eq_rename_of_wellScoped
              (lessThanNumeralBody bound).raw 1
              (lessThanNumeralBody bound).isScoped
            intro index bounded
            cases index with
            | zero => rfl
            | succ index =>
                exact (Nat.not_lt_of_ge
                  (Nat.succ_le_succ (Nat.zero_le index)) bounded).elim
          have lessDoubleRename :
              ((lessThanNumeralBody bound).raw.rename Nat.succ).rename
                  Nat.succ =
                (lessThanNumeralBody bound).raw.rename doubleSucc :=
            (lessThanNumeralBody bound).raw.rename_compose_pointwise
              Nat.succ Nat.succ
          have lessInstantiation :
              (lessThanNumeralBody bound).raw.substitute
                  (singleTermSubstitution twiceLiftedValue.raw) =
                lessAtValue.raw := by
            rfl
          apply congrArgTwo RawFormula.impl
          · exact lessDoubleRename.trans
              (lessSubstitutionAsRename.symm.trans lessInstantiation)
          · rw [ScopedFormula.liftMany_raw]
            rfl
        calc
          (recursiveUniversalBody.instantiate twiceLiftedValue).raw =
              recursiveCore.raw.substitute
                (singleTermSubstitution twiceLiftedValue.raw) := by
            change recursiveUniversalBody.raw.substitute
                (singleTermSubstitution twiceLiftedValue.raw) = _
            rw [liftedRaw]
          _ = recursiveCore.raw.rename doubleSucc := substitutionAsRename
          _ = (recursiveCore.raw.rename Nat.succ).rename Nat.succ :=
            doubleRename.symm
          _ = (ScopedFormula.impl lessAtValue
                (ScopedFormula.liftMany 2
                  (boundedCasesBody bound))).raw := renamedCoreExact
      have recursiveAtValue : Derivation LogicMode.intuitionistic haTheory
          FormulaContext.nil
          (ScopedFormula.impl lessAtValue
            (ScopedFormula.liftMany 2 (boundedCasesBody bound))) := by
        exact Derivation.castConclusion recursiveAtValueExact
          recursiveAtValueRaw
      let recursiveInContext :=
        recursiveAtValue.weakenClosedTo predecessorContext
      let earlierCases := Derivation.implicationElimination
        recursiveInContext normalizedLess
      let successorInnerBranch :=
        Derivation.disjunctionIntroductionRight
          (left := ScopedFormula.equal twiceLiftedValue
            (ScopedTerm.numeral 3 bound)) earlierCases
      have successorConclusionExact :
          (ScopedFormula.disj
            (ScopedFormula.equal twiceLiftedValue
              (ScopedTerm.numeral 3 bound))
            (ScopedFormula.liftMany 2 (boundedCasesBody bound))) =
            (boundedCasesBody (Nat.succ bound)).lift.lift := by
        apply ScopedFormula.eq_of_raw_eq
        change RawFormula.disj _
            (ScopedFormula.liftMany 2 (boundedCasesBody bound)).raw = _
        rw [ScopedFormula.liftMany_raw]
        change
          RawFormula.disj
              (RawFormula.equal (RawTerm.bvar 2)
                (RawTerm.numeral bound))
              (((boundedCasesBody bound).raw.rename Nat.succ).rename
                Nat.succ) =
            ((RawFormula.disj
                (RawFormula.equal (RawTerm.bvar 0)
                  (RawTerm.numeral bound))
                (boundedCasesBody bound).raw).rename Nat.succ).rename
              Nat.succ
        apply congrArgTwo RawFormula.disj
        · apply congrArgTwo RawFormula.equal
          · rfl
          · rw [RawTerm.numeral_rename_any]
            rw [RawTerm.numeral_rename_any]
        · rfl
      let normalizedInnerConclusion := Derivation.castConclusion
        successorConclusionExact successorInnerBranch
      have normalizedInnerContext : Derivation LogicMode.intuitionistic haTheory
          (FormulaContext.cons predecessorBody successorContext.lift)
          (boundedCasesBody (Nat.succ bound)).lift.lift := by
        simpa [predecessorContext, predecessorEquation, successorContext,
          FormulaContext.lift]
          using normalizedInnerConclusion
      let successorBranch := Derivation.existentialElimination
        (conclusion := (boundedCasesBody (Nat.succ bound)).lift)
        successorHypothesis normalizedInnerContext
      have zeroConclusionExact :
          (ScopedFormula.disj
            (ScopedFormula.equal liftedValue
              (ScopedTerm.numeral 2 bound))
            (boundedCasesBody bound).lift) =
            (boundedCasesBody (Nat.succ bound)).lift := by
        apply ScopedFormula.eq_of_raw_eq
        change
          RawFormula.disj
              (RawFormula.equal (RawTerm.bvar 1)
                (RawTerm.numeral bound))
              ((boundedCasesBody bound).raw.rename Nat.succ) =
            (RawFormula.disj
              (RawFormula.equal (RawTerm.bvar 0)
                (RawTerm.numeral bound))
              (boundedCasesBody bound).raw).rename Nat.succ
        apply congrArgTwo RawFormula.disj
        · apply congrArgTwo RawFormula.equal
          · rfl
          · rw [RawTerm.numeral_rename_any]
        · rfl
      let normalizedZeroBranch := Derivation.castConclusion
        zeroConclusionExact zeroBranch
      let casesInBranch := Derivation.disjunctionElimination
        (conclusion := (boundedCasesBody (Nat.succ bound)).lift)
        gapCasesAtBranch normalizedZeroBranch successorBranch
      have lessExact : lessThanNumeralBody (Nat.succ bound) =
          ScopedFormula.ex equationBody := by
        apply ScopedFormula.eq_of_raw_eq
        apply congrArg RawFormula.ex
        apply congrArgTwo RawFormula.equal
        · rfl
        · exact RawTerm.numeral_rename_any (Nat.succ bound) Nat.succ
      let normalizedLessHypothesis := Derivation.castConclusion lessExact
        lessHypothesis
      let eliminated := Derivation.existentialElimination
        (body := equationBody)
        (conclusion := boundedCasesBody (Nat.succ bound))
        normalizedLessHypothesis casesInBranch
      exact eliminated

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.boundedCasesZeroProof
#print axioms RelationalPerimeter.HeytingArithmetic.boundedCasesProof
/- AXIOM_AUDIT_END -/
