import RelationalPerimeter.Constitution.HeytingArithmetic.InternalExistentialBlocks
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveEvaluation

/-!
# Proof-producing internal representation of primitive-recursive programs

This module complements semantic representability with actual object-language
derivations.  The construction is structural on the positive `PRFunction`
tree and never appeals to semantic truth as an inference rule.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def NatVector.numeralTerms :
    {arity : Nat} -> NatVector arity -> RawTermVector arity :=
  fun {arity} values =>
    match values with
    | NatVector.nil => RawTermVector.nil
    | NatVector.cons head tail =>
        RawTermVector.cons (RawTerm.numeral head) tail.numeralTerms

theorem NatVector.numeralTerms_wellScoped
    {arity bound : Nat}
    (values : NatVector arity) :
    values.numeralTerms.WellScoped bound :=
  NatVector.rec
    (motive := fun _length vector =>
      vector.numeralTerms.WellScoped bound)
    trivial
    (fun head _tail tailScoped =>
      And.intro (RawTerm.numeral_wellScoped head bound) tailScoped)
    values

theorem numeralClosingSubstitutionAtDepth_wellScoped
    {count : Nat}
    (values : NatVector count)
    (depth index : Nat)
    (bounded : index < depth + count) :
    (numeralClosingSubstitutionAtDepth values depth index).WellScoped depth := by
  induction depth generalizing index with
  | zero =>
      exact RawTerm.numeral_wellScoped (values.getD index) 0
  | succ depth inductionHypothesis =>
      rw [numeralClosingSubstitutionAtDepth_succ]
      apply liftSubstitution_wellScoped
      · intro inner innerBound
        exact inductionHypothesis inner innerBound
      · exact Eq.mp
          (congrArg (fun upper => index < upper)
          (Nat.succ_add depth count))
          bounded

private theorem internalLiftSubstitutionCompose
    (first second : Substitution)
    (index : Nat) :
    (liftSubstitution first index).substitute (liftSubstitution second) =
      liftSubstitution (fun inner => (first inner).substitute second) index := by
  cases index with
  | zero => rfl
  | succ index =>
      exact RawTerm.renameSucc_substituteLift_local (first index) second

theorem RawTerm.internalSubstituteCompose
    (term : RawTerm)
    (first second : Substitution) :
    (term.substitute first).substitute second =
      term.substitute (fun index => (first index).substitute second) := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawTerm.internalSubstituteCongr
    (term : RawTerm)
    (first second : Substitution)
    (pointwise : (index : Nat) -> first index = second index) :
    term.substitute first = term.substitute second := by
  induction term with
  | bvar index => exact pointwise index
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawFormula.internalSubstituteCongr
    (formula : RawFormula)
    (first second : Substitution)
    (pointwise : (index : Nat) -> first index = second index) :
    formula.substitute first = formula.substitute second := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.internalSubstituteCongr first second pointwise)
        (right.internalSubstituteCongr first second pointwise)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | all body inductionHypothesis =>
      exact congrArg RawFormula.all
        (inductionHypothesis (liftSubstitution first)
          (liftSubstitution second) (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                exact congrArg (fun term => term.rename Nat.succ)
                  (pointwise index)))
  | ex body inductionHypothesis =>
      exact congrArg RawFormula.ex
        (inductionHypothesis (liftSubstitution first)
          (liftSubstitution second) (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                exact congrArg (fun term => term.rename Nat.succ)
                  (pointwise index)))

theorem RawFormula.internalSubstituteCompose
    (formula : RawFormula)
    (first second : Substitution) :
    (formula.substitute first).substitute second =
      formula.substitute (fun index => (first index).substitute second) := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.internalSubstituteCompose first second)
        (right.internalSubstituteCompose first second)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second) (rightHypothesis first second)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second) (rightHypothesis first second)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second) (rightHypothesis first second)
  | all body inductionHypothesis =>
      exact congrArg RawFormula.all
        ((inductionHypothesis (liftSubstitution first)
          (liftSubstitution second)).trans
          (body.internalSubstituteCongr _ _
            (internalLiftSubstitutionCompose first second)))
  | ex body inductionHypothesis =>
      exact congrArg RawFormula.ex
        ((inductionHypothesis (liftSubstitution first)
          (liftSubstitution second)).trans
          (body.internalSubstituteCongr _ _
            (internalLiftSubstitutionCompose first second)))

theorem RawTerm.numeral_substitute
    (value : Nat)
    (substitution : Substitution) :
    (RawTerm.numeral value).substitute substitution =
      RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis

private theorem RawTerm.renameSucc_substituteNumeralClosingCons
    {count : Nat}
    (term : RawTerm)
    (head : Nat)
    (tail : NatVector count) :
    (term.rename Nat.succ).substitute
        (numeralClosingSubstitution (NatVector.cons head tail)) =
      term.substitute (numeralClosingSubstitution tail) := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

private theorem numeralClosing_inside
    {baseCount depth : Nat}
    (base : NatVector baseCount)
    (middle : NatVector depth)
    (index : Nat)
    (bounded : index < depth) :
    (numeralClosingSubstitutionAtDepth base depth index).substitute
        (numeralClosingSubstitution middle) =
      RawTerm.numeral (middle.getD index) := by
  induction middle generalizing index with
  | nil => exact (Nat.not_lt_zero index bounded).elim
  | @cons depth head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            ((numeralClosingSubstitutionAtDepth base depth index).rename
                Nat.succ).substitute
                (numeralClosingSubstitution (NatVector.cons head tail)) =
              RawTerm.numeral (tail.getD index)
          rw [RawTerm.renameSucc_substituteNumeralClosingCons]
          exact inductionHypothesis index (Nat.lt_of_succ_lt_succ bounded)

private theorem numeralClosing_after
    {baseCount depth : Nat}
    (base : NatVector baseCount)
    (middle : NatVector depth)
    (index : Nat) :
    (numeralClosingSubstitutionAtDepth base depth (depth + index)).substitute
        (numeralClosingSubstitution middle) =
      RawTerm.numeral (base.getD index) := by
  induction middle with
  | nil =>
      rw [Nat.zero_add]
      exact RawTerm.numeral_substitute (base.getD index)
        (numeralClosingSubstitution NatVector.nil)
  | @cons depth head tail inductionHypothesis =>
      rw [Nat.succ_add]
      change
        ((numeralClosingSubstitutionAtDepth base depth (depth + index)).rename
            Nat.succ).substitute
            (numeralClosingSubstitution (NatVector.cons head tail)) =
          RawTerm.numeral (base.getD index)
      rw [RawTerm.renameSucc_substituteNumeralClosingCons]
      exact inductionHypothesis

theorem RawTermVector.variables_getD_inside
    (start length index : Nat)
    (bounded : index < length) :
    (RawTermVector.variables start length).getD index =
      RawTerm.bvar (start + index) := by
  induction length generalizing start index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ length inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            (RawTermVector.variables (Nat.succ start) length).getD index =
              RawTerm.bvar (start + Nat.succ index)
          rw [Nat.add_succ]
          exact (inductionHypothesis (Nat.succ start) index
            (Nat.lt_of_succ_lt_succ bounded)).trans
            (congrArg RawTerm.bvar (Nat.succ_add start index))

theorem RawTermVector.variables_getD_outside
    (start length index : Nat)
    (outside : length <= index) :
    (RawTermVector.variables start length).getD index = RawTerm.zero := by
  induction length generalizing start index with
  | zero => cases index <;> rfl
  | succ length inductionHypothesis =>
      cases index with
      | zero => exact (Nat.not_succ_le_zero length outside).elim
      | succ index =>
          exact inductionHypothesis (Nat.succ start) index
            (Nat.le_of_succ_le_succ outside)

theorem NatVector.numeralTerms_getD
    {length : Nat}
    (values : NatVector length)
    (index : Nat) :
    values.numeralTerms.getD index = RawTerm.numeral (values.getD index) := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis index

theorem NatVector.getD_outside
    {length : Nat}
    (values : NatVector length)
    (index : Nat)
    (outside : length <= index) :
    values.getD index = 0 := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => exact (Nat.not_succ_le_zero _ outside).elim
      | succ index =>
          exact inductionHypothesis index (Nat.le_of_succ_le_succ outside)

private theorem outerApplication_close_exact
    {inputArity outputArity : Nat}
    (outer : ArithmeticGraph outputArity)
    (inputs : NatVector inputArity)
    (middle : NatVector outputArity)
    (output : Nat) :
    (((outer.apply (RawTerm.bvar outputArity)
          (RawTermVector.variables 0 outputArity)).substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons output inputs) outputArity)).substitute
        (numeralClosingSubstitution middle)) =
      outer.apply (RawTerm.numeral output) middle.numeralTerms := by
  rw [RawFormula.internalSubstituteCompose]
  unfold ArithmeticGraph.apply
  rw [RawFormula.internalSubstituteCompose]
  apply RawFormula.internalSubstituteCongr
  intro index
  cases index with
  | zero =>
      exact numeralClosing_after (NatVector.cons output inputs) middle 0
  | succ index =>
      simp only
      by_cases bounded : index < outputArity
      · rw [RawTermVector.variables_getD_inside 0 outputArity index bounded,
          Nat.zero_add]
        exact (numeralClosing_inside
          (NatVector.cons output inputs) middle index bounded).trans
          (middle.numeralTerms_getD index).symm
      · have outside : outputArity <= index := Nat.le_of_not_gt bounded
        rw [RawTermVector.variables_getD_outside 0 outputArity index outside]
        change RawTerm.zero = middle.numeralTerms.getD index
        rw [NatVector.numeralTerms_getD,
          NatVector.getD_outside middle index outside]
        rfl

private theorem innerApplication_close_exact
    {inputArity outputArity : Nat}
    (graph : ArithmeticGraph inputArity)
    (inputs : NatVector inputArity)
    (middle : NatVector outputArity)
    (output : Nat)
    (offset : Nat)
    (bounded : offset < outputArity) :
    (((graph.apply (RawTerm.bvar offset)
          (RawTermVector.variables (Nat.succ outputArity) inputArity)).substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons output inputs) outputArity)).substitute
        (numeralClosingSubstitution middle)) =
      graph.apply (RawTerm.numeral (middle.getD offset))
        inputs.numeralTerms := by
  rw [RawFormula.internalSubstituteCompose]
  unfold ArithmeticGraph.apply
  rw [RawFormula.internalSubstituteCompose]
  apply RawFormula.internalSubstituteCongr
  intro index
  cases index with
  | zero =>
      exact numeralClosing_inside
        (NatVector.cons output inputs) middle offset bounded
  | succ index =>
      simp only
      by_cases inputBounded : index < inputArity
      · rw [RawTermVector.variables_getD_inside
          (Nat.succ outputArity) inputArity index inputBounded]
        have positionEquality :
            Nat.succ outputArity + index = outputArity + Nat.succ index :=
          (Nat.succ_add outputArity index).trans
            (Nat.add_succ outputArity index).symm
        rw [positionEquality]
        exact (numeralClosing_after
          (NatVector.cons output inputs) middle (Nat.succ index)).trans
          (inputs.numeralTerms_getD index).symm
      · have outside : inputArity <= index := Nat.le_of_not_gt inputBounded
        rw [RawTermVector.variables_getD_outside
          (Nat.succ outputArity) inputArity index outside]
        change RawTerm.zero = inputs.numeralTerms.getD index
        rw [NatVector.numeralTerms_getD,
          NatVector.getD_outside inputs index outside]
        rfl

theorem RawFormula.existsMany_substitute_numeralClosing
    {count : Nat}
    (formula : RawFormula)
    (values : NatVector count)
    (depth : Nat) :
    (formula.substitute
        (numeralClosingSubstitutionAtDepth values depth)).existsMany depth =
      (formula.existsMany depth).substitute
        (numeralClosingSubstitution values) := by
  induction depth generalizing formula with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [numeralClosingSubstitutionAtDepth_succ,
        RawFormula.existsMany_succ, RawFormula.existsMany_succ]
      exact inductionHypothesis (RawFormula.ex formula)

def ArithmeticGraph.numeralInstance
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (inputs : NatVector arity)
    (output : Nat) : ScopedFormula 0 :=
  { raw := graph.apply (RawTerm.numeral output) inputs.numeralTerms
    isScoped := graph.apply_wellScoped
      (RawTerm.numeral output) inputs.numeralTerms
      (RawTerm.numeral_wellScoped output 0)
      inputs.numeralTerms_wellScoped }

def PRFunction.numeralGraphInstance
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity)
    (output : Nat) : ScopedFormula 0 :=
  program.graphFormula.numeralInstance inputs output

def internalZeroGraphNumeralProof
    {arity : Nat}
    (inputs : NatVector arity)
    (output : Nat)
    (evaluation :
      PRFunction.Evaluates (PRFunction.zero : PRFunction arity)
        inputs output) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      ((PRFunction.zero : PRFunction arity).numeralGraphInstance
        inputs output) := by
  have outputZero : output = 0 := evaluation
  cases outputZero
  let expected := ScopedFormula.equal (ScopedTerm.zero 0) (ScopedTerm.zero 0)
  have sameFormula :
      (PRFunction.zero : PRFunction arity).numeralGraphInstance inputs 0 =
        expected := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  exact Eq.mp
    (congrArg
      (fun formula =>
        Derivation LogicMode.intuitionistic haTheory FormulaContext.nil formula)
      sameFormula.symm)
    (Derivation.equalityReflexivity (ScopedTerm.zero 0))

def internalSuccessorGraphNumeralProof
    (inputs : NatVector 1)
    (output : Nat)
    (evaluation :
      PRFunction.Evaluates PRFunction.successor inputs output) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (PRFunction.successor.numeralGraphInstance inputs output) := by
  have outputSuccessor : output = Nat.succ (inputs.getD 0) := evaluation
  cases outputSuccessor
  let expected := ScopedFormula.equal
    (ScopedTerm.numeral 0 (Nat.succ (inputs.getD 0)))
    (ScopedTerm.numeral 0 (Nat.succ (inputs.getD 0)))
  have sameFormula :
      PRFunction.successor.numeralGraphInstance inputs
        (Nat.succ (inputs.getD 0)) = expected := by
    apply ScopedFormula.eq_of_raw_eq
    change RawFormula.equal
      (RawTerm.numeral (Nat.succ (inputs.getD 0)))
      (RawTerm.succ (inputs.numeralTerms.getD 0)) =
        RawFormula.equal
          (RawTerm.numeral (Nat.succ (inputs.getD 0)))
          (RawTerm.numeral (Nat.succ (inputs.getD 0)))
    exact congrArg
      (RawFormula.equal (RawTerm.numeral (Nat.succ (inputs.getD 0))))
      (congrArg RawTerm.succ (NatVector.numeralTerms_getD inputs 0))
  exact Eq.mp
    (congrArg
      (fun formula =>
        Derivation LogicMode.intuitionistic haTheory FormulaContext.nil formula)
      sameFormula.symm)
    (Derivation.equalityReflexivity
      (ScopedTerm.numeral 0 (Nat.succ (inputs.getD 0))))

def internalProjectionGraphNumeralProof
    (arity index : Nat)
    (bounded : index < arity)
    (inputs : NatVector arity)
    (output : Nat)
    (evaluation :
      PRFunction.Evaluates
        (PRFunction.projection arity index bounded) inputs output) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      ((PRFunction.projection arity index bounded).numeralGraphInstance
        inputs output) := by
  have outputProjection : output = inputs.getD index :=
    evaluation.trans (NatVector.getD_eq_get inputs bounded).symm
  cases outputProjection
  let expected := ScopedFormula.equal
    (ScopedTerm.numeral 0 (inputs.getD index))
    (ScopedTerm.numeral 0 (inputs.getD index))
  have sameFormula :
      (PRFunction.projection arity index bounded).numeralGraphInstance
        inputs (inputs.getD index) = expected := by
    apply ScopedFormula.eq_of_raw_eq
    change RawFormula.equal
      (RawTerm.numeral (inputs.getD index))
      (inputs.numeralTerms.getD index) =
        RawFormula.equal
          (RawTerm.numeral (inputs.getD index))
          (RawTerm.numeral (inputs.getD index))
    exact congrArg (RawFormula.equal (RawTerm.numeral (inputs.getD index)))
      (NatVector.numeralTerms_getD inputs index)
  exact Eq.mp
    (congrArg
      (fun formula =>
        Derivation LogicMode.intuitionistic haTheory FormulaContext.nil formula)
      sameFormula.symm)
    (Derivation.equalityReflexivity
      (ScopedTerm.numeral 0 (inputs.getD index)))

/-! ## Positive numeralwise representation package -/

structure InternallyNumeralwiseRepresentedPRFunction
    {arity : Nat}
    (program : PRFunction arity) where
  numeralProof : (inputs : NatVector arity) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (program.numeralGraphInstance inputs (program.run inputs))

inductive InternallyNumeralwiseRepresentedPRFunctionVector
    {inputArity : Nat} :
    {outputArity : Nat} ->
    PRFunctionVector inputArity outputArity -> Type
  | nil : InternallyNumeralwiseRepresentedPRFunctionVector
      (PRFunctionVector.nil : PRFunctionVector inputArity 0)
  | cons
      {outputArity : Nat}
      {head : PRFunction inputArity}
      {tail : PRFunctionVector inputArity outputArity} :
      InternallyNumeralwiseRepresentedPRFunction head ->
      InternallyNumeralwiseRepresentedPRFunctionVector tail ->
      InternallyNumeralwiseRepresentedPRFunctionVector
        (PRFunctionVector.cons head tail)

def ArithmeticGraphVector.numeralInstances
    {inputArity outputArity : Nat} :
    ArithmeticGraphVector inputArity outputArity ->
    NatVector inputArity -> NatVector outputArity -> ScopedFormula 0 :=
  fun graphs inputs outputs =>
    match graphs with
    | ArithmeticGraphVector.nil =>
        { raw := trueFormula, isScoped := trueFormula_wellScoped 0 }
    | ArithmeticGraphVector.cons head tail =>
        ScopedFormula.conj
          (head.numeralInstance inputs (outputs.getD 0))
          (tail.numeralInstances inputs outputs.tailD)

private theorem NatVector.tailD_getD
    {length : Nat}
    (values : NatVector (Nat.succ length))
    (index : Nat)
    (bounded : index < length) :
    values.tailD.getD index = values.getD (Nat.succ index) :=
  (NatVector.getD_eq_get values.tailD bounded).trans
    ((NatVector.tailD_get values bounded).trans
      (NatVector.getD_eq_get values (Nat.succ_lt_succ bounded)).symm)

private theorem ArithmeticGraphVector.body_close_exact
    {inputArity length total : Nat}
    (graphs : ArithmeticGraphVector inputArity length)
    (inputs : NatVector inputArity)
    (middle : NatVector total)
    (output : Nat)
    (offset : Nat)
    (fits : offset + length <= total)
    (outputs : NatVector length)
    (agrees : (index : Nat) -> index < length ->
      middle.getD (offset + index) = outputs.getD index) :
    (((graphs.body offset total fits).raw.substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons output inputs) total)).substitute
        (numeralClosingSubstitution middle)) =
      (graphs.numeralInstances inputs outputs).raw :=
  (ArithmeticGraphVector.rec
    (motive := fun vectorLength vector =>
      (localOffset : Nat) ->
      (localFits : localOffset + vectorLength <= total) ->
      (localOutputs : NatVector vectorLength) ->
      ((index : Nat) -> index < vectorLength ->
        middle.getD (localOffset + index) = localOutputs.getD index) ->
      (((vector.body localOffset total localFits).raw.substitute
          (numeralClosingSubstitutionAtDepth
            (NatVector.cons output inputs) total)).substitute
          (numeralClosingSubstitution middle)) =
        (vector.numeralInstances inputs localOutputs).raw)
    (fun _localOffset _localFits _localOutputs _localAgrees => rfl)
    (fun {tailLength} head tail inductionHypothesis localOffset localFits
        localOutputs localAgrees => by
      apply congrArgTwo RawFormula.conj
      · have offsetBounded : localOffset < total :=
          Nat.lt_of_lt_of_le
            (Nat.lt_add_of_pos_right (Nat.succ_pos tailLength)) localFits
        exact (innerApplication_close_exact head inputs middle output
          localOffset offsetBounded).trans (by
            apply congrArg (fun value =>
              head.apply (RawTerm.numeral value) inputs.numeralTerms)
            exact localAgrees 0 (Nat.zero_lt_succ tailLength))
      · apply inductionHypothesis (Nat.succ localOffset)
          (succOffsetTailFits localFits) localOutputs.tailD
        intro index bounded
        have shifted := localAgrees (Nat.succ index)
          (Nat.succ_lt_succ bounded)
        have shiftedTail :
            middle.getD (localOffset + Nat.succ index) =
              localOutputs.tailD.getD index :=
          shifted.trans
            (NatVector.tailD_getD localOutputs index bounded).symm
        have positionEquality :
            Nat.succ localOffset + index =
              localOffset + Nat.succ index :=
          (Nat.succ_add localOffset index).trans
            (Nat.add_succ localOffset index).symm
        exact Eq.mp
          (congrArg (fun position =>
            middle.getD position = localOutputs.tailD.getD index)
            positionEquality).symm
          shiftedTail)
    graphs) offset fits outputs agrees

def trueFormulaProof :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      { raw := trueFormula, isScoped := trueFormula_wellScoped 0 } := by
  let falseFormula := ScopedFormula.falsum 0
  have proof : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl falseFormula falseFormula) :=
    Derivation.implicationIntroduction
      (Derivation.hypothesis ContextMember.here)
  change Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
    (ScopedFormula.impl falseFormula falseFormula)
  exact proof

def InternallyNumeralwiseRepresentedPRFunctionVector.numeralProof
    {inputArity outputArity : Nat}
    {programs : PRFunctionVector inputArity outputArity}
    (represented :
      InternallyNumeralwiseRepresentedPRFunctionVector programs)
    (inputs : NatVector inputArity) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (programs.graphFormulas.numeralInstances inputs (programs.run inputs)) :=
  match represented with
  | .nil => trueFormulaProof
  | .cons head tail => by
      simpa only [ArithmeticGraphVector.numeralInstances,
        PRFunction.numeralGraphInstance, PRFunction.graphFormula,
        PRFunctionVector.graphFormulas,
        PRFunctionVector.certifiedGraphCompiler,
        certifiedConsGraphVector,
        PRFunctionVector.run, PRFunctionVector.runCore,
        NatVector.getD, NatVector.tailD_cons] using
        (Derivation.conjunctionIntroduction
          (head.numeralProof inputs) (tail.numeralProof inputs))

def internallyNumeralwiseRepresentedZero
    {arity : Nat} :
    InternallyNumeralwiseRepresentedPRFunction
      (PRFunction.zero : PRFunction arity) :=
  { numeralProof := fun inputs =>
      internalZeroGraphNumeralProof inputs 0 rfl }

def internallyNumeralwiseRepresentedSuccessor :
    InternallyNumeralwiseRepresentedPRFunction PRFunction.successor :=
  { numeralProof := fun inputs =>
      internalSuccessorGraphNumeralProof inputs
        (Nat.succ (inputs.getD 0)) rfl }

def internallyNumeralwiseRepresentedProjection
    (arity index : Nat)
    (bounded : index < arity) :
    InternallyNumeralwiseRepresentedPRFunction
      (PRFunction.projection arity index bounded) :=
  { numeralProof := fun inputs =>
      internalProjectionGraphNumeralProof arity index bounded inputs
        (inputs.get index bounded) rfl }

theorem compositionNumeralBody_exact
    {inputArity outputArity : Nat}
    (outer : ArithmeticGraph outputArity)
    (inner : ArithmeticGraphVector inputArity outputArity)
    (inputs : NatVector inputArity)
    (intermediates : NatVector outputArity)
    (output : Nat) :
    let intermediateTerms := RawTermVector.variables 0 outputArity
    let outerApplication :=
      outer.apply (RawTerm.bvar outputArity) intermediateTerms
    let innerBody := inner.body 0 outputArity
      (zeroOffsetFits outputArity)
    let body : ScopedFormula outputArity :=
      { raw := (RawFormula.conj outerApplication innerBody.raw).substitute
          (numeralClosingSubstitutionAtDepth
            (NatVector.cons output inputs) outputArity)
        isScoped := by
          apply RawFormula.wellScoped_substitute
          · exact And.intro
              (outer.apply_wellScoped
                (RawTerm.bvar outputArity) intermediateTerms
                (Nat.lt_add_of_pos_right (Nat.succ_pos inputArity))
                (RawTermVector.variables_wellScoped 0 outputArity
                  (outputArity + Nat.succ inputArity)
                  (Nat.le_trans (zeroOffsetFits outputArity)
                    (Nat.le_add_right outputArity (Nat.succ inputArity)))))
              innerBody.isScoped
          · intro index bounded
            exact numeralClosingSubstitutionAtDepth_wellScoped
              (NatVector.cons output inputs) outputArity index bounded }
    body.closeWithNumerals intermediates =
      ScopedFormula.conj
        (outer.numeralInstance intermediates output)
        (inner.numeralInstances inputs intermediates) := by
  apply ScopedFormula.eq_of_raw_eq
  change
    (((outer.apply (RawTerm.bvar outputArity)
          (RawTermVector.variables 0 outputArity)).substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons output inputs) outputArity)).substitute
        (numeralClosingSubstitution intermediates)).conj
      (((inner.body 0 outputArity (zeroOffsetFits outputArity)).raw.substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons output inputs) outputArity)).substitute
        (numeralClosingSubstitution intermediates)) =
      (outer.numeralInstance intermediates output).raw.conj
        (inner.numeralInstances inputs intermediates).raw
  apply congrArgTwo RawFormula.conj
  · exact outerApplication_close_exact outer inputs intermediates output
  · apply ArithmeticGraphVector.body_close_exact inner inputs intermediates
      output 0 (zeroOffsetFits outputArity) intermediates
    intro index _bounded
    rw [Nat.zero_add]

def internallyNumeralwiseRepresentedComposition
    {inputArity outputArity : Nat}
    {outer : PRFunction outputArity}
    {inner : PRFunctionVector inputArity outputArity}
    (outerRepresented :
      InternallyNumeralwiseRepresentedPRFunction outer)
    (innerRepresented :
      InternallyNumeralwiseRepresentedPRFunctionVector inner) :
    InternallyNumeralwiseRepresentedPRFunction
      (PRFunction.composition outer inner) := by
  refine { numeralProof := ?_ }
  intro inputs
  let intermediates := inner.run inputs
  let output := outer.run intermediates
  let outerProof := outerRepresented.numeralProof intermediates
  let innerProof := innerRepresented.numeralProof inputs
  let bodyProof : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.conj
        (outer.graphFormula.numeralInstance intermediates output)
        (inner.graphFormulas.numeralInstances inputs intermediates)) :=
    Derivation.conjunctionIntroduction outerProof innerProof
  let intermediateTerms := RawTermVector.variables 0 outputArity
  let outerApplication := outer.graphFormula.apply
    (RawTerm.bvar outputArity) intermediateTerms
  let innerBody := inner.graphFormulas.body 0 outputArity
    (zeroOffsetFits outputArity)
  let openBody : ScopedFormula outputArity :=
    { raw := (RawFormula.conj outerApplication innerBody.raw).substitute
        (numeralClosingSubstitutionAtDepth
          (NatVector.cons output inputs) outputArity)
      isScoped := by
        apply RawFormula.wellScoped_substitute
        · exact And.intro
            (outer.graphFormula.apply_wellScoped
              (RawTerm.bvar outputArity) intermediateTerms
              (Nat.lt_add_of_pos_right (Nat.succ_pos inputArity))
              (RawTermVector.variables_wellScoped 0 outputArity
                (outputArity + Nat.succ inputArity)
                (Nat.le_trans (zeroOffsetFits outputArity)
                  (Nat.le_add_right outputArity (Nat.succ inputArity)))))
            innerBody.isScoped
        · intro index bounded
          exact numeralClosingSubstitutionAtDepth_wellScoped
            (NatVector.cons output inputs) outputArity index bounded }
  have closedBodyProof : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil (openBody.closeWithNumerals intermediates) := by
    rw [compositionNumeralBody_exact outer.graphFormula
      inner.graphFormulas inputs intermediates output]
    exact bodyProof
  have existsProof := Derivation.introduceExistsMany openBody
    intermediates closedBodyProof
  have sameFormula : openBody.existsManyBlock =
      (PRFunction.composition outer inner).numeralGraphInstance inputs
        ((PRFunction.composition outer inner).run inputs) := by
    apply ScopedFormula.eq_of_raw_eq
    let core := RawFormula.conj outerApplication innerBody.raw
    let block := core.existsMany outputArity
    have closingAgreement : (index : Nat) ->
        numeralClosingSubstitution (NatVector.cons output inputs) index =
          (match index with
          | 0 => RawTerm.numeral output
          | Nat.succ inputIndex => inputs.numeralTerms.getD inputIndex) := by
      intro index
      cases index with
      | zero => rfl
      | succ index => exact (inputs.numeralTerms_getD index).symm
    have normalizedClosing :
        block.substitute
            (numeralClosingSubstitution (NatVector.cons output inputs)) =
          block.substitute (fun index =>
            match index with
            | 0 => RawTerm.numeral output
            | Nat.succ inputIndex => inputs.numeralTerms.getD inputIndex) :=
      block.internalSubstituteCongr _ _ closingAgreement
    have rawEquality :=
      (RawFormula.existsMany_substitute_numeralClosing core
        (NatVector.cons output inputs) outputArity).trans normalizedClosing
    have leftRaw : openBody.existsManyBlock.raw =
        RawFormula.existsMany outputArity
          (core.substitute (numeralClosingSubstitutionAtDepth
            (NatVector.cons output inputs) outputArity)) := by
      rfl
    have rightRaw :
        ((PRFunction.composition outer inner).numeralGraphInstance inputs
          ((PRFunction.composition outer inner).run inputs)).raw =
        block.substitute (fun index =>
          match index with
          | 0 => RawTerm.numeral output
          | Nat.succ inputIndex => inputs.numeralTerms.getD inputIndex) := by
      simp [
        PRFunction.numeralGraphInstance, PRFunction.graphFormula,
        PRFunction.certifiedGraphCompiler, certifiedCompositionGraph,
        PRFunctionVector.graphFormulas,
        compositionGraph, ArithmeticGraph.numeralInstance,
        ArithmeticGraph.apply, outerApplication, innerBody,
        intermediateTerms, output, intermediates, core, block,
        PRFunction.run_composition]
      apply congrArg (fun formula : RawFormula => formula.substitute
        (fun index =>
          match index with
          | 0 => RawTerm.numeral output
          | Nat.succ inputIndex => inputs.numeralTerms.getD inputIndex))
      apply congrArg (RawFormula.existsMany outputArity)
      apply congrArg (fun formula => RawFormula.conj _ formula)
      apply congrArg ScopedFormula.raw
      apply congrArg (fun fits =>
        inner.certifiedGraphCompiler.graphs.body 0 outputArity fits)
      exact Subsingleton.elim _ _
    exact leftRaw.trans (rawEquality.trans rightRaw.symm)
  exact Eq.mp (congrArg
    (fun formula => Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil formula)
    sameFormula) existsProof

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.numeralTerms
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.numeralTerms_wellScoped
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.internalSubstituteCompose
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.internalSubstituteCongr
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.internalSubstituteCongr
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.internalSubstituteCompose
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.numeral_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.numeralTerms_getD
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.variables_getD_inside
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.variables_getD_outside
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.getD_outside
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraphVector.numeralInstances
#print axioms RelationalPerimeter.HeytingArithmetic.internalZeroGraphNumeralProof
#print axioms RelationalPerimeter.HeytingArithmetic.internalSuccessorGraphNumeralProof
#print axioms RelationalPerimeter.HeytingArithmetic.internalProjectionGraphNumeralProof
#print axioms RelationalPerimeter.HeytingArithmetic.InternallyNumeralwiseRepresentedPRFunction
#print axioms RelationalPerimeter.HeytingArithmetic.compositionNumeralBody_exact
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralwiseRepresentedComposition
/- AXIOM_AUDIT_END -/
