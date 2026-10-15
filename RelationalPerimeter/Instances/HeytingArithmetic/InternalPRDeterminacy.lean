import RelationalPerimeter.Instances.HeytingArithmetic.InternalFormulaVariableReplacement
import RelationalPerimeter.Instances.HeytingArithmetic.InternalRemainderFunctionality
import RelationalPerimeter.Instances.HeytingArithmetic.InternalPRNumeralwiseCompiler

/-!
# Internal numeral determinacy of primitive-recursive graphs

For fixed numeral inputs, every output satisfying the compiled graph is
proved inside HA to equal the structural evaluator's output.  This is the
functional half needed to turn a positive computation certificate into a
negative certificate for every other numeral.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

def ArithmeticGraph.numeralApplicationAt
    {arity bound : Nat}
    (graph : ArithmeticGraph arity)
    (inputs : NatVector arity)
    (output : ScopedTerm bound) : ScopedFormula bound :=
  { raw := graph.apply output.raw inputs.numeralTerms
    isScoped := graph.apply_wellScoped output.raw inputs.numeralTerms
      output.isScoped inputs.numeralTerms_wellScoped }

def ArithmeticGraphVector.numeralBodyAt
    {inputArity length : Nat}
    (graphs : ArithmeticGraphVector inputArity length)
    (inputs : NatVector inputArity)
    (offset bound : Nat)
    (fits : offset + length <= bound) : ScopedFormula bound :=
  match graphs with
  | ArithmeticGraphVector.nil =>
      { raw := trueFormula, isScoped := trueFormula_wellScoped bound }
  | @ArithmeticGraphVector.cons _ tailLength head tail =>
      ScopedFormula.conj
        (head.numeralApplicationAt inputs
          (ScopedTerm.bvar offset
            (Nat.lt_of_lt_of_le
              (Nat.lt_add_of_pos_right (Nat.succ_pos tailLength)) fits)))
        (tail.numeralBodyAt inputs (Nat.succ offset) bound
          (succOffsetTailFits fits))

structure InternallyNumeralDeterminatePRFunction
    {arity : Nat}
    (program : PRFunction arity) : Type where
  determine :
    {bound : Nat} ->
    {context : FormulaContext bound} ->
    (inputs : NatVector arity) ->
    (output : ScopedTerm bound) ->
    Derivation LogicMode.intuitionistic haTheory context
      (program.graphFormula.numeralApplicationAt inputs output) ->
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal output
        (ScopedTerm.numeral bound (program.run inputs)))

inductive InternallyNumeralDeterminatePRFunctionVector
    {inputArity : Nat} :
    {length : Nat} -> PRFunctionVector inputArity length -> Type
  | nil : InternallyNumeralDeterminatePRFunctionVector
      (PRFunctionVector.nil : PRFunctionVector inputArity 0)
  | cons
      {length : Nat}
      {head : PRFunction inputArity}
      {tail : PRFunctionVector inputArity length} :
      InternallyNumeralDeterminatePRFunction head ->
      InternallyNumeralDeterminatePRFunctionVector tail ->
      InternallyNumeralDeterminatePRFunctionVector
        (PRFunctionVector.cons head tail)

def InternallyNumeralDeterminatePRFunctionVector.equalities
    {inputArity length bound : Nat}
    {programs : PRFunctionVector inputArity length}
    (determinate : InternallyNumeralDeterminatePRFunctionVector programs)
    {context : FormulaContext bound}
    (inputs : NatVector inputArity)
    (offset : Nat)
    (fits : offset + length <= bound)
    (proof : Derivation LogicMode.intuitionistic haTheory context
      (programs.graphFormulas.numeralBodyAt inputs offset bound fits)) :
    VariableNumeralEqualities context offset (programs.run inputs) :=
  match determinate with
  | .nil => VariableNumeralEqualities.nil offset
  | .cons headDeterminate tailDeterminate => by
      let headBounded : offset < bound :=
        Nat.lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (Nat.succ_pos _)) fits
      let headProof := Derivation.conjunctionEliminationLeft proof
      let tailProof := Derivation.conjunctionEliminationRight proof
      let headEquality := headDeterminate.determine inputs
        (ScopedTerm.bvar offset headBounded) headProof
      exact VariableNumeralEqualities.cons headBounded headEquality
        (tailDeterminate.equalities inputs (Nat.succ offset)
          (succOffsetTailFits fits) tailProof)

def internallyNumeralDeterminateZero
    {arity : Nat} :
    InternallyNumeralDeterminatePRFunction
      (PRFunction.zero : PRFunction arity) :=
  { determine := by
      intro bound context inputs output proof
      simpa [ArithmeticGraph.numeralApplicationAt,
        PRFunction.graphFormula, PRFunction.certifiedGraphCompiler,
        certifiedZeroGraph, ArithmeticGraph.apply,
        NatVector.numeralTerms, RawFormula.substitute,
        RawTerm.substitute, ScopedFormula.equal, ScopedTerm.numeral,
        RawTerm.numeral] using proof }

def internallyNumeralDeterminateSuccessor :
    InternallyNumeralDeterminatePRFunction PRFunction.successor :=
  { determine := by
      intro bound context inputs output proof
      let head := inputs.getD 0
      have inputsRebuilt :
          NatVector.cons head NatVector.nil = inputs := by
        exact NatVector.rebuildD inputs
      rw [← inputsRebuilt] at proof ⊢
      simpa [ArithmeticGraph.numeralApplicationAt,
        PRFunction.graphFormula, PRFunction.certifiedGraphCompiler,
        certifiedSuccessorGraph, ArithmeticGraph.apply,
        NatVector.numeralTerms, RawFormula.substitute,
        RawTerm.substitute, PRFunction.run, PRFunction.runCore,
        ScopedFormula.equal, ScopedTerm.numeral, RawTerm.numeral,
        RawTermVector.getD, NatVector.getD]
        using proof }

def internallyNumeralDeterminateProjection
    (arity index : Nat)
    (bounded : index < arity) :
    InternallyNumeralDeterminatePRFunction
      (PRFunction.projection arity index bounded) :=
  { determine := by
      intro bound context inputs output proof
      have normalized : Derivation LogicMode.intuitionistic haTheory context
          (ScopedFormula.equal output
            (ScopedTerm.numeral bound (inputs.getD index))) := by
        refine Derivation.castConclusion ?_ proof
        apply ScopedFormula.eq_of_raw_eq
        change
          RawFormula.equal output.raw (inputs.numeralTerms.getD index) =
            RawFormula.equal output.raw
              (RawTerm.numeral (inputs.getD index))
        exact congrArg (RawFormula.equal output.raw)
          (NatVector.numeralTerms_getD inputs index)
      refine Derivation.castConclusion ?_ normalized
      exact congrArg
        (fun result => ScopedFormula.equal output
          (ScopedTerm.numeral bound result))
        (NatVector.getD_eq_get inputs bounded) }

private theorem ScopedTerm.transport_raw_mpr
    {source target : Nat}
    (sameBound : source = target)
    (term : ScopedTerm target) :
    (Eq.mpr (congrArg ScopedTerm sameBound) term).raw = term.raw := by
  cases sameBound
  rfl

theorem ScopedTerm.liftMany_raw
    {bound : Nat}
    (count : Nat)
    (term : ScopedTerm bound) :
    (term.liftMany count).raw = term.raw.raise count := by
  induction count with
  | zero =>
      exact ScopedTerm.transport_raw_mpr (Nat.zero_add bound) term
  | succ count inductionHypothesis =>
      change
        (Eq.mpr (congrArg ScopedTerm (Nat.succ_add count bound))
          (ScopedTerm.lift (ScopedTerm.liftMany count term))).raw = _
      rw [ScopedTerm.transport_raw_mpr (Nat.succ_add count bound)]
      change (ScopedTerm.liftMany count term).raw.rename Nat.succ = _
      rw [inductionHypothesis]
      rfl

private theorem ScopedFormula.transport_raw_mpr
    {source target : Nat}
    (sameBound : source = target)
    (formula : ScopedFormula target) :
    (Eq.mpr (congrArg ScopedFormula sameBound) formula).raw = formula.raw := by
  cases sameBound
  rfl

theorem ScopedFormula.liftMany_raw_rec
    {bound : Nat}
    (count : Nat)
    (formula : ScopedFormula bound) :
    (formula.liftMany count).raw =
      Nat.rec formula.raw
        (fun _ previous => previous.rename Nat.succ) count := by
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

theorem ScopedFormula.liftMany_equal
    {bound : Nat}
    (count : Nat)
    (left right : ScopedTerm bound) :
    (ScopedFormula.equal left right).liftMany count =
      ScopedFormula.equal (left.liftMany count) (right.liftMany count) := by
  apply ScopedFormula.eq_of_raw_eq
  rw [ScopedFormula.liftMany_raw_rec]
  change
    Nat.rec (RawFormula.equal left.raw right.raw)
        (fun _ previous => previous.rename Nat.succ) count =
      RawFormula.equal (left.liftMany count).raw (right.liftMany count).raw
  rw [left.liftMany_raw,
    right.liftMany_raw]
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        ((Nat.rec (motive := fun _ => RawFormula)
          (RawFormula.equal left.raw right.raw)
          (fun _ previous => previous.rename Nat.succ) count).rename Nat.succ) =
        RawFormula.equal ((left.raw.raise count).rename Nat.succ)
          ((right.raw.raise count).rename Nat.succ)
      rw [inductionHypothesis]
      rfl

/-- Substitute one arbitrary output term followed by numeral inputs. -/
def termNumeralApplicationSubstitution
    {arity : Nat}
    (output : RawTerm)
    (inputs : NatVector arity) : Substitution
  | 0 => output
  | Nat.succ index => inputs.numeralTerms.getD index

/-- Lift a term-and-numerals application through an existential prefix. -/
def termNumeralApplicationSubstitutionAtDepth
    {arity : Nat}
    (output : RawTerm)
    (inputs : NatVector arity) : Nat -> Substitution
  | 0 => termNumeralApplicationSubstitution output inputs
  | Nat.succ depth =>
      liftSubstitution
        (termNumeralApplicationSubstitutionAtDepth output inputs depth)

theorem RawFormula.existsMany_substitute_termNumeralApplication
    {arity : Nat}
    (formula : RawFormula)
    (output : RawTerm)
    (inputs : NatVector arity)
    (depth : Nat) :
    (formula.existsMany depth).substitute
        (termNumeralApplicationSubstitution output inputs) =
      (formula.substitute
        (termNumeralApplicationSubstitutionAtDepth output inputs depth)).existsMany
          depth := by
  induction depth generalizing formula with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [RawFormula.existsMany_succ, RawFormula.existsMany_succ,
        inductionHypothesis]
      rfl

theorem termNumeralApplicationSubstitutionAtDepth_below
    {arity : Nat}
    (output : RawTerm)
    (inputs : NatVector arity)
    (depth index : Nat)
    (below : index < depth) :
    termNumeralApplicationSubstitutionAtDepth output inputs depth index =
      RawTerm.bvar index := by
  induction depth generalizing index with
  | zero => exact (Nat.not_lt_zero index below).elim
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            (termNumeralApplicationSubstitutionAtDepth output inputs depth
              index).rename Nat.succ = RawTerm.bvar (Nat.succ index)
          rw [inductionHypothesis index (Nat.lt_of_succ_lt_succ below)]
          rfl

theorem termNumeralApplicationSubstitutionAtDepth_after
    {arity : Nat}
    (output : RawTerm)
    (inputs : NatVector arity)
    (depth index : Nat) :
    termNumeralApplicationSubstitutionAtDepth output inputs depth
        (depth + index) =
      (termNumeralApplicationSubstitution output inputs index).raise depth := by
  induction depth with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ depth inductionHypothesis =>
      rw [Nat.succ_add]
      change
        (termNumeralApplicationSubstitutionAtDepth output inputs depth
          (depth + index)).rename Nat.succ = _
      rw [inductionHypothesis]
      rfl

theorem RawTerm.numeral_raise_any
    (value depth : Nat) :
    (RawTerm.numeral value).raise depth = RawTerm.numeral value := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change ((RawTerm.numeral value).raise depth).rename Nat.succ = _
      rw [inductionHypothesis, RawTerm.numeral_rename]

theorem RawTerm.raise_bvar_local
    (index count : Nat) :
    (RawTerm.bvar index).raise count = RawTerm.bvar (index + count) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change ((RawTerm.bvar index).raise count).rename Nat.succ = _
      rw [inductionHypothesis, Nat.add_succ]
      rfl

theorem RawTermVector.cons_cons_getD_add_two
    {length : Nat}
    (first second : RawTerm)
    (tail : RawTermVector length)
    (index : Nat) :
    (RawTermVector.cons first (RawTermVector.cons second tail)).getD
        (2 + index) = tail.getD index := by
  rw [Nat.add_comm 2 index, Nat.add_succ, Nat.add_succ, Nat.add_zero]
  rfl

theorem ScopedTerm.liftMany_numeral
    (bound count value : Nat) :
    (ScopedTerm.numeral bound value).liftMany count =
      ScopedTerm.numeral (count + bound) value := by
  apply ScopedTerm.eq_of_raw_eq
  rw [ScopedTerm.liftMany_raw]
  change (RawTerm.numeral value).raise count = RawTerm.numeral value
  rw [RawTerm.numeral_raise_any]

theorem RawTerm.substitute_bvars_eq_rename
    (term : RawTerm)
    (rho : Renaming) :
    term.substitute (fun index => RawTerm.bvar (rho index)) =
      term.rename rho := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawFormula.substitute_bvars_eq_rename
    (formula : RawFormula)
    (rho : Renaming) :
    formula.substitute (fun index => RawTerm.bvar (rho index)) =
      formula.rename rho := by
  induction formula generalizing rho with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.substitute_bvars_eq_rename rho)
        (right.substitute_bvars_eq_rename rho)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis rho) (rightHypothesis rho)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis rho) (rightHypothesis rho)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis rho) (rightHypothesis rho)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      calc
        body.substitute
              (liftSubstitution (fun index => RawTerm.bvar (rho index))) =
            body.substitute
              (fun index => RawTerm.bvar (liftRenaming rho index)) := by
                apply RawFormula.substitute_congr
                intro index
                cases index <;> rfl
        _ = body.rename (liftRenaming rho) :=
          inductionHypothesis (liftRenaming rho)
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      calc
        body.substitute
              (liftSubstitution (fun index => RawTerm.bvar (rho index))) =
            body.substitute
              (fun index => RawTerm.bvar (liftRenaming rho index)) := by
                apply RawFormula.substitute_congr
                intro index
                cases index <;> rfl
        _ = body.rename (liftRenaming rho) :=
          inductionHypothesis (liftRenaming rho)

theorem scopedBetaValueFormulaAt_lift
    {bound : Nat}
    (dividend coefficient index value : ScopedTerm bound) :
    scopedBetaValueFormulaAt dividend.lift coefficient.lift index.lift
        value.lift =
      (scopedBetaValueFormulaAt dividend coefficient index value).lift := by
  apply ScopedFormula.eq_of_raw_eq
  change
    betaValueFormula (dividend.raw.rename Nat.succ)
        (coefficient.raw.rename Nat.succ) (index.raw.rename Nat.succ)
        (value.raw.rename Nat.succ) =
      (betaValueFormula dividend.raw coefficient.raw index.raw value.raw).rename
        Nat.succ
  rw [← RawFormula.substitute_bvars_eq_rename]
  exact (betaValueFormula_substitute_exact dividend.raw coefficient.raw
    index.raw value.raw (fun current => RawTerm.bvar (Nat.succ current))
    (dividend.raw.rename Nat.succ) (coefficient.raw.rename Nat.succ)
    (index.raw.rename Nat.succ) (value.raw.rename Nat.succ)
    (dividend.raw.substitute_bvars_eq_rename Nat.succ)
    (coefficient.raw.substitute_bvars_eq_rename Nat.succ)
    (index.raw.substitute_bvars_eq_rename Nat.succ)
    (value.raw.substitute_bvars_eq_rename Nat.succ)).symm

theorem betaValueFormula_renameSucc
    (dividend coefficient index value : RawTerm) :
    (betaValueFormula dividend coefficient index value).rename Nat.succ =
      betaValueFormula (dividend.rename Nat.succ)
        (coefficient.rename Nat.succ) (index.rename Nat.succ)
        (value.rename Nat.succ) := by
  rw [← RawFormula.substitute_bvars_eq_rename,
    betaValueFormula_substitute,
    RawTerm.substitute_bvars_eq_rename,
    RawTerm.substitute_bvars_eq_rename,
    RawTerm.substitute_bvars_eq_rename,
    RawTerm.substitute_bvars_eq_rename]

theorem ScopedFormula.liftMany_betaValue
    {bound : Nat}
    (count : Nat)
    (dividend coefficient index value : ScopedTerm bound) :
    (scopedBetaValueFormulaAt dividend coefficient index value).liftMany count =
      scopedBetaValueFormulaAt (dividend.liftMany count)
        (coefficient.liftMany count) (index.liftMany count)
        (value.liftMany count) := by
  apply ScopedFormula.eq_of_raw_eq
  rw [ScopedFormula.liftMany_raw_rec]
  change
    Nat.rec
        (betaValueFormula dividend.raw coefficient.raw index.raw value.raw)
        (fun _ previous => previous.rename Nat.succ) count =
      betaValueFormula (dividend.liftMany count).raw
        (coefficient.liftMany count).raw (index.liftMany count).raw
        (value.liftMany count).raw
  rw [
    ScopedTerm.liftMany_raw, ScopedTerm.liftMany_raw,
    ScopedTerm.liftMany_raw, ScopedTerm.liftMany_raw]
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (Nat.rec (motive := fun _ => RawFormula)
          (betaValueFormula dividend.raw coefficient.raw index.raw value.raw)
          (fun _ previous => previous.rename Nat.succ) count).rename Nat.succ =
        betaValueFormula ((dividend.raw.raise count).rename Nat.succ)
          ((coefficient.raw.raise count).rename Nat.succ)
          ((index.raw.raise count).rename Nat.succ)
          ((value.raw.raise count).rename Nat.succ)
      rw [inductionHypothesis, betaValueFormula_renameSucc]

def Derivation.weakenToExistsManyEliminationContext
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (count : Nat)
    (body : ScopedFormula (count + bound))
    (proof : Derivation mode theory context conclusion) :
    Derivation mode theory
      (existsManyEliminationContext count body context)
      (conclusion.liftMany count) := by
  induction count with
  | zero => exact proof.liftMany 0
  | succ count inductionHypothesis =>
      let sameBound := Nat.succ_add count bound
      let normalizedBody : ScopedFormula (Nat.succ (count + bound)) :=
        Eq.mp (congrArg ScopedFormula sameBound) body
      let existentialBody : ScopedFormula (count + bound) :=
        ScopedFormula.ex normalizedBody
      let earlier := inductionHypothesis existentialBody
      let weakened := Derivation.weaken normalizedBody
        (Derivation.liftVariables earlier)
      exact Derivation.transportBound sameBound.symm weakened

theorem ArithmeticGraphVector.body_substitute_termNumeralApplication
    {inputArity length : Nat}
    (graphs : ArithmeticGraphVector inputArity length)
    (output : RawTerm)
    (inputs : NatVector inputArity)
    (offset total bound : Nat)
    (fits : offset + length <= total) :
    (graphs.body offset total fits).raw.substitute
        (termNumeralApplicationSubstitutionAtDepth output inputs total) =
      (graphs.numeralBodyAt inputs offset (total + bound)
        (Nat.le_trans fits (Nat.le_add_right total bound))).raw := by
  induction graphs generalizing offset with
  | nil => rfl
  | @cons tailLength head tail inductionHypothesis =>
      apply congrArgTwo RawFormula.conj
      · apply ArithmeticGraph.apply_substitute_exact_bounded
        · exact termNumeralApplicationSubstitutionAtDepth_below
            output inputs total offset
            (Nat.lt_of_lt_of_le
              (Nat.lt_add_of_pos_right (Nat.succ_pos tailLength)) fits)
        · intro index bounded
          rw [RawTermVector.variables_getD_inside
            (Nat.succ total) inputArity index bounded]
          have position : Nat.succ total + index = total + Nat.succ index :=
            (Nat.succ_add total index).trans (Nat.add_succ total index).symm
          rw [position]
          change
            termNumeralApplicationSubstitutionAtDepth output inputs total
                (total + Nat.succ index) = inputs.numeralTerms.getD index
          rw [termNumeralApplicationSubstitutionAtDepth_after]
          change
            (inputs.numeralTerms.getD index).raise total =
              inputs.numeralTerms.getD index
          rw [NatVector.numeralTerms_getD, RawTerm.numeral_raise_any]
      · exact inductionHypothesis (Nat.succ offset)
          (succOffsetTailFits fits)

def internallyNumeralDeterminateComposition
    {inputArity outputArity : Nat}
    {outer : PRFunction outputArity}
    {inner : PRFunctionVector inputArity outputArity}
    (outerDeterminate : InternallyNumeralDeterminatePRFunction outer)
    (innerDeterminate :
      InternallyNumeralDeterminatePRFunctionVector inner) :
    InternallyNumeralDeterminatePRFunction
      (PRFunction.composition outer inner) :=
  { determine := by
      intro bound context inputs output proof
      let intermediates := inner.run inputs
      let intermediateTerms := RawTermVector.variables 0 outputArity
      let outerFormula : ScopedFormula (outputArity + bound) :=
        { raw := outer.graphFormula.apply (output.liftMany outputArity).raw
            intermediateTerms
          isScoped := outer.graphFormula.apply_wellScoped
            (output.liftMany outputArity).raw intermediateTerms
            (output.liftMany outputArity).isScoped
            (RawTermVector.variables_wellScoped 0 outputArity
              (outputArity + bound)
              (Nat.le_trans (zeroOffsetFits outputArity)
                (Nat.le_add_right outputArity bound))) }
      let innerFormula := inner.graphFormulas.numeralBodyAt inputs 0
        (outputArity + bound)
        (Nat.le_trans (zeroOffsetFits outputArity)
          (Nat.le_add_right outputArity bound))
      let openBody := ScopedFormula.conj outerFormula innerFormula
      let blockProof : Derivation LogicMode.intuitionistic haTheory context
          { raw := openBody.raw.existsMany outputArity
            isScoped := RawFormula.existsMany_wellScoped outputArity bound
              openBody.raw openBody.isScoped } := by
        refine Derivation.castConclusion ?_ proof
        apply ScopedFormula.eq_of_raw_eq
        change
          (compositionGraph outer.graphFormula inner.graphFormulas).raw.substitute
              (termNumeralApplicationSubstitution output.raw inputs) =
            openBody.raw.existsMany outputArity
        unfold compositionGraph
        rw [RawFormula.existsMany_substitute_termNumeralApplication]
        dsimp [openBody, outerFormula, innerFormula, intermediateTerms]
        apply congrArg (RawFormula.existsMany outputArity)
        apply congrArgTwo RawFormula.conj
        · apply ArithmeticGraph.apply_substitute_exact_bounded
          · change
              termNumeralApplicationSubstitutionAtDepth output.raw inputs
                  outputArity outputArity =
                (output.liftMany outputArity).raw
            have atOutput :=
              termNumeralApplicationSubstitutionAtDepth_after output.raw
                inputs outputArity 0
            rw [Nat.add_zero] at atOutput
            exact atOutput.trans
              (ScopedTerm.liftMany_raw outputArity output).symm
          · intro index bounded
            rw [RawTermVector.variables_getD_inside 0 outputArity index
                bounded,
              Nat.zero_add]
            change
              termNumeralApplicationSubstitutionAtDepth output.raw inputs
                  outputArity index = RawTerm.bvar index
            exact termNumeralApplicationSubstitutionAtDepth_below
              output.raw inputs outputArity index bounded
        · exact ArithmeticGraphVector.body_substitute_termNumeralApplication
            inner.graphFormulas output.raw inputs 0 outputArity bound
            (zeroOffsetFits outputArity)
      apply Derivation.eliminateExistsMany outputArity openBody blockProof
      intro bodyProof
      let outerProof := Derivation.conjunctionEliminationLeft bodyProof
      let innerProof := Derivation.conjunctionEliminationRight bodyProof
      let fits : 0 + outputArity <= outputArity + bound := by
        exact Nat.le_trans (zeroOffsetFits outputArity)
          (Nat.le_add_right outputArity bound)
      let equalities := innerDeterminate.equalities inputs 0 fits innerProof
      let transported := equalities.transport outerFormula outerProof
      have normalizedFormula :
          outerFormula.replaceVariables 0 intermediates =
            outer.graphFormula.numeralApplicationAt intermediates
              (output.liftMany outputArity) := by
        apply ScopedFormula.eq_of_raw_eq
        rw [ScopedFormula.replaceVariables_raw]
        change
          (outer.graphFormula.apply (output.liftMany outputArity).raw
            intermediateTerms).replaceVariables 0 intermediates =
          outer.graphFormula.apply (output.liftMany outputArity).raw
            intermediates.numeralTerms
        rw [outer.graphFormula.apply_replaceVariables]
        rw [output.liftMany_raw, RawTerm.raise_replaceVariables_below]
        rw [RawTermVector.variables_replaceVariables]
      rw [normalizedFormula] at transported
      let determined := outerDeterminate.determine intermediates
        (output.liftMany outputArity) transported
      refine Derivation.castConclusion ?_ determined
      have sameConclusion :=
        (ScopedFormula.liftMany_equal outputArity output
          (ScopedTerm.numeral bound (outer.run (inner.run inputs)))).symm
      rw [ScopedTerm.liftMany_numeral] at sameConclusion
      simpa [intermediates, PRFunction.run, PRFunction.runCore] using
        sameConclusion }

def addNumeralsProofAt
    (bound : Nat) : (left right : Nat) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add (ScopedTerm.numeral bound left)
          (ScopedTerm.numeral bound right))
        (ScopedTerm.numeral bound (left + right)))
  | left, 0 =>
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addZero (ScopedTerm.numeral bound left))
  | left, Nat.succ right => by
      let unfolded : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
          (ScopedFormula.equal
            (ScopedTerm.add (ScopedTerm.numeral bound left)
              (ScopedTerm.numeral bound (Nat.succ right)))
            (ScopedTerm.succ
              (ScopedTerm.add (ScopedTerm.numeral bound left)
                (ScopedTerm.numeral bound right)))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addSuccessor
            (ScopedTerm.numeral bound left)
            (ScopedTerm.numeral bound right))
      let recursive := successorCongruenceAt
        (addNumeralsProofAt bound left right)
      exact Derivation.equalityTransitivity unfolded recursive

private theorem natAddComputedGapEqAt
    {smaller larger : Nat}
    (strict : smaller < larger) :
    smaller + Nat.succ (larger - Nat.succ smaller) = larger := by
  induction smaller generalizing larger with
  | zero =>
      cases larger with
      | zero => exact (Nat.not_lt_zero 0 strict).elim
      | succ larger =>
          rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.zero_add]
  | succ smaller inductionHypothesis =>
      cases larger with
      | zero => exact (Nat.not_lt_zero (Nat.succ smaller) strict).elim
      | succ larger =>
          have earlier : smaller < larger := Nat.lt_of_succ_lt_succ strict
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_add]
          exact congrArg Nat.succ (inductionHypothesis earlier)

private theorem addTwo_add_eq_add_succ_succ
    (base index : Nat) :
    (base + 2) + index = base + Nat.succ (Nat.succ index) := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [Nat.add_succ, Nat.add_succ]
      exact congrArg Nat.succ inductionHypothesis

private theorem add_one_add_one_eq_two_add
    (index : Nat) : index + 1 + 1 = 2 + index := by
  calc
    index + 1 + 1 = index + 2 := rfl
    _ = 2 + index := Nat.add_comm index 2

def lessThanNumeralsProofAt
    (bound left right : Nat)
    (strict : left < right) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedLessThanFormulaAt
        (ScopedTerm.numeral bound left)
        (ScopedTerm.numeral bound right)) := by
  let gap := right - Nat.succ left
  let computed := addNumeralsProofAt bound left (Nat.succ gap)
  let exactResult := numeralEqualityProof bound
    (left + Nat.succ gap) right (natAddComputedGapEqAt strict)
  let equation := Derivation.equalityTransitivity computed exactResult
  exact lessThanIntroductionAt
    (ScopedTerm.numeral bound left)
    (ScopedTerm.numeral bound right)
    (ScopedTerm.numeral bound gap) equation

def internallyNumeralDeterminatePrimitiveRecursion
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    (baseDeterminate : InternallyNumeralDeterminatePRFunction base)
    (stepDeterminate : InternallyNumeralDeterminatePRFunction step) :
    InternallyNumeralDeterminatePRFunction
      (PRFunction.primitiveRecursion base step) :=
  { determine := by
      intro bound context inputs output proof
      let counter := inputs.getD 0
      let parameters := inputs.tailD
      have inputsRebuilt : NatVector.cons counter parameters = inputs :=
        NatVector.rebuildD inputs
      rw [← inputsRebuilt] at proof ⊢
      ·
        let outerBound := 2 + bound
        let dividend : ScopedTerm outerBound := ScopedTerm.bvar 0 (by
          exact Nat.lt_of_lt_of_le (by decide)
            (Nat.le_add_right 2 bound))
        let coefficient : ScopedTerm outerBound := ScopedTerm.bvar 1 (by
          exact Nat.lt_of_lt_of_le (by decide)
            (Nat.le_add_right 2 bound))
        let baseValueVariable := ScopedTerm.bvar 0
          (Nat.zero_lt_succ outerBound)
        let baseCore : ScopedFormula (Nat.succ outerBound) :=
          ScopedFormula.conj
            (scopedBetaValueFormulaAt dividend.lift coefficient.lift
              (ScopedTerm.zero _) baseValueVariable)
            (base.graphFormula.numeralApplicationAt parameters
              baseValueVariable)
        let baseClause := ScopedFormula.ex baseCore
        let transitionIndex := ScopedTerm.bvar 0
          (Nat.zero_lt_succ outerBound)
        let transitionScope := 2 + Nat.succ outerBound
        let previousVariable : ScopedTerm transitionScope :=
          ScopedTerm.bvar 0 (by
            dsimp [transitionScope]
            exact Nat.zero_lt_succ _)
        let nextVariable : ScopedTerm transitionScope :=
          ScopedTerm.bvar 1 (by
            dsimp [transitionScope]
            exact Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le (by decide)
                (Nat.le_add_right 2 outerBound)))
        let liftedIndex := transitionIndex.liftMany 2
        let liftedDividend := dividend.lift.liftMany 2
        let liftedCoefficient := coefficient.lift.liftMany 2
        have liftedIndex_raw : liftedIndex.raw = RawTerm.bvar 2 := by
          rw [ScopedTerm.liftMany_raw]
          change (RawTerm.bvar 0).raise 2 = RawTerm.bvar 2
          exact RawTerm.raise_bvar_local 0 2
        have liftedDividend_raw : liftedDividend.raw = RawTerm.bvar 3 := by
          rw [ScopedTerm.liftMany_raw]
          change ((RawTerm.bvar 0).rename Nat.succ).raise 2 =
            RawTerm.bvar 3
          change (RawTerm.bvar 1).raise 2 = RawTerm.bvar 3
          exact RawTerm.raise_bvar_local 1 2
        have liftedCoefficient_raw : liftedCoefficient.raw =
            RawTerm.bvar 4 := by
          rw [ScopedTerm.liftMany_raw]
          change ((RawTerm.bvar 1).rename Nat.succ).raise 2 =
            RawTerm.bvar 4
          change (RawTerm.bvar 2).raise 2 = RawTerm.bvar 4
          exact RawTerm.raise_bvar_local 2 2
        let stepInputs : RawTermVector (Nat.succ (Nat.succ parameterArity)) :=
          RawTermVector.cons liftedIndex.raw
            (RawTermVector.cons previousVariable.raw
              parameters.numeralTerms)
        let stepFormula : ScopedFormula transitionScope :=
          { raw := step.graphFormula.apply nextVariable.raw stepInputs
            isScoped := step.graphFormula.apply_wellScoped nextVariable.raw
              stepInputs nextVariable.isScoped
              (And.intro liftedIndex.isScoped
                (And.intro previousVariable.isScoped
                  parameters.numeralTerms_wellScoped)) }
        let transitionCore : ScopedFormula transitionScope :=
          ScopedFormula.conj
            (scopedBetaValueFormulaAt liftedDividend liftedCoefficient
              liftedIndex previousVariable)
            (ScopedFormula.conj
              (scopedBetaValueFormulaAt liftedDividend liftedCoefficient
                liftedIndex.succ nextVariable)
              stepFormula)
        let transitionExists : ScopedFormula (Nat.succ outerBound) :=
          { raw := transitionCore.raw.existsMany 2
            isScoped := RawFormula.existsMany_wellScoped 2
              (Nat.succ outerBound) transitionCore.raw transitionCore.isScoped }
        let transitionLess := scopedLessThanFormulaAt transitionIndex
          (ScopedTerm.numeral (Nat.succ outerBound) counter)
        let transitionClause := ScopedFormula.all
          (ScopedFormula.impl transitionLess transitionExists)
        let outputClause := scopedBetaValueFormulaAt dividend coefficient
          (ScopedTerm.numeral outerBound counter) (output.liftMany 2)
        let openBody := ScopedFormula.conj baseClause
          (ScopedFormula.conj transitionClause outputClause)
        let blockProof : Derivation LogicMode.intuitionistic haTheory context
            { raw := openBody.raw.existsMany 2
              isScoped := RawFormula.existsMany_wellScoped 2 bound
                openBody.raw openBody.isScoped } := by
          refine Derivation.castConclusion ?_ proof
          apply ScopedFormula.eq_of_raw_eq
          change
            (primitiveRecursionGraph base.graphFormula
              step.graphFormula).raw.substitute
                (termNumeralApplicationSubstitution output.raw
                  (NatVector.cons counter parameters)) =
              openBody.raw.existsMany 2
          unfold primitiveRecursionGraph
          rw [RawFormula.existsMany_substitute_termNumeralApplication]
          apply congrArg (RawFormula.existsMany 2)
          dsimp [openBody, baseClause, baseCore, transitionClause,
            transitionLess, transitionExists, transitionCore,
            stepFormula, stepInputs, outputClause,
            dividend, coefficient, baseValueVariable,
            transitionIndex, previousVariable, nextVariable,
            liftedIndex, liftedDividend, liftedCoefficient,
            outerBound, transitionScope, primitiveBaseParameters,
            primitiveStepInputs]
          apply congrArgTwo RawFormula.conj
          · apply congrArg RawFormula.ex
            apply congrArgTwo RawFormula.conj
            · apply betaValueFormula_substitute_exact
              · exact termNumeralApplicationSubstitutionAtDepth_below
                  output.raw (NatVector.cons counter parameters) 3 1 (by decide)
              · exact termNumeralApplicationSubstitutionAtDepth_below
                  output.raw (NatVector.cons counter parameters) 3 2 (by decide)
              · rfl
              · exact termNumeralApplicationSubstitutionAtDepth_below
                  output.raw (NatVector.cons counter parameters) 3 0 (by decide)
            · apply ArithmeticGraph.apply_substitute_exact_bounded
              · exact termNumeralApplicationSubstitutionAtDepth_below
                  output.raw (NatVector.cons counter parameters) 3 0 (by decide)
              · intro index bounded
                rw [RawTermVector.variables_getD_inside 5 parameterArity
                  index bounded]
                have position :
                    5 + index = 3 + Nat.succ (Nat.succ index) :=
                  addTwo_add_eq_add_succ_succ 3 index
                rw [position]
                change
                  termNumeralApplicationSubstitutionAtDepth output.raw
                      (NatVector.cons counter parameters) 3
                      (3 + Nat.succ (Nat.succ index)) =
                    parameters.numeralTerms.getD index
                rw [termNumeralApplicationSubstitutionAtDepth_after]
                change (parameters.numeralTerms.getD index).raise 3 =
                  parameters.numeralTerms.getD index
                rw [NatVector.numeralTerms_getD, RawTerm.numeral_raise_any]
          · apply congrArgTwo RawFormula.conj
            · apply congrArg RawFormula.all
              apply congrArgTwo RawFormula.impl
              · rw [lessThanFormula_substitute]
                apply congrArgTwo lessThanFormula
                · change
                    termNumeralApplicationSubstitutionAtDepth output.raw
                        (NatVector.cons counter parameters) 3 0 =
                      RawTerm.bvar 0
                  exact termNumeralApplicationSubstitutionAtDepth_below
                    output.raw (NatVector.cons counter parameters) 3 0
                    (by decide)
                ·
                  have atCounter :=
                    termNumeralApplicationSubstitutionAtDepth_after
                      output.raw (NatVector.cons counter parameters) 3 1
                  change
                    termNumeralApplicationSubstitutionAtDepth output.raw
                        (NatVector.cons counter parameters) 3 4 =
                      RawTerm.numeral counter
                  exact atCounter.trans (RawTerm.numeral_raise_any counter 3)
              · apply congrArg RawFormula.ex
                apply congrArg RawFormula.ex
                apply congrArgTwo RawFormula.conj
                · apply betaValueFormula_substitute_exact
                  · change
                      termNumeralApplicationSubstitutionAtDepth output.raw
                          (NatVector.cons counter parameters) 5 3 =
                        liftedDividend.raw
                    exact (termNumeralApplicationSubstitutionAtDepth_below
                      output.raw (NatVector.cons counter parameters) 5 3
                      (by decide)).trans liftedDividend_raw.symm
                  · change
                      termNumeralApplicationSubstitutionAtDepth output.raw
                          (NatVector.cons counter parameters) 5 4 =
                        liftedCoefficient.raw
                    exact (termNumeralApplicationSubstitutionAtDepth_below
                      output.raw (NatVector.cons counter parameters) 5 4
                      (by decide)).trans liftedCoefficient_raw.symm
                  · change
                      termNumeralApplicationSubstitutionAtDepth output.raw
                          (NatVector.cons counter parameters) 5 2 =
                        liftedIndex.raw
                    exact (termNumeralApplicationSubstitutionAtDepth_below
                      output.raw (NatVector.cons counter parameters) 5 2
                      (by decide)).trans liftedIndex_raw.symm
                  · change
                      termNumeralApplicationSubstitutionAtDepth output.raw
                          (NatVector.cons counter parameters) 5 0 =
                        RawTerm.bvar 0
                    exact termNumeralApplicationSubstitutionAtDepth_below
                      output.raw (NatVector.cons counter parameters) 5 0
                      (by decide)
                · apply congrArgTwo RawFormula.conj
                  · apply betaValueFormula_substitute_exact
                    · change
                        termNumeralApplicationSubstitutionAtDepth output.raw
                            (NatVector.cons counter parameters) 5 3 =
                          liftedDividend.raw
                      exact (termNumeralApplicationSubstitutionAtDepth_below
                        output.raw (NatVector.cons counter parameters) 5 3
                        (by decide)).trans liftedDividend_raw.symm
                    · change
                        termNumeralApplicationSubstitutionAtDepth output.raw
                            (NatVector.cons counter parameters) 5 4 =
                          liftedCoefficient.raw
                      exact (termNumeralApplicationSubstitutionAtDepth_below
                        output.raw (NatVector.cons counter parameters) 5 4
                        (by decide)).trans liftedCoefficient_raw.symm
                    · change
                        RawTerm.succ
                            (termNumeralApplicationSubstitutionAtDepth output.raw
                              (NatVector.cons counter parameters) 5 2) =
                          RawTerm.succ liftedIndex.raw
                      exact congrArg RawTerm.succ
                        ((termNumeralApplicationSubstitutionAtDepth_below
                          output.raw (NatVector.cons counter parameters) 5 2
                          (by decide)).trans liftedIndex_raw.symm)
                    · change
                        termNumeralApplicationSubstitutionAtDepth output.raw
                            (NatVector.cons counter parameters) 5 1 =
                          RawTerm.bvar 1
                      exact termNumeralApplicationSubstitutionAtDepth_below
                        output.raw (NatVector.cons counter parameters) 5 1
                        (by decide)
                  · apply ArithmeticGraph.apply_substitute_exact_bounded
                    · change
                        termNumeralApplicationSubstitutionAtDepth output.raw
                            (NatVector.cons counter parameters) 5 1 =
                          RawTerm.bvar 1
                      exact
                          termNumeralApplicationSubstitutionAtDepth_below
                            output.raw (NatVector.cons counter parameters) 5 1
                            (by decide)
                    · intro position bounded
                      cases position with
                      | zero =>
                          change
                            termNumeralApplicationSubstitutionAtDepth output.raw
                                (NatVector.cons counter parameters) 5 2 =
                              liftedIndex.raw
                          exact
                            (termNumeralApplicationSubstitutionAtDepth_below
                              output.raw (NatVector.cons counter parameters)
                              5 2 (by decide)).trans liftedIndex_raw.symm
                      | succ position =>
                          cases position with
                          | zero =>
                              change
                                termNumeralApplicationSubstitutionAtDepth
                                    output.raw
                                    (NatVector.cons counter parameters) 5 0 =
                                  RawTerm.bvar 0
                              exact
                                termNumeralApplicationSubstitutionAtDepth_below
                                  output.raw
                                  (NatVector.cons counter parameters) 5 0
                                  (by decide)
                          | succ position =>
                              have vectorPosition :
                                  position + 1 + 1 = 2 + position :=
                                add_one_add_one_eq_two_add position
                              rw [vectorPosition]
                              change
                                ((RawTermVector.cons (RawTerm.bvar 2)
                                  (RawTermVector.cons (RawTerm.bvar 0)
                                    (RawTermVector.variables 7
                                      parameterArity))).getD
                                    (2 + position)).substitute _ =
                                  (RawTermVector.cons liftedIndex.raw
                                    (RawTermVector.cons previousVariable.raw
                                      parameters.numeralTerms)).getD
                                    (2 + position)
                              rw [
                                RawTermVector.cons_cons_getD_add_two,
                                RawTermVector.cons_cons_getD_add_two]
                              rw [RawTermVector.variables_getD_inside 7
                                parameterArity position
                                (Nat.lt_of_succ_lt_succ
                                  (Nat.lt_of_succ_lt_succ bounded))]
                              have positionExact :
                                  7 + position =
                                    5 + Nat.succ (Nat.succ position) :=
                                addTwo_add_eq_add_succ_succ 5 position
                              rw [positionExact]
                              change
                                termNumeralApplicationSubstitutionAtDepth
                                    output.raw
                                    (NatVector.cons counter parameters) 5
                                    (5 + Nat.succ (Nat.succ position)) =
                                  parameters.numeralTerms.getD position
                              rw [
                                termNumeralApplicationSubstitutionAtDepth_after]
                              change
                                (parameters.numeralTerms.getD position).raise 5 =
                                  parameters.numeralTerms.getD position
                              rw [NatVector.numeralTerms_getD,
                                RawTerm.numeral_raise_any]
            · apply betaValueFormula_substitute_exact
              · change
                  termNumeralApplicationSubstitutionAtDepth output.raw
                      (NatVector.cons counter parameters) 2 0 = RawTerm.bvar 0
                exact termNumeralApplicationSubstitutionAtDepth_below
                  output.raw (NatVector.cons counter parameters) 2 0
                  (by decide)
              · change
                  termNumeralApplicationSubstitutionAtDepth output.raw
                      (NatVector.cons counter parameters) 2 1 = RawTerm.bvar 1
                exact termNumeralApplicationSubstitutionAtDepth_below
                  output.raw (NatVector.cons counter parameters) 2 1
                  (by decide)
              ·
                have atCounter :=
                  termNumeralApplicationSubstitutionAtDepth_after
                    output.raw (NatVector.cons counter parameters) 2 1
                change
                  termNumeralApplicationSubstitutionAtDepth output.raw
                      (NatVector.cons counter parameters) 2 3 =
                    RawTerm.numeral counter
                exact atCounter.trans (RawTerm.numeral_raise_any counter 2)
              ·
                have atOutput :=
                  termNumeralApplicationSubstitutionAtDepth_after
                    output.raw (NatVector.cons counter parameters) 2 0
                rw [Nat.add_zero] at atOutput
                exact atOutput.trans
                  (ScopedTerm.liftMany_raw 2 output).symm
        apply Derivation.eliminateExistsMany 2 openBody blockProof
        intro bodyProof
        let openedContext := existsManyEliminationContext 2 openBody context
        let baseProof := Derivation.conjunctionEliminationLeft bodyProof
        let restProof := Derivation.conjunctionEliminationRight bodyProof
        let transitionProof := Derivation.conjunctionEliminationLeft restProof
        let outputBeta := Derivation.conjunctionEliminationRight restProof
        let baseResult := base.run parameters
        let baseBetaTarget := scopedBetaValueFormulaAt dividend coefficient
          (ScopedTerm.zero outerBound)
          (ScopedTerm.numeral outerBound baseResult)
        let baseBeta : Derivation LogicMode.intuitionistic haTheory openedContext
            baseBetaTarget := by
          let baseBranchContext := FormulaContext.cons baseCore
            openedContext.lift
          let baseCoreProof : Derivation LogicMode.intuitionistic haTheory
              baseBranchContext baseCore :=
            Derivation.hypothesis ContextMember.here
          let betaAtWitness := Derivation.conjunctionEliminationLeft
            baseCoreProof
          let graphAtWitness := Derivation.conjunctionEliminationRight
            baseCoreProof
          let witnessEquality := baseDeterminate.determine parameters
            baseValueVariable graphAtWitness
          let betaAtFormula : ScopedFormula (Nat.succ outerBound) :=
            scopedBetaValueFormulaAt dividend.lift coefficient.lift
              (ScopedTerm.zero _) baseValueVariable
          let transported := replaceVariableUsingEquality betaAtFormula 0
            (Nat.zero_lt_succ outerBound)
            (ScopedTerm.numeral (Nat.succ outerBound) baseResult)
            witnessEquality betaAtWitness
          have replacedExact :
              betaAtFormula.replaceVariable 0
                  (ScopedTerm.numeral (Nat.succ outerBound) baseResult) =
                scopedBetaValueFormulaAt dividend.lift coefficient.lift
                  (ScopedTerm.zero outerBound).lift
                  (ScopedTerm.numeral outerBound baseResult).lift := by
            apply ScopedFormula.eq_of_raw_eq
            apply betaValueFormula_substitute_exact
            · exact RawTerm.renameSucc_replaceVariableZero dividend.raw
                (ScopedTerm.numeral (Nat.succ outerBound) baseResult).raw
            · exact RawTerm.renameSucc_replaceVariableZero coefficient.raw
                (ScopedTerm.numeral (Nat.succ outerBound) baseResult).raw
            · rfl
            ·
              change RawTerm.numeral baseResult =
                (RawTerm.numeral baseResult).rename Nat.succ
              exact (RawTerm.numeral_rename _ _).symm
          let eliminated := Derivation.existentialElimination
            (conclusion := baseBetaTarget) baseProof
            (by
              refine Derivation.castConclusion ?_ transported
              exact replacedExact.trans
                (scopedBetaValueFormulaAt_lift dividend coefficient
                  (ScopedTerm.zero outerBound)
                  (ScopedTerm.numeral outerBound baseResult)))
          exact eliminated
        let valueAt := fun index =>
          (PRFunction.primitiveRecursion base step).run
            (NatVector.cons index parameters)
        have betaAt :
            (index : Nat) ->
            (bounded : index <= counter) ->
            Derivation LogicMode.intuitionistic haTheory openedContext
              (scopedBetaValueFormulaAt dividend coefficient
                (ScopedTerm.numeral outerBound index)
                (ScopedTerm.numeral outerBound (valueAt index))) :=
          Nat.rec
            (motive := fun index =>
              (bounded : index <= counter) ->
              Derivation LogicMode.intuitionistic haTheory openedContext
                (scopedBetaValueFormulaAt dividend coefficient
                  (ScopedTerm.numeral outerBound index)
                  (ScopedTerm.numeral outerBound (valueAt index))))
            (fun _bounded => by
              have valueAtZero : valueAt 0 = baseResult :=
                PRFunction.run_primitive_zero base step parameters
              refine Derivation.castConclusion ?_ baseBeta
              dsimp [baseBetaTarget]
              exact congrArg
                (fun result => scopedBetaValueFormulaAt dividend coefficient
                  (ScopedTerm.zero outerBound)
                  (ScopedTerm.numeral outerBound result)) valueAtZero.symm)
            (fun index inductionHypothesis bounded => by
              have indexStrict : index < counter :=
                Nat.lt_of_succ_le bounded
              let localPrevious : ScopedTerm (2 + outerBound) :=
                ScopedTerm.bvar 0 (Nat.lt_of_lt_of_le (by decide)
                  (Nat.le_add_right 2 outerBound))
              let localNext : ScopedTerm (2 + outerBound) :=
                ScopedTerm.bvar 1 (Nat.lt_of_lt_of_le (by decide)
                  (Nat.le_add_right 2 outerBound))
              let localDividend := dividend.liftMany 2
              let localCoefficient := coefficient.liftMany 2
              let localIndex := ScopedTerm.numeral (2 + outerBound) index
              have localDividend_raw : localDividend.raw = RawTerm.bvar 2 := by
                rw [ScopedTerm.liftMany_raw]
                change (RawTerm.bvar 0).raise 2 = RawTerm.bvar 2
                exact RawTerm.raise_bvar_local 0 2
              have localCoefficient_raw : localCoefficient.raw =
                  RawTerm.bvar 3 := by
                rw [ScopedTerm.liftMany_raw]
                change (RawTerm.bvar 1).raise 2 = RawTerm.bvar 3
                exact RawTerm.raise_bvar_local 1 2
              let localStepFormula : ScopedFormula (2 + outerBound) :=
                { raw := step.graphFormula.apply localNext.raw
                    (RawTermVector.cons localIndex.raw
                      (RawTermVector.cons localPrevious.raw
                        parameters.numeralTerms))
                  isScoped := step.graphFormula.apply_wellScoped _ _
                    localNext.isScoped
                    (And.intro localIndex.isScoped
                      (And.intro localPrevious.isScoped
                        parameters.numeralTerms_wellScoped)) }
              let localTransitionCore : ScopedFormula (2 + outerBound) :=
                ScopedFormula.conj
                  (scopedBetaValueFormulaAt localDividend localCoefficient
                    localIndex localPrevious)
                  (ScopedFormula.conj
                    (scopedBetaValueFormulaAt localDividend localCoefficient
                      localIndex.succ localNext)
                    localStepFormula)
              let localTransitionBlock : ScopedFormula outerBound :=
                { raw := localTransitionCore.raw.existsMany 2
                  isScoped := RawFormula.existsMany_wellScoped 2 outerBound
                    localTransitionCore.raw localTransitionCore.isScoped }
              let transitionAt := Derivation.universalElimination
                (ScopedTerm.numeral outerBound index) transitionProof
              let lessProof := (lessThanNumeralsProofAt outerBound index
                counter indexStrict).weakenClosedTo openedContext
              have normalizedTransitionAt : Derivation LogicMode.intuitionistic
                  haTheory openedContext
                  (ScopedFormula.impl
                    (scopedLessThanFormulaAt
                      (ScopedTerm.numeral outerBound index)
                      (ScopedTerm.numeral outerBound counter))
                    localTransitionBlock) := by
                refine Derivation.castConclusion ?_ transitionAt
                apply ScopedFormula.eq_of_raw_eq
                change
                  (RawFormula.impl transitionLess.raw
                    transitionExists.raw).substitute
                      (singleTermSubstitution (RawTerm.numeral index)) =
                    RawFormula.impl
                      (scopedLessThanFormulaAt
                        (ScopedTerm.numeral outerBound index)
                        (ScopedTerm.numeral outerBound counter)).raw
                      localTransitionBlock.raw
                apply congrArgTwo RawFormula.impl
                · dsimp [transitionLess, transitionIndex]
                  change
                    (lessThanFormula (RawTerm.bvar 0)
                        (RawTerm.numeral counter)).substitute
                        (singleTermSubstitution (RawTerm.numeral index)) =
                      lessThanFormula (RawTerm.numeral index)
                        (RawTerm.numeral counter)
                  rw [lessThanFormula_substitute]
                  apply congrArgTwo lessThanFormula
                  · rfl
                  · exact RawTerm.numeral_substitute _ _
                · apply congrArg RawFormula.ex
                  apply congrArg RawFormula.ex
                  apply congrArgTwo RawFormula.conj
                  · apply betaValueFormula_substitute_exact
                    · rw [liftedDividend_raw]
                      have lowered := termSubstitutionAtDepth_after
                        (RawTerm.numeral index) 2 0
                      exact lowered.trans localDividend_raw.symm
                    · rw [liftedCoefficient_raw]
                      have lowered := termSubstitutionAtDepth_after
                        (RawTerm.numeral index) 2 1
                      exact lowered.trans localCoefficient_raw.symm
                    · rw [liftedIndex_raw]
                      exact (termSubstitutionAtDepth_at
                        (RawTerm.numeral index) 2).trans
                          ((RawTerm.numeral_raise_any index 2).trans rfl)
                    · exact termSubstitutionAtDepth_of_lt
                        (RawTerm.numeral index) 2 0 (by decide)
                  · apply congrArgTwo RawFormula.conj
                    · apply betaValueFormula_substitute_exact
                      · rw [liftedDividend_raw]
                        have lowered := termSubstitutionAtDepth_after
                          (RawTerm.numeral index) 2 0
                        exact lowered.trans localDividend_raw.symm
                      · rw [liftedCoefficient_raw]
                        have lowered := termSubstitutionAtDepth_after
                          (RawTerm.numeral index) 2 1
                        exact lowered.trans localCoefficient_raw.symm
                      · apply congrArg RawTerm.succ
                        rw [liftedIndex_raw]
                        exact (termSubstitutionAtDepth_at
                          (RawTerm.numeral index) 2).trans
                            ((RawTerm.numeral_raise_any index 2).trans rfl)
                      · exact termSubstitutionAtDepth_of_lt
                          (RawTerm.numeral index) 2 1 (by decide)
                    · apply ArithmeticGraph.apply_substitute_exact_bounded
                      · exact termSubstitutionAtDepth_of_lt
                          (RawTerm.numeral index) 2 1 (by decide)
                      · intro position bounded
                        cases position with
                        | zero =>
                            change
                              liftedIndex.raw.substitute
                                  (termSubstitutionAtDepth
                                    (RawTerm.numeral index) 2) =
                                localIndex.raw
                            rw [liftedIndex_raw]
                            exact
                              (termSubstitutionAtDepth_at
                                (RawTerm.numeral index) 2).trans
                                ((RawTerm.numeral_raise_any index 2).trans rfl)
                        | succ position =>
                            cases position with
                            | zero =>
                                exact termSubstitutionAtDepth_of_lt
                                  (RawTerm.numeral index) 2 0 (by decide)
                            | succ position =>
                                change
                                  (parameters.numeralTerms.getD position).substitute
                                      (termSubstitutionAtDepth
                                        (RawTerm.numeral index) 2) =
                                    parameters.numeralTerms.getD position
                                rw [NatVector.numeralTerms_getD]
                                exact RawTerm.numeral_substitute _ _
              let transitionBlock := Derivation.implicationElimination
                normalizedTransitionAt lessProof
              let previousResult := valueAt index
              let nextResult := valueAt (Nat.succ index)
              let previousKnown := inductionHypothesis
                (Nat.le_of_lt indexStrict)
              apply Derivation.eliminateExistsMany 2 localTransitionCore
                transitionBlock
              intro transitionCoreProof
              let previousBeta := Derivation.conjunctionEliminationLeft
                transitionCoreProof
              let transitionRest := Derivation.conjunctionEliminationRight
                transitionCoreProof
              let nextBeta := Derivation.conjunctionEliminationLeft
                transitionRest
              let localStepGraph := Derivation.conjunctionEliminationRight
                transitionRest
              let transitionOpenedContext := existsManyEliminationContext 2
                localTransitionCore openedContext
              let liftedPreviousKnown : Derivation LogicMode.intuitionistic haTheory
                  transitionOpenedContext
                  (scopedBetaValueFormulaAt localDividend localCoefficient
                    localIndex
                    (ScopedTerm.numeral (2 + outerBound) previousResult)) := by
                let lifted :=
                  Derivation.weakenToExistsManyEliminationContext 2
                    localTransitionCore previousKnown
                refine Derivation.castConclusion ?_ lifted
                have liftedFormula := ScopedFormula.liftMany_betaValue 2
                  dividend coefficient (ScopedTerm.numeral outerBound index)
                  (ScopedTerm.numeral outerBound previousResult)
                rw [ScopedTerm.liftMany_numeral,
                  ScopedTerm.liftMany_numeral] at liftedFormula
                exact liftedFormula
              let previousEquality := betaValueFunctionalAt localDividend
                localCoefficient localIndex localPrevious
                (ScopedTerm.numeral (2 + outerBound) previousResult)
                previousBeta liftedPreviousKnown
              let replacedStep := replaceVariableUsingEquality
                localStepFormula 0 localPrevious.isScoped
                (ScopedTerm.numeral (2 + outerBound) previousResult)
                previousEquality localStepGraph
              have normalizedStep : Derivation LogicMode.intuitionistic haTheory
                  transitionOpenedContext
                  (step.graphFormula.numeralApplicationAt
                    (NatVector.cons index
                      (NatVector.cons previousResult parameters))
                    localNext) := by
                refine Derivation.castConclusion ?_ replacedStep
                apply ScopedFormula.eq_of_raw_eq
                change
                  (step.graphFormula.apply localNext.raw
                    (RawTermVector.cons localIndex.raw
                      (RawTermVector.cons localPrevious.raw
                        parameters.numeralTerms))).substitute
                      (replaceVariableSubstitutionAt 0
                        (ScopedTerm.numeral (2 + outerBound)
                          previousResult).raw 0) =
                    step.graphFormula.apply localNext.raw
                      (NatVector.cons index
                        (NatVector.cons previousResult parameters)).numeralTerms
                apply ArithmeticGraph.apply_substitute_exact_bounded
                · rfl
                · intro position bounded
                  cases position with
                  | zero =>
                      change
                        (RawTerm.numeral index).substitute _ =
                          RawTerm.numeral index
                      exact RawTerm.numeral_substitute _ _
                  | succ position =>
                      cases position with
                      | zero => rfl
                      | succ position =>
                          change
                            (parameters.numeralTerms.getD position).substitute _ =
                              parameters.numeralTerms.getD position
                          rw [NatVector.numeralTerms_getD]
                          exact RawTerm.numeral_substitute _ _
              let nextEquality := stepDeterminate.determine
                (NatVector.cons index
                  (NatVector.cons previousResult parameters))
                localNext normalizedStep
              have nextResultExact : nextResult =
                  step.run (NatVector.cons index
                    (NatVector.cons previousResult parameters)) := by
                exact PRFunction.run_primitive_succ base step index parameters
              let normalizedNextEquality : Derivation LogicMode.intuitionistic
                  haTheory transitionOpenedContext
                  (ScopedFormula.equal localNext
                    (ScopedTerm.numeral (2 + outerBound) nextResult)) := by
                refine Derivation.castConclusion ?_ nextEquality
                exact congrArg
                  (fun result => ScopedFormula.equal localNext
                    (ScopedTerm.numeral (2 + outerBound) result))
                  nextResultExact.symm
              let nextBetaFormula := scopedBetaValueFormulaAt localDividend
                localCoefficient localIndex.succ localNext
              let transportedNext := replaceVariableUsingEquality
                nextBetaFormula 1 localNext.isScoped
                (ScopedTerm.numeral (2 + outerBound) nextResult)
                normalizedNextEquality nextBeta
              have replacedNextExact :
                  nextBetaFormula.replaceVariable 1
                      (ScopedTerm.numeral (2 + outerBound) nextResult) =
                    scopedBetaValueFormulaAt localDividend localCoefficient
                      localIndex.succ
                      (ScopedTerm.numeral (2 + outerBound) nextResult) := by
                apply ScopedFormula.eq_of_raw_eq
                apply betaValueFormula_substitute_exact
                · rw [ScopedTerm.liftMany_raw]
                  dsimp [dividend]
                  rfl
                · rw [ScopedTerm.liftMany_raw]
                  dsimp [coefficient]
                  rfl
                · change
                    (RawTerm.succ (RawTerm.numeral index)).substitute _ =
                      RawTerm.succ (RawTerm.numeral index)
                  exact congrArg RawTerm.succ
                    (RawTerm.numeral_substitute index _)
                · rfl
              refine Derivation.castConclusion ?_ transportedNext
              have indexSuccessor : localIndex.succ =
                  ScopedTerm.numeral (2 + outerBound) (Nat.succ index) := by
                apply ScopedTerm.eq_of_raw_eq
                rfl
              have liftedFormula := ScopedFormula.liftMany_betaValue 2
                dividend coefficient
                (ScopedTerm.numeral outerBound (Nat.succ index))
                (ScopedTerm.numeral outerBound nextResult)
              rw [ScopedTerm.liftMany_numeral,
                ScopedTerm.liftMany_numeral] at liftedFormula
              change
                nextBetaFormula.replaceVariable 1
                    (ScopedTerm.numeral (2 + outerBound) nextResult) =
                  (scopedBetaValueFormulaAt dividend coefficient
                    (ScopedTerm.numeral outerBound (Nat.succ index))
                    (ScopedTerm.numeral outerBound nextResult)).liftMany 2
              exact replacedNextExact.trans ((congrArg
                  (fun currentIndex => scopedBetaValueFormulaAt localDividend
                    localCoefficient currentIndex
                    (ScopedTerm.numeral (2 + outerBound) nextResult))
                  indexSuccessor).trans liftedFormula.symm))
        let finalBeta := betaAt counter (Nat.le_refl counter)
        let result := betaValueFunctionalAt dividend coefficient
          (ScopedTerm.numeral outerBound counter) (output.liftMany 2)
          (ScopedTerm.numeral outerBound (valueAt counter))
          outputBeta finalBeta
        refine Derivation.castConclusion ?_ result
        have liftedConclusion := ScopedFormula.liftMany_equal 2 output
          (ScopedTerm.numeral bound
            ((PRFunction.primitiveRecursion base step).run
              (NatVector.cons counter parameters)))
        rw [ScopedTerm.liftMany_numeral] at liftedConclusion
        exact liftedConclusion.symm }

mutual
  def PRFunction.internalDeterminacyCompiler :
      {arity : Nat} ->
      (program : PRFunction arity) ->
      InternallyNumeralDeterminatePRFunction program
    | _, PRFunction.zero => internallyNumeralDeterminateZero
    | _, PRFunction.successor => internallyNumeralDeterminateSuccessor
    | _, PRFunction.projection arity index bounded =>
        internallyNumeralDeterminateProjection arity index bounded
    | _, PRFunction.composition outer inner =>
        internallyNumeralDeterminateComposition
          outer.internalDeterminacyCompiler
          inner.internalDeterminacyCompiler
    | _, PRFunction.primitiveRecursion base step =>
        internallyNumeralDeterminatePrimitiveRecursion
          base.internalDeterminacyCompiler step.internalDeterminacyCompiler

  def PRFunctionVector.internalDeterminacyCompiler :
      {inputArity outputArity : Nat} ->
      (programs : PRFunctionVector inputArity outputArity) ->
      InternallyNumeralDeterminatePRFunctionVector programs
    | _, _, PRFunctionVector.nil =>
        InternallyNumeralDeterminatePRFunctionVector.nil
    | _, _, PRFunctionVector.cons head tail =>
        InternallyNumeralDeterminatePRFunctionVector.cons
          head.internalDeterminacyCompiler tail.internalDeterminacyCompiler
end

def PRFunction.internalGraphFunctional
    {arity bound : Nat}
    (program : PRFunction arity)
    {context : FormulaContext bound}
    (inputs : NatVector arity)
    (output : ScopedTerm bound)
    (proof : Derivation LogicMode.intuitionistic haTheory context
      (program.graphFormula.numeralApplicationAt inputs output)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal output
        (ScopedTerm.numeral bound (program.run inputs))) :=
  program.internalDeterminacyCompiler.determine inputs output proof

def PRFunction.internalGraphNumeralRefutation
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity)
    (output : Nat)
    (different : output = program.run inputs -> False) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.neg (program.numeralGraphInstance inputs output)) := by
  apply Derivation.implicationIntroduction
  let wrongFormula := program.numeralGraphInstance inputs output
  let wrongContext := FormulaContext.cons wrongFormula FormulaContext.nil
  let wrongProof : Derivation LogicMode.intuitionistic haTheory wrongContext
      wrongFormula := Derivation.hypothesis ContextMember.here
  let normalizedWrong : Derivation LogicMode.intuitionistic haTheory wrongContext
      (program.graphFormula.numeralApplicationAt inputs
        (ScopedTerm.numeral 0 output)) := by
    simpa [wrongFormula, PRFunction.numeralGraphInstance,
      ArithmeticGraph.numeralInstance,
      ArithmeticGraph.numeralApplicationAt, ScopedTerm.numeral] using
        wrongProof
  let forced := program.internalGraphFunctional inputs
    (ScopedTerm.numeral 0 output) normalizedWrong
  let impossible := (numeralInequalityProof 0 output
    (program.run inputs) different).weakenClosedTo wrongContext
  let contradiction := Derivation.implicationElimination impossible (by
    simpa [numeralEqualityFormula] using forced)
  exact contradiction

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralDeterminateZero
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralDeterminateSuccessor
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralDeterminateProjection
#print axioms RelationalPerimeter.HeytingArithmetic.InternallyNumeralDeterminatePRFunction
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralDeterminateComposition
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralDeterminatePrimitiveRecursion
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.internalDeterminacyCompiler
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.internalGraphFunctional
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.internalGraphNumeralRefutation
/- AXIOM_AUDIT_END -/
