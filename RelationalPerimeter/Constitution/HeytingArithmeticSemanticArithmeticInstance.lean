import RelationalPerimeter.Constitution.HeytingArithmetic.InformativeRepresentability

/-!
# Informative semantic arithmetic instance for Heyting arithmetic

This module gives the already checked HA calculus the exact first-order
arithmetic presentation required by `SemanticallyDefinedProofArithmeticTheory`.
The translation is syntactic, its inverse is executable on the disjunction-free
fragment used here, and soundness is obtained from informative realizers rather
than by eliminating a proposition-valued existential.
-/

/-! ## Exact syntax bridge -/

namespace StrongPerimetralTurning

open RelationalPerimeter.HeytingArithmetic

def FirstOrderArithmeticTerm.toRaw
    {arity : Nat} (term : FirstOrderArithmeticTerm arity) : RawTerm :=
  match term with
  | .variable index => .bvar index.val
  | .zero => .zero
  | .successor body => .succ body.toRaw
  | .addition left right => .add left.toRaw right.toRaw
  | .multiplication left right => .mul left.toRaw right.toRaw

def FirstOrderArithmeticTerm.toScoped
    {arity : Nat} (term : FirstOrderArithmeticTerm arity) :
    ScopedTerm arity :=
  match term with
  | .variable index => ScopedTerm.bvar index.val index.isLt
  | .zero => ScopedTerm.zero arity
  | .successor body => ScopedTerm.succ body.toScoped
  | .addition left right => ScopedTerm.add left.toScoped right.toScoped
  | .multiplication left right => ScopedTerm.mul left.toScoped right.toScoped

@[simp] theorem FirstOrderArithmeticTerm.toScoped_raw
    {arity : Nat} (term : FirstOrderArithmeticTerm arity) :
    term.toScoped.raw = term.toRaw := by
  induction term with
  | «variable» index =>
      unfold FirstOrderArithmeticTerm.toScoped
        FirstOrderArithmeticTerm.toRaw ScopedTerm.bvar
      rfl
  | zero =>
      unfold FirstOrderArithmeticTerm.toScoped
        FirstOrderArithmeticTerm.toRaw ScopedTerm.zero
      rfl
  | successor body inductionHypothesis =>
      unfold FirstOrderArithmeticTerm.toScoped
        FirstOrderArithmeticTerm.toRaw ScopedTerm.succ
      exact congrArg RawTerm.succ inductionHypothesis
  | addition left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticTerm.toScoped
        FirstOrderArithmeticTerm.toRaw ScopedTerm.add
      exact congrArgTwo RawTerm.add leftInduction rightInduction
  | multiplication left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticTerm.toScoped
        FirstOrderArithmeticTerm.toRaw ScopedTerm.mul
      exact congrArgTwo RawTerm.mul leftInduction rightInduction

def FirstOrderArithmeticFormula.toScoped :
    {arity : Nat} -> FirstOrderArithmeticFormula arity -> ScopedFormula arity
  | _, .equal left right => ScopedFormula.equal left.toScoped right.toScoped
  | arity, .falsity => ScopedFormula.falsum arity
  | _, .implication left right =>
      ScopedFormula.impl left.toScoped right.toScoped
  | _, .conjunction left right =>
      ScopedFormula.conj left.toScoped right.toScoped
  | _, .universal body => ScopedFormula.all body.toScoped
  | _, .existential body => ScopedFormula.ex body.toScoped

end StrongPerimetralTurning

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

set_option linter.defProp false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

def RawTerm.toFirstOrder? (arity : Nat) : RawTerm ->
    Option (FirstOrderArithmeticTerm arity)
  | .bvar index =>
      if bounded : index < arity then
        some (.variable ⟨index, bounded⟩)
      else
        none
  | .zero => some .zero
  | .succ body => do
      pure (.successor (← body.toFirstOrder? arity))
  | .add left right => do
      pure (.addition (← left.toFirstOrder? arity)
        (← right.toFirstOrder? arity))
  | .mul left right => do
      pure (.multiplication (← left.toFirstOrder? arity)
        (← right.toFirstOrder? arity))

def RawFormula.toFirstOrder? (arity : Nat) : RawFormula ->
    Option (FirstOrderArithmeticFormula arity)
  | .falsum => some .falsity
  | .equal left right => do
      pure (.equal (← left.toFirstOrder? arity)
        (← right.toFirstOrder? arity))
  | .conj left right => do
      pure (.conjunction (← left.toFirstOrder? arity)
        (← right.toFirstOrder? arity))
  | .disj _left _right => none
  | .impl left right => do
      pure (.implication (← left.toFirstOrder? arity)
        (← right.toFirstOrder? arity))
  | .all body => do
      pure (.universal (← body.toFirstOrder? (Nat.succ arity)))
  | .ex body => do
      pure (.existential (← body.toFirstOrder? (Nat.succ arity)))

theorem RawTerm.toFirstOrder?_toRaw
    {arity : Nat} (term : FirstOrderArithmeticTerm arity) :
    term.toRaw.toFirstOrder? arity = some term := by
  induction term with
  | «variable» index =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.toFirstOrder?
      rw [dif_pos index.isLt]
  | zero =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.toFirstOrder?
      rfl
  | successor body inductionHypothesis =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.toFirstOrder?
      rw [inductionHypothesis]
      rfl
  | addition left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.toFirstOrder?
      rw [leftInduction, rightInduction]
      rfl
  | multiplication left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.toFirstOrder?
      rw [leftInduction, rightInduction]
      rfl

theorem RawFormula.toFirstOrder?_toScopedRaw
    {arity : Nat} (formula : FirstOrderArithmeticFormula arity) :
    formula.toScoped.raw.toFirstOrder? arity = some formula := by
  induction formula with
  | equal left right =>
      unfold FirstOrderArithmeticFormula.toScoped ScopedFormula.equal
        RawFormula.toFirstOrder?
      rw [FirstOrderArithmeticTerm.toScoped_raw,
        FirstOrderArithmeticTerm.toScoped_raw,
        RawTerm.toFirstOrder?_toRaw, RawTerm.toFirstOrder?_toRaw]
      rfl
  | falsity => rfl
  | implication left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticFormula.toScoped ScopedFormula.impl
        RawFormula.toFirstOrder?
      rw [leftInduction, rightInduction]
      rfl
  | conjunction left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticFormula.toScoped ScopedFormula.conj
        RawFormula.toFirstOrder?
      rw [leftInduction, rightInduction]
      rfl
  | universal body inductionHypothesis =>
      unfold FirstOrderArithmeticFormula.toScoped ScopedFormula.all
        RawFormula.toFirstOrder?
      rw [inductionHypothesis]
      rfl
  | existential body inductionHypothesis =>
      unfold FirstOrderArithmeticFormula.toScoped ScopedFormula.ex
        RawFormula.toFirstOrder?
      rw [inductionHypothesis]
      rfl

def RawFormula.DisjunctionFree : RawFormula -> Prop
  | .falsum => True
  | .equal _left _right => True
  | .conj left right => left.DisjunctionFree ∧ right.DisjunctionFree
  | .disj _left _right => False
  | .impl left right => left.DisjunctionFree ∧ right.DisjunctionFree
  | .all body => body.DisjunctionFree
  | .ex body => body.DisjunctionFree

def RawTerm.toFirstOrder (arity : Nat) :
    (term : RawTerm) -> term.WellScoped arity ->
      FirstOrderArithmeticTerm arity
  | .bvar index, bounded => .variable ⟨index, bounded⟩
  | .zero, _scopeEvidence => .zero
  | .succ body, scopeEvidence =>
      .successor (body.toFirstOrder arity scopeEvidence)
  | .add left right, scopeEvidence =>
      .addition (left.toFirstOrder arity scopeEvidence.1)
        (right.toFirstOrder arity scopeEvidence.2)
  | .mul left right, scopeEvidence =>
      .multiplication (left.toFirstOrder arity scopeEvidence.1)
        (right.toFirstOrder arity scopeEvidence.2)

def RawFormula.toFirstOrder (arity : Nat) :
    (formula : RawFormula) -> formula.WellScoped arity ->
      formula.DisjunctionFree -> FirstOrderArithmeticFormula arity
  | .falsum, _scopeEvidence, _disjunctionFree => .falsity
  | .equal left right, scopeEvidence, _disjunctionFree =>
      .equal (left.toFirstOrder arity scopeEvidence.1)
        (right.toFirstOrder arity scopeEvidence.2)
  | .conj left right, scopeEvidence, disjunctionFree =>
      .conjunction
        (left.toFirstOrder arity scopeEvidence.1 disjunctionFree.1)
        (right.toFirstOrder arity scopeEvidence.2 disjunctionFree.2)
  | .disj _left _right, _scopeEvidence, disjunctionFree =>
      disjunctionFree.elim
  | .impl left right, scopeEvidence, disjunctionFree =>
      .implication
        (left.toFirstOrder arity scopeEvidence.1 disjunctionFree.1)
        (right.toFirstOrder arity scopeEvidence.2 disjunctionFree.2)
  | .all body, scopeEvidence, disjunctionFree =>
      .universal
        (body.toFirstOrder (Nat.succ arity) scopeEvidence disjunctionFree)
  | .ex body, scopeEvidence, disjunctionFree =>
      .existential
        (body.toFirstOrder (Nat.succ arity) scopeEvidence disjunctionFree)

theorem RawTerm.toFirstOrder_translation
    (term : RawTerm) (arity : Nat) (scopeEvidence : term.WellScoped arity) :
    (term.toFirstOrder arity scopeEvidence).toRaw = term := by
  induction term with
  | bvar index =>
      unfold RawTerm.toFirstOrder FirstOrderArithmeticTerm.toRaw
      rfl
  | zero =>
      unfold RawTerm.toFirstOrder FirstOrderArithmeticTerm.toRaw
      rfl
  | succ body inductionHypothesis =>
      unfold RawTerm.toFirstOrder FirstOrderArithmeticTerm.toRaw
      exact congrArg RawTerm.succ (inductionHypothesis scopeEvidence)
  | add left right leftInduction rightInduction =>
      unfold RawTerm.toFirstOrder FirstOrderArithmeticTerm.toRaw
      exact congrArgTwo RawTerm.add
        (leftInduction scopeEvidence.1) (rightInduction scopeEvidence.2)
  | mul left right leftInduction rightInduction =>
      unfold RawTerm.toFirstOrder FirstOrderArithmeticTerm.toRaw
      exact congrArgTwo RawTerm.mul
        (leftInduction scopeEvidence.1) (rightInduction scopeEvidence.2)

theorem RawFormula.toFirstOrder_translation
    (formula : RawFormula) (arity : Nat)
    (scopeEvidence : formula.WellScoped arity)
    (disjunctionFree : formula.DisjunctionFree) :
    (formula.toFirstOrder arity scopeEvidence disjunctionFree).toScoped.raw =
      formula := by
  induction formula generalizing arity with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (Eq.trans
          (FirstOrderArithmeticTerm.toScoped_raw
            (left.toFirstOrder arity scopeEvidence.1))
          (left.toFirstOrder_translation arity scopeEvidence.1))
        (Eq.trans
          (FirstOrderArithmeticTerm.toScoped_raw
            (right.toFirstOrder arity scopeEvidence.2))
          (right.toFirstOrder_translation arity scopeEvidence.2))
  | conj left right leftInduction rightInduction =>
      exact congrArgTwo RawFormula.conj
        (leftInduction arity scopeEvidence.1 disjunctionFree.1)
        (rightInduction arity scopeEvidence.2 disjunctionFree.2)
  | disj left right => exact disjunctionFree.elim
  | impl left right leftInduction rightInduction =>
      exact congrArgTwo RawFormula.impl
        (leftInduction arity scopeEvidence.1 disjunctionFree.1)
        (rightInduction arity scopeEvidence.2 disjunctionFree.2)
  | all body inductionHypothesis =>
      exact congrArg RawFormula.all
        (inductionHypothesis (Nat.succ arity) scopeEvidence disjunctionFree)
  | ex body inductionHypothesis =>
      exact congrArg RawFormula.ex
        (inductionHypothesis (Nat.succ arity) scopeEvidence disjunctionFree)

def ScopedFormula.toFirstOrder
    {arity : Nat} (formula : ScopedFormula arity)
    (disjunctionFree : formula.raw.DisjunctionFree) :
    FirstOrderArithmeticFormula arity :=
  formula.raw.toFirstOrder arity formula.isScoped disjunctionFree

theorem ScopedFormula.toFirstOrder_translation
    {arity : Nat} (formula : ScopedFormula arity)
    (disjunctionFree : formula.raw.DisjunctionFree) :
    (formula.toFirstOrder disjunctionFree).toScoped = formula := by
  apply ScopedFormula.eq_of_raw_eq
  exact formula.raw.toFirstOrder_translation arity
    formula.isScoped disjunctionFree

def decodeFirstOrderFormula (arity code : Nat) :
    Option (FirstOrderArithmeticFormula arity) := do
  let formula ← decodeScopedFormula arity code
  formula.raw.toFirstOrder? arity

def encodeFirstOrderFormula
    {arity : Nat} (formula : FirstOrderArithmeticFormula arity) : Nat :=
  formula.toScoped.raw.code

theorem decodeFirstOrderFormula_encode
    {arity : Nat} (formula : FirstOrderArithmeticFormula arity) :
    decodeFirstOrderFormula arity (encodeFirstOrderFormula formula) =
      some formula := by
  unfold decodeFirstOrderFormula encodeFirstOrderFormula
  rw [decodeScopedFormula_code formula.toScoped]
  exact RawFormula.toFirstOrder?_toScopedRaw formula

/-! ## Closure of the represented fragment -/

def firstOrderArithmeticFormulaToScoped_disjunctionFree :
    {arity : Nat} -> (formula : FirstOrderArithmeticFormula arity) ->
      formula.toScoped.raw.DisjunctionFree
  | _, .equal _left _right => trivial
  | _, .falsity => trivial
  | _, .implication left right =>
      And.intro
        (firstOrderArithmeticFormulaToScoped_disjunctionFree left)
        (firstOrderArithmeticFormulaToScoped_disjunctionFree right)
  | _, .conjunction left right =>
      And.intro
        (firstOrderArithmeticFormulaToScoped_disjunctionFree left)
        (firstOrderArithmeticFormulaToScoped_disjunctionFree right)
  | _, .universal body =>
      firstOrderArithmeticFormulaToScoped_disjunctionFree body
  | _, .existential body =>
      firstOrderArithmeticFormulaToScoped_disjunctionFree body

def RawFormula.disjunctionFree_rename
    (formula : RawFormula) (rho : Renaming) :
    formula.DisjunctionFree -> (formula.rename rho).DisjunctionFree :=
  match formula with
  | .falsum => fun _evidence => trivial
  | .equal _left _right => fun _evidence => trivial
  | .conj left right => fun evidence =>
      And.intro (left.disjunctionFree_rename rho evidence.1)
        (right.disjunctionFree_rename rho evidence.2)
  | .disj _left _right => fun evidence => evidence.elim
  | .impl left right => fun evidence =>
      And.intro (left.disjunctionFree_rename rho evidence.1)
        (right.disjunctionFree_rename rho evidence.2)
  | .all body => fun evidence =>
      body.disjunctionFree_rename (liftRenaming rho) evidence
  | .ex body => fun evidence =>
      body.disjunctionFree_rename (liftRenaming rho) evidence

def RawFormula.disjunctionFree_substitute
    (formula : RawFormula) (substitution : Substitution) :
    formula.DisjunctionFree ->
      (formula.substitute substitution).DisjunctionFree :=
  match formula with
  | .falsum => fun _evidence => trivial
  | .equal _left _right => fun _evidence => trivial
  | .conj left right => fun evidence =>
      And.intro (left.disjunctionFree_substitute substitution evidence.1)
        (right.disjunctionFree_substitute substitution evidence.2)
  | .disj _left _right => fun evidence => evidence.elim
  | .impl left right => fun evidence =>
      And.intro (left.disjunctionFree_substitute substitution evidence.1)
        (right.disjunctionFree_substitute substitution evidence.2)
  | .all body => fun evidence =>
      body.disjunctionFree_substitute (liftSubstitution substitution) evidence
  | .ex body => fun evidence =>
      body.disjunctionFree_substitute (liftSubstitution substitution) evidence

def RawFormula.existsMany_disjunctionFree
    (count : Nat) (formula : RawFormula) :
    formula.DisjunctionFree -> (formula.existsMany count).DisjunctionFree :=
  match count with
  | 0 => fun evidence => evidence
  | Nat.succ earlier => fun evidence =>
      (RawFormula.ex formula).existsMany_disjunctionFree earlier evidence

def lessThanFormula_disjunctionFree (left right : RawTerm) :
    (lessThanFormula left right).DisjunctionFree :=
  trivial

def remainderFormula_disjunctionFree
    (dividend modulus remainder : RawTerm) :
    (remainderFormula dividend modulus remainder).DisjunctionFree :=
  And.intro (lessThanFormula_disjunctionFree remainder modulus) trivial

def betaValueFormula_disjunctionFree
    (dividend coefficient index value : RawTerm) :
    (betaValueFormula dividend coefficient index value).DisjunctionFree :=
  remainderFormula_disjunctionFree dividend
    (betaModulusTerm coefficient index) value

def ArithmeticGraph.apply_disjunctionFree
    {arity : Nat} (graph : ArithmeticGraph arity)
    (output : RawTerm) (inputs : RawTermVector arity) :
    graph.raw.DisjunctionFree ->
      (graph.apply output inputs).DisjunctionFree :=
  graph.raw.disjunctionFree_substitute _

def ArithmeticGraphVector.DisjunctionFree :
    {inputArity length : Nat} ->
      ArithmeticGraphVector inputArity length -> Prop
  | _, _, .nil => True
  | _, _, .cons head tail =>
      head.raw.DisjunctionFree ∧ tail.DisjunctionFree

def ArithmeticGraphVector.body_disjunctionFree
    {inputArity length : Nat}
    (graphs : ArithmeticGraphVector inputArity length) :
    (offset total : Nat) ->
    (fits : offset + length <= total) ->
    graphs.DisjunctionFree ->
      (graphs.body offset total fits).raw.DisjunctionFree :=
  match graphs with
  | .nil => fun _offset _total _fits _evidence => And.intro trivial trivial
  | .cons head tail => fun offset total fits evidence =>
      And.intro
        (head.apply_disjunctionFree
          (RawTerm.bvar offset)
          (RawTermVector.variables (Nat.succ total) inputArity)
          evidence.1)
        (tail.body_disjunctionFree (Nat.succ offset) total
          (succOffsetTailFits fits) evidence.2)

mutual
  def PRFunction.graphFormula_disjunctionFree :
      {arity : Nat} -> (program : PRFunction arity) ->
        program.graphFormula.raw.DisjunctionFree
    | _, .zero => trivial
    | _, .successor => trivial
    | _, .projection _arity _index _bounded => trivial
    | _, .composition outer inner =>
        (RawFormula.conj
          (outer.graphFormula.apply
            (RawTerm.bvar _)
            (RawTermVector.variables 0 _))
          (inner.graphFormulas.body 0 _ (zeroOffsetFits _)).raw
        ).existsMany_disjunctionFree _
          (And.intro
            (outer.graphFormula.apply_disjunctionFree _ _
              outer.graphFormula_disjunctionFree)
            (inner.graphFormulas.body_disjunctionFree
              0 _ (zeroOffsetFits _)
              inner.graphFormulas_disjunctionFree))
    | _, @PRFunction.primitiveRecursion parameterArity base step =>
        let baseCore := RawFormula.conj
          (betaValueFormula
            (RawTerm.bvar 1) (RawTerm.bvar 2)
            RawTerm.zero (RawTerm.bvar 0))
          (base.graphFormula.apply (RawTerm.bvar 0)
            (primitiveBaseParameters parameterArity))
        let baseClause := RawFormula.ex baseCore
        let transitionCore := RawFormula.conj
          (betaValueFormula
            (RawTerm.bvar 3) (RawTerm.bvar 4)
            (RawTerm.bvar 2) (RawTerm.bvar 0))
          (RawFormula.conj
            (betaValueFormula
              (RawTerm.bvar 3) (RawTerm.bvar 4)
              (RawTerm.succ (RawTerm.bvar 2)) (RawTerm.bvar 1))
            (step.graphFormula.apply (RawTerm.bvar 1)
              (primitiveStepInputs parameterArity)))
        let transitionClause := RawFormula.all
          (RawFormula.impl
            (lessThanFormula (RawTerm.bvar 0) (RawTerm.bvar 4))
            (transitionCore.existsMany 2))
        let outputClause := betaValueFormula
          (RawTerm.bvar 0) (RawTerm.bvar 1)
          (RawTerm.bvar 3) (RawTerm.bvar 2)
        let body := RawFormula.conj baseClause
          (RawFormula.conj transitionClause outputClause)
        body.existsMany_disjunctionFree 2
          (And.intro
            (And.intro
              (betaValueFormula_disjunctionFree _ _ _ _)
              (base.graphFormula.apply_disjunctionFree _ _
                base.graphFormula_disjunctionFree))
            (And.intro
              (And.intro (lessThanFormula_disjunctionFree _ _)
                (transitionCore.existsMany_disjunctionFree 2
                  (And.intro
                    (betaValueFormula_disjunctionFree _ _ _ _)
                    (And.intro
                      (betaValueFormula_disjunctionFree _ _ _ _)
                      (step.graphFormula.apply_disjunctionFree _ _
                        step.graphFormula_disjunctionFree)))))
              (betaValueFormula_disjunctionFree _ _ _ _)))

  def PRFunctionVector.graphFormulas_disjunctionFree :
      {inputArity outputArity : Nat} ->
      (programs : PRFunctionVector inputArity outputArity) ->
        programs.graphFormulas.DisjunctionFree
    | _, _, .nil => trivial
    | _, _, .cons head tail =>
        And.intro head.graphFormula_disjunctionFree
          tail.graphFormulas_disjunctionFree
end

def PRFunctionVector.graphFormulas_body_disjunctionFree
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity) :
    (offset total : Nat) ->
    (fits : offset + outputArity <= total) ->
    (programs.graphFormulas.body offset total fits).raw.DisjunctionFree :=
  fun offset total fits => programs.graphFormulas.body_disjunctionFree
    offset total fits programs.graphFormulas_disjunctionFree

/-! ## Informative semantic preservation -/

theorem firstOrderArithmeticTermToRaw_evaluate
    {arity : Nat} (term : FirstOrderArithmeticTerm arity)
    (assignment : Nat → Nat) :
    term.toRaw.evaluate assignment = term.evaluate assignment := by
  induction term with
  | «variable» index => rfl
  | zero => rfl
  | successor body inductionHypothesis =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.evaluate
        FirstOrderArithmeticTerm.evaluate
      exact congrArg Nat.succ inductionHypothesis
  | addition left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.evaluate
        FirstOrderArithmeticTerm.evaluate
      exact congrArgTwo Nat.add leftInduction rightInduction
  | multiplication left right leftInduction rightInduction =>
      unfold FirstOrderArithmeticTerm.toRaw RawTerm.evaluate
        FirstOrderArithmeticTerm.evaluate
      exact congrArgTwo Nat.mul leftInduction rightInduction

def firstOrderArithmeticFormulaTruthRealizerEquivalence
    {arity : Nat} (formula : FirstOrderArithmeticFormula arity)
    (assignment : Nat → Nat) :
    RealizerEquivalence
      (formula.Truth assignment)
      (formula.toScoped.raw.Realizes assignment) :=
  match formula with
  | .equal left right =>
      { forward := fun equality => ⟨by
          rw [FirstOrderArithmeticTerm.toScoped_raw,
            FirstOrderArithmeticTerm.toScoped_raw,
            firstOrderArithmeticTermToRaw_evaluate,
            firstOrderArithmeticTermToRaw_evaluate]
          exact equality.down⟩
        backward := fun equality => ⟨by
          change PLift
            (left.toScoped.raw.evaluate assignment =
              right.toScoped.raw.evaluate assignment) at equality
          rw [FirstOrderArithmeticTerm.toScoped_raw,
            FirstOrderArithmeticTerm.toScoped_raw,
            firstOrderArithmeticTermToRaw_evaluate,
            firstOrderArithmeticTermToRaw_evaluate] at equality
          exact equality.down⟩ }
  | .falsity =>
      { forward := fun impossible => impossible.elim
        backward := fun impossible => impossible.elim }
  | .implication antecedent consequent =>
      let antecedentEquivalence :=
        firstOrderArithmeticFormulaTruthRealizerEquivalence
          antecedent assignment
      let consequentEquivalence :=
        firstOrderArithmeticFormulaTruthRealizerEquivalence
          consequent assignment
      { forward := fun implication antecedentRealizer =>
          consequentEquivalence.forward
            (implication
              (antecedentEquivalence.backward antecedentRealizer))
        backward := fun implication antecedentTruth =>
          consequentEquivalence.backward
            (implication
              (antecedentEquivalence.forward antecedentTruth)) }
  | .conjunction left right =>
      let leftEquivalence :=
        firstOrderArithmeticFormulaTruthRealizerEquivalence left assignment
      let rightEquivalence :=
        firstOrderArithmeticFormulaTruthRealizerEquivalence right assignment
      { forward := fun pair =>
          (leftEquivalence.forward pair.1,
            rightEquivalence.forward pair.2)
        backward := fun pair =>
          (leftEquivalence.backward pair.1,
            rightEquivalence.backward pair.2) }
  | .universal body =>
      { forward := fun universal value =>
          let recursive := firstOrderArithmeticFormulaTruthRealizerEquivalence
            body
            (FirstOrderArithmeticFormula.extendAssignment value assignment)
          let congruence := body.toScoped.raw.realizes_congr
            (FirstOrderArithmeticFormula.extendAssignment value assignment)
            (pushEnvironment assignment value)
            (fun index => by cases index <;> rfl)
          congruence.forward (recursive.forward (universal value))
        backward := fun universal value =>
          let recursive := firstOrderArithmeticFormulaTruthRealizerEquivalence
            body
            (FirstOrderArithmeticFormula.extendAssignment value assignment)
          let congruence := body.toScoped.raw.realizes_congr
            (FirstOrderArithmeticFormula.extendAssignment value assignment)
            (pushEnvironment assignment value)
            (fun index => by cases index <;> rfl)
          recursive.backward (congruence.backward (universal value)) }
  | .existential body =>
      { forward := fun existential =>
          let recursive := firstOrderArithmeticFormulaTruthRealizerEquivalence
            body
            (FirstOrderArithmeticFormula.extendAssignment
              existential.1 assignment)
          let congruence := body.toScoped.raw.realizes_congr
            (FirstOrderArithmeticFormula.extendAssignment
              existential.1 assignment)
            (pushEnvironment assignment existential.1)
            (fun index => by cases index <;> rfl)
          ⟨existential.1,
            congruence.forward (recursive.forward existential.2)⟩
        backward := fun existential =>
          let recursive := firstOrderArithmeticFormulaTruthRealizerEquivalence
            body
            (FirstOrderArithmeticFormula.extendAssignment
              existential.1 assignment)
          let congruence := body.toScoped.raw.realizes_congr
            (FirstOrderArithmeticFormula.extendAssignment
              existential.1 assignment)
            (pushEnvironment assignment existential.1)
            (fun index => by cases index <;> rfl)
          ⟨existential.1,
            recursive.backward (congruence.backward existential.2)⟩ }

/-- The indexed form of the same semantic bridge. Keeping the translated
formula as an index avoids normalizing the full proof-checker graph when the
bridge is specialized to the represented proof relation. -/
def firstOrderArithmeticFormulaTruthInformativeWitnessEquivalence
    {arity : Nat} (formula : FirstOrderArithmeticFormula arity)
    (assignment : Nat → Nat) :
    RealizerEquivalence
      (formula.Truth assignment)
      (RawFormula.InformativeWitness assignment formula.toScoped.raw) :=
  let direct :=
    firstOrderArithmeticFormulaTruthRealizerEquivalence formula assignment
  { forward := fun truth =>
      RawFormula.realizesToInformativeWitness formula.toScoped.raw assignment
        (direct.forward truth)
    backward := fun witness =>
      direct.backward
        (RawFormula.informativeWitnessToRealizes formula.toScoped.raw assignment
          witness) }

def Predicate.applyNumeral_realizerEquivalence
    (predicate : Predicate) (value : Nat) :
    RealizerEquivalence
      ((predicate.applyNumeral value).raw.Realizes emptyEnvironment)
      (predicate.raw.Realizes (pushEnvironment emptyEnvironment value)) :=
  let substituted := predicate.raw.realizes_substitute
    (fun _index => RawTerm.numeral value) emptyEnvironment
  let scopedCongruence := predicate.raw.realizes_congrScoped
    predicate.isScoped
    (fun index => (RawTerm.numeral value).evaluate emptyEnvironment)
    (pushEnvironment emptyEnvironment value)
    (fun index bounded => by
      cases index with
      | zero => exact RawTerm.evaluate_numeral value emptyEnvironment
      | succ index =>
          exact (Nat.not_lt_zero index
            (Nat.lt_of_succ_lt_succ bounded)).elim)
  { forward := fun realizer =>
      scopedCongruence.forward (substituted.forward realizer)
    backward := fun realizer =>
      substituted.backward (scopedCongruence.backward realizer) }

/-! ## Exact HA operations presented in first-order arithmetic -/

def firstOrderPredicate
    (formula : FirstOrderArithmeticFormula 1) : Predicate :=
  { raw := formula.toScoped.raw
    isScoped := formula.toScoped.isScoped }

def firstOrderSentence
    (formula : FirstOrderArithmeticFormula 0) : Sentence :=
  { raw := formula.toScoped.raw
    isScoped := formula.toScoped.isScoped }

def firstOrderSubstituteNumeralDisjunctionFree
    (formula : FirstOrderArithmeticFormula 1) (value : Nat) :
    ((firstOrderPredicate formula).applyNumeral value).raw.DisjunctionFree := by
  unfold firstOrderPredicate Predicate.applyNumeral
    RawFormula.instantiateNumeral
  exact RawFormula.disjunctionFree_substitute _ _
    (firstOrderArithmeticFormulaToScoped_disjunctionFree formula)

def firstOrderSubstituteNumeral
    (formula : FirstOrderArithmeticFormula 1) (value : Nat) :
    FirstOrderArithmeticFormula 0 :=
  let sentence := (firstOrderPredicate formula).applyNumeral value
  sentence.scopedFormula.toFirstOrder
    (firstOrderSubstituteNumeralDisjunctionFree formula value)

theorem firstOrderSubstituteNumeral_translation
    (formula : FirstOrderArithmeticFormula 1) (value : Nat) :
    (firstOrderSubstituteNumeral formula value).toScoped =
      ((firstOrderPredicate formula).applyNumeral value).scopedFormula :=
  ScopedFormula.toFirstOrder_translation _ _

def firstOrderSubstituteNumeralTruthForward
    (formula : FirstOrderArithmeticFormula 1) (value : Nat) :
    FirstOrderArithmeticFormula.sentenceTruth
        (firstOrderSubstituteNumeral formula value) ->
      FirstOrderArithmeticFormula.Truth
        (FirstOrderArithmeticFormula.unaryAssignment value) formula :=
  fun sentenceTruth =>
    let sentenceEquivalence :=
      firstOrderArithmeticFormulaTruthRealizerEquivalence
        (firstOrderSubstituteNumeral formula value) emptyEnvironment
    let translatedSentenceRealizer := sentenceEquivalence.forward sentenceTruth
    let appliedRealizer :
        ((firstOrderPredicate formula).applyNumeral value).raw.Realizes
          emptyEnvironment :=
      Eq.mp
        (congrArg
          (fun scopedFormula : ScopedFormula 0 =>
            scopedFormula.raw.Realizes emptyEnvironment)
          (firstOrderSubstituteNumeral_translation formula value))
        translatedSentenceRealizer
    let predicateRealizer :=
      ((firstOrderPredicate formula).applyNumeral_realizerEquivalence value).forward
        appliedRealizer
    let unaryCongruence := formula.toScoped.raw.realizes_congr
      (pushEnvironment emptyEnvironment value)
      (FirstOrderArithmeticFormula.unaryAssignment value)
      (fun index => by cases index <;> rfl)
    (firstOrderArithmeticFormulaTruthRealizerEquivalence formula
      (FirstOrderArithmeticFormula.unaryAssignment value)).backward
        (unaryCongruence.forward predicateRealizer)

def firstOrderSubstituteNumeralTruthBackward
    (formula : FirstOrderArithmeticFormula 1) (value : Nat) :
    FirstOrderArithmeticFormula.Truth
        (FirstOrderArithmeticFormula.unaryAssignment value) formula ->
      FirstOrderArithmeticFormula.sentenceTruth
        (firstOrderSubstituteNumeral formula value) :=
  fun formulaTruth =>
    let formulaEquivalence :=
      firstOrderArithmeticFormulaTruthRealizerEquivalence formula
        (FirstOrderArithmeticFormula.unaryAssignment value)
    let unaryCongruence := formula.toScoped.raw.realizes_congr
      (FirstOrderArithmeticFormula.unaryAssignment value)
      (pushEnvironment emptyEnvironment value)
      (fun index => by cases index <;> rfl)
    let predicateRealizer := unaryCongruence.forward
      (formulaEquivalence.forward formulaTruth)
    let appliedRealizer :=
      ((firstOrderPredicate formula).applyNumeral_realizerEquivalence value).backward
        predicateRealizer
    let translatedSentenceRealizer :
        (firstOrderSubstituteNumeral formula value).toScoped.raw.Realizes
          emptyEnvironment :=
      Eq.mpr
        (congrArg
          (fun scopedFormula : ScopedFormula 0 =>
            scopedFormula.raw.Realizes emptyEnvironment)
          (firstOrderSubstituteNumeral_translation formula value))
        appliedRealizer
    (firstOrderArithmeticFormulaTruthRealizerEquivalence
      (firstOrderSubstituteNumeral formula value) emptyEnvironment).backward
        translatedSentenceRealizer

def internalFixedPointBody_disjunctionFree
    (target : Predicate) (targetDisjunctionFree : target.raw.DisjunctionFree) :
    (internalFixedPointBody target).raw.DisjunctionFree := by
  unfold internalFixedPointBody
  exact And.intro
    (diagonalSubstitutionGraph.apply_disjunctionFree _ _
      PRFunction.captureAvoidingDiagonalSubstitution.graphFormula_disjunctionFree)
    (target.raw.disjunctionFree_substitute _ targetDisjunctionFree)

def firstOrderDiagonalize
    (formula : FirstOrderArithmeticFormula 1) :
    FirstOrderArithmeticFormula 1 :=
  let diagonal := internalFixedPointBody (firstOrderPredicate formula)
  let scopedDiagonal : ScopedFormula 1 :=
    { raw := diagonal.raw, isScoped := diagonal.isScoped }
  scopedDiagonal.toFirstOrder
    (internalFixedPointBody_disjunctionFree
      (firstOrderPredicate formula)
      (firstOrderArithmeticFormulaToScoped_disjunctionFree formula))

theorem firstOrderDiagonalize_translation
    (formula : FirstOrderArithmeticFormula 1) :
    (firstOrderDiagonalize formula).toScoped =
      { raw := (internalFixedPointBody (firstOrderPredicate formula)).raw
        isScoped :=
          (internalFixedPointBody (firstOrderPredicate formula)).isScoped } :=
  ScopedFormula.toFirstOrder_translation _ _

def informativeProofFormula_disjunctionFree :
    informativeProofFormula.raw.DisjunctionFree := by
  unfold informativeProofFormula
  exact informativeProofCheckProgram.graphFormula.apply_disjunctionFree _ _
    informativeProofCheckProgram.graphFormula_disjunctionFree

def informativeHistoryProofFormula_disjunctionFree
    (history : TheoryHistory) :
    (informativeHistoryProofFormula history).raw.DisjunctionFree := by
  unfold informativeHistoryProofFormula ScopedFormula.instantiate
    RawFormula.instantiateTerm
  exact informativeProofFormula.raw.disjunctionFree_substitute _
    informativeProofFormula_disjunctionFree

def firstOrderHistoryProofFormula (history : TheoryHistory) :
    FirstOrderArithmeticFormula 2 :=
  (informativeHistoryProofFormula history).toFirstOrder
    (informativeHistoryProofFormula_disjunctionFree history)

theorem firstOrderHistoryProofFormula_translation
    (history : TheoryHistory) :
    (firstOrderHistoryProofFormula history).toScoped =
      informativeHistoryProofFormula history :=
  ScopedFormula.toFirstOrder_translation _ _

/-! ## Checked-proof transport through the exact translation -/

theorem firstOrderSentence_biconditional_eq
    (left right : FirstOrderArithmeticFormula 0) :
    firstOrderSentence
        (FirstOrderArithmeticFormula.biconditional left right) =
      haBiconditional (firstOrderSentence left) (firstOrderSentence right) := by
  apply Sentence.eq_of_raw_eq
  rfl

theorem firstOrderSentence_substituteNumeral_eq
    (formula : FirstOrderArithmeticFormula 1) (value : Nat) :
    firstOrderSentence (firstOrderSubstituteNumeral formula value) =
      (firstOrderPredicate formula).applyNumeral value := by
  apply Sentence.eq_of_raw_eq
  exact congrArg ScopedFormula.raw
    (firstOrderSubstituteNumeral_translation formula value)

theorem firstOrderPredicate_diagonalize_eq
    (formula : FirstOrderArithmeticFormula 1) :
    firstOrderPredicate (firstOrderDiagonalize formula) =
      internalFixedPointBody (firstOrderPredicate formula) := by
  apply Predicate.eq_of_raw_eq
  exact congrArg ScopedFormula.raw
    (firstOrderDiagonalize_translation formula)

def checkedFirstOrderProofToHA
    {sentence : FirstOrderArithmeticFormula 0} :
    CheckedArithmeticProof encodeFirstOrderFormula haProofCheck sentence ->
      CheckedSentenceProof Sentence.quote haProofCheck
        (firstOrderSentence sentence) :=
  fun proof => proof

def checkedHAProofToFirstOrder
    {sentence : FirstOrderArithmeticFormula 0} :
    CheckedSentenceProof Sentence.quote haProofCheck
        (firstOrderSentence sentence) ->
      CheckedArithmeticProof encodeFirstOrderFormula haProofCheck sentence :=
  fun proof => proof

theorem firstOrderDiagonalLeft_eq
    (target source : FirstOrderArithmeticFormula 1) :
    firstOrderSentence
        (firstOrderSubstituteNumeral (firstOrderDiagonalize target)
          (encodeFirstOrderFormula source)) =
      haDiagonalLeft (firstOrderPredicate target)
        (firstOrderPredicate source) := by
  rw [firstOrderSentence_substituteNumeral_eq]
  rw [firstOrderPredicate_diagonalize_eq]
  rfl

theorem firstOrderSelfApplicationCode_eq
    (source : FirstOrderArithmeticFormula 1) :
    encodeFirstOrderFormula
        (firstOrderSubstituteNumeral source
          (encodeFirstOrderFormula source)) =
      ((firstOrderPredicate source).applyNumeral
        (firstOrderPredicate source).raw.code).quote := by
  exact congrArg Sentence.quote
    (firstOrderSentence_substituteNumeral_eq source
      (encodeFirstOrderFormula source))

theorem firstOrderDiagonalRight_eq
    (target source : FirstOrderArithmeticFormula 1) :
    firstOrderSentence
        (firstOrderSubstituteNumeral target
          (encodeFirstOrderFormula
            (firstOrderSubstituteNumeral source
              (encodeFirstOrderFormula source)))) =
      haDiagonalRight (firstOrderPredicate target)
        (firstOrderPredicate source) := by
  rw [firstOrderSentence_substituteNumeral_eq]
  rw [firstOrderSelfApplicationCode_eq]
  rfl

def firstOrderDiagonalIffProof
    (target source : FirstOrderArithmeticFormula 1) :
    CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      (FirstOrderArithmeticFormula.biconditional
        (firstOrderSubstituteNumeral (firstOrderDiagonalize target)
          (encodeFirstOrderFormula source))
        (firstOrderSubstituteNumeral target
          (encodeFirstOrderFormula
            (firstOrderSubstituteNumeral source
              (encodeFirstOrderFormula source))))) := by
  let haProof := haCheckedProofOfDerivation
    (haDiagonalDerivation
      (firstOrderPredicate target) (firstOrderPredicate source))
  let expected := firstOrderSentence
    (FirstOrderArithmeticFormula.biconditional
      (firstOrderSubstituteNumeral (firstOrderDiagonalize target)
        (encodeFirstOrderFormula source))
      (firstOrderSubstituteNumeral target
        (encodeFirstOrderFormula
          (firstOrderSubstituteNumeral source
            (encodeFirstOrderFormula source)))))
  have expectedEquality : expected =
      haBiconditional
        (haDiagonalLeft (firstOrderPredicate target)
          (firstOrderPredicate source))
        (haDiagonalRight (firstOrderPredicate target)
          (firstOrderPredicate source)) := by
    unfold expected
    rw [firstOrderSentence_biconditional_eq,
      firstOrderDiagonalLeft_eq, firstOrderDiagonalRight_eq]
  have translatedProof :
      CheckedSentenceProof Sentence.quote haProofCheck expected := by
    rw [expectedEquality]
    exact haProof
  exact checkedHAProofToFirstOrder translatedProof

def firstOrderIffProofForward
    {left right : FirstOrderArithmeticFormula 0}
    (equivalence : CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      (FirstOrderArithmeticFormula.biconditional left right))
    (leftProof : CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      left) :
    CheckedArithmeticProof encodeFirstOrderFormula haProofCheck right := by
  let biconditionalProof := haDerivationOfCheckedProof
    (checkedFirstOrderProofToHA equivalence)
  let implicationProof :=
    Derivation.conjunctionEliminationLeft biconditionalProof
  let argumentProof := haDerivationOfCheckedProof
    (checkedFirstOrderProofToHA leftProof)
  exact checkedHAProofToFirstOrder
    (haCheckedProofOfDerivation
      (Derivation.implicationElimination implicationProof argumentProof))

def firstOrderIffProofBackward
    {left right : FirstOrderArithmeticFormula 0}
    (equivalence : CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      (FirstOrderArithmeticFormula.biconditional left right))
    (rightProof : CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      right) :
    CheckedArithmeticProof encodeFirstOrderFormula haProofCheck left := by
  let biconditionalProof := haDerivationOfCheckedProof
    (checkedFirstOrderProofToHA equivalence)
  let implicationProof :=
    Derivation.conjunctionEliminationRight biconditionalProof
  let argumentProof := haDerivationOfCheckedProof
    (checkedFirstOrderProofToHA rightProof)
  exact checkedHAProofToFirstOrder
    (haCheckedProofOfDerivation
      (Derivation.implicationElimination implicationProof argumentProof))

def firstOrderProofSound
    {sentence : FirstOrderArithmeticFormula 0}
    (proof : CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      sentence) :
    FirstOrderArithmeticFormula.sentenceTruth sentence :=
  let derivation := haDerivationOfCheckedProof
    (checkedFirstOrderProofToHA proof)
  let realizer := haDerivation_realizes derivation emptyEnvironment Unit.unit
  (firstOrderArithmeticFormulaTruthRealizerEquivalence
    sentence emptyEnvironment).backward realizer

def firstOrderEqualityReflexivityProof
    (term : FirstOrderArithmeticTerm 0) :
    CheckedArithmeticProof encodeFirstOrderFormula haProofCheck
      (FirstOrderArithmeticFormula.equal term term) :=
  checkedHAProofToFirstOrder
    (haCheckedProofOfDerivation
      (Derivation.equalityReflexivity term.toScoped))

def proofRelationTruthEquivalenceFromTranslation
    (formula : FirstOrderArithmeticFormula 2)
    (translation : formula.toScoped =
      informativeHistoryProofFormula TheoryHistory.root)
    (proofCode sentenceCode : Nat) :
    RealizerEquivalence
      (FirstOrderArithmeticFormula.Truth
        (FirstOrderArithmeticFormula.binaryAssignment proofCode sentenceCode)
        formula)
      (PLift (haProofCheck proofCode sentenceCode = true)) :=
  let assignment :=
    FirstOrderArithmeticFormula.binaryAssignment proofCode sentenceCode
  let semantic :=
    firstOrderArithmeticFormulaTruthInformativeWitnessEquivalence
      formula assignment
  let transported : RealizerEquivalence
      (RawFormula.InformativeWitness assignment formula.toScoped.raw)
      (RawFormula.InformativeWitness assignment
        (informativeHistoryProofFormula TheoryHistory.root).raw) :=
    { forward := fun witness =>
        Eq.mp
          (congrArg
            (fun scopedFormula : ScopedFormula 2 =>
              RawFormula.InformativeWitness assignment scopedFormula.raw)
            translation)
          witness
      backward := fun witness =>
        Eq.mpr
          (congrArg
            (fun scopedFormula : ScopedFormula 2 =>
              RawFormula.InformativeWitness assignment scopedFormula.raw)
            translation)
          witness }
  let represented :=
    informativeRootHistoryProofFormula_realizerEquivalence
      proofCode sentenceCode
  { forward := fun truth =>
      represented.forward (transported.forward (semantic.forward truth))
    backward := fun checked =>
      semantic.backward (transported.backward (represented.backward checked)) }

/-- A proof-relation formula packaged with the informative equivalence for that
same formula. The dependent field preserves exact identity without forcing
clients to normalize the formula in order to see the two directions. -/
structure FirstOrderProofRelationPresentation : Type where
  formula : FirstOrderArithmeticFormula 2
  truthEquivalence : (proofCode sentenceCode : Nat) ->
    RealizerEquivalence
      (FirstOrderArithmeticFormula.Truth
        (FirstOrderArithmeticFormula.binaryAssignment proofCode sentenceCode)
        formula)
      (PLift (haProofCheck proofCode sentenceCode = true))

def proofRelationPresentationFromTranslation
    (formula : FirstOrderArithmeticFormula 2)
    (translation : formula.toScoped =
      informativeHistoryProofFormula TheoryHistory.root) :
    FirstOrderProofRelationPresentation :=
  { formula := formula
    truthEquivalence :=
      proofRelationTruthEquivalenceFromTranslation formula translation }

def firstOrderProofRelationPresentation :
    FirstOrderProofRelationPresentation :=
  proofRelationPresentationFromTranslation
    (firstOrderHistoryProofFormula TheoryHistory.root)
    (firstOrderHistoryProofFormula_translation TheoryHistory.root)

def heytingArithmeticSemanticallyDefinedProofArithmeticTheory :
    SemanticallyDefinedProofArithmeticTheory where
  encodeUnary := encodeFirstOrderFormula
  decodeUnary := decodeFirstOrderFormula 1
  decodeUnary_encode := decodeFirstOrderFormula_encode
  encodeSentence := encodeFirstOrderFormula
  decodeSentence := decodeFirstOrderFormula 0
  decodeSentence_encode := decodeFirstOrderFormula_encode
  substituteNumeral := firstOrderSubstituteNumeral
  substituteNumeralTruthForward := firstOrderSubstituteNumeralTruthForward
  substituteNumeralTruthBackward := firstOrderSubstituteNumeralTruthBackward
  diagonalize := firstOrderDiagonalize
  proofCheck := haProofCheck
  diagonalIffProof := firstOrderDiagonalIffProof
  iffProofForward := firstOrderIffProofForward
  iffProofBackward := firstOrderIffProofBackward
  proofSound := firstOrderProofSound
  equalityReflexivityProof := firstOrderEqualityReflexivityProof
  proofRelationFormula := firstOrderProofRelationPresentation.formula
  proofRelationTruthForward := fun proofCode sentenceCode =>
    (firstOrderProofRelationPresentation.truthEquivalence
      proofCode sentenceCode).forward
  proofRelationTruthBackward := fun proofCode sentenceCode =>
    (firstOrderProofRelationPresentation.truthEquivalence
      proofCode sentenceCode).backward

theorem firstOrderProofRelationPresentation_formula_eq :
    firstOrderProofRelationPresentation.formula =
      firstOrderHistoryProofFormula TheoryHistory.root := by
  rfl

theorem firstOrderProofRelationPresentation_translation :
    firstOrderProofRelationPresentation.formula.toScoped =
      informativeHistoryProofFormula TheoryHistory.root := by
  rw [firstOrderProofRelationPresentation_formula_eq]
  exact firstOrderHistoryProofFormula_translation TheoryHistory.root

theorem heytingArithmeticSemanticArithmeticProofCheck_eq
    (proofCode sentenceCode : Nat) :
    heytingArithmeticSemanticallyDefinedProofArithmeticTheory.proofCheck
        proofCode sentenceCode =
      haProofCheck proofCode sentenceCode := by
  rfl

def heytingArithmeticSemanticallyDefinedArithmeticGodelConclusion :=
  semanticallyDefinedArithmeticGodelPerimetralConclusion
    heytingArithmeticSemanticallyDefinedProofArithmeticTheory

def heytingArithmeticSemanticallyDefinedArithmeticGodelDiagnostic :=
  semanticallyDefinedArithmeticGodelDiagnostic
    heytingArithmeticSemanticallyDefinedProofArithmeticTheory

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.toRaw
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.toScoped
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.toScoped_raw
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.toScoped
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.toFirstOrder
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.toFirstOrder
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.toFirstOrder?_toRaw
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.toFirstOrder_translation
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.toFirstOrder?_toScopedRaw
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.toFirstOrder_translation
#print axioms RelationalPerimeter.HeytingArithmetic.ScopedFormula.toFirstOrder_translation
#print axioms RelationalPerimeter.HeytingArithmetic.decodeFirstOrderFormula_encode
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderArithmeticFormulaTruthInformativeWitnessEquivalence
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderSubstituteNumeralTruthForward
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderSubstituteNumeralTruthBackward
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.graphFormula_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.existsMany_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraph.apply_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraphVector.body_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.graphFormulas_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.graphFormulas_body_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.informativeProofFormula_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.informativeHistoryProofFormula_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.internalFixedPointBody_disjunctionFree
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderDiagonalize
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderSentence_biconditional_eq
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderDiagonalLeft_eq
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderDiagonalRight_eq
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderDiagonalIffProof
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderProofSound
#print axioms RelationalPerimeter.HeytingArithmetic.proofRelationTruthEquivalenceFromTranslation
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderHistoryProofFormula
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderHistoryProofFormula_translation
#print axioms RelationalPerimeter.HeytingArithmetic.proofRelationPresentationFromTranslation
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderProofRelationPresentation
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderProofRelationPresentation_formula_eq
#print axioms RelationalPerimeter.HeytingArithmetic.firstOrderProofRelationPresentation_translation
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSemanticArithmeticProofCheck_eq
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSemanticallyDefinedProofArithmeticTheory
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSemanticallyDefinedArithmeticGodelConclusion
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSemanticallyDefinedArithmeticGodelDiagnostic
/- AXIOM_AUDIT_END -/
