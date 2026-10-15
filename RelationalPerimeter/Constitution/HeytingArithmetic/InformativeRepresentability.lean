import RelationalPerimeter.Constitution.HeytingArithmetic.InformativeSemantics
import RelationalPerimeter.Constitution.HeytingArithmetic.Representability
import RelationalPerimeter.Constitution.HeytingArithmeticGodelInstance

/-!
# Informative representability of primitive-recursive graphs

The existing graph compiler proves a proposition-valued specification.  This
module supplies its missing constructive direction: an execution builds every
existential witness carried by the compiled formula.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

/-- A constructive positive gap for strict natural-number order. -/
def gapWitnessOfLt :
    {smaller larger : Nat} ->
      smaller < larger ->
        Sigma fun gap : Nat => PLift (smaller + Nat.succ gap = larger)
  | 0, 0, impossible => (Nat.not_lt_zero 0 impossible).elim
  | 0, Nat.succ larger, _strict =>
      ⟨larger, ⟨Nat.zero_add (Nat.succ larger)⟩⟩
  | Nat.succ smaller, 0, impossible =>
      (Nat.not_lt_zero (Nat.succ smaller) impossible).elim
  | Nat.succ smaller, Nat.succ larger, strict =>
      let earlier := gapWitnessOfLt (Nat.lt_of_succ_lt_succ strict)
      ⟨earlier.1, ⟨by
        rw [Nat.succ_add]
        exact congrArg Nat.succ earlier.2.down⟩⟩

/-- Strict order constructs the existential witness in its arithmetic formula. -/
def lessThanFormula_realizesOfLt
    (left right : RawTerm)
    (environment : Environment)
    (strict : left.evaluate environment < right.evaluate environment) :
    (lessThanFormula left right).Realizes environment :=
  let witness := gapWitnessOfLt strict
  ⟨witness.1, ⟨by
    change
      left.shift.evaluate (pushEnvironment environment witness.1) +
          Nat.succ witness.1 =
        right.shift.evaluate (pushEnvironment environment witness.1)
    rw [left.shift_evaluate environment witness.1]
    rw [right.shift_evaluate environment witness.1]
    exact witness.2.down⟩⟩

/-- A concrete list of witnesses realizes its existential block. -/
def RawFormula.existsManyRealizesBackwardFromList :
    (values : List Nat) ->
    (body : RawFormula) ->
    (environment : Environment) ->
    body.Realizes (prependListEnvironment values environment) ->
      (body.existsMany values.length).Realizes environment
  | [], _body, _environment, bodyRealizer => bodyRealizer
  | head :: tail, body, environment, bodyRealizer =>
      RawFormula.existsManyRealizesBackwardFromList tail
        (RawFormula.ex body) environment ⟨head, bodyRealizer⟩

/-- An explicit vector of witnesses realizes an existential block. -/
def RawFormula.existsManyRealizesBackward
    {count : Nat}
    (body : RawFormula)
    (environment : Environment)
    (values : NatVector count)
    (bodyRealizer : body.Realizes (prependEnvironment values environment)) :
    (body.existsMany count).Realizes environment :=
  let listRealizer : body.Realizes
      (prependListEnvironment values.toList environment) :=
    (body.realizes_congr
      (prependListEnvironment values.toList environment)
      (prependEnvironment values environment)
      (prependListEnvironment_toList values environment)).backward bodyRealizer
  let blockRealizer := RawFormula.existsManyRealizesBackwardFromList
    values.toList body environment listRealizer
  Eq.mp
    (congrArg
      (fun length => (body.existsMany length).Realizes environment)
      values.toList_length)
    blockRealizer

/-- An existential block exposes the witness vector it actually contains. -/
def RawFormula.existsManyRealizesForward :
    (count : Nat) ->
    (body : RawFormula) ->
    (environment : Environment) ->
    (body.existsMany count).Realizes environment ->
      Sigma fun values : NatVector count =>
        body.Realizes (prependEnvironment values environment)
  | 0, body, environment, bodyRealizer =>
      ⟨NatVector.nil,
        (body.realizes_congr environment
          (prependEnvironment NatVector.nil environment)
          (fun _index => rfl)).forward bodyRealizer⟩
  | Nat.succ count, body, environment, blockRealizer =>
      let tailWitness := RawFormula.existsManyRealizesForward count
        (RawFormula.ex body) environment blockRealizer
      let tailValues := tailWitness.1
      let headValue := tailWitness.2.1
      ⟨NatVector.cons headValue tailValues,
        (body.realizes_congr
          (pushEnvironment (prependEnvironment tailValues environment) headValue)
          (prependEnvironment (NatVector.cons headValue tailValues) environment)
          (fun index => by cases index <;> rfl)).forward tailWitness.2.2⟩

/-- Read strict order back from its informative arithmetic realizer. -/
def lessThanFormula_ltOfRealizer
    (left right : RawTerm)
    (environment : Environment) :
    (lessThanFormula left right).Realizes environment ->
      PLift (left.evaluate environment < right.evaluate environment) :=
  fun realizer => ⟨(lessThanFormula_holds left right environment).mp
    (Exists.intro realizer.1 realizer.2.down)⟩

/-- Read the computed beta value back from its informative realizer. -/
def betaValueFormula_equalityOfRealizer
    (dividend coefficient index value : RawTerm)
    (environment : Environment) :
    (betaValueFormula dividend coefficient index value).Realizes environment ->
      PLift
        (value.evaluate environment =
          constructiveRemainder
            (dividend.evaluate environment)
            ((index.evaluate environment + 1) *
              coefficient.evaluate environment + 1)) :=
  fun realizer => ⟨(betaValueFormula_holds
    dividend coefficient index value environment).mp
      (And.intro
        (Exists.intro realizer.1.1 realizer.1.2.down)
        (Exists.intro realizer.2.1 realizer.2.2.down))⟩

/-- Informative semantics of one applied arithmetic graph. -/
def ArithmeticGraph.apply_realizes
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (outputTerm : RawTerm)
    (inputTerms : RawTermVector arity)
    (environment : Environment)
    (inputs : NatVector arity)
    (output : Nat)
    (outputValue : outputTerm.evaluate environment = output)
    (inputValues :
      (index : Nat) ->
        (bounded : index < arity) ->
          (inputTerms.getD index).evaluate environment =
            inputs.get index bounded) :
    RealizerEquivalence
      ((graph.apply outputTerm inputTerms).Realizes environment)
      (graph.raw.Realizes (graphEnvironment inputs output)) :=
  let substituted := graph.raw.realizes_substitute
    (fun index =>
      match index with
      | 0 => outputTerm
      | Nat.succ inputIndex => inputTerms.getD inputIndex)
    environment
  let canonicalCongruence := graph.raw.realizes_congr
    (fun index =>
      (match index with
        | 0 => outputTerm
        | Nat.succ inputIndex => inputTerms.getD inputIndex).evaluate environment)
    (graphEnvironment (inputTerms.evaluate environment)
      (outputTerm.evaluate environment))
    (fun index => by
      cases index with
      | zero => rfl
      | succ inputIndex =>
          exact (RawTermVector.evaluate_getD inputTerms environment inputIndex).symm)
  let valueCongruence := graph.raw.realizes_congrScoped graph.isScoped
    (graphEnvironment (inputTerms.evaluate environment)
      (outputTerm.evaluate environment))
    (graphEnvironment inputs output)
    (fun index bounded => by
      cases index with
      | zero => exact outputValue
      | succ inputIndex =>
          have inputBounded : inputIndex < arity :=
            Nat.lt_of_succ_lt_succ bounded
          exact Eq.trans
            (RawTermVector.evaluate_getD inputTerms environment inputIndex)
            (Eq.trans (inputValues inputIndex inputBounded)
              (NatVector.getD_eq_get inputs inputBounded).symm))
  { forward := fun realizer => valueCongruence.forward
      (canonicalCongruence.forward (substituted.forward realizer))
    backward := fun realizer => substituted.backward
      (canonicalCongruence.backward (valueCongruence.backward realizer)) }

/-- Beta evaluation constructs the quotient and bounded-gap witnesses used by
the compiled arithmetic formula. -/
def betaValueFormula_realizesOfEquality
    (dividend coefficient index value : RawTerm)
    (environment : Environment)
    (equality :
      value.evaluate environment =
        constructiveRemainder
          (dividend.evaluate environment)
          ((index.evaluate environment + 1) *
            coefficient.evaluate environment + 1)) :
    (betaValueFormula dividend coefficient index value).Realizes environment := by
  let syntacticModulus :=
    (betaModulusTerm coefficient index).evaluate environment
  have modulusEquality : syntacticModulus =
      (index.evaluate environment + 1) *
        coefficient.evaluate environment + 1 := by
    exact Eq.trans
      (congrArg Nat.succ
        (congrArg
          (fun factor => factor * coefficient.evaluate environment)
          (Nat.succ_eq_add_one (index.evaluate environment))))
      (Nat.succ_eq_add_one
        ((index.evaluate environment + 1) *
          coefficient.evaluate environment))
  have positive : 0 < syntacticModulus := by
    change 0 < Nat.succ _
    exact Nat.zero_lt_succ _
  let correctness := constructiveDivModCorrect syntacticModulus positive
    (dividend.evaluate environment)
  have valueAtSyntacticModulus : value.evaluate environment =
      constructiveRemainder (dividend.evaluate environment)
        syntacticModulus :=
    equality.trans
      (congrArg (constructiveRemainder (dividend.evaluate environment))
        modulusEquality).symm
  constructor
  · apply lessThanFormula_realizesOfLt
    rw [valueAtSyntacticModulus]
    exact correctness.bounded
  · refine ⟨constructiveQuotient
      (dividend.evaluate environment) syntacticModulus, ⟨?_⟩⟩
    change
      dividend.shift.evaluate
          (pushEnvironment environment
            (constructiveQuotient
              (dividend.evaluate environment) syntacticModulus)) =
        constructiveQuotient
              (dividend.evaluate environment) syntacticModulus *
            (betaModulusTerm coefficient index).shift.evaluate
              (pushEnvironment environment
                (constructiveQuotient
                  (dividend.evaluate environment) syntacticModulus)) +
          value.shift.evaluate
            (pushEnvironment environment
              (constructiveQuotient
                (dividend.evaluate environment) syntacticModulus))
    rw [dividend.shift_evaluate]
    rw [(betaModulusTerm coefficient index).shift_evaluate]
    rw [value.shift_evaluate]
    exact correctness.equation.trans
      (congrArg
        (fun remainder =>
          constructiveQuotient
              (dividend.evaluate environment) syntacticModulus *
              syntacticModulus + remainder)
        valueAtSyntacticModulus.symm)

/-- A Type-valued finite execution trace for primitive recursion. -/
structure InformativePrimitiveRecursionRun
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (parameters : NatVector parameterArity)
    (counter output : Nat)
    (values : NatVector (Nat.succ counter)) : Type where
  baseEvaluation :
    PLift (PRFunction.Evaluates base parameters
      (values.get 0 (Nat.zero_lt_succ counter)))
  stepEvaluation :
    (index : Nat) ->
      (bounded : index < counter) ->
        PLift (PRFunction.Evaluates step
          (NatVector.cons index
            (NatVector.cons
              (values.get index
                (Nat.lt_trans bounded (Nat.lt_succ_self counter)))
              parameters))
          (values.get (Nat.succ index) (Nat.succ_lt_succ bounded)))
  finalValue : PLift
    (values.get counter (Nat.lt_succ_self counter) = output)

/-- Every primitive-recursion execution computes a positive finite trace. -/
def informativePrimitiveRecursionRunOfEvaluation
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    (parameters : NatVector parameterArity) :
    (counter output : Nat) ->
    PRFunction.Evaluates
      (PRFunction.primitiveRecursion base step)
      (NatVector.cons counter parameters) output ->
    Sigma fun values : NatVector (Nat.succ counter) =>
      InformativePrimitiveRecursionRun
        base step parameters counter output values
  | 0, output, evaluation =>
      ⟨NatVector.cons output NatVector.nil,
        { baseEvaluation := ⟨evaluation.trans
            (PRFunction.Evaluates.runCore_primitive_zero
              base step parameters)⟩
          stepEvaluation := fun index impossible =>
            (Nat.not_lt_zero index impossible).elim
          finalValue := ⟨rfl⟩ }⟩
  | Nat.succ counter, output, evaluation =>
      let previous :=
        PRFunction.runCore (PRFunction.primitiveRecursion base step)
          (NatVector.cons counter parameters)
      let earlier := informativePrimitiveRecursionRunOfEvaluation parameters
        counter previous rfl
      let previousValues := earlier.1
      let previousRun := earlier.2
      ⟨previousValues.snoc output,
        { baseEvaluation := ⟨by
            rw [NatVector.get_snoc_of_lt]
            exact previousRun.baseEvaluation.down⟩
          stepEvaluation := fun index bounded => ⟨by
            have boundedOrFinal : index < counter ∨ index = counter :=
              Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bounded)
            cases boundedOrFinal with
            | inl earlierIndex =>
                rw [NatVector.get_snoc_of_lt,
                  NatVector.get_snoc_of_lt]
                exact previousRun.stepEvaluation index earlierIndex |>.down
            | inr finalIndex =>
                cases finalIndex
                rw [NatVector.get_snoc_of_lt
                    previousValues output (Nat.lt_succ_self counter),
                  NatVector.get_snoc_last previousValues output,
                  previousRun.finalValue.down]
                exact evaluation.trans
                  (PRFunction.Evaluates.runCore_primitive_succ
                    base step counter parameters)⟩
          finalValue := ⟨NatVector.get_snoc_last previousValues output⟩ }⟩

mutual
  /-- Read the execution equation from a compiled graph realizer. -/
  def PRFunction.graphFormula_evaluationOfRealizer :
      {arity : Nat} ->
      (program : PRFunction arity) ->
      (inputs : NatVector arity) ->
      (output : Nat) ->
      program.graphFormula.raw.Realizes (graphEnvironment inputs output) ->
        PLift (PRFunction.Evaluates program inputs output)
    | _, PRFunction.zero, inputs, output, realizer => realizer
    | _, PRFunction.successor, inputs, output, realizer => realizer
    | _, PRFunction.projection arity index bounded, inputs, output, realizer =>
        ⟨realizer.down.trans (NatVector.getD_eq_get inputs bounded)⟩
    | _, PRFunction.composition outer inner, inputs, output, realizer => by
        change
          ((RawFormula.conj
            (outer.graphFormula.apply
              (RawTerm.bvar _)
              (RawTermVector.variables 0 _))
            (inner.graphFormulas.body 0 _ (zeroOffsetFits _)).raw).existsMany
              _).Realizes (graphEnvironment inputs output) at realizer
        let witness := RawFormula.existsManyRealizesForward _ _ _ realizer
        let intermediate := witness.1
        let bodyRealizer := witness.2
        have outerRealizer :=
          (outer.graphFormula.apply_realizes
            (RawTerm.bvar _)
            (RawTermVector.variables 0 _)
            (prependEnvironment intermediate (graphEnvironment inputs output))
            intermediate output
            (prependEnvironment_shift intermediate
              (graphEnvironment inputs output) 0)
            (fun index bounded =>
              (RawTermVector.variables_evaluate_get 0 _ _ index bounded).trans
                (by
                  rw [Nat.zero_add]
                  exact prependEnvironment_get intermediate
                    (graphEnvironment inputs output) bounded))).forward
              bodyRealizer.1
        have outerEvaluation :=
          PRFunction.graphFormula_evaluationOfRealizer outer intermediate output
            outerRealizer
        have innerEvaluation :=
          PRFunctionVector.graphFormulas_bodyEvaluationOfRealizer inner
            0 _ (zeroOffsetFits _)
            (prependEnvironment intermediate (graphEnvironment inputs output))
            inputs intermediate
            (fun index bounded =>
              prependEnvironment_originalInput intermediate inputs output bounded)
            (fun index bounded => by
              rw [Nat.zero_add]
              exact prependEnvironment_get intermediate
                (graphEnvironment inputs output) bounded)
            bodyRealizer.2
        exact ⟨PRFunction.Evaluates.composition
          innerEvaluation.down outerEvaluation.down⟩
    | _, @PRFunction.primitiveRecursion parameterArity base step,
        inputs, output, realizer => by
        let counter := inputs.getD 0
        let parameters := inputs.tailD
        have inputsEquality : NatVector.cons counter parameters = inputs :=
          NatVector.rebuildD inputs
        rw [← inputsEquality] at realizer ⊢
        let baseCore := RawFormula.conj
          (betaValueFormula
            (RawTerm.bvar 1) (RawTerm.bvar 2) RawTerm.zero (RawTerm.bvar 0))
          (base.graphFormula.apply (RawTerm.bvar 0)
            (primitiveBaseParameters _))
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
              (primitiveStepInputs _)))
        let transitionClause := RawFormula.all
          (RawFormula.impl
            (lessThanFormula (RawTerm.bvar 0) (RawTerm.bvar 4))
            (transitionCore.existsMany 2))
        let outputClause := betaValueFormula
          (RawTerm.bvar 0) (RawTerm.bvar 1)
          (RawTerm.bvar 3) (RawTerm.bvar 2)
        let body := RawFormula.conj baseClause
          (RawFormula.conj transitionClause outputClause)
        change (body.existsMany 2).Realizes
          (graphEnvironment (NatVector.cons counter parameters) output) at realizer
        let sequenceWitness :=
          RawFormula.existsManyRealizesForward 2 body _ realizer
        let sequenceParameters := sequenceWitness.1
        let dividend := sequenceParameters.getD 0
        let coefficient := sequenceParameters.getD 1
        have sequenceParametersEquality :
            NatVector.cons dividend
                (NatVector.cons coefficient NatVector.nil) =
              sequenceParameters :=
          NatVector.tabulateD_getD_self sequenceParameters
        have bodyRealizer := sequenceWitness.2
        change body.Realizes
          (prependEnvironment sequenceParameters
            (graphEnvironment (NatVector.cons counter parameters) output))
          at bodyRealizer
        rw [← sequenceParametersEquality] at bodyRealizer
        let originalEnvironment :=
          graphEnvironment (NatVector.cons counter parameters) output
        let topEnvironment := prependEnvironment
          (NatVector.cons dividend (NatVector.cons coefficient NatVector.nil))
          originalEnvironment
        have topParameterValues :
            (index : Nat) -> (bounded : index < parameterArity) ->
              topEnvironment (4 + index) = parameters.get index bounded := by
          intro index bounded
          exact prependTwo_graphParameter
            dividend coefficient counter output parameters bounded
        let baseRealizer := bodyRealizer.1
        let baseValue := baseRealizer.1
        let baseEnvironment := pushEnvironment topEnvironment baseValue
        have baseBeta : baseValue = betaComponent dividend coefficient 0 :=
          (betaValueFormula_equalityOfRealizer
            (RawTerm.bvar 1) (RawTerm.bvar 2) RawTerm.zero
            (RawTerm.bvar 0) baseEnvironment baseRealizer.2.1).down
        have baseGraphRealizer :=
          (base.graphFormula.apply_realizes
            (RawTerm.bvar 0) (primitiveBaseParameters _)
            baseEnvironment parameters baseValue rfl
            (primitiveBaseParameters_evaluate topEnvironment parameters
              baseValue topParameterValues)).forward baseRealizer.2.2
        have baseAtWitness :=
            PRFunction.graphFormula_evaluationOfRealizer base parameters baseValue
            baseGraphRealizer |>.down
        have baseExecution : PRFunction.Evaluates base parameters
            (betaComponent dividend coefficient 0) := by
          rw [← baseBeta]
          exact baseAtWitness
        let transitionRealizer := bodyRealizer.2.1
        have stepExecution : (index : Nat) -> index < counter ->
            PRFunction.Evaluates step
              (NatVector.cons index
                (NatVector.cons (betaComponent dividend coefficient index)
                  parameters))
              (betaComponent dividend coefficient (Nat.succ index)) := by
          intro index bounded
          let indexEnvironment := pushEnvironment topEnvironment index
          have conditionRealizer := lessThanFormula_realizesOfLt
            (RawTerm.bvar 0) (RawTerm.bvar 4) indexEnvironment bounded
          let transitionBlock := transitionRealizer index conditionRealizer
          let adjacentWitness := RawFormula.existsManyRealizesForward
            2 transitionCore indexEnvironment transitionBlock
          let adjacent := adjacentWitness.1
          let previous := adjacent.getD 0
          let next := adjacent.getD 1
          have adjacentEquality :
              NatVector.cons previous (NatVector.cons next NatVector.nil) =
                adjacent := NatVector.tabulateD_getD_self adjacent
          have transitionCoreRealizer := adjacentWitness.2
          change transitionCore.Realizes
            (prependEnvironment adjacent indexEnvironment)
            at transitionCoreRealizer
          rw [← adjacentEquality] at transitionCoreRealizer
          let stepEnvironment := prependEnvironment
            (NatVector.cons previous (NatVector.cons next NatVector.nil))
            indexEnvironment
          have previousBeta : previous =
              betaComponent dividend coefficient index :=
            (betaValueFormula_equalityOfRealizer
              (RawTerm.bvar 3) (RawTerm.bvar 4) (RawTerm.bvar 2)
              (RawTerm.bvar 0) stepEnvironment
              transitionCoreRealizer.1).down
          have nextBeta : next =
              betaComponent dividend coefficient (Nat.succ index) :=
            (betaValueFormula_equalityOfRealizer
              (RawTerm.bvar 3) (RawTerm.bvar 4)
              (RawTerm.succ (RawTerm.bvar 2)) (RawTerm.bvar 1)
              stepEnvironment transitionCoreRealizer.2.1).down
          have stepGraphRealizer :=
            (step.graphFormula.apply_realizes
              (RawTerm.bvar 1) (primitiveStepInputs _)
              stepEnvironment
              (NatVector.cons index (NatVector.cons previous parameters))
              next rfl (fun inputIndex inputBounded => by
                cases inputIndex with
                | zero => rfl
                | succ inputIndex =>
                    cases inputIndex with
                    | zero => rfl
                    | succ parameterIndex =>
                        exact primitiveStepParameters_evaluate
                          topEnvironment parameters index previous next
                          topParameterValues parameterIndex
                          (Nat.lt_of_succ_lt_succ
                            (Nat.lt_of_succ_lt_succ inputBounded)))).forward
              transitionCoreRealizer.2.2
          have stepAtWitness :=
            PRFunction.graphFormula_evaluationOfRealizer step
              (NatVector.cons index (NatVector.cons previous parameters))
              next stepGraphRealizer |>.down
          rw [← previousBeta, ← nextBeta]
          exact stepAtWitness
        have buildExecution : (index : Nat) -> index <= counter ->
            PRFunction.Evaluates (PRFunction.primitiveRecursion base step)
              (NatVector.cons index parameters)
              (betaComponent dividend coefficient index) := by
          intro index within
          induction index with
          | zero => exact PRFunction.Evaluates.primitiveZero baseExecution
          | succ index inductionHypothesis =>
              exact PRFunction.Evaluates.primitiveSucc
                (inductionHypothesis
                  (Nat.le_trans (Nat.le_succ index) within))
                (stepExecution index (Nat.lt_of_succ_le within))
        have outputBeta : output = betaComponent dividend coefficient counter :=
          (betaValueFormula_equalityOfRealizer
            (RawTerm.bvar 0) (RawTerm.bvar 1)
            (RawTerm.bvar 3) (RawTerm.bvar 2)
            topEnvironment bodyRealizer.2.2).down
        exact ⟨outputBeta.trans
          (buildExecution counter (Nat.le_refl counter))⟩

  /-- Build the compiled graph realizer from its execution equation. -/
  def PRFunction.graphFormula_realizerOfEvaluation :
      {arity : Nat} ->
      (program : PRFunction arity) ->
      (inputs : NatVector arity) ->
      (output : Nat) ->
      PLift (PRFunction.Evaluates program inputs output) ->
        program.graphFormula.raw.Realizes (graphEnvironment inputs output)
    | _, PRFunction.zero, _inputs, _output, evaluation => evaluation
    | _, PRFunction.successor, _inputs, _output, evaluation => evaluation
    | _, PRFunction.projection arity index bounded, inputs, output, evaluation =>
        ⟨evaluation.down.trans (NatVector.getD_eq_get inputs bounded).symm⟩
    | _, PRFunction.composition outer inner, inputs, output, evaluation => by
        change
          ((RawFormula.conj
            (outer.graphFormula.apply (RawTerm.bvar _)
              (RawTermVector.variables 0 _))
            (inner.graphFormulas.body 0 _ (zeroOffsetFits _)).raw).existsMany
              _).Realizes (graphEnvironment inputs output)
        let intermediate := PRFunctionVector.runCore inner inputs
        apply RawFormula.existsManyRealizesBackward _ _ intermediate
        constructor
        · apply (outer.graphFormula.apply_realizes
            (RawTerm.bvar _) (RawTermVector.variables 0 _)
            (prependEnvironment intermediate (graphEnvironment inputs output))
            intermediate output
            (prependEnvironment_shift intermediate
              (graphEnvironment inputs output) 0)
            (fun index bounded =>
              (RawTermVector.variables_evaluate_get 0 _ _ index bounded).trans
                (by
                  rw [Nat.zero_add]
                  exact prependEnvironment_get intermediate
                    (graphEnvironment inputs output) bounded))).backward
          exact PRFunction.graphFormula_realizerOfEvaluation
            outer intermediate output
            evaluation
        · exact PRFunctionVector.graphFormulas_bodyRealizerOfEvaluation inner
            0 _ (zeroOffsetFits _)
            (prependEnvironment intermediate (graphEnvironment inputs output))
            inputs intermediate
            (fun index bounded =>
              prependEnvironment_originalInput intermediate inputs output bounded)
            (fun index bounded => by
              rw [Nat.zero_add]
              exact prependEnvironment_get intermediate
                (graphEnvironment inputs output) bounded)
            ⟨rfl⟩
    | _, @PRFunction.primitiveRecursion parameterArity base step,
        inputs, output, evaluation => by
        let counter := inputs.getD 0
        let parameters := inputs.tailD
        have inputsEquality : NatVector.cons counter parameters = inputs :=
          NatVector.rebuildD inputs
        rw [← inputsEquality] at evaluation ⊢
        let baseCore := RawFormula.conj
          (betaValueFormula
            (RawTerm.bvar 1) (RawTerm.bvar 2) RawTerm.zero (RawTerm.bvar 0))
          (base.graphFormula.apply (RawTerm.bvar 0)
            (primitiveBaseParameters _))
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
              (primitiveStepInputs _)))
        let transitionClause := RawFormula.all
          (RawFormula.impl
            (lessThanFormula (RawTerm.bvar 0) (RawTerm.bvar 4))
            (transitionCore.existsMany 2))
        let outputClause := betaValueFormula
          (RawTerm.bvar 0) (RawTerm.bvar 1)
          (RawTerm.bvar 3) (RawTerm.bvar 2)
        let body := RawFormula.conj baseClause
          (RawFormula.conj transitionClause outputClause)
        change (body.existsMany 2).Realizes
          (graphEnvironment (NatVector.cons counter parameters) output)
        let runWitness := informativePrimitiveRecursionRunOfEvaluation
          parameters counter output evaluation.down
        let runValues := runWitness.1
        let run := runWitness.2
        let dividend := runValues.betaDividend
        let coefficient := runValues.betaCoefficient
        let sequenceParameters :=
          NatVector.cons dividend (NatVector.cons coefficient NatVector.nil)
        apply RawFormula.existsManyRealizesBackward _ _ sequenceParameters
        let originalEnvironment :=
          graphEnvironment (NatVector.cons counter parameters) output
        let topEnvironment := prependEnvironment sequenceParameters
          originalEnvironment
        have topParameterValues :
            (index : Nat) -> (bounded : index < parameterArity) ->
              topEnvironment (4 + index) = parameters.get index bounded := by
          intro index bounded
          exact prependTwo_graphParameter
            dividend coefficient counter output parameters bounded
        constructor
        · let baseValue := runValues.get 0 (Nat.zero_lt_succ counter)
          refine ⟨baseValue, ?_⟩
          let baseEnvironment := pushEnvironment topEnvironment baseValue
          constructor
          · apply betaValueFormula_realizesOfEquality
            exact (betaComponent_encoded_vector runValues
              (Nat.zero_lt_succ counter)).symm
          · apply (base.graphFormula.apply_realizes
              (RawTerm.bvar 0) (primitiveBaseParameters _)
              baseEnvironment parameters baseValue rfl
              (primitiveBaseParameters_evaluate topEnvironment parameters
                baseValue topParameterValues)).backward
            exact PRFunction.graphFormula_realizerOfEvaluation
              base parameters baseValue
              run.baseEvaluation
        · constructor
          · intro index conditionRealizer
            let bounded :=
              (lessThanFormula_ltOfRealizer
                (RawTerm.bvar 0) (RawTerm.bvar 4)
                (pushEnvironment topEnvironment index) conditionRealizer).down
            let previous := runValues.get index
              (Nat.lt_trans bounded (Nat.lt_succ_self counter))
            let next := runValues.get (Nat.succ index)
              (Nat.succ_lt_succ bounded)
            let adjacent :=
              NatVector.cons previous (NatVector.cons next NatVector.nil)
            apply RawFormula.existsManyRealizesBackward _ _ adjacent
            let stepEnvironment := prependEnvironment adjacent
              (pushEnvironment topEnvironment index)
            constructor
            · apply betaValueFormula_realizesOfEquality
              exact (betaComponent_encoded_vector runValues
                (Nat.lt_trans bounded (Nat.lt_succ_self counter))).symm
            · constructor
              · apply betaValueFormula_realizesOfEquality
                exact (betaComponent_encoded_vector runValues
                  (Nat.succ_lt_succ bounded)).symm
              · apply (step.graphFormula.apply_realizes
                  (RawTerm.bvar 1) (primitiveStepInputs _)
                  stepEnvironment
                  (NatVector.cons index (NatVector.cons previous parameters))
                  next rfl (fun inputIndex inputBounded => by
                    cases inputIndex with
                    | zero => rfl
                    | succ inputIndex =>
                        cases inputIndex with
                        | zero => rfl
                        | succ parameterIndex =>
                            exact primitiveStepParameters_evaluate
                              topEnvironment parameters index previous next
                              topParameterValues parameterIndex
                              (Nat.lt_of_succ_lt_succ
                                (Nat.lt_of_succ_lt_succ inputBounded)))).backward
                exact PRFunction.graphFormula_realizerOfEvaluation step
                  (NatVector.cons index (NatVector.cons previous parameters))
                  next (run.stepEvaluation index bounded)
          · apply betaValueFormula_realizesOfEquality
            exact run.finalValue.down.symm.trans
              (betaComponent_encoded_vector runValues
                (Nat.lt_succ_self counter)).symm

  /-- Read vector execution from the conjunction compiled for its graphs. -/
  def PRFunctionVector.graphFormulas_bodyEvaluationOfRealizer :
      {inputArity length : Nat} ->
      (programs : PRFunctionVector inputArity length) ->
      (offset total : Nat) ->
      (fits : offset + length <= total) ->
      (environment : Environment) ->
      (inputs : NatVector inputArity) ->
      (outputs : NatVector length) ->
      ((index : Nat) -> (bounded : index < inputArity) ->
        environment (Nat.succ total + index) = inputs.get index bounded) ->
      ((index : Nat) -> (bounded : index < length) ->
        environment (offset + index) = outputs.get index bounded) ->
      (programs.graphFormulas.body offset total fits).raw.Realizes environment ->
        PLift (PRFunctionVector.Evaluates programs inputs outputs)
    | _, _, PRFunctionVector.nil, _offset, _total, _fits, _environment,
        _inputs, outputs, _inputValues, _outputValues, _realizer =>
        ⟨(NatVector.tabulateD_getD_self outputs).symm⟩
    | _, _, PRFunctionVector.cons head tail, offset, total, fits, environment,
        inputs, outputs, inputValues, outputValues, realizer => by
        change
          ((head.graphFormula.apply (RawTerm.bvar offset)
              (RawTermVector.variables (Nat.succ total) _)).Realizes environment ×
            (tail.graphFormulas.body (Nat.succ offset) total
              (succOffsetTailFits fits)).raw.Realizes environment) at realizer
        have headGraphRealizer :=
          (head.graphFormula.apply_realizes
            (RawTerm.bvar offset)
            (RawTermVector.variables (Nat.succ total) _)
            environment inputs (outputs.getD 0)
            ((outputValues 0 (Nat.zero_lt_succ _)).trans
              (NatVector.getD_eq_get outputs (Nat.zero_lt_succ _)).symm)
            (fun index bounded =>
              (RawTermVector.variables_evaluate_get
                (Nat.succ total) _ environment index bounded).trans
                (inputValues index bounded))).forward realizer.1
        have headEvaluation :=
          PRFunction.graphFormula_evaluationOfRealizer
            head inputs (outputs.getD 0)
            headGraphRealizer
        have tailEvaluation :=
          PRFunctionVector.graphFormulas_bodyEvaluationOfRealizer tail
            (Nat.succ offset) total (succOffsetTailFits fits)
            environment inputs outputs.tailD inputValues
            (fun index bounded => by
              have mapped := outputValues (Nat.succ index)
                (Nat.succ_lt_succ bounded)
              rw [Nat.succ_add]
              exact mapped.trans (NatVector.tailD_get outputs bounded).symm)
            realizer.2
        exact ⟨(NatVector.rebuildD outputs).symm.trans
          ((congrArg (fun headValue => NatVector.cons headValue outputs.tailD)
            headEvaluation.down).trans
            (congrArg
              (fun tailValues =>
                NatVector.cons (PRFunction.runCore head inputs) tailValues)
              tailEvaluation.down))⟩

  /-- Build the compiled graph-vector conjunction from vector execution. -/
  def PRFunctionVector.graphFormulas_bodyRealizerOfEvaluation :
      {inputArity length : Nat} ->
      (programs : PRFunctionVector inputArity length) ->
      (offset total : Nat) ->
      (fits : offset + length <= total) ->
      (environment : Environment) ->
      (inputs : NatVector inputArity) ->
      (outputs : NatVector length) ->
      ((index : Nat) -> (bounded : index < inputArity) ->
        environment (Nat.succ total + index) = inputs.get index bounded) ->
      ((index : Nat) -> (bounded : index < length) ->
        environment (offset + index) = outputs.get index bounded) ->
      PLift (PRFunctionVector.Evaluates programs inputs outputs) ->
        (programs.graphFormulas.body offset total fits).raw.Realizes environment
    | _, _, PRFunctionVector.nil, _offset, _total, _fits, _environment,
        _inputs, _outputs, _inputValues, _outputValues, _evaluation =>
        fun impossible => impossible.elim
    | _, _, PRFunctionVector.cons head tail, offset, total, fits, environment,
        inputs, outputs, inputValues, outputValues, evaluation => by
        change
          (head.graphFormula.apply (RawTerm.bvar offset)
              (RawTermVector.variables (Nat.succ total) _)).Realizes environment ×
            (tail.graphFormulas.body (Nat.succ offset) total
              (succOffsetTailFits fits)).raw.Realizes environment
        have headEvaluation : PRFunction.Evaluates head inputs
            (outputs.getD 0) := by
          unfold PRFunction.Evaluates
          exact congrArg (fun values => values.getD 0) evaluation.down
        have tailEvaluation : PRFunctionVector.Evaluates tail inputs
            outputs.tailD := by
          unfold PRFunctionVector.Evaluates
          exact (congrArg (fun values => values.tailD) evaluation.down).trans
            (NatVector.tailD_cons
              (PRFunction.runCore head inputs)
              (PRFunctionVector.runCore tail inputs))
        constructor
        · apply (head.graphFormula.apply_realizes
            (RawTerm.bvar offset)
            (RawTermVector.variables (Nat.succ total) _)
            environment inputs (outputs.getD 0)
            ((outputValues 0 (Nat.zero_lt_succ _)).trans
              (NatVector.getD_eq_get outputs (Nat.zero_lt_succ _)).symm)
            (fun index bounded =>
              (RawTermVector.variables_evaluate_get
                (Nat.succ total) _ environment index bounded).trans
                (inputValues index bounded))).backward
          exact PRFunction.graphFormula_realizerOfEvaluation
            head inputs (outputs.getD 0)
            ⟨headEvaluation⟩
        · exact PRFunctionVector.graphFormulas_bodyRealizerOfEvaluation tail
            (Nat.succ offset) total (succOffsetTailFits fits)
            environment inputs outputs.tailD inputValues
            (fun index bounded => by
              have mapped := outputValues (Nat.succ index)
                (Nat.succ_lt_succ bounded)
              rw [Nat.succ_add]
              exact mapped.trans (NatVector.tailD_get outputs bounded).symm)
            ⟨tailEvaluation⟩
end

/-- The existing graph compiler is informatively exact in both directions. -/
def PRFunction.graphFormula_realizerEquivalence
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity)
    (output : Nat) :
    RealizerEquivalence
      (program.graphFormula.raw.Realizes (graphEnvironment inputs output))
      (PLift (PRFunction.Evaluates program inputs output)) :=
  { forward := program.graphFormula_evaluationOfRealizer inputs output
    backward := program.graphFormula_realizerOfEvaluation inputs output }

/-- Substituting concrete term arguments into a compiled graph preserves the
same informative execution witness without exposing the compiler tree. -/
def PRFunction.appliedGraph_realizerEquivalence
    {arity : Nat}
    (program : PRFunction arity)
    (outputTerm : RawTerm)
    (inputTerms : RawTermVector arity)
    (environment : Environment)
    (inputs : NatVector arity)
    (output : Nat)
    (outputValue : outputTerm.evaluate environment = output)
    (inputValues :
      (index : Nat) ->
        (bounded : index < arity) ->
          (inputTerms.getD index).evaluate environment =
            inputs.get index bounded) :
    RealizerEquivalence
      ((program.graphFormula.apply outputTerm inputTerms).Realizes environment)
      (PLift (PRFunction.Evaluates program inputs output)) :=
  let applied := program.graphFormula.apply_realizes
    outputTerm inputTerms environment inputs output outputValue inputValues
  let represented := program.graphFormula_realizerEquivalence inputs output
  { forward := fun realizer => represented.forward (applied.forward realizer)
    backward := fun evaluation =>
      applied.backward (represented.backward evaluation) }

/-- Indexed counterpart of `appliedGraph_realizerEquivalence`. Its result type
does not normalize a large compiled graph merely to expose products and sigma
types. -/
def PRFunction.appliedGraph_informativeWitnessEquivalence
    {arity : Nat}
    (program : PRFunction arity)
    (outputTerm : RawTerm)
    (inputTerms : RawTermVector arity)
    (environment : Environment)
    (inputs : NatVector arity)
    (output : Nat)
    (outputValue : outputTerm.evaluate environment = output)
    (inputValues :
      (index : Nat) ->
        (bounded : index < arity) ->
          (inputTerms.getD index).evaluate environment =
            inputs.get index bounded) :
    RealizerEquivalence
      (RawFormula.InformativeWitness environment
        (program.graphFormula.apply outputTerm inputTerms))
      (PLift (PRFunction.Evaluates program inputs output)) :=
  let direct := program.appliedGraph_realizerEquivalence
    outputTerm inputTerms environment inputs output outputValue inputValues
  { forward := fun witness =>
      direct.forward
        (RawFormula.informativeWitnessToRealizes
          (program.graphFormula.apply outputTerm inputTerms)
          environment witness)
    backward := fun evaluation =>
      RawFormula.realizesToInformativeWitness
        (program.graphFormula.apply outputTerm inputTerms)
        environment (direct.backward evaluation) }

/-! ## Exact informative interpretation of the root-history proof checker -/

/-- A named boundary for the existing checker program keeps elaboration from
normalizing its large primitive-recursive tree while preserving it exactly. -/
def informativeProofCheckProgram : PRFunction 3 := PRFunction.proofCheck

theorem informativeProofCheckProgram_evaluates
    (historyCode proofCode sentenceCode : Nat) :
    PRFunction.Evaluates informativeProofCheckProgram
      (NatVector.cons historyCode
        (NatVector.cons proofCode
          (NatVector.cons sentenceCode NatVector.nil)))
      (proofCheckBit historyCode proofCode sentenceCode) := by
  unfold informativeProofCheckProgram
  exact PRFunction.proofCheck_evaluates historyCode proofCode sentenceCode

def informativeProofFormula : ScopedFormula 3 :=
  { raw := informativeProofCheckProgram.graphFormula.apply
      (RawTerm.numeral 1) proofFormulaInputs
    isScoped := informativeProofCheckProgram.graphFormula.apply_wellScoped
      (RawTerm.numeral 1) proofFormulaInputs
      (RawTerm.numeral_wellScoped 1 3)
      proofFormulaInputs_wellScoped }

def informativeHistoryProofFormula (history : TheoryHistory) :
    ScopedFormula 2 :=
  informativeProofFormula.instantiate
    (ScopedTerm.numeral 2 history.quote)

theorem informativeProofFormula_raw_eq :
    informativeProofFormula.raw = proofFormula.raw := by
  have graphEquality :
      informativeProofCheckProgram.graphFormula =
        PRFunction.proofCheck.graphFormula :=
    congrArg PRFunction.graphFormula (Eq.refl PRFunction.proofCheck)
  unfold informativeProofFormula proofFormula proofCheckGraph
  exact congrArg
    (fun graph : ArithmeticGraph 3 =>
      graph.apply (RawTerm.numeral 1) proofFormulaInputs)
    graphEquality

theorem informativeHistoryProofFormula_raw_eq
    (history : TheoryHistory) :
    (informativeHistoryProofFormula history).raw =
      (historyProofFormula history).raw := by
  unfold informativeHistoryProofFormula historyProofFormula
    ScopedFormula.instantiate RawFormula.instantiateTerm
  exact congrArg
    (fun rawFormula : RawFormula =>
      rawFormula.substitute
        (singleTermSubstitution
          (ScopedTerm.numeral 2 history.quote).raw))
    informativeProofFormula_raw_eq

def informativeRootHistoryProofFormula_realizerEquivalence
    (proofCode sentenceCode : Nat) :
    RealizerEquivalence
      (RawFormula.InformativeWitness
        (FirstOrderArithmeticFormula.binaryAssignment proofCode sentenceCode)
        (informativeHistoryProofFormula TheoryHistory.root).raw)
      (PLift (haProofCheck proofCode sentenceCode = true)) :=
  let environment := FirstOrderArithmeticFormula.binaryAssignment
    proofCode sentenceCode
  let numeral := ScopedTerm.numeral 2 TheoryHistory.root.quote
  let proofEnvironment := pushEnvironment environment
    (numeral.raw.evaluate environment)
  let inputs := NatVector.cons (proofEnvironment 0)
    (NatVector.cons (proofEnvironment 1)
      (NatVector.cons (proofEnvironment 2) NatVector.nil))
  let instantiated := informativeProofFormula.informativeWitness_instantiate
    numeral environment
  let represented :=
    informativeProofCheckProgram.appliedGraph_informativeWitnessEquivalence
      (RawTerm.numeral 1) proofFormulaInputs proofEnvironment inputs 1
      (RawTerm.evaluate_numeral 1 proofEnvironment)
      (fun index bounded => by
        cases index with
        | zero => rfl
        | succ index =>
            cases index with
            | zero => rfl
            | succ index =>
                cases index with
                | zero => rfl
                | succ index =>
                    exact (Nat.not_lt_zero index
                      (Nat.lt_of_succ_lt_succ
                        (Nat.lt_of_succ_lt_succ
                          (Nat.lt_of_succ_lt_succ bounded)))).elim)
  { forward := fun realizer =>
      let evaluation := represented.forward
        (instantiated.forward realizer)
      let canonical := informativeProofCheckProgram_evaluates
        (proofEnvironment 0) (proofEnvironment 1) (proofEnvironment 2)
      have checkedAtEnvironment :
          proofCheckBit (proofEnvironment 0)
            (proofEnvironment 1) (proofEnvironment 2) = 1 :=
        canonical.trans evaluation.down.symm
      have checked : proofCheckBit TheoryHistory.root.quote
          proofCode sentenceCode = 1 := by
        change proofCheckBit (numeral.raw.evaluate environment)
          proofCode sentenceCode = 1 at checkedAtEnvironment
        unfold numeral ScopedTerm.numeral at checkedAtEnvironment
        rw [RawTerm.evaluate_numeral TheoryHistory.root.quote environment]
          at checkedAtEnvironment
        exact checkedAtEnvironment
      ⟨(haProofCheck_eq_true_iff proofCode sentenceCode).mpr checked⟩
    backward := fun checked =>
      have checkedBit : proofCheckBit TheoryHistory.root.quote
          proofCode sentenceCode = 1 :=
        (haProofCheck_eq_true_iff proofCode sentenceCode).mp checked.down
      have checkedAtEnvironment :
          proofCheckBit (proofEnvironment 0)
            (proofEnvironment 1) (proofEnvironment 2) = 1 := by
        change proofCheckBit (numeral.raw.evaluate environment)
          proofCode sentenceCode = 1
        unfold numeral ScopedTerm.numeral
        rw [RawTerm.evaluate_numeral TheoryHistory.root.quote environment]
        exact checkedBit
      let canonical := informativeProofCheckProgram_evaluates
        (proofEnvironment 0) (proofEnvironment 1) (proofEnvironment 2)
      instantiated.backward
        (represented.backward
          ⟨checkedAtEnvironment.symm.trans canonical⟩) }

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.existsManyRealizesBackward
#print axioms RelationalPerimeter.HeytingArithmetic.betaValueFormula_realizesOfEquality
#print axioms RelationalPerimeter.HeytingArithmetic.informativePrimitiveRecursionRunOfEvaluation
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.graphFormula_realizerEquivalence
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.appliedGraph_realizerEquivalence
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.appliedGraph_informativeWitnessEquivalence
#print axioms RelationalPerimeter.HeytingArithmetic.informativeProofFormula_raw_eq
#print axioms RelationalPerimeter.HeytingArithmetic.informativeHistoryProofFormula_raw_eq
#print axioms RelationalPerimeter.HeytingArithmetic.informativeRootHistoryProofFormula_realizerEquivalence
/- AXIOM_AUDIT_END -/
