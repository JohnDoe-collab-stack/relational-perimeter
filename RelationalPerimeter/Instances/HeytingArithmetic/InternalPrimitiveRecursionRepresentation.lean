import RelationalPerimeter.Instances.HeytingArithmetic.InternalBoundedUniversal
import RelationalPerimeter.Instances.HeytingArithmetic.InternalPRRepresentability
import RelationalPerimeter.Instances.HeytingArithmetic.InternalScopedSubstitution

/-!
# Positive internal certificate for primitive recursion
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A run and its finite value trace kept together as positive data in `Type`. -/
structure PrimitiveRecursionRunCertificate
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (parameters : NatVector parameterArity)
    (counter output : Nat) : Type where
  values : NatVector (Nat.succ counter)
  run : PrimitiveRecursionRun base step parameters counter output values

/-- Construct the complete finite trace of a primitive-recursive execution. -/
def PrimitiveRecursionRunCertificate.ofEvaluation
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    {parameters : NatVector parameterArity}
    {counter output : Nat}
    (evaluation : PRFunction.Evaluates
      (PRFunction.primitiveRecursion base step)
      (NatVector.cons counter parameters) output) :
    PrimitiveRecursionRunCertificate base step parameters counter output :=
  Nat.rec
    (motive := fun counter =>
      (output : Nat) ->
      PRFunction.Evaluates
        (PRFunction.primitiveRecursion base step)
        (NatVector.cons counter parameters) output ->
      PrimitiveRecursionRunCertificate base step parameters counter output)
    (fun output zeroEvaluation =>
      { values := NatVector.cons output NatVector.nil
        run :=
          { baseEvaluation :=
              zeroEvaluation.trans
                (PRFunction.Evaluates.runCore_primitive_zero
                  base step parameters)
            stepEvaluation := by
              intro index impossible
              exact (Nat.not_lt_zero index impossible).elim
            finalValue := rfl } })
    (fun counter inductionHypothesis output successorEvaluation =>
      let previous :=
        PRFunction.runCore (PRFunction.primitiveRecursion base step)
          (NatVector.cons counter parameters)
      let previousCertificate := inductionHypothesis previous rfl
      let previousValues := previousCertificate.values
      let previousRun := previousCertificate.run
      { values := previousValues.snoc output
        run :=
          { baseEvaluation := by
              rw [NatVector.get_snoc_of_lt]
              exact previousRun.baseEvaluation
            stepEvaluation := by
              intro index bounded
              have boundedOrFinal : index < counter ∨ index = counter :=
                Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bounded)
              cases boundedOrFinal with
              | inl earlier =>
                  have oldStep := previousRun.stepEvaluation index earlier
                  rw [NatVector.get_snoc_of_lt,
                    NatVector.get_snoc_of_lt]
                  exact oldStep
              | inr finalIndex =>
                  cases finalIndex
                  rw [NatVector.get_snoc_of_lt
                      previousValues output (Nat.lt_succ_self counter),
                    NatVector.get_snoc_last previousValues output,
                    previousRun.finalValue]
                  exact successorEvaluation.trans
                    (PRFunction.Evaluates.runCore_primitive_succ
                      base step counter parameters)
            finalValue := NatVector.get_snoc_last previousValues output } })
    counter output evaluation

/-- Substitution commutes exactly with application of an arithmetic graph. -/
theorem ArithmeticGraph.apply_substitute_exact
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity)
    (substitution : Substitution)
    (outputAfter : RawTerm)
    (inputsAfter : RawTermVector arity)
    (outputExact : output.substitute substitution = outputAfter)
    (inputsExact : (index : Nat) ->
      (inputs.getD index).substitute substitution = inputsAfter.getD index) :
    (graph.apply output inputs).substitute substitution =
      graph.apply outputAfter inputsAfter := by
  unfold ArithmeticGraph.apply
  rw [RawFormula.internalSubstituteCompose]
  apply RawFormula.internalSubstituteCongr
  intro index
  cases index with
  | zero => exact outputExact
  | succ index => exact inputsExact index

/-- A graph application only needs agreement on its declared input arity. -/
theorem ArithmeticGraph.apply_substitute_exact_bounded
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity)
    (substitution : Substitution)
    (outputAfter : RawTerm)
    (inputsAfter : RawTermVector arity)
    (outputExact : output.substitute substitution = outputAfter)
    (inputsExact : (index : Nat) -> index < arity ->
      (inputs.getD index).substitute substitution = inputsAfter.getD index) :
    (graph.apply output inputs).substitute substitution =
      graph.apply outputAfter inputsAfter := by
  unfold ArithmeticGraph.apply
  rw [RawFormula.internalSubstituteCompose]
  apply RawFormula.substitute_eq_of_scoped_agreement
    graph.raw graph.isScoped
  intro index bounded
  cases index with
  | zero => exact outputExact
  | succ index =>
      exact inputsExact index (Nat.lt_of_succ_lt_succ bounded)

/-- Renaming never changes a closed numeral. -/
theorem RawTerm.numeral_rename
    (value : Nat)
    (rho : Renaming) :
    (RawTerm.numeral value).rename rho = RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis

/-- Two leading entries are skipped by an index offset of two. -/
theorem NatVector.cons_cons_getD_add_two
    {length : Nat}
    (first second : Nat)
    (tail : NatVector length)
    (index : Nat) :
    (NatVector.cons first (NatVector.cons second tail)).getD (2 + index) =
      tail.getD index := by
  rw [Nat.add_comm 2 index]
  rw [Nat.add_succ, Nat.add_succ, Nat.add_zero]
  rfl

/-- Substitution acts componentwise on the strict-order formula. -/
theorem lessThanFormula_substitute
    (left right : RawTerm)
    (substitution : Substitution) :
    (lessThanFormula left right).substitute substitution =
      lessThanFormula (left.substitute substitution)
        (right.substitute substitution) := by
  apply congrArg RawFormula.ex
  apply congrArgTwo RawFormula.equal
  · apply congrArgTwo RawTerm.add
    · exact RawTerm.renameSucc_substituteLift_local left substitution
    · rfl
  · exact RawTerm.renameSucc_substituteLift_local right substitution

/-- Substitution acts componentwise on the remainder formula. -/
theorem remainderFormula_substitute
    (dividend modulus remainder : RawTerm)
    (substitution : Substitution) :
    (remainderFormula dividend modulus remainder).substitute substitution =
      remainderFormula
        (dividend.substitute substitution)
        (modulus.substitute substitution)
        (remainder.substitute substitution) := by
  apply congrArgTwo RawFormula.conj
  · exact lessThanFormula_substitute remainder modulus substitution
  · apply congrArg RawFormula.ex
    apply congrArgTwo RawFormula.equal
    · exact RawTerm.renameSucc_substituteLift_local dividend substitution
    · apply congrArgTwo RawTerm.add
      · apply congrArgTwo RawTerm.mul
        · rfl
        · exact RawTerm.renameSucc_substituteLift_local modulus substitution
      · exact RawTerm.renameSucc_substituteLift_local remainder substitution

/-- Substitution acts componentwise on the arithmetic beta formula. -/
theorem betaValueFormula_substitute
    (dividend coefficient index value : RawTerm)
    (substitution : Substitution) :
    (betaValueFormula dividend coefficient index value).substitute
        substitution =
      betaValueFormula
        (dividend.substitute substitution)
        (coefficient.substitute substitution)
        (index.substitute substitution)
        (value.substitute substitution) := by
  exact remainderFormula_substitute dividend
    (betaModulusTerm coefficient index) value substitution

/-- Component equalities determine the substituted beta formula exactly. -/
theorem betaValueFormula_substitute_exact
    (dividend coefficient index value : RawTerm)
    (substitution : Substitution)
    (dividendAfter coefficientAfter indexAfter valueAfter : RawTerm)
    (dividendExact : dividend.substitute substitution = dividendAfter)
    (coefficientExact : coefficient.substitute substitution = coefficientAfter)
    (indexExact : index.substitute substitution = indexAfter)
    (valueExact : value.substitute substitution = valueAfter) :
    (betaValueFormula dividend coefficient index value).substitute
        substitution =
      betaValueFormula dividendAfter coefficientAfter indexAfter valueAfter := by
  rw [betaValueFormula_substitute, dividendExact, coefficientExact,
    indexExact, valueExact]

/-- Closing substitution fixes every variable protected by the binder depth. -/
theorem numeralClosingSubstitutionAtDepth_inside
    {count : Nat}
    (values : NatVector count)
    (depth index : Nat)
    (bounded : index < depth) :
    numeralClosingSubstitutionAtDepth values depth index =
      RawTerm.bvar index := by
  induction depth generalizing index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            (numeralClosingSubstitutionAtDepth values depth index).rename
                Nat.succ = RawTerm.bvar (Nat.succ index)
          rw [inductionHypothesis index (Nat.lt_of_succ_lt_succ bounded)]
          rfl

/-- Variables after the binder depth are replaced by the corresponding numeral. -/
theorem numeralClosingSubstitutionAtDepth_after
    {count : Nat}
    (values : NatVector count)
    (depth index : Nat) :
    numeralClosingSubstitutionAtDepth values depth (depth + index) =
      RawTerm.numeral (values.getD index) := by
  induction depth with
  | zero =>
      rw [Nat.zero_add]
      change numeralClosingSubstitution values index =
        RawTerm.numeral (values.getD index)
      rfl
  | succ depth inductionHypothesis =>
      rw [Nat.succ_add]
      change
        (numeralClosingSubstitutionAtDepth values depth
          (depth + index)).rename Nat.succ = _
      rw [inductionHypothesis, RawTerm.numeral_rename]

def internallyNumeralwiseRepresentedPrimitiveRecursion
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    (baseRepresented : InternallyNumeralwiseRepresentedPRFunction base)
    (stepRepresented : InternallyNumeralwiseRepresentedPRFunction step) :
    InternallyNumeralwiseRepresentedPRFunction
      (PRFunction.primitiveRecursion base step) := by
  refine { numeralProof := ?_ }
  intro inputs
  let counter := inputs.getD 0
  let parameters := inputs.tailD
  have inputsRebuilt : NatVector.cons counter parameters = inputs := by
    exact NatVector.rebuildD inputs
  rw [← inputsRebuilt]
  ·
      let output := (PRFunction.primitiveRecursion base step).run
        (NatVector.cons counter parameters)
      have evaluation : PRFunction.Evaluates
          (PRFunction.primitiveRecursion base step)
          (NatVector.cons counter parameters) output := rfl
      let certificate :=
        PrimitiveRecursionRunCertificate.ofEvaluation evaluation
      let values := certificate.values
      let run := certificate.run
      exact by
          let dividend := values.betaDividend
          let coefficient := values.betaCoefficient
          let dividendTerm := ScopedTerm.numeral 0 dividend
          let coefficientTerm := ScopedTerm.numeral 0 coefficient
          let baseValue := values.get 0 (Nat.zero_lt_succ counter)
          have baseValueExact : baseValue = base.run parameters :=
            run.baseEvaluation
          let baseBeta := betaValueClosedProof dividendTerm coefficientTerm
            (ScopedTerm.zero 0) (ScopedTerm.numeral 0 baseValue)
            (by
              simpa only [dividendTerm, coefficientTerm,
                ScopedTerm.numeral, ScopedTerm.zero,
                RawTerm.evaluate_numeral, RawTerm.evaluate,
                betaComponent] using
                (betaComponent_encoded_vector values
                  (Nat.zero_lt_succ counter)).symm)
          have baseGraph : Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil
              (base.graphFormula.numeralInstance parameters baseValue) := by
            rw [baseValueExact]
            exact baseRepresented.numeralProof parameters
          let baseConjunction := Derivation.conjunctionIntroduction
            baseBeta baseGraph
          let baseCore : ScopedFormula 1 :=
            { raw := RawFormula.conj
                (betaValueFormula
                  (RawTerm.numeral dividend)
                  (RawTerm.numeral coefficient)
                  RawTerm.zero (RawTerm.bvar 0))
                (base.graphFormula.apply (RawTerm.bvar 0)
                  parameters.numeralTerms)
              isScoped := And.intro
                (betaValueFormula_wellScoped _ _ _ _
                  (RawTerm.numeral_wellScoped dividend 1)
                  (RawTerm.numeral_wellScoped coefficient 1)
                  trivial (Nat.zero_lt_succ 0))
                (base.graphFormula.apply_wellScoped
                  (RawTerm.bvar 0) parameters.numeralTerms
                  (Nat.zero_lt_succ 0)
                  parameters.numeralTerms_wellScoped) }
          have baseConjunctionExact : Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil
              (baseCore.instantiate (ScopedTerm.numeral 0 baseValue)) := by
            refine Derivation.castConclusion ?_ baseConjunction
            apply ScopedFormula.eq_of_raw_eq
            apply congrArgTwo RawFormula.conj
            · change betaValueFormula (RawTerm.numeral dividend)
                  (RawTerm.numeral coefficient) RawTerm.zero
                  (RawTerm.numeral baseValue) =
                (betaValueFormula (RawTerm.numeral dividend)
                  (RawTerm.numeral coefficient) RawTerm.zero
                  (RawTerm.bvar 0)).substitute
                  (singleTermSubstitution (RawTerm.numeral baseValue))
              exact (betaValueFormula_substitute_exact
                (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                RawTerm.zero (RawTerm.bvar 0)
                (singleTermSubstitution (RawTerm.numeral baseValue))
                (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                RawTerm.zero (RawTerm.numeral baseValue)
                (RawTerm.numeral_substitute _ _)
                (RawTerm.numeral_substitute _ _) rfl rfl).symm
            · change base.graphFormula.apply (RawTerm.numeral baseValue)
                  parameters.numeralTerms =
                (base.graphFormula.apply (RawTerm.bvar 0)
                  parameters.numeralTerms).substitute
                  (singleTermSubstitution (RawTerm.numeral baseValue))
              exact (ArithmeticGraph.apply_substitute_exact
                base.graphFormula (RawTerm.bvar 0)
                parameters.numeralTerms
                (singleTermSubstitution (RawTerm.numeral baseValue))
                (RawTerm.numeral baseValue) parameters.numeralTerms rfl
                (fun index => by
                  rw [NatVector.numeralTerms_getD]
                  exact RawTerm.numeral_substitute _ _)).symm
          let baseClause := Derivation.existentialIntroduction
            (body := baseCore) (ScopedTerm.numeral 0 baseValue)
            baseConjunctionExact
          let previousVariable3 : ScopedTerm 3 :=
            ScopedTerm.bvar 0 (Nat.zero_lt_succ 2)
          let nextVariable3 : ScopedTerm 3 := ScopedTerm.bvar 1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
          let indexVariable3 : ScopedTerm 3 := ScopedTerm.bvar 2
            (Nat.succ_lt_succ
              (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
          let transitionCore : ScopedFormula 3 :=
            ScopedFormula.conj
              (scopedBetaValueFormula
                (ScopedTerm.numeral 3 dividend)
                (ScopedTerm.numeral 3 coefficient)
                indexVariable3 previousVariable3)
              (ScopedFormula.conj
                (scopedBetaValueFormula
                  (ScopedTerm.numeral 3 dividend)
                  (ScopedTerm.numeral 3 coefficient)
                  indexVariable3.succ nextVariable3)
                { raw := step.graphFormula.apply nextVariable3.raw
                    (RawTermVector.cons indexVariable3.raw
                      (RawTermVector.cons previousVariable3.raw
                        parameters.numeralTerms))
                  isScoped := step.graphFormula.apply_wellScoped
                    nextVariable3.raw
                    (RawTermVector.cons indexVariable3.raw
                      (RawTermVector.cons previousVariable3.raw
                        parameters.numeralTerms))
                    nextVariable3.isScoped
                    (And.intro indexVariable3.isScoped
                      (And.intro previousVariable3.isScoped
                        parameters.numeralTerms_wellScoped)) })
          let transitionBody : ScopedFormula 1 :=
            { raw := transitionCore.raw.existsMany 2
              isScoped := RawFormula.existsMany_wellScoped 2 1
                transitionCore.raw transitionCore.isScoped }
          have transitionInstances : (index : Nat) -> index < counter ->
              Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
                (transitionBody.instantiate
                  (ScopedTerm.numeral 0 index)) := by
            intro index bounded
            let previous := values.get index
              (Nat.lt_trans bounded (Nat.lt_succ_self counter))
            let next := values.get (Nat.succ index)
              (Nat.succ_lt_succ bounded)
            let previousTerm := ScopedTerm.numeral 0 previous
            let nextTerm := ScopedTerm.numeral 0 next
            let indexTerm := ScopedTerm.numeral 0 index
            let previousBeta := betaValueClosedProof dividendTerm
              coefficientTerm indexTerm previousTerm (by
                simpa only [dividendTerm, coefficientTerm, indexTerm,
                  previousTerm, ScopedTerm.numeral,
                  RawTerm.evaluate_numeral, RawTerm.evaluate,
                  betaComponent] using
                  (betaComponent_encoded_vector values
                    (Nat.lt_trans bounded
                      (Nat.lt_succ_self counter))).symm)
            let nextBeta := betaValueClosedProof dividendTerm coefficientTerm
              indexTerm.succ nextTerm (by
                simpa only [dividendTerm, coefficientTerm, indexTerm,
                  nextTerm, ScopedTerm.numeral, ScopedTerm.succ,
                  RawTerm.evaluate_numeral, RawTerm.evaluate,
                  betaComponent] using
                  (betaComponent_encoded_vector values
                    (Nat.succ_lt_succ bounded)).symm)
            have stepValueExact : next = step.run
                (NatVector.cons index
                  (NatVector.cons previous parameters)) :=
              run.stepEvaluation index bounded
            have stepGraph : Derivation LogicMode.intuitionistic haTheory
                FormulaContext.nil
                (step.graphFormula.numeralInstance
                  (NatVector.cons index
                    (NatVector.cons previous parameters)) next) := by
              rw [stepValueExact]
              exact stepRepresented.numeralProof _
            let conjunction := Derivation.conjunctionIntroduction previousBeta
              (Derivation.conjunctionIntroduction nextBeta stepGraph)
            let openTransition : ScopedFormula 2 :=
              let previousVariable := ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)
              let nextVariable := ScopedTerm.bvar 1
                (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
              ScopedFormula.conj
                (scopedBetaValueFormula
                  (ScopedTerm.numeral 2 dividend)
                  (ScopedTerm.numeral 2 coefficient)
                  (ScopedTerm.numeral 2 index) previousVariable)
                (ScopedFormula.conj
                  (scopedBetaValueFormula
                    (ScopedTerm.numeral 2 dividend)
                    (ScopedTerm.numeral 2 coefficient)
                    (ScopedTerm.numeral 2 (Nat.succ index)) nextVariable)
                  { raw := step.graphFormula.apply nextVariable.raw
                      (RawTermVector.cons (RawTerm.numeral index)
                        (RawTermVector.cons previousVariable.raw
                          parameters.numeralTerms))
                    isScoped := step.graphFormula.apply_wellScoped
                      nextVariable.raw
                      (RawTermVector.cons (RawTerm.numeral index)
                        (RawTermVector.cons previousVariable.raw
                          parameters.numeralTerms))
                      nextVariable.isScoped
                      (And.intro (RawTerm.numeral_wellScoped index 2)
                        (And.intro previousVariable.isScoped
                          parameters.numeralTerms_wellScoped)) })
            have closedTransition : Derivation LogicMode.intuitionistic haTheory
                FormulaContext.nil
                (openTransition.closeWithNumerals
                  (NatVector.cons previous
                    (NatVector.cons next NatVector.nil))) := by
              refine Derivation.castConclusion ?_ conjunction
              apply ScopedFormula.eq_of_raw_eq
              apply congrArgTwo RawFormula.conj
              · change betaValueFormula (RawTerm.numeral dividend)
                    (RawTerm.numeral coefficient) (RawTerm.numeral index)
                    (RawTerm.numeral previous) =
                  (betaValueFormula (RawTerm.numeral dividend)
                    (RawTerm.numeral coefficient) (RawTerm.numeral index)
                    (RawTerm.bvar 0)).substitute
                    (numeralClosingSubstitution
                      (NatVector.cons previous
                        (NatVector.cons next NatVector.nil)))
                exact (betaValueFormula_substitute_exact
                  (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                  (RawTerm.numeral index) (RawTerm.bvar 0)
                  (numeralClosingSubstitution
                    (NatVector.cons previous
                      (NatVector.cons next NatVector.nil)))
                  (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                  (RawTerm.numeral index) (RawTerm.numeral previous)
                  (RawTerm.numeral_substitute _ _)
                  (RawTerm.numeral_substitute _ _)
                  (RawTerm.numeral_substitute _ _) rfl).symm
              · apply congrArgTwo RawFormula.conj
                · change betaValueFormula (RawTerm.numeral dividend)
                      (RawTerm.numeral coefficient)
                      (RawTerm.numeral (Nat.succ index))
                      (RawTerm.numeral next) =
                    (betaValueFormula (RawTerm.numeral dividend)
                      (RawTerm.numeral coefficient)
                      (RawTerm.numeral (Nat.succ index))
                      (RawTerm.bvar 1)).substitute
                      (numeralClosingSubstitution
                        (NatVector.cons previous
                          (NatVector.cons next NatVector.nil)))
                  exact (betaValueFormula_substitute_exact
                    (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                    (RawTerm.numeral (Nat.succ index)) (RawTerm.bvar 1)
                    (numeralClosingSubstitution
                      (NatVector.cons previous
                        (NatVector.cons next NatVector.nil)))
                    (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                    (RawTerm.numeral (Nat.succ index)) (RawTerm.numeral next)
                    (RawTerm.numeral_substitute _ _)
                    (RawTerm.numeral_substitute _ _)
                    (RawTerm.numeral_substitute _ _) rfl).symm
                · change step.graphFormula.apply (RawTerm.numeral next)
                      (RawTermVector.cons (RawTerm.numeral index)
                        (RawTermVector.cons (RawTerm.numeral previous)
                          parameters.numeralTerms)) =
                    (step.graphFormula.apply (RawTerm.bvar 1)
                      (RawTermVector.cons (RawTerm.numeral index)
                        (RawTermVector.cons (RawTerm.bvar 0)
                          parameters.numeralTerms))).substitute
                      (numeralClosingSubstitution
                        (NatVector.cons previous
                          (NatVector.cons next NatVector.nil)))
                  exact (ArithmeticGraph.apply_substitute_exact
                    step.graphFormula (RawTerm.bvar 1)
                    (RawTermVector.cons (RawTerm.numeral index)
                      (RawTermVector.cons (RawTerm.bvar 0)
                        parameters.numeralTerms))
                    (numeralClosingSubstitution
                      (NatVector.cons previous
                        (NatVector.cons next NatVector.nil)))
                    (RawTerm.numeral next)
                    (RawTermVector.cons (RawTerm.numeral index)
                      (RawTermVector.cons (RawTerm.numeral previous)
                        parameters.numeralTerms))
                    rfl (fun position => by
                      cases position with
                      | zero => exact RawTerm.numeral_substitute _ _
                      | succ position =>
                          cases position with
                          | zero => rfl
                          | succ position =>
                              change (parameters.numeralTerms.getD position).substitute
                                  (numeralClosingSubstitution
                                    (NatVector.cons previous
                                      (NatVector.cons next NatVector.nil))) =
                                parameters.numeralTerms.getD position
                              rw [NatVector.numeralTerms_getD]
                              exact RawTerm.numeral_substitute _ _)).symm
            let witnessed := Derivation.introduceExistsMany openTransition
              (NatVector.cons previous
                (NatVector.cons next NatVector.nil)) closedTransition
            let indexVector := NatVector.cons index NatVector.nil
            have indexSubstitutionExact :
                numeralClosingSubstitutionAtDepth indexVector 2 2 =
                  RawTerm.numeral index := by
              change numeralClosingSubstitutionAtDepth indexVector 2 (2 + 0) =
                RawTerm.numeral index
              rw [numeralClosingSubstitutionAtDepth_after]
              rfl
            have openTransitionExact : openTransition.raw =
                transitionCore.raw.substitute
                  (numeralClosingSubstitutionAtDepth indexVector 2) := by
              apply congrArgTwo RawFormula.conj
              · change betaValueFormula (RawTerm.numeral dividend)
                    (RawTerm.numeral coefficient) (RawTerm.numeral index)
                    (RawTerm.bvar 0) =
                  (betaValueFormula (RawTerm.numeral dividend)
                    (RawTerm.numeral coefficient) (RawTerm.bvar 2)
                    (RawTerm.bvar 0)).substitute
                    (numeralClosingSubstitutionAtDepth indexVector 2)
                exact (betaValueFormula_substitute_exact
                  (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                  (RawTerm.bvar 2) (RawTerm.bvar 0)
                  (numeralClosingSubstitutionAtDepth indexVector 2)
                  (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                  (RawTerm.numeral index) (RawTerm.bvar 0)
                  (RawTerm.numeral_substitute _ _)
                  (RawTerm.numeral_substitute _ _)
                  indexSubstitutionExact rfl).symm
              · apply congrArgTwo RawFormula.conj
                · change betaValueFormula (RawTerm.numeral dividend)
                      (RawTerm.numeral coefficient)
                      (RawTerm.numeral (Nat.succ index))
                      (RawTerm.bvar 1) =
                    (betaValueFormula (RawTerm.numeral dividend)
                      (RawTerm.numeral coefficient)
                      (RawTerm.succ (RawTerm.bvar 2))
                      (RawTerm.bvar 1)).substitute
                      (numeralClosingSubstitutionAtDepth indexVector 2)
                  exact (betaValueFormula_substitute_exact
                    (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                    (RawTerm.succ (RawTerm.bvar 2)) (RawTerm.bvar 1)
                    (numeralClosingSubstitutionAtDepth indexVector 2)
                    (RawTerm.numeral dividend) (RawTerm.numeral coefficient)
                    (RawTerm.numeral (Nat.succ index)) (RawTerm.bvar 1)
                    (RawTerm.numeral_substitute _ _)
                    (RawTerm.numeral_substitute _ _)
                    (congrArg RawTerm.succ indexSubstitutionExact) rfl).symm
                · change step.graphFormula.apply (RawTerm.bvar 1)
                      (RawTermVector.cons (RawTerm.numeral index)
                        (RawTermVector.cons (RawTerm.bvar 0)
                          parameters.numeralTerms)) =
                    (step.graphFormula.apply (RawTerm.bvar 1)
                      (RawTermVector.cons (RawTerm.bvar 2)
                        (RawTermVector.cons (RawTerm.bvar 0)
                          parameters.numeralTerms))).substitute
                      (numeralClosingSubstitutionAtDepth indexVector 2)
                  exact (ArithmeticGraph.apply_substitute_exact
                    step.graphFormula (RawTerm.bvar 1)
                    (RawTermVector.cons (RawTerm.bvar 2)
                      (RawTermVector.cons (RawTerm.bvar 0)
                        parameters.numeralTerms))
                    (numeralClosingSubstitutionAtDepth indexVector 2)
                    (RawTerm.bvar 1)
                    (RawTermVector.cons (RawTerm.numeral index)
                      (RawTermVector.cons (RawTerm.bvar 0)
                        parameters.numeralTerms)) rfl
                    (fun position => by
                      cases position with
                      | zero =>
                          exact indexSubstitutionExact
                      | succ position =>
                          cases position with
                          | zero => rfl
                          | succ position =>
                              change (parameters.numeralTerms.getD position).substitute
                                  (numeralClosingSubstitutionAtDepth indexVector 2) =
                                parameters.numeralTerms.getD position
                              rw [NatVector.numeralTerms_getD]
                              exact RawTerm.numeral_substitute _ _)).symm
            refine Derivation.castConclusion ?_ witnessed
            apply ScopedFormula.eq_of_raw_eq
            change openTransition.raw.existsMany 2 =
              (transitionCore.raw.existsMany 2).substitute
                (singleTermSubstitution (RawTerm.numeral index))
            calc
              openTransition.raw.existsMany 2 =
                  (transitionCore.raw.substitute
                    (numeralClosingSubstitutionAtDepth indexVector 2)).existsMany 2 :=
                congrArg (fun formula => formula.existsMany 2)
                  openTransitionExact
              _ = (transitionCore.raw.existsMany 2).substitute
                    (numeralClosingSubstitution indexVector) :=
                RawFormula.existsMany_substitute_numeralClosing
                  transitionCore.raw indexVector 2
              _ = (transitionCore.raw.existsMany 2).substitute
                    (singleTermSubstitution (RawTerm.numeral index)) := by
                apply RawFormula.substitute_eq_of_scoped_agreement
                  (transitionCore.raw.existsMany 2)
                  transitionBody.isScoped
                intro position positionBounded
                cases position with
                | zero => rfl
                | succ position =>
                    exact (Nat.not_lt_zero position
                      (Nat.lt_of_succ_lt_succ positionBounded)).elim
          let transitionClause := proveBoundedUniversal transitionBody counter
            transitionInstances
          let outputBeta := betaValueClosedProof dividendTerm coefficientTerm
            (ScopedTerm.numeral 0 counter) (ScopedTerm.numeral 0 output)
            (by
              simpa only [dividendTerm, coefficientTerm,
                ScopedTerm.numeral, RawTerm.evaluate_numeral,
                RawTerm.evaluate, betaComponent] using
                (run.finalValue.symm.trans
                  (betaComponent_encoded_vector values
                    (Nat.lt_succ_self counter)).symm))
          let bodyConjunction := Derivation.conjunctionIntroduction baseClause
            (Derivation.conjunctionIntroduction transitionClause outputBeta)
          let witnessBody : ScopedFormula 2 :=
            let dividendVariable := ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)
            let coefficientVariable := ScopedTerm.bvar 1
              (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
            let baseCoreRaw := RawFormula.conj
              (betaValueFormula (RawTerm.bvar 1)
                (RawTerm.bvar 2) RawTerm.zero
                (RawTerm.bvar 0))
              (base.graphFormula.apply (RawTerm.bvar 0)
                parameters.numeralTerms)
            let baseClauseRaw := RawFormula.ex baseCoreRaw
            let transitionCoreRaw := RawFormula.conj
              (betaValueFormula (RawTerm.bvar 3) (RawTerm.bvar 4)
                (RawTerm.bvar 2) (RawTerm.bvar 0))
              (RawFormula.conj
                (betaValueFormula (RawTerm.bvar 3) (RawTerm.bvar 4)
                  (RawTerm.succ (RawTerm.bvar 2)) (RawTerm.bvar 1))
                (step.graphFormula.apply (RawTerm.bvar 1)
                  (RawTermVector.cons (RawTerm.bvar 2)
                    (RawTermVector.cons (RawTerm.bvar 0)
                      parameters.numeralTerms))))
            let transitionClauseRaw := RawFormula.all
              (RawFormula.impl
                (lessThanFormula (RawTerm.bvar 0)
                  (RawTerm.numeral counter))
                (transitionCoreRaw.existsMany 2))
            let outputClauseRaw := betaValueFormula dividendVariable.raw
              coefficientVariable.raw (RawTerm.numeral counter)
              (RawTerm.numeral output)
            { raw := RawFormula.conj baseClauseRaw
                (RawFormula.conj transitionClauseRaw outputClauseRaw)
              isScoped := by
                constructor
                · change baseCoreRaw.WellScoped 3
                  constructor
                  · exact betaValueFormula_wellScoped _ _ _ _
                      (by decide) (by decide) trivial (by decide)
                  · exact base.graphFormula.apply_wellScoped
                      (RawTerm.bvar 0) parameters.numeralTerms
                      (by decide) parameters.numeralTerms_wellScoped
                · constructor
                  · constructor
                    · exact lessThanFormula_wellScoped _ _
                        (by decide) (RawTerm.numeral_wellScoped counter 3)
                    · apply RawFormula.existsMany_wellScoped 2 3
                      constructor
                      · exact betaValueFormula_wellScoped _ _ _ _
                          (by decide) (by decide) (by decide) (by decide)
                      · constructor
                        · exact betaValueFormula_wellScoped _ _ _ _
                            (by decide) (by decide) (by decide) (by decide)
                        · exact step.graphFormula.apply_wellScoped
                            (RawTerm.bvar 1)
                            (RawTermVector.cons (RawTerm.bvar 2)
                              (RawTermVector.cons (RawTerm.bvar 0)
                                parameters.numeralTerms))
                            (by decide)
                            (And.intro (by decide)
                              (And.intro (by decide)
                                parameters.numeralTerms_wellScoped))
                  · exact betaValueFormula_wellScoped _ _ _ _
                      (by decide) (by decide)
                      (RawTerm.numeral_wellScoped counter 2)
                      (RawTerm.numeral_wellScoped output 2) }
          let outerClosing := numeralClosingSubstitution
            (NatVector.cons dividend
              (NatVector.cons coefficient NatVector.nil))
          have baseGraphPreserved :
              (base.graphFormula.apply (RawTerm.bvar 0)
                parameters.numeralTerms).substitute
                  (liftSubstitution outerClosing) =
                base.graphFormula.apply (RawTerm.bvar 0)
                  parameters.numeralTerms := by
            exact ArithmeticGraph.apply_substitute_exact
              base.graphFormula (RawTerm.bvar 0) parameters.numeralTerms
              (liftSubstitution outerClosing) (RawTerm.bvar 0)
              parameters.numeralTerms rfl (fun position => by
                rw [NatVector.numeralTerms_getD]
                exact RawTerm.numeral_substitute _ _)
          have transitionGraphPreserved :
              (step.graphFormula.apply (RawTerm.bvar 1)
                (RawTermVector.cons (RawTerm.bvar 2)
                  (RawTermVector.cons (RawTerm.bvar 0)
                    parameters.numeralTerms))).substitute
                  (liftSubstitution
                    (liftSubstitution (liftSubstitution outerClosing))) =
                step.graphFormula.apply (RawTerm.bvar 1)
                  (RawTermVector.cons (RawTerm.bvar 2)
                    (RawTermVector.cons (RawTerm.bvar 0)
                      parameters.numeralTerms)) := by
            exact ArithmeticGraph.apply_substitute_exact
              step.graphFormula (RawTerm.bvar 1)
              (RawTermVector.cons (RawTerm.bvar 2)
                (RawTermVector.cons (RawTerm.bvar 0)
                  parameters.numeralTerms))
              (liftSubstitution
                (liftSubstitution (liftSubstitution outerClosing)))
              (RawTerm.bvar 1)
              (RawTermVector.cons (RawTerm.bvar 2)
                (RawTermVector.cons (RawTerm.bvar 0)
                  parameters.numeralTerms)) rfl (fun position => by
                cases position with
                | zero => rfl
                | succ position =>
                    cases position with
                    | zero => rfl
                    | succ position =>
                        change (parameters.numeralTerms.getD position).substitute
                            (liftSubstitution
                              (liftSubstitution (liftSubstitution outerClosing))) =
                          parameters.numeralTerms.getD position
                        rw [NatVector.numeralTerms_getD]
                        exact RawTerm.numeral_substitute _ _)
          have closedWitnessBody : Derivation LogicMode.intuitionistic haTheory
              FormulaContext.nil
              (witnessBody.closeWithNumerals
                (NatVector.cons dividend
                  (NatVector.cons coefficient NatVector.nil))) := by
            refine Derivation.castConclusion ?_ bodyConjunction
            apply ScopedFormula.eq_of_raw_eq
            dsimp [witnessBody, transitionBody, transitionCore, baseCore,
              ScopedFormula.closeWithNumerals,
              ScopedFormula.conj, ScopedFormula.impl,
              ScopedFormula.all, ScopedFormula.ex,
              outerClosing, numeralClosingSubstitution,
              scopedBetaValueFormula,
              dividendTerm, coefficientTerm, ScopedTerm.numeral,
              ScopedTerm.zero, ScopedTerm.bvar, ScopedTerm.succ,
              previousVariable3, nextVariable3, indexVariable3,
              betaValueFormula, betaModulusTerm, remainderFormula,
              lessThanFormula, RawTerm.shift, RawTerm.rename,
              liftSubstitution,
              ArithmeticGraph.numeralInstance,
              RawFormula.substitute, RawTerm.substitute,
              RawFormula.existsMany, lessThanNumeralBody,
              scopedLessThanFormula, NatVector.getD]
            rw [baseGraphPreserved, transitionGraphPreserved]
            repeat' rw [RawTerm.numeral_rename]
            repeat' rw [RawTerm.numeral_substitute]
          let witnessed := Derivation.introduceExistsMany witnessBody
            (NatVector.cons dividend
              (NatVector.cons coefficient NatVector.nil)) closedWitnessBody
          let allValues := NatVector.cons output
            (NatVector.cons counter parameters)
          let originalBaseCore := RawFormula.conj
            (betaValueFormula (RawTerm.bvar 1) (RawTerm.bvar 2)
              RawTerm.zero (RawTerm.bvar 0))
            (base.graphFormula.apply (RawTerm.bvar 0)
              (primitiveBaseParameters parameterArity))
          let originalTransitionCore := RawFormula.conj
            (betaValueFormula (RawTerm.bvar 3) (RawTerm.bvar 4)
              (RawTerm.bvar 2) (RawTerm.bvar 0))
            (RawFormula.conj
              (betaValueFormula (RawTerm.bvar 3) (RawTerm.bvar 4)
                (RawTerm.succ (RawTerm.bvar 2)) (RawTerm.bvar 1))
              (step.graphFormula.apply (RawTerm.bvar 1)
                (primitiveStepInputs parameterArity)))
          let originalBody := RawFormula.conj
            (RawFormula.ex originalBaseCore)
            (RawFormula.conj
              (RawFormula.all
                (RawFormula.impl
                  (lessThanFormula (RawTerm.bvar 0) (RawTerm.bvar 4))
                  (originalTransitionCore.existsMany 2)))
              (betaValueFormula (RawTerm.bvar 0) (RawTerm.bvar 1)
                (RawTerm.bvar 3) (RawTerm.bvar 2)))
          have baseApplicationExact :
              (base.graphFormula.apply (RawTerm.bvar 0)
                (primitiveBaseParameters parameterArity)).substitute
                  (numeralClosingSubstitutionAtDepth allValues 3) =
                base.graphFormula.apply (RawTerm.bvar 0)
                  parameters.numeralTerms := by
            apply ArithmeticGraph.apply_substitute_exact_bounded
              base.graphFormula (RawTerm.bvar 0)
              (primitiveBaseParameters parameterArity)
              (numeralClosingSubstitutionAtDepth allValues 3)
              (RawTerm.bvar 0) parameters.numeralTerms
            · exact numeralClosingSubstitutionAtDepth_inside
                allValues 3 0 (by decide)
            · intro position bounded
              change ((RawTermVector.variables 5 parameterArity).getD
                  position).substitute
                    (numeralClosingSubstitutionAtDepth allValues 3) =
                parameters.numeralTerms.getD position
              rw [RawTermVector.variables_getD_inside 5 parameterArity
                  position bounded,
                NatVector.numeralTerms_getD]
              change numeralClosingSubstitutionAtDepth allValues 3
                  (5 + position) = RawTerm.numeral (parameters.getD position)
              rw [show 5 + position = 3 + (2 + position) from
                Nat.add_assoc 3 2 position]
              rw [numeralClosingSubstitutionAtDepth_after]
              exact congrArg RawTerm.numeral
                (NatVector.cons_cons_getD_add_two
                  output counter parameters position)
          have stepApplicationExact :
              (step.graphFormula.apply (RawTerm.bvar 1)
                (primitiveStepInputs parameterArity)).substitute
                  (numeralClosingSubstitutionAtDepth allValues 5) =
                step.graphFormula.apply (RawTerm.bvar 1)
                  (RawTermVector.cons (RawTerm.bvar 2)
                    (RawTermVector.cons (RawTerm.bvar 0)
                      parameters.numeralTerms)) := by
            apply ArithmeticGraph.apply_substitute_exact_bounded
              step.graphFormula (RawTerm.bvar 1)
              (primitiveStepInputs parameterArity)
              (numeralClosingSubstitutionAtDepth allValues 5)
              (RawTerm.bvar 1)
              (RawTermVector.cons (RawTerm.bvar 2)
                (RawTermVector.cons (RawTerm.bvar 0)
                  parameters.numeralTerms))
            · exact numeralClosingSubstitutionAtDepth_inside
                allValues 5 1 (by decide)
            · intro position positionBounded
              cases position with
              | zero =>
                  exact numeralClosingSubstitutionAtDepth_inside
                    allValues 5 2 (by decide)
              | succ position =>
                  cases position with
                  | zero =>
                      exact numeralClosingSubstitutionAtDepth_inside
                        allValues 5 0 (by decide)
                  | succ position =>
                      have bounded : position < parameterArity :=
                        Nat.lt_of_succ_lt_succ
                          (Nat.lt_of_succ_lt_succ positionBounded)
                      change ((RawTermVector.variables 7 parameterArity).getD
                          position).substitute
                            (numeralClosingSubstitutionAtDepth allValues 5) =
                        parameters.numeralTerms.getD position
                      rw [RawTermVector.variables_getD_inside 7 parameterArity
                          position bounded,
                        NatVector.numeralTerms_getD]
                      change numeralClosingSubstitutionAtDepth allValues 5
                          (7 + position) =
                        RawTerm.numeral (parameters.getD position)
                      rw [show 7 + position = 5 + (2 + position) from
                        Nat.add_assoc 5 2 position]
                      rw [numeralClosingSubstitutionAtDepth_after]
                      exact congrArg RawTerm.numeral
                        (NatVector.cons_cons_getD_add_two
                          output counter parameters position)
          have baseApplicationExactExpanded :
              (base.graphFormula.apply (RawTerm.bvar 0)
                (primitiveBaseParameters parameterArity)).substitute
                  (liftSubstitution (liftSubstitution (liftSubstitution
                    (numeralClosingSubstitution allValues)))) =
                base.graphFormula.apply (RawTerm.bvar 0)
                  parameters.numeralTerms :=
            baseApplicationExact
          have stepApplicationExactExpanded :
              (step.graphFormula.apply (RawTerm.bvar 1)
                (primitiveStepInputs parameterArity)).substitute
                  (liftSubstitution (liftSubstitution (liftSubstitution
                    (liftSubstitution (liftSubstitution
                      (numeralClosingSubstitution allValues)))))) =
                step.graphFormula.apply (RawTerm.bvar 1)
                  (RawTermVector.cons (RawTerm.bvar 2)
                    (RawTermVector.cons (RawTerm.bvar 0)
                      parameters.numeralTerms)) :=
            stepApplicationExact
          have witnessBodyExact : witnessBody.raw =
              originalBody.substitute
                (numeralClosingSubstitutionAtDepth allValues 2) := by
            dsimp [witnessBody, originalBody, originalBaseCore,
              originalTransitionCore, allValues,
              numeralClosingSubstitutionAtDepth,
              numeralClosingSubstitution, betaValueFormula,
              betaModulusTerm, remainderFormula, lessThanFormula,
              RawFormula.substitute, RawTerm.substitute,
              RawTerm.shift, RawTerm.rename, liftSubstitution,
              NatVector.getD, RawFormula.existsMany,
              ScopedTerm.bvar]
            rw [baseApplicationExactExpanded, stepApplicationExactExpanded]
            repeat' rw [RawTerm.numeral_rename]
          refine Derivation.castConclusion ?_ witnessed
          apply ScopedFormula.eq_of_raw_eq
          let recursionGraph := primitiveRecursionGraph
            base.graphFormula step.graphFormula
          have blockExact : witnessBody.raw.existsMany 2 =
              recursionGraph.raw.substitute
                (numeralClosingSubstitution allValues) := by
            calc
              witnessBody.raw.existsMany 2 =
                  (originalBody.substitute
                    (numeralClosingSubstitutionAtDepth allValues 2)).existsMany 2 :=
                congrArg (fun formula => formula.existsMany 2)
                  witnessBodyExact
              _ = (originalBody.existsMany 2).substitute
                    (numeralClosingSubstitution allValues) :=
                RawFormula.existsMany_substitute_numeralClosing
                  originalBody allValues 2
              _ = recursionGraph.raw.substitute
                    (numeralClosingSubstitution allValues) := by
                rfl
          have graphClosingExact :
              recursionGraph.raw.substitute
                  (numeralClosingSubstitution allValues) =
                recursionGraph.apply (RawTerm.numeral output)
                  (RawTermVector.cons (RawTerm.numeral counter)
                    parameters.numeralTerms) := by
            unfold ArithmeticGraph.apply
            apply RawFormula.substitute_eq_of_scoped_agreement
              recursionGraph.raw recursionGraph.isScoped
            intro position positionBounded
            cases position with
            | zero => rfl
            | succ position =>
                cases position with
                | zero => rfl
                | succ position =>
                    have positionExact : position + 1 + 1 =
                        Nat.succ (Nat.succ position) := by
                      rw [Nat.add_assoc, Nat.add_zero]
                    rw [positionExact]
                    change RawTerm.numeral
                        (allValues.getD (Nat.succ (Nat.succ position))) =
                      parameters.numeralTerms.getD position
                    rw [NatVector.numeralTerms_getD]
                    rfl
          change witnessBody.raw.existsMany 2 =
            ((PRFunction.primitiveRecursion base step).numeralGraphInstance
              (NatVector.cons counter parameters) output).raw
          rw [blockExact, graphClosingExact]
          rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.internallyNumeralwiseRepresentedPrimitiveRecursion
#print axioms RelationalPerimeter.HeytingArithmetic.PrimitiveRecursionRunCertificate.ofEvaluation
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraph.apply_substitute_exact
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.substitute_eq_of_scoped_agreement
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitute_eq_of_scoped_agreement
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraph.apply_substitute_exact_bounded
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.numeral_rename
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.cons_cons_getD_add_two
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanFormula_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.remainderFormula_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.betaValueFormula_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.betaValueFormula_substitute_exact
#print axioms RelationalPerimeter.HeytingArithmetic.numeralClosingSubstitutionAtDepth_inside
#print axioms RelationalPerimeter.HeytingArithmetic.numeralClosingSubstitutionAtDepth_after
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.existsMany_substitute_numeralClosing
/- AXIOM_AUDIT_END -/
