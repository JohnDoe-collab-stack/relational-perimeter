import RelationalPerimeter.Instances.HeytingArithmetic.ConstructiveBetaEncoding

/-!
# Constructive arithmetic representation of primitive-recursive programs

Every positive `PRFunction` tree is compiled to a formula in the bare
first-order language `{0,S,+,*,=,∧,∨,→,∀,∃}`.  Primitive recursion is encoded
with Goedel beta sequences.  The compiler introduces no semantic predicate and
no new arithmetic function symbol.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Vectors of already compiled graphs -/

/-- A length-indexed vector of arithmetic graph formulas of common arity. -/
inductive ArithmeticGraphVector (inputArity : Nat) : Nat -> Type
  | nil : ArithmeticGraphVector inputArity 0
  | cons {length : Nat} :
      ArithmeticGraph inputArity ->
      ArithmeticGraphVector inputArity length ->
      ArithmeticGraphVector inputArity (Nat.succ length)

/-- A raw formula together with a selected ambient scope. -/
structure ScopedFormula (bound : Nat) where
  raw : RawFormula
  isScoped : raw.WellScoped bound

/-- Constructive truth, used as the neutral conjunction formula. -/
def trueFormula : RawFormula := RawFormula.impl RawFormula.falsum RawFormula.falsum

/-- The truth abbreviation is scoped in every context. -/
theorem trueFormula_wellScoped (bound : Nat) :
    trueFormula.WellScoped bound :=
  And.intro trivial trivial

/-- Reassociate one successor from a vector length to its starting offset. -/
theorem succOffsetTailFits
    {offset tailLength total : Nat}
    (fits : offset + Nat.succ tailLength <= total) :
    Nat.succ offset + tailLength <= total :=
  Eq.mp
    (congrArg (fun value => value <= total)
      ((Nat.succ_add offset tailLength).trans
        (Nat.add_succ offset tailLength).symm).symm)
    fits

/-- The head offset of a nonempty fitted block lies in the ambient scope. -/
theorem fittedOffset_lt_ambient
    {offset tailLength total inputArity : Nat}
    (fits : offset + Nat.succ tailLength <= total) :
    offset < total + Nat.succ inputArity :=
  Nat.lt_trans
    (Nat.lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (Nat.succ_pos tailLength))
      fits)
    (Nat.lt_add_of_pos_right (Nat.succ_pos inputArity))

/-- Original graph inputs fit exactly after the intermediate block. -/
theorem originalInputsFit (total inputArity : Nat) :
    Nat.succ total + inputArity <= total + Nat.succ inputArity := by
  rw [Nat.succ_add, Nat.add_succ]
  exact Nat.le_refl _

/-- A block beginning at zero and using its whole declared length fits. -/
theorem zeroOffsetFits (length : Nat) : 0 + length <= length :=
  Eq.mp
    (congrArg (fun value => value <= length) (Nat.zero_add length).symm)
    (Nat.le_refl length)

/-- Read one original input after a prefixed vector and the graph output. -/
theorem prependEnvironment_originalInput
    {prefixLength inputArity index : Nat}
    (prefixValues : NatVector prefixLength)
    (inputs : NatVector inputArity)
    (output : Nat)
    (bounded : index < inputArity) :
    prependEnvironment prefixValues (graphEnvironment inputs output)
        (Nat.succ prefixLength + index) =
      inputs.get index bounded := by
  have shifted :=
    prependEnvironment_shift prefixValues (graphEnvironment inputs output)
      (Nat.succ index)
  have positionEquality :
      Nat.succ prefixLength + index = prefixLength + Nat.succ index :=
    (Nat.succ_add prefixLength index).trans
      (Nat.add_succ prefixLength index).symm
  have normalized :
      prependEnvironment prefixValues (graphEnvironment inputs output)
          (Nat.succ prefixLength + index) =
        graphEnvironment inputs output (Nat.succ index) :=
    Eq.mp
      (congrArg
        (fun position =>
          prependEnvironment prefixValues (graphEnvironment inputs output)
              position =
            graphEnvironment inputs output (Nat.succ index))
        positionEquality.symm)
      shifted
  exact normalized.trans (NatVector.getD_eq_get inputs bounded)

/-- Two outer witnesses leave primitive-recursion parameters at offset four. -/
theorem prependTwo_graphParameter
    {parameterArity index : Nat}
    (first second counter output : Nat)
    (parameters : NatVector parameterArity)
    (bounded : index < parameterArity) :
    prependEnvironment
        (NatVector.cons first (NatVector.cons second NatVector.nil))
        (graphEnvironment (NatVector.cons counter parameters) output)
        (4 + index) =
      parameters.get index bounded := by
  have readInput :=
    prependEnvironment_originalInput
      (NatVector.cons first (NatVector.cons second NatVector.nil))
      (NatVector.cons counter parameters)
      output
      (Nat.succ_lt_succ bounded)
  have positionEquality :
      4 + index = Nat.succ 2 + Nat.succ index :=
    (Nat.succ_add 3 index).trans
      (Nat.add_succ 3 index).symm
  exact Eq.mp
    (congrArg
      (fun position =>
        prependEnvironment
            (NatVector.cons first (NatVector.cons second NatVector.nil))
            (graphEnvironment (NatVector.cons counter parameters) output)
            position =
          parameters.get index bounded)
      positionEquality.symm)
    readInput

/-- Two local step witnesses and one pushed counter preserve parameter access. -/
theorem prependTwo_pushedParameter
    {index : Nat}
    (previous next counterValue : Nat)
    (topEnvironment : Environment) :
    prependEnvironment
        (NatVector.cons previous (NatVector.cons next NatVector.nil))
        (pushEnvironment topEnvironment counterValue)
        (7 + index) =
      topEnvironment (4 + index) := by
  have shifted :=
    prependEnvironment_shift
      (NatVector.cons previous (NatVector.cons next NatVector.nil))
      (pushEnvironment topEnvironment counterValue)
      (5 + index)
  have positionEquality : 7 + index = 2 + (5 + index) :=
    Nat.add_assoc 2 5 index
  have normalized :
      prependEnvironment
          (NatVector.cons previous (NatVector.cons next NatVector.nil))
          (pushEnvironment topEnvironment counterValue)
          (7 + index) =
        pushEnvironment topEnvironment counterValue (5 + index) :=
    Eq.mp
      (congrArg
        (fun position =>
          prependEnvironment
              (NatVector.cons previous (NatVector.cons next NatVector.nil))
              (pushEnvironment topEnvironment counterValue)
              position =
            pushEnvironment topEnvironment counterValue (5 + index))
        positionEquality.symm)
      shifted
  have successorEquality : 5 + index = Nat.succ (4 + index) :=
    Nat.succ_add 4 index
  exact normalized.trans
    (Eq.mp
      (congrArg
        (fun position =>
          pushEnvironment topEnvironment counterValue position =
            topEnvironment (4 + index))
        successorEquality.symm)
      rfl)

/--
All component graphs applied to consecutive intermediate-output variables.

The complete intermediate vector occupies variables `[0,total)`.  The
original graph environment begins at `total`: its output is variable `total`
and its inputs begin at `total+1`.
-/
def ArithmeticGraphVector.body
    {inputArity length : Nat}
    (graphs : ArithmeticGraphVector inputArity length)
    (offset total : Nat)
    (fits : offset + length <= total) :
    ScopedFormula (total + Nat.succ inputArity) :=
  match graphs with
  | ArithmeticGraphVector.nil =>
      { raw := trueFormula
        isScoped := trueFormula_wellScoped _ }
  | @ArithmeticGraphVector.cons _ tailLength head tail =>
      let originalInputs :=
        RawTermVector.variables (Nat.succ total) inputArity
      let headApplication :=
        head.apply (RawTerm.bvar offset) originalInputs
      let tailBody :=
        tail.body (Nat.succ offset) total (succOffsetTailFits fits)
      { raw := RawFormula.conj headApplication tailBody.raw
        isScoped := And.intro
          (head.apply_wellScoped
            (RawTerm.bvar offset)
            originalInputs
            (fittedOffset_lt_ambient fits)
            (RawTermVector.variables_wellScoped
              (Nat.succ total)
              inputArity
              (total + Nat.succ inputArity)
              (originalInputsFit total inputArity)))
          tailBody.isScoped }

/-! ## Closure of graph formulas under composition -/

/-- Arithmetic graph formula for composition through finitely many outputs. -/
def compositionGraph
    {inputArity outputArity : Nat}
    (outer : ArithmeticGraph outputArity)
    (inner : ArithmeticGraphVector inputArity outputArity) :
    ArithmeticGraph inputArity :=
  let intermediateTerms := RawTermVector.variables 0 outputArity
  let outerApplication :=
    outer.apply (RawTerm.bvar outputArity) intermediateTerms
  let innerBody := inner.body 0 outputArity (zeroOffsetFits outputArity)
  let body := RawFormula.conj outerApplication innerBody.raw
  { raw := body.existsMany outputArity
    isScoped := RawFormula.existsMany_wellScoped
      outputArity
      (Nat.succ inputArity)
      body
      (And.intro
        (outer.apply_wellScoped
          (RawTerm.bvar outputArity)
          intermediateTerms
          (Nat.lt_add_of_pos_right (Nat.succ_pos inputArity))
          (RawTermVector.variables_wellScoped
            0 outputArity
            (outputArity + Nat.succ inputArity)
            (Nat.le_trans
              (zeroOffsetFits outputArity)
              (Nat.le_add_right outputArity (Nat.succ inputArity)))))
        innerBody.isScoped) }

/-! ## Closure of graph formulas under primitive recursion -/

/-- Terms for the parameter block of a primitive-recursion base clause. -/
def primitiveBaseParameters (parameterArity : Nat) :
    RawTermVector parameterArity :=
  RawTermVector.variables 5 parameterArity

/-- Terms for the step inputs `(counter, previous, parameters)`. -/
def primitiveStepInputs (parameterArity : Nat) :
    RawTermVector (Nat.succ (Nat.succ parameterArity)) :=
  RawTermVector.cons (RawTerm.bvar 2)
    (RawTermVector.cons (RawTerm.bvar 0)
      (RawTermVector.variables 7 parameterArity))

/-- Normal form of the scope used by the primitive-recursion base clause. -/
theorem primitiveBaseScope_eq (parameterArity : Nat) :
    Nat.succ (2 + Nat.succ (Nat.succ parameterArity)) =
      5 + parameterArity := by
  induction parameterArity with
  | zero => rfl
  | succ parameterArity inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- Normal form of the scope used by the primitive-recursion transition. -/
theorem primitiveStepScope_eq (parameterArity : Nat) :
    2 + Nat.succ (2 + Nat.succ (Nat.succ parameterArity)) =
      7 + parameterArity := by
  induction parameterArity with
  | zero => rfl
  | succ parameterArity inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- Normal form of the scope used by the outer output clause. -/
theorem primitiveOutputScope_eq (parameterArity : Nat) :
    2 + Nat.succ (Nat.succ parameterArity) =
      4 + parameterArity := by
  induction parameterArity with
  | zero => rfl
  | succ parameterArity inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- A fixed De Bruijn index remains below a scope enlarged on the right. -/
theorem fixedIndex_lt_add
    (index fixed extra : Nat)
    (bounded : index < fixed) :
    index < fixed + extra :=
  Nat.lt_of_lt_of_le bounded (Nat.le_add_right fixed extra)

/--
Arithmetic graph of primitive recursion.

After the two outer witnesses, variables `0,1` are the beta dividend and
coefficient, while the original graph variables begin at `2`.  The transition
clause binds its counter universally and its adjacent sequence values
existentially.
-/
def primitiveRecursionGraph
    {parameterArity : Nat}
    (base : ArithmeticGraph parameterArity)
    (step : ArithmeticGraph (Nat.succ (Nat.succ parameterArity))) :
    ArithmeticGraph (Nat.succ parameterArity) :=
  let baseCore := RawFormula.conj
    (betaValueFormula
      (RawTerm.bvar 1)
      (RawTerm.bvar 2)
      RawTerm.zero
      (RawTerm.bvar 0))
    (base.apply
      (RawTerm.bvar 0)
      (primitiveBaseParameters parameterArity))
  let baseClause := RawFormula.ex baseCore
  let transitionCore := RawFormula.conj
    (betaValueFormula
      (RawTerm.bvar 3)
      (RawTerm.bvar 4)
      (RawTerm.bvar 2)
      (RawTerm.bvar 0))
    (RawFormula.conj
      (betaValueFormula
        (RawTerm.bvar 3)
        (RawTerm.bvar 4)
        (RawTerm.succ (RawTerm.bvar 2))
        (RawTerm.bvar 1))
      (step.apply
        (RawTerm.bvar 1)
        (primitiveStepInputs parameterArity)))
  let transitionClause := RawFormula.all
    (RawFormula.impl
      (lessThanFormula (RawTerm.bvar 0) (RawTerm.bvar 4))
      (transitionCore.existsMany 2))
  let outputClause := betaValueFormula
    (RawTerm.bvar 0)
    (RawTerm.bvar 1)
    (RawTerm.bvar 3)
    (RawTerm.bvar 2)
  let body := RawFormula.conj baseClause
    (RawFormula.conj transitionClause outputClause)
  { raw := body.existsMany 2
    isScoped := by
      apply RawFormula.existsMany_wellScoped
      constructor
      · constructor
        · apply betaValueFormula_wellScoped
          · change 1 < (2 + parameterArity.succ.succ).succ
            rw [primitiveBaseScope_eq]
            exact fixedIndex_lt_add 1 5 parameterArity (by decide)
          · change 2 < (2 + parameterArity.succ.succ).succ
            rw [primitiveBaseScope_eq]
            exact fixedIndex_lt_add 2 5 parameterArity (by decide)
          · trivial
          · change 0 < (2 + parameterArity.succ.succ).succ
            exact Nat.zero_lt_succ _
        · apply base.apply_wellScoped
          · change 0 < (2 + parameterArity.succ.succ).succ
            exact Nat.zero_lt_succ _
          · apply RawTermVector.variables_wellScoped
            rw [primitiveBaseScope_eq]
            exact Nat.le_refl _
      · constructor
        · constructor
          · apply lessThanFormula_wellScoped
            · change 0 < (2 + parameterArity.succ.succ).succ
              exact Nat.zero_lt_succ _
            · change 4 < (2 + parameterArity.succ.succ).succ
              rw [primitiveBaseScope_eq]
              exact fixedIndex_lt_add 4 5 parameterArity (by decide)
          · apply RawFormula.existsMany_wellScoped
            constructor
            · apply betaValueFormula_wellScoped
              · rw [primitiveStepScope_eq]
                exact fixedIndex_lt_add 3 7 parameterArity (by decide)
              · rw [primitiveStepScope_eq]
                exact fixedIndex_lt_add 4 7 parameterArity (by decide)
              · rw [primitiveStepScope_eq]
                exact fixedIndex_lt_add 2 7 parameterArity (by decide)
              · rw [primitiveStepScope_eq]
                exact fixedIndex_lt_add 0 7 parameterArity (by decide)
            · constructor
              · apply betaValueFormula_wellScoped
                · rw [primitiveStepScope_eq]
                  exact fixedIndex_lt_add 3 7 parameterArity (by decide)
                · rw [primitiveStepScope_eq]
                  exact fixedIndex_lt_add 4 7 parameterArity (by decide)
                · rw [primitiveStepScope_eq]
                  exact fixedIndex_lt_add 2 7 parameterArity (by decide)
                · rw [primitiveStepScope_eq]
                  exact fixedIndex_lt_add 1 7 parameterArity (by decide)
              · apply step.apply_wellScoped
                · change 1 < 2 + Nat.succ
                    (2 + Nat.succ (Nat.succ parameterArity))
                  rw [primitiveStepScope_eq]
                  exact fixedIndex_lt_add 1 7 parameterArity (by decide)
                · constructor
                  · change 2 < 2 + Nat.succ
                      (2 + Nat.succ (Nat.succ parameterArity))
                    rw [primitiveStepScope_eq]
                    exact fixedIndex_lt_add 2 7 parameterArity (by decide)
                  · constructor
                    · change 0 < 2 + Nat.succ
                        (2 + Nat.succ (Nat.succ parameterArity))
                      rw [primitiveStepScope_eq]
                      exact fixedIndex_lt_add 0 7 parameterArity (by decide)
                    · apply RawTermVector.variables_wellScoped
                      rw [primitiveStepScope_eq]
                      exact Nat.le_refl _
        · apply betaValueFormula_wellScoped
          · rw [primitiveOutputScope_eq]
            exact fixedIndex_lt_add 0 4 parameterArity (by decide)
          · rw [primitiveOutputScope_eq]
            exact fixedIndex_lt_add 1 4 parameterArity (by decide)
          · rw [primitiveOutputScope_eq]
            exact fixedIndex_lt_add 3 4 parameterArity (by decide)
          · rw [primitiveOutputScope_eq]
            exact fixedIndex_lt_add 2 4 parameterArity (by decide) }

/-! ## Semantic correctness of composition -/

/-- A graph formula represents a positive execution relation exactly. -/
def ArithmeticGraph.Represents
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (program : PRFunction arity) :
    Prop :=
  (inputs : NatVector arity) ->
    (output : Nat) ->
      graph.Holds inputs output ↔
        PRFunction.Evaluates program inputs output

/-- Positive pointwise certificate for a vector of represented programs. -/
inductive ArithmeticGraphVector.Represents
    {inputArity : Nat} :
    {length : Nat} ->
      ArithmeticGraphVector inputArity length ->
      PRFunctionVector inputArity length ->
      Type
  | nil :
      ArithmeticGraphVector.Represents
        ArithmeticGraphVector.nil
        PRFunctionVector.nil
  | cons
      {length : Nat}
      {headGraph : ArithmeticGraph inputArity}
      {tailGraphs : ArithmeticGraphVector inputArity length}
      {headProgram : PRFunction inputArity}
      {tailPrograms : PRFunctionVector inputArity length}
      (headRepresents : headGraph.Represents headProgram)
      (tailRepresents : tailGraphs.Represents tailPrograms) :
      ArithmeticGraphVector.Represents
        (ArithmeticGraphVector.cons headGraph tailGraphs)
        (PRFunctionVector.cons headProgram tailPrograms)

/-- Consecutive variable vectors read consecutive environment entries. -/
theorem RawTermVector.variables_evaluate_get
    (start length : Nat)
    (environment : Environment)
    (index : Nat)
    (bounded : index < length) :
    ((RawTermVector.variables start length).getD index).evaluate environment =
      environment (start + index) := by
  induction length generalizing start index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ length inductionHypothesis =>
      cases index with
      | zero =>
          exact congrArg environment (Nat.add_zero start).symm
      | succ index =>
          change
            ((RawTermVector.variables (Nat.succ start) length).getD index).evaluate
                environment =
              environment (start + Nat.succ index)
          rw [inductionHypothesis
            (start := Nat.succ start)
            (index := index)
            (Nat.lt_of_succ_lt_succ bounded)]
          rw [Nat.succ_add, Nat.add_succ]

/-- Evaluate an applied graph from pointwise values of all supplied terms. -/
theorem ArithmeticGraph.apply_holds_of_values
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
    (graph.apply outputTerm inputTerms).Holds environment ↔
      graph.Holds inputs output := by
  apply Iff.trans (graph.apply_holds outputTerm inputTerms environment)
  apply graph.raw.holds_iff_of_scoped_agreement graph.isScoped
  intro index bounded
  cases index with
  | zero => exact outputValue
  | succ index =>
      have inputBounded : index < arity := Nat.lt_of_succ_lt_succ bounded
      change
        (inputTerms.evaluate environment).getD index = inputs.getD index
      exact Eq.trans
        (RawTermVector.evaluate_getD inputTerms environment index)
        (Eq.trans
          (inputValues index inputBounded)
          (NatVector.getD_eq_get inputs inputBounded).symm)

/--
The conjunction generated for a graph vector represents pointwise vector
execution under any environment satisfying the documented variable layout.
-/
theorem ArithmeticGraphVector.body_holds_iff
    {inputArity length : Nat}
    {graphs : ArithmeticGraphVector inputArity length}
    {programs : PRFunctionVector inputArity length}
    (represents : graphs.Represents programs)
    (offset total : Nat)
    (fits : offset + length <= total)
    (environment : Environment)
    (inputs : NatVector inputArity)
    (outputs : NatVector length)
    (inputValues :
      (index : Nat) ->
        (bounded : index < inputArity) ->
          environment (Nat.succ total + index) =
            inputs.get index bounded)
    (outputValues :
      (index : Nat) ->
        (bounded : index < length) ->
          environment (offset + index) =
            outputs.get index bounded) :
    (graphs.body offset total fits).raw.Holds environment ↔
      PRFunctionVector.Evaluates programs inputs outputs := by
  induction represents generalizing offset with
  | nil =>
      constructor
      · intro _truth
        unfold PRFunctionVector.Evaluates
        exact (NatVector.tabulateD_getD_self outputs).symm
      · intro _evaluation impossible
        exact impossible
  | @cons length headGraph tailGraphs headProgram tailPrograms
      headRepresents tailRepresents inductionHypothesis =>
      change
        ((headGraph.apply
            (RawTerm.bvar offset)
            (RawTermVector.variables
              (Nat.succ total) inputArity)).Holds environment ∧
          (tailGraphs.body
            (Nat.succ offset)
            total
            (succOffsetTailFits fits)).raw.Holds environment) ↔
          PRFunctionVector.Evaluates
            (PRFunctionVector.cons headProgram tailPrograms)
            inputs outputs
      have headFormula :
          (headGraph.apply
            (RawTerm.bvar offset)
            (RawTermVector.variables
              (Nat.succ total) inputArity)).Holds environment ↔
            PRFunction.Evaluates headProgram inputs (outputs.getD 0) := by
        apply Iff.trans
          (headGraph.apply_holds_of_values
            (RawTerm.bvar offset)
            (RawTermVector.variables
              (Nat.succ total) inputArity)
            environment
            inputs
            (outputs.getD 0)
            ((outputValues 0 (Nat.zero_lt_succ length)).trans
              (NatVector.getD_eq_get outputs
                (Nat.zero_lt_succ length)).symm)
            (fun index bounded =>
              (RawTermVector.variables_evaluate_get
                (Nat.succ total)
                inputArity
                environment
                index
                bounded).trans
                (inputValues index bounded)))
        exact headRepresents inputs (outputs.getD 0)
      have tailFormula :
          (tailGraphs.body
            (Nat.succ offset)
            total
            (succOffsetTailFits fits)).raw.Holds environment ↔
            PRFunctionVector.Evaluates
              tailPrograms inputs outputs.tailD := by
        exact inductionHypothesis
          (offset := Nat.succ offset)
          (fits := succOffsetTailFits fits)
          (outputs := outputs.tailD)
          (fun index bounded => by
            have mapped :=
              outputValues
                (Nat.succ index)
                (Nat.succ_lt_succ bounded)
            rw [Nat.succ_add]
            exact mapped.trans
              (NatVector.tailD_get outputs bounded).symm)
      constructor
      · intro conjunction
        unfold PRFunctionVector.Evaluates
        exact (NatVector.rebuildD outputs).symm.trans
          ((congrArg
            (fun headValue => NatVector.cons headValue outputs.tailD)
            (headFormula.mp conjunction.1)).trans
            (congrArg
              (fun tailValues =>
                NatVector.cons
                  (PRFunction.runCore headProgram inputs) tailValues)
              (tailFormula.mp conjunction.2)))
      · intro evaluation
        have headEvaluation :
            PRFunction.Evaluates headProgram inputs (outputs.getD 0) := by
          unfold PRFunction.Evaluates
          exact congrArg (fun values => values.getD 0) evaluation
        have tailEvaluation :
            PRFunctionVector.Evaluates
              tailPrograms inputs outputs.tailD := by
          unfold PRFunctionVector.Evaluates
          exact (congrArg (fun values => values.tailD) evaluation).trans
            (NatVector.tailD_cons
              (PRFunction.runCore headProgram inputs)
              (PRFunctionVector.runCore tailPrograms inputs))
        exact And.intro
          (headFormula.mpr headEvaluation)
          (tailFormula.mpr tailEvaluation)

/-- The arithmetic graph constructor for composition is semantically exact. -/
theorem compositionGraph_represents
    {inputArity outputArity : Nat}
    {outerProgram : PRFunction outputArity}
    {innerPrograms : PRFunctionVector inputArity outputArity}
    (outerGraph : ArithmeticGraph outputArity)
    (innerGraphs : ArithmeticGraphVector inputArity outputArity)
    (outerRepresents : outerGraph.Represents outerProgram)
    (innerRepresents : innerGraphs.Represents innerPrograms) :
    (compositionGraph outerGraph innerGraphs).Represents
      (PRFunction.composition outerProgram innerPrograms) := by
  intro inputs output
  change
    ((RawFormula.conj
      (outerGraph.apply
        (RawTerm.bvar outputArity)
        (RawTermVector.variables 0 outputArity))
      (innerGraphs.body
        0 outputArity (zeroOffsetFits outputArity)).raw).existsMany
          outputArity).Holds (graphEnvironment inputs output) ↔ _
  constructor
  · intro blockHolds
    have witness :=
      RawFormula.existsManyForward
        outputArity _ _ blockHolds
    cases witness with
    | intro intermediate bodyHolds =>
        have outerFormula :
            (outerGraph.apply
              (RawTerm.bvar outputArity)
              (RawTermVector.variables 0 outputArity)).Holds
                (prependEnvironment intermediate
                  (graphEnvironment inputs output)) ↔
              PRFunction.Evaluates
                outerProgram intermediate output := by
          apply Iff.trans
            (outerGraph.apply_holds_of_values
              (RawTerm.bvar outputArity)
              (RawTermVector.variables 0 outputArity)
              (prependEnvironment intermediate
                (graphEnvironment inputs output))
              intermediate
              output
              (prependEnvironment_shift
                intermediate
                (graphEnvironment inputs output)
                0)
              (fun index bounded =>
                (RawTermVector.variables_evaluate_get
                  0 outputArity
                  (prependEnvironment intermediate
                    (graphEnvironment inputs output))
                  index bounded).trans (by
                    rw [Nat.zero_add]
                    exact prependEnvironment_get
                      intermediate
                      (graphEnvironment inputs output)
                      bounded)))
          exact outerRepresents intermediate output
        have innerFormula :
            (innerGraphs.body
              0 outputArity (zeroOffsetFits outputArity)).raw.Holds
                (prependEnvironment intermediate
                  (graphEnvironment inputs output)) ↔
              PRFunctionVector.Evaluates
                innerPrograms inputs intermediate := by
          apply innerGraphs.body_holds_iff
            innerRepresents
            0
            outputArity
            (zeroOffsetFits outputArity)
          · intro index bounded
            exact prependEnvironment_originalInput
              intermediate inputs output bounded
          · intro index bounded
            rw [Nat.zero_add]
            exact prependEnvironment_get
              intermediate
              (graphEnvironment inputs output)
              bounded
        exact PRFunction.Evaluates.composition
          (innerFormula.mp bodyHolds.2)
          (outerFormula.mp bodyHolds.1)
  · intro evaluation
    apply RawFormula.existsManyBackward outputArity _ _
    let intermediate := PRFunctionVector.runCore innerPrograms inputs
    refine Exists.intro intermediate ?_
    constructor
    · exact ((outerGraph.apply_holds_of_values
        (RawTerm.bvar outputArity)
        (RawTermVector.variables 0 outputArity)
        (prependEnvironment intermediate
          (graphEnvironment inputs output))
        intermediate
        output
        (prependEnvironment_shift
          intermediate
          (graphEnvironment inputs output)
          0)
        (fun index bounded =>
          (RawTermVector.variables_evaluate_get
            0 outputArity
            (prependEnvironment intermediate
              (graphEnvironment inputs output))
            index bounded).trans (by
              rw [Nat.zero_add]
              exact prependEnvironment_get
                intermediate
                (graphEnvironment inputs output)
                bounded))).mpr
      ((outerRepresents intermediate output).mpr evaluation))
    · exact ((innerGraphs.body_holds_iff
        innerRepresents
        0
        outputArity
        (zeroOffsetFits outputArity)
        (prependEnvironment intermediate
          (graphEnvironment inputs output))
        inputs
        intermediate
        (fun index bounded =>
          prependEnvironment_originalInput
            intermediate inputs output bounded)
        (fun index bounded => by
          rw [Nat.zero_add]
          exact prependEnvironment_get
            intermediate
            (graphEnvironment inputs output)
            bounded)).mpr
      rfl)

/-! ## Finite execution runs for primitive recursion -/

/-- Append one value at the end of a length-indexed vector. -/
def NatVector.snoc {length : Nat} :
    NatVector length -> Nat -> NatVector (Nat.succ length)
  | NatVector.nil, value => NatVector.cons value NatVector.nil
  | NatVector.cons head tail, value =>
      NatVector.cons head (tail.snoc value)

/-- Appending preserves every prior vector entry. -/
theorem NatVector.get_snoc_of_lt
    {length index : Nat}
    (values : NatVector length)
    (value : Nat)
    (bounded : index < length) :
    (values.snoc value).get index (Nat.lt_trans bounded (Nat.lt_succ_self length)) =
      values.get index bounded := by
  induction values generalizing index with
  | nil => exact (Nat.not_lt_zero index bounded).elim
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis
            (index := index)
            (Nat.lt_of_succ_lt_succ bounded)

/-- The new final vector entry is the appended value. -/
theorem NatVector.get_snoc_last
    {length : Nat}
    (values : NatVector length)
    (value : Nat) :
    (values.snoc value).get length (Nat.lt_succ_self length) = value := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis => exact inductionHypothesis

/-- Numeric beta component with its two sequence parameters kept separate. -/
def betaComponent (dividend coefficient index : Nat) : Nat :=
  constructiveRemainder
    dividend
    ((index + 1) * coefficient + 1)

/-- The internal beta witness supplies every entry of a finite vector. -/
theorem betaComponent_encoded_vector
    {length index : Nat}
    (values : NatVector length)
    (bounded : index < length) :
    betaComponent
        values.betaDividend
        values.betaCoefficient
        index =
      values.get index bounded := by
  change
    constructiveRemainder values.betaDividend (values.betaModulus index) =
      values.get index bounded
  exact constructiveRemainder_betaDividend values bounded

/-- Positive run predicate for one explicitly supplied finite value vector. -/
structure PrimitiveRecursionRun
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (parameters : NatVector parameterArity)
    (counter output : Nat)
    (values : NatVector (Nat.succ counter)) : Prop where
  baseEvaluation :
    PRFunction.Evaluates base parameters
      (values.get 0 (Nat.zero_lt_succ counter))
  stepEvaluation :
    (index : Nat) ->
      (bounded : index < counter) ->
        PRFunction.Evaluates step
          (NatVector.cons index
            (NatVector.cons
              (values.get index
                (Nat.lt_trans bounded (Nat.lt_succ_self counter)))
              parameters))
          (values.get (Nat.succ index) (Nat.succ_lt_succ bounded))
  finalValue :
    values.get counter (Nat.lt_succ_self counter) = output

/-- Every primitive-recursion execution has a positive finite run witness. -/
theorem PrimitiveRecursionRun.exists_of_evaluation
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    {parameters : NatVector parameterArity}
    {counter output : Nat}
    (evaluation :
      PRFunction.Evaluates
        (PRFunction.primitiveRecursion base step)
        (NatVector.cons counter parameters)
        output) :
    Exists fun values : NatVector (Nat.succ counter) =>
      PrimitiveRecursionRun base step parameters counter output values :=
  Nat.rec
    (motive := fun counter =>
      (output : Nat) ->
      PRFunction.Evaluates
        (PRFunction.primitiveRecursion base step)
        (NatVector.cons counter parameters) output ->
      Exists fun values : NatVector (Nat.succ counter) =>
        PrimitiveRecursionRun base step parameters counter output values)
    (fun output zeroEvaluation =>
      Exists.intro
        (NatVector.cons output NatVector.nil)
        { baseEvaluation :=
            zeroEvaluation.trans
              (PRFunction.Evaluates.runCore_primitive_zero
                base step parameters)
          stepEvaluation := by
            intro index impossible
            exact (Nat.not_lt_zero index impossible).elim
          finalValue := rfl })
    (fun counter inductionHypothesis output successorEvaluation =>
      let previous :=
        PRFunction.runCore (PRFunction.primitiveRecursion base step)
          (NatVector.cons counter parameters)
      match inductionHypothesis previous rfl with
      | Exists.intro previousValues previousRun =>
          Exists.intro (previousValues.snoc output)
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
              finalValue := NatVector.get_snoc_last previousValues output })
    counter output evaluation

/-! ## Semantic correctness of primitive recursion -/

/-- Values of the parameter variables in the primitive-recursion base body. -/
theorem primitiveBaseParameters_evaluate
    {parameterArity : Nat}
    (topEnvironment : Environment)
    (parameters : NatVector parameterArity)
    (baseValue : Nat)
    (parameterValues :
      (index : Nat) ->
        (bounded : index < parameterArity) ->
          topEnvironment (4 + index) = parameters.get index bounded)
    (index : Nat)
    (bounded : index < parameterArity) :
    ((primitiveBaseParameters parameterArity).getD index).evaluate
        (pushEnvironment topEnvironment baseValue) =
      parameters.get index bounded := by
  unfold primitiveBaseParameters
  rw [RawTermVector.variables_evaluate_get
    5 parameterArity _ index bounded]
  have positionEquality : 5 + index = Nat.succ (4 + index) :=
    Nat.succ_add 4 index
  exact Eq.trans
    (Eq.mp
      (congrArg
        (fun position =>
          pushEnvironment topEnvironment baseValue position =
            topEnvironment (4 + index))
        positionEquality.symm)
      rfl)
    (parameterValues index bounded)

/-- Values of the parameter variables in a primitive-recursion step body. -/
theorem primitiveStepParameters_evaluate
    {parameterArity : Nat}
    (topEnvironment : Environment)
    (parameters : NatVector parameterArity)
    (counterValue previous next : Nat)
    (parameterValues :
      (index : Nat) ->
        (bounded : index < parameterArity) ->
          topEnvironment (4 + index) = parameters.get index bounded)
    (index : Nat)
    (bounded : index < parameterArity) :
    ((RawTermVector.variables 7 parameterArity).getD index).evaluate
        (prependEnvironment
          (NatVector.cons previous
            (NatVector.cons next NatVector.nil))
          (pushEnvironment topEnvironment counterValue)) =
      parameters.get index bounded := by
  rw [RawTermVector.variables_evaluate_get
    7 parameterArity _ index bounded]
  exact (prependTwo_pushedParameter
    (index := index)
    previous next counterValue topEnvironment).trans
      (parameterValues index bounded)

/-- The arithmetic beta construction makes primitive recursion representable. -/
theorem primitiveRecursionGraph_represents
    {parameterArity : Nat}
    {baseProgram : PRFunction parameterArity}
    {stepProgram : PRFunction (Nat.succ (Nat.succ parameterArity))}
    (baseGraph : ArithmeticGraph parameterArity)
    (stepGraph : ArithmeticGraph (Nat.succ (Nat.succ parameterArity)))
    (baseRepresents : baseGraph.Represents baseProgram)
    (stepRepresents : stepGraph.Represents stepProgram) :
    (primitiveRecursionGraph baseGraph stepGraph).Represents
      (PRFunction.primitiveRecursion baseProgram stepProgram) := by
  intro inputs output
  let counter := inputs.getD 0
  let parameters := inputs.tailD
  have inputsEquality :
      NatVector.cons counter parameters = inputs :=
    NatVector.rebuildD inputs
  rw [← inputsEquality]
  focus
      let baseCore := RawFormula.conj
        (betaValueFormula
          (RawTerm.bvar 1)
          (RawTerm.bvar 2)
          RawTerm.zero
          (RawTerm.bvar 0))
        (baseGraph.apply
          (RawTerm.bvar 0)
          (primitiveBaseParameters parameterArity))
      let baseClause := RawFormula.ex baseCore
      let transitionCore := RawFormula.conj
        (betaValueFormula
          (RawTerm.bvar 3)
          (RawTerm.bvar 4)
          (RawTerm.bvar 2)
          (RawTerm.bvar 0))
        (RawFormula.conj
          (betaValueFormula
            (RawTerm.bvar 3)
            (RawTerm.bvar 4)
            (RawTerm.succ (RawTerm.bvar 2))
            (RawTerm.bvar 1))
          (stepGraph.apply
            (RawTerm.bvar 1)
            (primitiveStepInputs parameterArity)))
      let transitionClause := RawFormula.all
        (RawFormula.impl
          (lessThanFormula (RawTerm.bvar 0) (RawTerm.bvar 4))
          (transitionCore.existsMany 2))
      let outputClause := betaValueFormula
        (RawTerm.bvar 0)
        (RawTerm.bvar 1)
        (RawTerm.bvar 3)
        (RawTerm.bvar 2)
      let body := RawFormula.conj baseClause
        (RawFormula.conj transitionClause outputClause)
      change
        (body.existsMany 2).Holds
            (graphEnvironment
              (NatVector.cons counter parameters)
              output) ↔
          PRFunction.Evaluates
            (PRFunction.primitiveRecursion baseProgram stepProgram)
            (NatVector.cons counter parameters)
            output
      constructor
      · intro blockHolds
        have witness :=
          RawFormula.existsManyForward 2 body _ blockHolds
        cases witness with
        | intro sequenceParameters bodyHolds =>
            let dividend := sequenceParameters.getD 0
            let coefficient := sequenceParameters.getD 1
            have sequenceParametersEquality :
                NatVector.cons dividend
                    (NatVector.cons coefficient NatVector.nil) =
                  sequenceParameters :=
              NatVector.tabulateD_getD_self sequenceParameters
            rw [← sequenceParametersEquality] at bodyHolds
            focus
                    let originalEnvironment :=
                      graphEnvironment
                        (NatVector.cons counter parameters)
                        output
                    let topEnvironment :=
                      prependEnvironment
                        (NatVector.cons dividend
                          (NatVector.cons coefficient NatVector.nil))
                        originalEnvironment
                    have topParameterValues :
                        (index : Nat) ->
                          (bounded : index < parameterArity) ->
                            topEnvironment (4 + index) =
                              parameters.get index bounded := by
                      intro index bounded
                      exact prependTwo_graphParameter
                        dividend coefficient counter output parameters bounded
                    have baseHolds : baseClause.Holds topEnvironment :=
                      bodyHolds.1
                    cases baseHolds with
                    | intro baseValue baseCoreHolds =>
                        let baseEnvironment :=
                          pushEnvironment topEnvironment baseValue
                        have baseBeta :
                            baseValue =
                              betaComponent dividend coefficient 0 := by
                          apply (betaValueFormula_holds
                            (RawTerm.bvar 1)
                            (RawTerm.bvar 2)
                            RawTerm.zero
                            (RawTerm.bvar 0)
                            baseEnvironment).mp
                          exact baseCoreHolds.1
                        have baseExecutionAtWitness :
                            PRFunction.Evaluates
                              baseProgram parameters baseValue := by
                          apply (baseRepresents parameters baseValue).mp
                          apply (baseGraph.apply_holds_of_values
                            (RawTerm.bvar 0)
                            (primitiveBaseParameters parameterArity)
                            baseEnvironment
                            parameters
                            baseValue
                            rfl
                            (primitiveBaseParameters_evaluate
                              topEnvironment
                              parameters
                              baseValue
                              topParameterValues)).mp
                          exact baseCoreHolds.2
                        have baseExecution :
                            PRFunction.Evaluates
                              baseProgram parameters
                                (betaComponent dividend coefficient 0) := by
                          rw [← baseBeta]
                          exact baseExecutionAtWitness
                        have transitionHolds :
                            transitionClause.Holds topEnvironment :=
                          bodyHolds.2.1
                        have stepExecution :
                            (index : Nat) ->
                              index < counter ->
                                PRFunction.Evaluates stepProgram
                                  (NatVector.cons index
                                    (NatVector.cons
                                      (betaComponent
                                        dividend coefficient index)
                                      parameters))
                                  (betaComponent
                                    dividend coefficient (Nat.succ index)) := by
                          intro index bounded
                          let indexEnvironment :=
                            pushEnvironment topEnvironment index
                          have conditionHolds :
                              (lessThanFormula
                                (RawTerm.bvar 0)
                                (RawTerm.bvar 4)).Holds indexEnvironment := by
                            apply (lessThanFormula_holds
                              (RawTerm.bvar 0)
                              (RawTerm.bvar 4)
                              indexEnvironment).mpr
                            exact bounded
                          have transitionBlock :=
                            transitionHolds index conditionHolds
                          have transitionExists :=
                            RawFormula.existsManyForward
                              2 transitionCore indexEnvironment
                              transitionBlock
                          cases transitionExists with
                          | intro adjacent transitionCoreHolds =>
                              let previous := adjacent.getD 0
                              let next := adjacent.getD 1
                              have adjacentEquality :
                                  NatVector.cons previous
                                      (NatVector.cons next NatVector.nil) =
                                    adjacent :=
                                NatVector.tabulateD_getD_self adjacent
                              rw [← adjacentEquality] at transitionCoreHolds
                              focus
                                      let stepEnvironment :=
                                        prependEnvironment
                                          (NatVector.cons previous
                                            (NatVector.cons next NatVector.nil))
                                          indexEnvironment
                                      have previousBeta :
                                          previous =
                                            betaComponent
                                              dividend coefficient index := by
                                        apply (betaValueFormula_holds
                                          (RawTerm.bvar 3)
                                          (RawTerm.bvar 4)
                                          (RawTerm.bvar 2)
                                          (RawTerm.bvar 0)
                                          stepEnvironment).mp
                                        exact transitionCoreHolds.1
                                      have nextBeta :
                                          next =
                                            betaComponent
                                              dividend coefficient
                                              (Nat.succ index) := by
                                        have betaSemantics :=
                                          (betaValueFormula_holds
                                            (RawTerm.bvar 3)
                                            (RawTerm.bvar 4)
                                            (RawTerm.succ (RawTerm.bvar 2))
                                            (RawTerm.bvar 1)
                                            stepEnvironment).mp
                                            transitionCoreHolds.2.1
                                        exact betaSemantics
                                      have stepAtWitness :
                                          PRFunction.Evaluates stepProgram
                                            (NatVector.cons index
                                              (NatVector.cons previous parameters))
                                            next := by
                                        apply (stepRepresents
                                          (NatVector.cons index
                                            (NatVector.cons previous parameters))
                                          next).mp
                                        apply (stepGraph.apply_holds_of_values
                                          (RawTerm.bvar 1)
                                          (primitiveStepInputs parameterArity)
                                          stepEnvironment
                                          (NatVector.cons index
                                            (NatVector.cons previous parameters))
                                          next
                                          rfl
                                          ?_).mp
                                        · exact transitionCoreHolds.2.2
                                        · intro inputIndex inputBounded
                                          cases inputIndex with
                                          | zero => rfl
                                          | succ inputIndex =>
                                              cases inputIndex with
                                              | zero => rfl
                                              | succ parameterIndex =>
                                                  exact
                                                    primitiveStepParameters_evaluate
                                                      topEnvironment
                                                      parameters
                                                      index
                                                      previous
                                                      next
                                                      topParameterValues
                                                      parameterIndex
                                                      (Nat.lt_of_succ_lt_succ
                                                        (Nat.lt_of_succ_lt_succ
                                                          inputBounded))
                                      rw [← previousBeta, ← nextBeta]
                                      exact stepAtWitness
                        have buildExecution :
                            (index : Nat) ->
                              index <= counter ->
                                PRFunction.Evaluates
                                  (PRFunction.primitiveRecursion
                                    baseProgram stepProgram)
                                  (NatVector.cons index parameters)
                                  (betaComponent
                                    dividend coefficient index) := by
                          intro index within
                          induction index with
                          | zero =>
                              exact PRFunction.Evaluates.primitiveZero
                                baseExecution
                          | succ index inductionHypothesis =>
                              exact PRFunction.Evaluates.primitiveSucc
                                (inductionHypothesis
                                  (Nat.le_trans
                                    (Nat.le_succ index)
                                    within))
                                (stepExecution index
                                  (Nat.lt_of_succ_le within))
                        have outputBeta :
                            output =
                              betaComponent
                                dividend coefficient counter := by
                          apply (betaValueFormula_holds
                            (RawTerm.bvar 0)
                            (RawTerm.bvar 1)
                            (RawTerm.bvar 3)
                            (RawTerm.bvar 2)
                            topEnvironment).mp
                          exact bodyHolds.2.2
                        rw [outputBeta]
                        exact buildExecution counter (Nat.le_refl counter)
      · intro evaluation
        apply RawFormula.existsManyBackward 2 body _
        obtain ⟨runValues, run⟩ :=
          PrimitiveRecursionRun.exists_of_evaluation evaluation
        let dividend := runValues.betaDividend
        let coefficient := runValues.betaCoefficient
        refine Exists.intro
          (NatVector.cons dividend
            (NatVector.cons coefficient NatVector.nil)) ?_
        let originalEnvironment :=
          graphEnvironment
            (NatVector.cons counter parameters)
            output
        let topEnvironment :=
          prependEnvironment
            (NatVector.cons dividend
              (NatVector.cons coefficient NatVector.nil))
            originalEnvironment
        have topParameterValues :
            (index : Nat) ->
              (bounded : index < parameterArity) ->
                topEnvironment (4 + index) =
                  parameters.get index bounded := by
          intro index bounded
          exact prependTwo_graphParameter
            dividend coefficient counter output parameters bounded
        constructor
        · let baseValue :=
            runValues.get 0 (Nat.zero_lt_succ counter)
          refine Exists.intro baseValue ?_
          let baseEnvironment := pushEnvironment topEnvironment baseValue
          constructor
          · apply (betaValueFormula_holds
              (RawTerm.bvar 1)
              (RawTerm.bvar 2)
              RawTerm.zero
              (RawTerm.bvar 0)
              baseEnvironment).mpr
            exact (betaComponent_encoded_vector
              runValues
              (Nat.zero_lt_succ counter)).symm
          · apply (baseGraph.apply_holds_of_values
              (RawTerm.bvar 0)
              (primitiveBaseParameters parameterArity)
              baseEnvironment
              parameters
              baseValue
              rfl
              (primitiveBaseParameters_evaluate
                topEnvironment
                parameters
                baseValue
                topParameterValues)).mpr
            exact (baseRepresents parameters baseValue).mpr
              run.baseEvaluation
        · constructor
          · intro index
            let indexEnvironment := pushEnvironment topEnvironment index
            intro conditionHolds
            have bounded : index < counter :=
              (lessThanFormula_holds
                (RawTerm.bvar 0)
                (RawTerm.bvar 4)
                indexEnvironment).mp conditionHolds
            let previous :=
              runValues.get index
                (Nat.lt_trans bounded (Nat.lt_succ_self counter))
            let next :=
              runValues.get (Nat.succ index)
                (Nat.succ_lt_succ bounded)
            apply RawFormula.existsManyBackward 2 transitionCore _
            refine Exists.intro
              (NatVector.cons previous
                (NatVector.cons next NatVector.nil)) ?_
            let stepEnvironment :=
              prependEnvironment
                (NatVector.cons previous
                  (NatVector.cons next NatVector.nil))
                indexEnvironment
            constructor
            · apply (betaValueFormula_holds
                (RawTerm.bvar 3)
                (RawTerm.bvar 4)
                (RawTerm.bvar 2)
                (RawTerm.bvar 0)
                stepEnvironment).mpr
              exact (betaComponent_encoded_vector
                runValues
                (Nat.lt_trans bounded
                  (Nat.lt_succ_self counter))).symm
            · constructor
              · apply (betaValueFormula_holds
                  (RawTerm.bvar 3)
                  (RawTerm.bvar 4)
                  (RawTerm.succ (RawTerm.bvar 2))
                  (RawTerm.bvar 1)
                  stepEnvironment).mpr
                exact (betaComponent_encoded_vector
                  runValues
                  (Nat.succ_lt_succ bounded)).symm
              · apply (stepGraph.apply_holds_of_values
                  (RawTerm.bvar 1)
                  (primitiveStepInputs parameterArity)
                  stepEnvironment
                  (NatVector.cons index
                    (NatVector.cons previous parameters))
                  next
                  rfl
                  ?_).mpr
                · exact (stepRepresents
                    (NatVector.cons index
                      (NatVector.cons previous parameters))
                    next).mpr
                    (run.stepEvaluation index bounded)
                · intro inputIndex inputBounded
                  cases inputIndex with
                  | zero => rfl
                  | succ inputIndex =>
                      cases inputIndex with
                      | zero => rfl
                      | succ parameterIndex =>
                          exact primitiveStepParameters_evaluate
                            topEnvironment
                            parameters
                            index
                            previous
                            next
                            topParameterValues
                            parameterIndex
                            (Nat.lt_of_succ_lt_succ
                              (Nat.lt_of_succ_lt_succ inputBounded))
          · apply (betaValueFormula_holds
              (RawTerm.bvar 0)
              (RawTerm.bvar 1)
              (RawTerm.bvar 3)
              (RawTerm.bvar 2)
              topEnvironment).mpr
            change output = betaComponent dividend coefficient counter
            rw [← run.finalValue]
            exact (betaComponent_encoded_vector
              runValues
              (Nat.lt_succ_self counter)).symm

/-! ## Correctness of the complete compiler -/

/-- A compiled graph kept together with its constructive correctness proof. -/
structure CertifiedArithmeticGraph
    {arity : Nat}
    (program : PRFunction arity) where
  graph : ArithmeticGraph arity
  represents : graph.Represents program

/-- A compiled vector kept together with its pointwise correctness proof. -/
structure CertifiedArithmeticGraphVector
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity) where
  graphs : ArithmeticGraphVector inputArity outputArity
  represents : graphs.Represents programs

/-- Certified graph of the constant-zero program. -/
def certifiedZeroGraph {arity : Nat} :
    CertifiedArithmeticGraph (PRFunction.zero : PRFunction arity) where
  graph :=
    { raw := RawFormula.equal (RawTerm.bvar 0) RawTerm.zero
      isScoped := And.intro (Nat.zero_lt_succ _) trivial }
  represents := by
    intro inputs output
    change (output = 0) ↔ PRFunction.Evaluates PRFunction.zero inputs output
    constructor
    · intro equality
      cases equality
      exact PRFunction.Evaluates.zero inputs
    · intro evaluation
      cases evaluation
      rfl

/-- Certified graph of successor. -/
def certifiedSuccessorGraph :
    CertifiedArithmeticGraph PRFunction.successor where
  graph :=
    { raw := RawFormula.equal
        (RawTerm.bvar 0)
        (RawTerm.succ (RawTerm.bvar 1))
      isScoped := And.intro
        (Nat.zero_lt_succ 1)
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)) }
  represents := by
    intro inputs output
    change
      (output = Nat.succ (inputs.getD 0)) ↔
        PRFunction.Evaluates PRFunction.successor inputs output
    constructor
    · intro equality
      cases equality
      exact PRFunction.Evaluates.successor inputs
    · intro evaluation
      exact evaluation

/-- Certified graph of one projection. -/
def certifiedProjectionGraph
    (arity index : Nat)
    (bounded : index < arity) :
    CertifiedArithmeticGraph (PRFunction.projection arity index bounded) where
  graph :=
    { raw := RawFormula.equal
        (RawTerm.bvar 0)
        (RawTerm.bvar (Nat.succ index))
      isScoped := And.intro
        (Nat.zero_lt_succ arity)
        (Nat.succ_lt_succ bounded) }
  represents := by
    intro inputs output
    change
      (output = inputs.getD index) ↔
        PRFunction.Evaluates
          (PRFunction.projection arity index bounded)
          inputs
          output
    constructor
    · intro equality
      have exactEquality : output = inputs.get index bounded :=
        equality.trans (NatVector.getD_eq_get inputs bounded)
      cases exactEquality
      exact PRFunction.Evaluates.projection index bounded inputs
    · intro evaluation
      cases evaluation
      exact (NatVector.getD_eq_get inputs bounded).symm

/-- Composition preserves certified arithmetic representability. -/
def certifiedCompositionGraph
    {inputArity outputArity : Nat}
    {outer : PRFunction outputArity}
    {inner : PRFunctionVector inputArity outputArity}
    (outerCompiler : CertifiedArithmeticGraph outer)
    (innerCompiler : CertifiedArithmeticGraphVector inner) :
    CertifiedArithmeticGraph (PRFunction.composition outer inner) where
  graph := compositionGraph outerCompiler.graph innerCompiler.graphs
  represents := compositionGraph_represents
    outerCompiler.graph innerCompiler.graphs
    outerCompiler.represents innerCompiler.represents

/-- Primitive recursion preserves certified arithmetic representability. -/
def certifiedPrimitiveRecursionGraph
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    (baseCompiler : CertifiedArithmeticGraph base)
    (stepCompiler : CertifiedArithmeticGraph step) :
    CertifiedArithmeticGraph (PRFunction.primitiveRecursion base step) where
  graph := primitiveRecursionGraph baseCompiler.graph stepCompiler.graph
  represents := primitiveRecursionGraph_represents
    baseCompiler.graph stepCompiler.graph
    baseCompiler.represents stepCompiler.represents

/-- Empty certified graph vector. -/
def certifiedNilGraphVector {inputArity : Nat} :
    CertifiedArithmeticGraphVector
      (PRFunctionVector.nil : PRFunctionVector inputArity 0) where
  graphs := ArithmeticGraphVector.nil
  represents := ArithmeticGraphVector.Represents.nil

/-- Pointwise extension of a certified graph vector. -/
def certifiedConsGraphVector
    {inputArity length : Nat}
    {head : PRFunction inputArity}
    {tail : PRFunctionVector inputArity length}
    (headCompiler : CertifiedArithmeticGraph head)
    (tailCompiler : CertifiedArithmeticGraphVector tail) :
    CertifiedArithmeticGraphVector (PRFunctionVector.cons head tail) where
  graphs := ArithmeticGraphVector.cons
    headCompiler.graph tailCompiler.graphs
  represents := ArithmeticGraphVector.Represents.cons
    headCompiler.represents tailCompiler.represents

mutual
  /-- Structural certified compiler for a positive program tree. -/
  def PRFunction.certifiedGraphCompiler :
      {arity : Nat} ->
      (program : PRFunction arity) ->
      CertifiedArithmeticGraph program
    | _, PRFunction.zero => certifiedZeroGraph
    | _, PRFunction.successor => certifiedSuccessorGraph
    | _, PRFunction.projection arity index bounded =>
        certifiedProjectionGraph arity index bounded
    | _, PRFunction.composition outer inner =>
        certifiedCompositionGraph
          (PRFunction.certifiedGraphCompiler outer)
          (PRFunctionVector.certifiedGraphCompiler inner)
    | _, PRFunction.primitiveRecursion base step =>
        certifiedPrimitiveRecursionGraph
          (PRFunction.certifiedGraphCompiler base)
          (PRFunction.certifiedGraphCompiler step)

  /-- Structural certified compiler for a vector of program trees. -/
  def PRFunctionVector.certifiedGraphCompiler :
      {inputArity outputArity : Nat} ->
      (programs : PRFunctionVector inputArity outputArity) ->
      CertifiedArithmeticGraphVector programs
    | _, _, PRFunctionVector.nil =>
        certifiedNilGraphVector
    | _, _, PRFunctionVector.cons head tail =>
        certifiedConsGraphVector
          (PRFunction.certifiedGraphCompiler head)
          (PRFunctionVector.certifiedGraphCompiler tail)
end

/-- Compile a positive primitive-recursive program to bare arithmetic. -/
def PRFunction.graphFormula
    {arity : Nat}
    (program : PRFunction arity) : ArithmeticGraph arity :=
  program.certifiedGraphCompiler.graph

/-- Compile a vector of positive programs pointwise. -/
def PRFunctionVector.graphFormulas
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity) :
    ArithmeticGraphVector inputArity outputArity :=
  programs.certifiedGraphCompiler.graphs

/-- Every compiled program graph is extensionally its execution relation. -/
theorem PRFunction.graphFormula_represents
    {arity : Nat}
    (program : PRFunction arity) :
    program.graphFormula.Represents program :=
  program.certifiedGraphCompiler.represents

/-- Every compiled vector graph carries a pointwise execution certificate. -/
def PRFunctionVector.graphFormulas_represent
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity) :
    programs.graphFormulas.Represents programs :=
  programs.certifiedGraphCompiler.represents

/-- Public biconditional specification of the arithmetic graph compiler. -/
theorem PRFunction.graphFormula_spec
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity)
    (output : Nat) :
    program.graphFormula.Holds inputs output ↔
      PRFunction.Evaluates program inputs output :=
  program.graphFormula_represents inputs output

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.originalInputsFit
#print axioms RelationalPerimeter.HeytingArithmetic.primitiveRecursionGraph
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.graphFormula
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.graphFormulas
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.graphFormula_spec
#print axioms RelationalPerimeter.HeytingArithmetic.prependTwo_pushedParameter
#print axioms RelationalPerimeter.HeytingArithmetic.compositionGraph_represents
#print axioms RelationalPerimeter.HeytingArithmetic.primitiveRecursionGraph_represents
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.certifiedGraphCompiler
/- AXIOM_AUDIT_END -/
