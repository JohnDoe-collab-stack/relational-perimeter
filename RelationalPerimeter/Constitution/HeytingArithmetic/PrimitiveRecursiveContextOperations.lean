import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveFormulaRaising
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveGeneralSubstitutionMachine
import RelationalPerimeter.Constitution.HeytingArithmetic.ProofCoding

/-!
# Primitive-recursive maps on coded formula contexts

Formula contexts use the same positive prefix coding as finite natural lists.
This module implements a generic map by two terminating passes: the first pass
maps while reversing, and the second reverses again.  Instantiating the generic
map with the certified formula-raising and formula-instantiation programs gives
the exact operations required by the numeric proof checker.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem contextIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem contextIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem contextIndexZero_lt_four : 0 < 4 := Nat.zero_lt_succ 3
private theorem contextIndexOne_lt_four : 1 < 4 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 2)
private theorem contextIndexThree_lt_four : 3 < 4 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

/-! ## Numeric two-pass list map -/

/-- One numeric step of a map-while-reversing traversal. -/
def prefixMapReverseStep
    (transform : Nat -> Nat -> Nat)
    (state parameter : Nat) : Nat :=
  let remaining := natUnpairLeft state
  let accumulated := natUnpairRight state
  match remaining with
  | 0 => state
  | Nat.succ encoded =>
      let head := natUnpairLeft encoded
      let tail := natUnpairRight encoded
      natPair tail
        (Nat.succ (natPair (transform head parameter) accumulated))

def prefixMapReverseRun
    (transform : Nat -> Nat -> Nat) : Nat -> Nat -> Nat -> Nat
  | 0, state, _parameter => state
  | Nat.succ steps, state, parameter =>
      prefixMapReverseRun transform steps
        (prefixMapReverseStep transform state parameter) parameter

def prefixMapReverse
    (transform : Nat -> Nat -> Nat)
    (code parameter : Nat) : Nat :=
  natUnpairRight
    (prefixMapReverseRun transform code (natPair code 0) parameter)

def prefixReverse (code : Nat) : Nat :=
  prefixMapReverse (fun head _parameter => head) code 0

def prefixMapCode
    (transform : Nat -> Nat -> Nat)
    (code parameter : Nat) : Nat :=
  prefixReverse (prefixMapReverse transform code parameter)

/-! ## Positive program trees -/

def PRFunction.prefixMapReverseIterationStep
    (transform : PRFunction 2) : PRFunction 4 :=
  let previous := PRFunction.projection 4 1 contextIndexOne_lt_four
  let parameter := PRFunction.projection 4 3 contextIndexThree_lt_four
  let remaining := PRFunction.unaryIn PRFunction.unpairLeft previous
  let accumulated := PRFunction.unaryIn PRFunction.unpairRight previous
  let encoded := PRFunction.unaryIn PRFunction.predecessor remaining
  let head := PRFunction.unaryIn PRFunction.unpairLeft encoded
  let tail := PRFunction.unaryIn PRFunction.unpairRight encoded
  let transformed := PRFunction.composition transform
    (PRFunctionVector.cons head (PRFunctionVector.singleton parameter))
  let pushed := PRFunction.unaryIn PRFunction.successor
    (PRFunction.binaryIn PRFunction.pair transformed accumulated)
  let next := PRFunction.binaryIn PRFunction.pair tail pushed
  PRFunction.select remaining previous next

def PRFunction.prefixMapReverseRun
    (transform : PRFunction 2) : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 contextIndexZero_lt_two)
    (PRFunction.prefixMapReverseIterationStep transform)

def PRFunction.prefixMapReverse
    (transform : PRFunction 2) : PRFunction 2 :=
  let code := PRFunction.projection 2 0 contextIndexZero_lt_two
  let parameter := PRFunction.projection 2 1 contextIndexOne_lt_two
  let initial := PRFunction.binaryIn PRFunction.pair code
    (PRFunction.constant 2 0)
  let finalState := PRFunction.composition
    (PRFunction.prefixMapReverseRun transform)
    (PRFunctionVector.cons code
      (PRFunctionVector.cons initial
        (PRFunctionVector.singleton parameter)))
  PRFunction.unaryIn PRFunction.unpairRight finalState

def PRFunction.prefixIdentityTransform : PRFunction 2 :=
  PRFunction.projection 2 0 contextIndexZero_lt_two

def PRFunction.prefixReverse : PRFunction 1 :=
  PRFunction.composition
    (PRFunction.prefixMapReverse PRFunction.prefixIdentityTransform)
    (PRFunctionVector.cons PRFunction.identity
      (PRFunctionVector.singleton (PRFunction.constant 1 0)))

def PRFunction.prefixMapCode
    (transform : PRFunction 2) : PRFunction 2 :=
  PRFunction.composition PRFunction.prefixReverse
    (PRFunctionVector.singleton (PRFunction.prefixMapReverse transform))

/-! ## Execution equations -/

private theorem prefixMapReverseRun_succ_right
    (transform : Nat -> Nat -> Nat)
    (steps state parameter : Nat) :
    prefixMapReverseRun transform (Nat.succ steps) state parameter =
      prefixMapReverseStep transform
        (prefixMapReverseRun transform steps state parameter) parameter := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change prefixMapReverseRun transform (Nat.succ steps)
          (prefixMapReverseStep transform state parameter) parameter = _
      rw [inductionHypothesis]
      rfl

@[simp] theorem PRFunction.run_prefixMapReverseIterationStep
    (transform : PRFunction 2)
    (counter previous state parameter : Nat) :
    (PRFunction.prefixMapReverseIterationStep transform).run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons parameter NatVector.nil)))) =
      prefixMapReverseStep
        (fun head argument => transform.run
          (NatVector.cons head (NatVector.cons argument NatVector.nil)))
        previous parameter := by
  unfold PRFunction.prefixMapReverseIterationStep prefixMapReverseStep
  repeat first
    | rw [PRFunction.run_select]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_unpairLeft]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_predecessor]
    | rw [PRFunction.run_successor]
    | rw [PRFunction.run_pair]
    | rw [PRFunction.run_constant]
  cases remaining : natUnpairLeft previous <;> rfl

theorem PRFunction.run_prefixMapReverseRun
    (transform : PRFunction 2)
    (steps state parameter : Nat) :
    (PRFunction.prefixMapReverseRun transform).run
        (NatVector.cons steps
          (NatVector.cons state (NatVector.cons parameter NatVector.nil))) =
      _root_.RelationalPerimeter.HeytingArithmetic.prefixMapReverseRun
        (fun head argument => transform.run
          (NatVector.cons head (NatVector.cons argument NatVector.nil)))
        steps state parameter := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change (PRFunction.prefixMapReverseIterationStep transform).run
          (NatVector.cons steps
            (NatVector.cons
              ((PRFunction.prefixMapReverseRun transform).run
                (NatVector.cons steps
                  (NatVector.cons state
                    (NatVector.cons parameter NatVector.nil))))
              (NatVector.cons state
                (NatVector.cons parameter NatVector.nil)))) = _
      rw [PRFunction.run_prefixMapReverseIterationStep,
        inductionHypothesis]
      rw [Nat.add_one]
      exact (prefixMapReverseRun_succ_right _ _ _ _).symm

@[simp] theorem PRFunction.run_prefixMapReverse
    (transform : PRFunction 2)
    (code parameter : Nat) :
    (PRFunction.prefixMapReverse transform).run
        (NatVector.cons code (NatVector.cons parameter NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.prefixMapReverse
        (fun head argument => transform.run
          (NatVector.cons head (NatVector.cons argument NatVector.nil)))
        code parameter := by
  unfold PRFunction.prefixMapReverse
  unfold _root_.RelationalPerimeter.HeytingArithmetic.prefixMapReverse
  repeat first
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_pair]
    | rw [PRFunction.run_prefixMapReverseRun]
    | rw [PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_prefixIdentityTransform
    (head parameter : Nat) :
    PRFunction.prefixIdentityTransform.run
        (NatVector.cons head (NatVector.cons parameter NatVector.nil)) = head :=
  rfl

@[simp] theorem PRFunction.run_prefixReverse (code : Nat) :
    PRFunction.prefixReverse.run (NatVector.cons code NatVector.nil) =
      _root_.RelationalPerimeter.HeytingArithmetic.prefixReverse code := by
  unfold PRFunction.prefixReverse
  unfold _root_.RelationalPerimeter.HeytingArithmetic.prefixReverse
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_identity,
    PRFunction.run_constant, PRFunction.run_prefixMapReverse]
  rfl

@[simp] theorem PRFunction.run_prefixMapCode
    (transform : PRFunction 2)
    (code parameter : Nat) :
    (PRFunction.prefixMapCode transform).run
        (NatVector.cons code (NatVector.cons parameter NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.prefixMapCode
        (fun head argument => transform.run
          (NatVector.cons head (NatVector.cons argument NatVector.nil)))
        code parameter := by
  unfold PRFunction.prefixMapCode
  unfold _root_.RelationalPerimeter.HeytingArithmetic.prefixMapCode
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_prefixMapReverse, PRFunction.run_prefixReverse]

/-! ## Correctness on canonical prefix quotations -/

/-
The list equalities used below are proved locally by structural recursion.
The corresponding imported convenience lemmas currently carry propositional
extensionality in their compiled dependency closure, although these equalities
need no extensionality principle.
-/

private theorem listAppend_assoc_constructive
    {alpha : Type} (first second third : List alpha) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

private theorem listAppend_nil_constructive
    {alpha : Type} (values : List alpha) :
    values ++ [] = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

private theorem listReverseAux_eq_append_constructive
    {alpha : Type} (values suffix : List alpha) :
    values.reverseAux suffix = values.reverseAux [] ++ suffix := by
  induction values generalizing suffix with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change tail.reverseAux (head :: suffix) =
        tail.reverseAux [head] ++ suffix
      calc
        tail.reverseAux (head :: suffix) =
            tail.reverseAux [] ++ (head :: suffix) :=
          inductionHypothesis (head :: suffix)
        _ = tail.reverseAux [] ++ ([head] ++ suffix) := rfl
        _ = (tail.reverseAux [] ++ [head]) ++ suffix :=
          (listAppend_assoc_constructive
            (tail.reverseAux []) [head] suffix).symm
        _ = tail.reverseAux [head] ++ suffix :=
          congrArg (fun initial => initial ++ suffix)
            (inductionHypothesis [head]).symm

private theorem listReverse_cons_constructive
    {alpha : Type} (head : alpha) (tail : List alpha) :
    (head :: tail).reverse = tail.reverse ++ [head] := by
  unfold List.reverse
  exact listReverseAux_eq_append_constructive tail [head]

private theorem listReverse_append_constructive
    {alpha : Type} (first second : List alpha) :
    (first ++ second).reverse = second.reverse ++ first.reverse := by
  induction first with
  | nil =>
      exact (listAppend_nil_constructive second.reverse).symm
  | cons head tail inductionHypothesis =>
      change (head :: (tail ++ second)).reverse =
        second.reverse ++ (head :: tail).reverse
      calc
        (head :: (tail ++ second)).reverse =
            (tail ++ second).reverse ++ [head] :=
          listReverse_cons_constructive head (tail ++ second)
        _ = (second.reverse ++ tail.reverse) ++ [head] :=
          congrArg (fun initial => initial ++ [head]) inductionHypothesis
        _ = second.reverse ++ (tail.reverse ++ [head]) :=
          listAppend_assoc_constructive second.reverse tail.reverse [head]
        _ = second.reverse ++ (head :: tail).reverse :=
          congrArg (List.append second.reverse)
            (listReverse_cons_constructive head tail).symm

private theorem listReverse_reverse_constructive
    {alpha : Type} (values : List alpha) :
    values.reverse.reverse = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [listReverse_cons_constructive,
        listReverse_append_constructive, inductionHypothesis]
      rfl

theorem quoteNatList_length_le (values : List Nat) :
    values.length <= quoteNatList values := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons head tail inductionHypothesis =>
      change Nat.succ tail.length <=
        Nat.succ (natPair head (quoteNatList tail))
      exact Nat.succ_le_succ
        (Nat.le_trans inductionHypothesis
          (natPair_right_le head (quoteNatList tail)))

theorem prefixMapReverseRun_completed
    (transform : Nat -> Nat -> Nat)
    (steps accumulated parameter : Nat) :
    prefixMapReverseRun transform steps
        (natPair 0 accumulated) parameter = natPair 0 accumulated := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change prefixMapReverseRun transform steps
        (prefixMapReverseStep transform (natPair 0 accumulated) parameter)
        parameter = _
      unfold prefixMapReverseStep
      rw [natUnpairLeft_pair, natUnpairRight_pair]
      exact inductionHypothesis

theorem prefixMapReverseRun_add
    (transform : Nat -> Nat -> Nat)
    (first second state parameter : Nat) :
    prefixMapReverseRun transform (first + second) state parameter =
      prefixMapReverseRun transform second
        (prefixMapReverseRun transform first state parameter) parameter := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add]
      change prefixMapReverseRun transform (first + second)
          (prefixMapReverseStep transform state parameter) parameter = _
      rw [prefixMapReverseRun]
      exact inductionHypothesis
        (prefixMapReverseStep transform state parameter)

theorem prefixMapReverseRun_quote_exact
    (transform : Nat -> Nat -> Nat)
    (values accumulated : List Nat)
    (parameter : Nat) :
    prefixMapReverseRun transform values.length
        (natPair (quoteNatList values) (quoteNatList accumulated)) parameter =
      natPair 0
        (quoteNatList
          ((values.map (fun value => transform value parameter)).reverse ++
            accumulated)) := by
  induction values generalizing accumulated with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change prefixMapReverseRun transform tail.length
        (prefixMapReverseStep transform
          (natPair (Nat.succ (natPair head (quoteNatList tail)))
            (quoteNatList accumulated)) parameter) parameter = _
      have stepExact : prefixMapReverseStep transform
          (natPair (Nat.succ (natPair head (quoteNatList tail)))
            (quoteNatList accumulated)) parameter =
          natPair (quoteNatList tail)
            (Nat.succ (natPair (transform head parameter)
              (quoteNatList accumulated))) := by
        unfold prefixMapReverseStep
        rw [natUnpairLeft_pair, natUnpairRight_pair]
        dsimp only
        repeat first
          | rw [natUnpairLeft_pair]
          | rw [natUnpairRight_pair]
      rw [stepExact]
      change prefixMapReverseRun transform tail.length
          (natPair (quoteNatList tail)
            (quoteNatList (transform head parameter :: accumulated)))
          parameter = _
      rw [inductionHypothesis (transform head parameter :: accumulated)]
      change natPair 0
          (quoteNatList
            ((tail.map (fun value => transform value parameter)).reverse ++
              (transform head parameter :: accumulated))) =
        natPair 0
          (quoteNatList
            ((transform head parameter ::
              tail.map (fun value => transform value parameter)).reverse ++
                accumulated))
      apply congrArg (natPair 0)
      apply congrArg quoteNatList
      rw [listReverse_cons_constructive,
        listAppend_assoc_constructive]
      rfl

theorem prefixMapReverse_quote
    (transform : Nat -> Nat -> Nat)
    (values : List Nat)
    (parameter : Nat) :
    prefixMapReverse transform (quoteNatList values) parameter =
      quoteNatList
        (values.map (fun value => transform value parameter)).reverse := by
  cases natExistsEqAddOfLe (quoteNatList_length_le values) with
  | intro extra equality =>
      unfold prefixMapReverse
      calc
        natUnpairRight
            (prefixMapReverseRun transform (quoteNatList values)
              (natPair (quoteNatList values) 0) parameter) =
            natUnpairRight
              (prefixMapReverseRun transform (values.length + extra)
                (natPair (quoteNatList values) 0) parameter) :=
          congrArg
            (fun fuel => natUnpairRight
              (prefixMapReverseRun transform fuel
                (natPair (quoteNatList values) 0) parameter))
            equality
        _ = natUnpairRight
              (prefixMapReverseRun transform extra
                (prefixMapReverseRun transform values.length
                  (natPair (quoteNatList values) 0) parameter) parameter) := by
          rw [prefixMapReverseRun_add]
        _ = quoteNatList
              (values.map (fun value => transform value parameter)).reverse := by
          change natUnpairRight
            (prefixMapReverseRun transform extra
              (prefixMapReverseRun transform values.length
                (natPair (quoteNatList values) (quoteNatList [])) parameter)
              parameter) = _
          rw [prefixMapReverseRun_quote_exact transform values [] parameter]
          rw [prefixMapReverseRun_completed]
          rw [natUnpairRight_pair]
          rw [listAppend_nil_constructive]

theorem prefixReverse_quote (values : List Nat) :
    prefixReverse (quoteNatList values) = quoteNatList values.reverse := by
  unfold prefixReverse
  rw [prefixMapReverse_quote]
  have same : values.map (fun value => value) = values := by
    induction values with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        exact congrArg (List.cons head) inductionHypothesis
  rw [same]

theorem prefixMapCode_quote
    (transform : Nat -> Nat -> Nat)
    (values : List Nat)
    (parameter : Nat) :
    prefixMapCode transform (quoteNatList values) parameter =
      quoteNatList (values.map (fun value => transform value parameter)) := by
  unfold prefixMapCode
  rw [prefixMapReverse_quote, prefixReverse_quote,
    listReverse_reverse_constructive]

/-! ## Formula-context specializations -/

/-- Binary formula-code map used by `FormulaContext.lift`. -/
def PRFunction.raiseContextCode : PRFunction 2 :=
  PRFunction.prefixMapCode PRFunction.raiseFormulaCode

/-- Binary formula-code map used by `FormulaContext.instantiate`. -/
def PRFunction.instantiateContextTermCode : PRFunction 2 :=
  PRFunction.prefixMapCode PRFunction.machineInstantiateTerm

def FormulaContext.rawCodes {bound : Nat} : FormulaContext bound -> List Nat
  | FormulaContext.nil => []
  | FormulaContext.cons head tail => head.raw.code :: tail.rawCodes

theorem FormulaContext.quote_eq_quoteNatList_rawCodes
    {bound : Nat}
    (context : FormulaContext bound) :
    context.quote = quoteNatList context.rawCodes := by
  induction context with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change Nat.succ (natPair head.raw.code tail.quote) =
        Nat.succ (natPair head.raw.code (quoteNatList tail.rawCodes))
      rw [inductionHypothesis]

theorem ScopedFormula.lift_code
    {bound : Nat}
    (formula : ScopedFormula bound) :
    formula.lift.raw.code =
      PRFunction.raiseFormulaCode.run
        (NatVector.cons formula.raw.code (NatVector.cons 1 NatVector.nil)) := by
  rw [PRFunction.run_raiseFormulaCode, machineRaiseFormulaCode_code,
    RawFormula.raiseFreeVariables_one]
  rfl

theorem FormulaContext.lift_rawCodes
    {bound : Nat}
    (context : FormulaContext bound) :
    context.lift.rawCodes =
      context.rawCodes.map (fun code =>
        PRFunction.raiseFormulaCode.run
          (NatVector.cons code (NatVector.cons 1 NatVector.nil))) := by
  induction context with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [FormulaContext.rawCodes, List.map]
      change head.lift.raw.code :: tail.lift.rawCodes = _
      rw [ScopedFormula.lift_code, inductionHypothesis]

theorem FormulaContext.instantiate_rawCodes
    {bound : Nat}
    (replacement : ScopedTerm bound)
    (context : FormulaContext (Nat.succ bound)) :
    (context.instantiate replacement).rawCodes =
      context.rawCodes.map (fun code =>
        PRFunction.machineInstantiateTerm.run
          (NatVector.cons code
            (NatVector.cons replacement.raw.code NatVector.nil))) := by
  induction context with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [FormulaContext.rawCodes, List.map]
      change (head.instantiate replacement).raw.code ::
          (tail.instantiate replacement).rawCodes = _
      rw [inductionHypothesis]
      change (head.raw.instantiateTerm replacement.raw).code :: _ = _
      rw [PRFunction.run_machineInstantiateTerm,
        machineInstantiateTermCode_code]

@[simp] theorem PRFunction.run_raiseContextCode
    (contextCode amount : Nat) :
    PRFunction.raiseContextCode.run
        (NatVector.cons contextCode (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.prefixMapCode
        (fun formulaCode argument => PRFunction.raiseFormulaCode.run
          (NatVector.cons formulaCode
            (NatVector.cons argument NatVector.nil)))
        contextCode amount :=
  PRFunction.run_prefixMapCode PRFunction.raiseFormulaCode
    contextCode amount

theorem PRFunction.raiseContextCode_lift
    {bound : Nat}
    (context : FormulaContext bound) :
    PRFunction.raiseContextCode.run
        (NatVector.cons context.quote (NatVector.cons 1 NatVector.nil)) =
      context.lift.quote := by
  rw [PRFunction.run_raiseContextCode,
    FormulaContext.quote_eq_quoteNatList_rawCodes,
    prefixMapCode_quote,
    FormulaContext.quote_eq_quoteNatList_rawCodes,
    FormulaContext.lift_rawCodes]

@[simp] theorem PRFunction.run_instantiateContextTermCode
    (contextCode termCode : Nat) :
    PRFunction.instantiateContextTermCode.run
        (NatVector.cons contextCode (NatVector.cons termCode NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.prefixMapCode
        (fun formulaCode replacementCode =>
          PRFunction.machineInstantiateTerm.run
            (NatVector.cons formulaCode
              (NatVector.cons replacementCode NatVector.nil)))
        contextCode termCode :=
  PRFunction.run_prefixMapCode PRFunction.machineInstantiateTerm
    contextCode termCode

theorem PRFunction.instantiateContextTermCode_code
    {bound : Nat}
    (replacement : ScopedTerm bound)
    (context : FormulaContext (Nat.succ bound)) :
    PRFunction.instantiateContextTermCode.run
        (NatVector.cons context.quote
          (NatVector.cons replacement.raw.code NatVector.nil)) =
      (context.instantiate replacement).quote := by
  rw [PRFunction.run_instantiateContextTermCode,
    FormulaContext.quote_eq_quoteNatList_rawCodes,
    prefixMapCode_quote,
    FormulaContext.quote_eq_quoteNatList_rawCodes,
    FormulaContext.instantiate_rawCodes]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.prefixMapCode
#print axioms RelationalPerimeter.HeytingArithmetic.prefixMapCode_quote
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseContextCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseContextCode_lift
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.instantiateContextTermCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.instantiateContextTermCode_code
/- AXIOM_AUDIT_END -/
