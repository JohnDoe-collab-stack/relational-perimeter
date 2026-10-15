import RelationalPerimeter.Instances.HeytingArithmetic.SubstitutionMachine

/-!
# Positive PR implementation of the capture-avoiding substitution machine

Every numeric operation of `SubstitutionMachine` is implemented below by an
explicit `PRFunction` tree.  The final unary program performs genuine
self-substitution on every well-formed formula code.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-!
Projection bounds are data carried by the positive program trees.  Keep them
as explicit constructive proofs so the programs do not inherit tactic axioms.
-/

private theorem indexZero_lt_two : 0 < 2 :=
  Nat.zero_lt_succ 1

private theorem indexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)

private theorem indexOne_lt_four : 1 < 4 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 2)

private theorem indexThree_lt_four : 3 < 4 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

private theorem indexZero_lt_five : 0 < 5 :=
  Nat.zero_lt_succ 4

private theorem indexOne_lt_five : 1 < 5 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 3)

private theorem indexTwo_lt_five : 2 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.zero_lt_succ 2))

private theorem indexThree_lt_five : 3 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))

private theorem indexFour_lt_five : 4 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

@[simp] theorem PRFunction.run_predecessor (value : Nat) :
    PRFunction.predecessor.run (NatVector.cons value NatVector.nil) =
      value.pred :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.predecessor_evaluates value)

@[simp] theorem PRFunction.run_lessBit (left right : Nat) :
    PRFunction.lessBit.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      natLessBit left right :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.lessBit_evaluates left right)

@[simp] theorem PRFunction.run_double (value : Nat) :
    PRFunction.double.run (NatVector.cons value NatVector.nil) =
      natDouble value :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.double_evaluates value)

@[simp] theorem PRFunction.run_identity (value : Nat) :
    PRFunction.identity.run (NatVector.cons value NatVector.nil) = value :=
  rfl

/-! ## Context-polymorphic numeric constructors -/

/-- Apply a binary program to two programs in a shared input context. -/
def PRFunction.binaryIn
    {arity : Nat}
    (constructor : PRFunction 2)
    (left right : PRFunction arity) :
    PRFunction arity :=
  PRFunction.composition constructor
    (PRFunctionVector.cons left (PRFunctionVector.singleton right))

/-- Apply a unary program in a shared input context. -/
def PRFunction.unaryIn
    {arity : Nat}
    (constructor : PRFunction 1)
    (argument : PRFunction arity) :
    PRFunction arity :=
  PRFunction.composition constructor (PRFunctionVector.singleton argument)

@[simp] theorem PRFunction.run_binaryIn
    {arity : Nat}
    (constructor : PRFunction 2)
    (left right : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.binaryIn constructor left right).run inputs =
      constructor.run
        (NatVector.cons (left.run inputs)
          (NatVector.cons (right.run inputs) NatVector.nil)) :=
  rfl

@[simp] theorem PRFunction.run_unaryIn
    {arity : Nat}
    (constructor : PRFunction 1)
    (argument : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.unaryIn constructor argument).run inputs =
      constructor.run (NatVector.cons (argument.run inputs) NatVector.nil) :=
  rfl

/-- Positive stack push and total positive-stack projections. -/
def PRFunction.machineStackPush : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.successor PRFunction.pair

def PRFunction.machineStackHead : PRFunction 1 :=
  PRFunction.select PRFunction.identity PRFunction.zero
    (PRFunction.unaryIn PRFunction.unpairLeft PRFunction.predecessor)

def PRFunction.machineStackTail : PRFunction 1 :=
  PRFunction.select PRFunction.identity PRFunction.zero
    (PRFunction.unaryIn PRFunction.unpairRight PRFunction.predecessor)

/-- Positive task constructor and paired machine state. -/
def PRFunction.machineTask : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.successor PRFunction.pair

def PRFunction.machineState : PRFunction 2 := PRFunction.pair

/-- Lift stack, task, and state construction to any input context. -/
def PRFunction.machineStackPushIn
    {arity : Nat}
    (item stack : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.machineStackPush item stack

def PRFunction.machineTaskIn
    {arity : Nat}
    (tag payload : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.machineTask tag payload

def PRFunction.machineStateIn
    {arity : Nat}
    (work results : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.machineState work results

def PRFunction.machineProcessTaskIn
    {arity : Nat}
    (taskTag code depth : PRFunction arity) : PRFunction arity :=
  PRFunction.machineTaskIn taskTag
    (PRFunction.binaryIn PRFunction.pair code depth)

def PRFunction.machinePushResultIn
    {arity : Nat}
    (work results result : PRFunction arity) : PRFunction arity :=
  PRFunction.machineStateIn work
    (PRFunction.machineStackPushIn result results)

def PRFunction.machineBuildUnaryIn
    {arity : Nat}
    (syntaxTag work results : PRFunction arity) : PRFunction arity :=
  PRFunction.machinePushResultIn
    work
    (PRFunction.unaryIn PRFunction.machineStackTail results)
    (PRFunction.unaryIn PRFunction.successor
      (PRFunction.binaryIn PRFunction.pair syntaxTag
        (PRFunction.unaryIn PRFunction.machineStackHead results)))

def PRFunction.machineBuildBinaryIn
    {arity : Nat}
    (syntaxTag work results : PRFunction arity) : PRFunction arity :=
  let right := PRFunction.unaryIn PRFunction.machineStackHead results
  let afterRight := PRFunction.unaryIn PRFunction.machineStackTail results
  let left := PRFunction.unaryIn PRFunction.machineStackHead afterRight
  let afterLeft := PRFunction.unaryIn PRFunction.machineStackTail afterRight
  PRFunction.machinePushResultIn
    work afterLeft
    (PRFunction.unaryIn PRFunction.successor
      (PRFunction.binaryIn PRFunction.pair syntaxTag
        (PRFunction.binaryIn PRFunction.pair left right)))

/-! ## Program for one term-processing task -/

def PRFunction.machineProcessTermStep : PRFunction 5 :=
  let code := PRFunction.projection 5 0 indexZero_lt_five
  let depth := PRFunction.projection 5 1 indexOne_lt_five
  let work := PRFunction.projection 5 2 indexTwo_lt_five
  let results := PRFunction.projection 5 3 indexThree_lt_five
  let value := PRFunction.projection 5 4 indexFour_lt_five
  let encoded := PRFunction.unaryIn PRFunction.predecessor code
  let tag := PRFunction.unaryIn PRFunction.unpairLeft encoded
  let payload := PRFunction.unaryIn PRFunction.unpairRight encoded
  let payloadLeft := PRFunction.unaryIn PRFunction.unpairLeft payload
  let payloadRight := PRFunction.unaryIn PRFunction.unpairRight payload
  let fallback := PRFunction.machinePushResultIn
    work results (PRFunction.constant 5 RawTerm.zero.code)
  let boundVariable := PRFunction.machinePushResultIn
    work results
    (PRFunction.unaryIn PRFunction.successor
      (PRFunction.binaryIn PRFunction.pair
        (PRFunction.constant 5 0) payload))
  let numeral := PRFunction.machinePushResultIn
    work results
    (PRFunction.unaryIn PRFunction.numeralCode value)
  let variableBranch := PRFunction.select
    (PRFunction.binaryIn PRFunction.lessBit payload depth)
    numeral boundVariable
  let zeroBranch := fallback
  let unaryBranch := PRFunction.machineStateIn
    (PRFunction.machineStackPushIn
      (PRFunction.machineProcessTaskIn
        (PRFunction.constant 5 0) payload depth)
      (PRFunction.machineStackPushIn
        (PRFunction.constant 5 substitutionBuildTermSuccTask)
        work))
    results
  let binaryBranch := fun (buildTask : Nat) =>
    PRFunction.machineStateIn
      (PRFunction.machineStackPushIn
        (PRFunction.machineProcessTaskIn
          (PRFunction.constant 5 0) payloadLeft depth)
        (PRFunction.machineStackPushIn
          (PRFunction.machineProcessTaskIn
            (PRFunction.constant 5 0) payloadRight depth)
          (PRFunction.machineStackPushIn
            (PRFunction.constant 5 buildTask) work)))
      results
  let nodeBranch := PRFunction.selectTag tag 0 variableBranch
    (PRFunction.selectTag tag 1 zeroBranch
      (PRFunction.selectTag tag 2 unaryBranch
        (PRFunction.selectTag tag 3
          (binaryBranch substitutionBuildTermAddTask)
          (PRFunction.selectTag tag 4
            (binaryBranch substitutionBuildTermMulTask)
            fallback))))
  PRFunction.select code fallback nodeBranch

/-! ## Program for one formula-processing task -/

def PRFunction.machineProcessFormulaStep : PRFunction 5 :=
  let code := PRFunction.projection 5 0 indexZero_lt_five
  let depth := PRFunction.projection 5 1 indexOne_lt_five
  let work := PRFunction.projection 5 2 indexTwo_lt_five
  let results := PRFunction.projection 5 3 indexThree_lt_five
  let encoded := PRFunction.unaryIn PRFunction.predecessor code
  let tag := PRFunction.unaryIn PRFunction.unpairLeft encoded
  let payload := PRFunction.unaryIn PRFunction.unpairRight encoded
  let payloadLeft := PRFunction.unaryIn PRFunction.unpairLeft payload
  let payloadRight := PRFunction.unaryIn PRFunction.unpairRight payload
  let fallback := PRFunction.machinePushResultIn
    work results (PRFunction.constant 5 RawFormula.falsum.code)
  let binaryBranch := fun (childTaskTag buildTask : Nat) =>
    PRFunction.machineStateIn
      (PRFunction.machineStackPushIn
        (PRFunction.machineProcessTaskIn
          (PRFunction.constant 5 childTaskTag) payloadLeft depth)
        (PRFunction.machineStackPushIn
          (PRFunction.machineProcessTaskIn
            (PRFunction.constant 5 childTaskTag) payloadRight depth)
          (PRFunction.machineStackPushIn
            (PRFunction.constant 5 buildTask) work)))
      results
  let unaryBranch := fun (buildTask : Nat) =>
    PRFunction.machineStateIn
      (PRFunction.machineStackPushIn
        (PRFunction.machineProcessTaskIn
          (PRFunction.constant 5 1)
          payload
          (PRFunction.unaryIn PRFunction.successor depth))
        (PRFunction.machineStackPushIn
          (PRFunction.constant 5 buildTask) work))
      results
  let nodeBranch := PRFunction.selectTag tag 0 fallback
    (PRFunction.selectTag tag 1
      (binaryBranch 0 substitutionBuildFormulaEqualTask)
      (PRFunction.selectTag tag 2
        (binaryBranch 1 substitutionBuildFormulaConjTask)
        (PRFunction.selectTag tag 3
          (binaryBranch 1 substitutionBuildFormulaDisjTask)
          (PRFunction.selectTag tag 4
            (binaryBranch 1 substitutionBuildFormulaImplTask)
            (PRFunction.selectTag tag 5
              (unaryBranch substitutionBuildFormulaAllTask)
              (PRFunction.selectTag tag 6
                (unaryBranch substitutionBuildFormulaExTask)
                fallback))))))
  PRFunction.select code fallback nodeBranch

/-- Embed the term-processing program in a shared input context. -/
def PRFunction.machineProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results value :
      PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.machineProcessTermStep
    (PRFunctionVector.cons processCode
      (PRFunctionVector.cons processDepth
        (PRFunctionVector.cons remainingWork
          (PRFunctionVector.cons results
            (PRFunctionVector.singleton value)))))

/-- Embed the formula-processing program in a shared input context. -/
def PRFunction.machineProcessFormulaDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results value :
      PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.machineProcessFormulaStep
    (PRFunctionVector.cons processCode
      (PRFunctionVector.cons processDepth
        (PRFunctionVector.cons remainingWork
          (PRFunctionVector.cons results
            (PRFunctionVector.singleton value)))))

/-! ## Complete one-step dispatcher -/

def PRFunction.machineStep : PRFunction 2 :=
  let state := PRFunction.projection 2 0 indexZero_lt_two
  let value := PRFunction.projection 2 1 indexOne_lt_two
  let work := PRFunction.unaryIn PRFunction.unpairLeft state
  let results := PRFunction.unaryIn PRFunction.unpairRight state
  let encodedWork := PRFunction.unaryIn PRFunction.predecessor work
  let task := PRFunction.unaryIn PRFunction.unpairLeft encodedWork
  let remainingWork := PRFunction.unaryIn PRFunction.unpairRight encodedWork
  let encodedTask := PRFunction.unaryIn PRFunction.predecessor task
  let tag := PRFunction.unaryIn PRFunction.unpairLeft encodedTask
  let payload := PRFunction.unaryIn PRFunction.unpairRight encodedTask
  let processCode := PRFunction.unaryIn PRFunction.unpairLeft payload
  let processDepth := PRFunction.unaryIn PRFunction.unpairRight payload
  let processTerm := PRFunction.machineProcessTermDispatchIn
    processCode processDepth remainingWork results value
  let processFormula := PRFunction.machineProcessFormulaDispatchIn
    processCode processDepth remainingWork results value
  let dropInvalid := PRFunction.machineStateIn remainingWork results
  let dispatch := PRFunction.selectTag tag 0 processTerm
    (PRFunction.selectTag tag 1 processFormula
      (PRFunction.selectTag tag 2
        (PRFunction.machineBuildUnaryIn
          (PRFunction.constant 2 2) remainingWork results)
        (PRFunction.selectTag tag 3
          (PRFunction.machineBuildBinaryIn
            (PRFunction.constant 2 3) remainingWork results)
          (PRFunction.selectTag tag 4
            (PRFunction.machineBuildBinaryIn
              (PRFunction.constant 2 4) remainingWork results)
            (PRFunction.selectTag tag 5
              (PRFunction.machineBuildBinaryIn
                (PRFunction.constant 2 1) remainingWork results)
              (PRFunction.selectTag tag 6
                (PRFunction.machineBuildBinaryIn
                  (PRFunction.constant 2 2) remainingWork results)
                (PRFunction.selectTag tag 7
                  (PRFunction.machineBuildBinaryIn
                    (PRFunction.constant 2 3) remainingWork results)
                  (PRFunction.selectTag tag 8
                    (PRFunction.machineBuildBinaryIn
                      (PRFunction.constant 2 4) remainingWork results)
                    (PRFunction.selectTag tag 9
                      (PRFunction.machineBuildUnaryIn
                        (PRFunction.constant 2 5) remainingWork results)
                      (PRFunction.selectTag tag 10
                        (PRFunction.machineBuildUnaryIn
                          (PRFunction.constant 2 6) remainingWork results)
                        dropInvalid))))))))))
  PRFunction.select work state
    (PRFunction.select task dropInvalid dispatch)

/-! ## Iteration and final substitution programs -/

def PRFunction.machineIterationArguments : PRFunctionVector 4 2 :=
  PRFunctionVector.cons
    (PRFunction.projection 4 1 indexOne_lt_four)
    (PRFunctionVector.singleton
      (PRFunction.projection 4 3 indexThree_lt_four))

def PRFunction.machineIterationStep : PRFunction 4 :=
  PRFunction.composition PRFunction.machineStep
    PRFunction.machineIterationArguments

def PRFunction.machineRun : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 indexZero_lt_two)
    PRFunction.machineIterationStep

def PRFunction.machineInitialState : PRFunction 1 :=
  PRFunction.machineStateIn
    (PRFunction.machineStackPushIn
      (PRFunction.machineProcessTaskIn
        (PRFunction.constant 1 1)
        PRFunction.identity
        (PRFunction.constant 1 0))
      (PRFunction.constant 1 0))
    (PRFunction.constant 1 0)

def PRFunction.machineSubstituteNumeral : PRFunction 2 :=
  let code := PRFunction.projection 2 0 indexZero_lt_two
  let value := PRFunction.projection 2 1 indexOne_lt_two
  let fuel := PRFunction.unaryIn PRFunction.double code
  let initial := PRFunction.unaryIn PRFunction.machineInitialState code
  let finalState := PRFunction.composition PRFunction.machineRun
    (PRFunctionVector.cons fuel
      (PRFunctionVector.cons initial (PRFunctionVector.singleton value)))
  PRFunction.unaryIn PRFunction.machineStackHead
    (PRFunction.unaryIn PRFunction.unpairRight finalState)

/-- Unary self-substitution used by the genuine diagonal lemma. -/
def PRFunction.captureAvoidingDiagonalSubstitution : PRFunction 1 :=
  PRFunction.composition PRFunction.machineSubstituteNumeral
    (PRFunctionVector.cons PRFunction.identity
      (PRFunctionVector.singleton PRFunction.identity))

/-! ## Correctness of the numeric program -/

@[simp] theorem PRFunction.run_machineStackPush (item stack : Nat) :
    PRFunction.machineStackPush.run
        (NatVector.cons item (NatVector.cons stack NatVector.nil)) =
      substitutionStackPush item stack := by
  change Nat.succ (PRFunction.pair.run _) = _
  rw [PRFunction.run_pair]
  rfl

@[simp] theorem PRFunction.run_machineStackHead (stack : Nat) :
    PRFunction.machineStackHead.run (NatVector.cons stack NatVector.nil) =
      substitutionStackHead stack := by
  cases stack with
  | zero => rfl
  | succ encoded =>
      unfold PRFunction.machineStackHead
      rw [PRFunction.run_select, PRFunction.run_identity,
        PRFunction.run_zero, PRFunction.run_unaryIn,
        PRFunction.run_predecessor, PRFunction.run_unpairLeft]
      rfl

@[simp] theorem PRFunction.run_machineStackTail (stack : Nat) :
    PRFunction.machineStackTail.run (NatVector.cons stack NatVector.nil) =
      substitutionStackTail stack := by
  cases stack with
  | zero => rfl
  | succ encoded =>
      unfold PRFunction.machineStackTail
      rw [PRFunction.run_select, PRFunction.run_identity,
        PRFunction.run_zero, PRFunction.run_unaryIn,
        PRFunction.run_predecessor, PRFunction.run_unpairRight]
      rfl

@[simp] theorem PRFunction.run_machineTask (tag payload : Nat) :
    PRFunction.machineTask.run
        (NatVector.cons tag (NatVector.cons payload NatVector.nil)) =
      substitutionTask tag payload := by
  change Nat.succ (PRFunction.pair.run _) = _
  rw [PRFunction.run_pair]
  rfl

@[simp] theorem PRFunction.run_machineState (work results : Nat) :
    PRFunction.machineState.run
        (NatVector.cons work (NatVector.cons results NatVector.nil)) =
      substitutionMachineState work results :=
  PRFunction.run_pair work results

@[simp] theorem PRFunction.run_machineStackPushIn
    {arity : Nat}
    (item stack : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineStackPushIn item stack).run inputs =
      substitutionStackPush (item.run inputs) (stack.run inputs) := by
  change PRFunction.machineStackPush.run
    (NatVector.cons (item.run inputs)
      (NatVector.cons (stack.run inputs) NatVector.nil)) = _
  rw [PRFunction.run_machineStackPush]

@[simp] theorem PRFunction.run_machineTaskIn
    {arity : Nat}
    (tag payload : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineTaskIn tag payload).run inputs =
      substitutionTask (tag.run inputs) (payload.run inputs) := by
  change PRFunction.machineTask.run
    (NatVector.cons (tag.run inputs)
      (NatVector.cons (payload.run inputs) NatVector.nil)) = _
  rw [PRFunction.run_machineTask]

@[simp] theorem PRFunction.run_machineStateIn
    {arity : Nat}
    (work results : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineStateIn work results).run inputs =
      substitutionMachineState (work.run inputs) (results.run inputs) := by
  change PRFunction.machineState.run
    (NatVector.cons (work.run inputs)
      (NatVector.cons (results.run inputs) NatVector.nil)) = _
  rw [PRFunction.run_machineState]

@[simp] theorem PRFunction.run_machineProcessTaskIn
    {arity : Nat}
    (taskTag code depth : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineProcessTaskIn taskTag code depth).run inputs =
      substitutionTask
        (taskTag.run inputs)
        (natPair (code.run inputs) (depth.run inputs)) := by
  unfold PRFunction.machineProcessTaskIn
  rw [PRFunction.run_machineTaskIn, PRFunction.run_binaryIn,
    PRFunction.run_pair]

@[simp] theorem PRFunction.run_machinePushResultIn
    {arity : Nat}
    (work results result : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machinePushResultIn work results result).run inputs =
      substitutionPushResult
        (work.run inputs) (results.run inputs) (result.run inputs) := by
  unfold PRFunction.machinePushResultIn substitutionPushResult
  rw [PRFunction.run_machineStateIn, PRFunction.run_machineStackPushIn]

@[simp] theorem PRFunction.run_machineBuildUnaryIn
    {arity : Nat}
    (syntaxTag work results : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineBuildUnaryIn syntaxTag work results).run inputs =
      substitutionBuildUnary
        (syntaxTag.run inputs) (work.run inputs) (results.run inputs) := by
  unfold PRFunction.machineBuildUnaryIn substitutionBuildUnary
  rw [PRFunction.run_machinePushResultIn,
    PRFunction.run_unaryIn, PRFunction.run_machineStackTail,
    PRFunction.run_unaryIn, PRFunction.run_successor,
    PRFunction.run_binaryIn, PRFunction.run_pair,
    PRFunction.run_unaryIn, PRFunction.run_machineStackHead]

@[simp] theorem PRFunction.run_machineBuildBinaryIn
    {arity : Nat}
    (syntaxTag work results : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineBuildBinaryIn syntaxTag work results).run inputs =
      substitutionBuildBinary
        (syntaxTag.run inputs) (work.run inputs) (results.run inputs) := by
  unfold PRFunction.machineBuildBinaryIn substitutionBuildBinary
  rw [PRFunction.run_machinePushResultIn,
    PRFunction.run_unaryIn, PRFunction.run_machineStackTail,
    PRFunction.run_unaryIn, PRFunction.run_machineStackTail,
    PRFunction.run_unaryIn, PRFunction.run_successor,
    PRFunction.run_binaryIn, PRFunction.run_pair,
    PRFunction.run_binaryIn, PRFunction.run_pair,
    PRFunction.run_unaryIn, PRFunction.run_machineStackHead,
    PRFunction.run_unaryIn, PRFunction.run_machineStackTail,
    PRFunction.run_unaryIn, PRFunction.run_machineStackHead]

/-- Numeric less-than bits are exact constructive characteristic values. -/
theorem natLessBit_eq_one_of_lt
    {left right : Nat}
    (strict : left < right) :
    natLessBit left right = 1 := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => exact (Nat.not_lt_zero 0 strict).elim
      | succ right => rfl
  | succ left inductionHypothesis =>
      cases right with
      | zero => exact (Nat.not_lt_zero (Nat.succ left) strict).elim
      | succ right =>
          unfold natLessBit
          repeat rw [Nat.add_one]
          rw [Nat.succ_sub_succ_eq_sub]
          exact inductionHypothesis (Nat.lt_of_succ_lt_succ strict)

theorem natLessBit_eq_zero_of_not_lt
    {left right : Nat}
    (notStrict : left < right -> False) :
    natLessBit left right = 0 := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ right => exact (notStrict (Nat.zero_lt_succ right)).elim
  | succ left inductionHypothesis =>
      cases right with
      | zero =>
          unfold natLessBit
          rw [Nat.zero_sub]
          rfl
      | succ right =>
          unfold natLessBit
          repeat rw [Nat.add_one]
          rw [Nat.succ_sub_succ_eq_sub]
          apply inductionHypothesis
          intro strict
          exact notStrict (Nat.succ_lt_succ strict)

private theorem natIfZero_zero_clean (whenZero whenPositive : Nat) :
    natIfZero 0 whenZero whenPositive = whenZero := rfl

private theorem natIfZero_succ_clean
    (selector whenZero whenPositive : Nat) :
    natIfZero (Nat.succ selector) whenZero whenPositive = whenPositive := rfl

private theorem natEqualBit_zero_zero_clean :
    natEqualBit 0 0 = 1 := rfl

private theorem natEqualBit_succ_zero_clean (value : Nat) :
    natEqualBit (Nat.succ value) 0 = 0 := by
  unfold natEqualBit natIsZero
  rw [Nat.sub_zero, Nat.zero_sub, Nat.add_zero]

private theorem natEqualBit_succ_succ_clean (left right : Nat) :
    natEqualBit (Nat.succ left) (Nat.succ right) = natEqualBit left right := by
  unfold natEqualBit
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]

macro "normalize_active_machine_program" : tactic =>
  `(tactic|
    repeat
      first
      | rw [PRFunction.run_select]
      | rw [PRFunction.run_selectTag]
      | rw [PRFunction.run_projection]
      | rw [NatVector.get_cons_zero]
      | rw [NatVector.get_cons_succ]
      | rw [PRFunction.run_machinePushResultIn]
      | rw [PRFunction.run_machineStateIn]
      | rw [PRFunction.run_machineStackPushIn]
      | rw [PRFunction.run_machineProcessTaskIn]
      | rw [PRFunction.run_constant]
      | rw [PRFunction.run_unaryIn]
      | rw [PRFunction.run_binaryIn]
      | rw [PRFunction.run_predecessor]
      | rw [PRFunction.run_unpairLeft]
      | rw [PRFunction.run_unpairRight]
      | rw [PRFunction.run_lessBit]
      | rw [PRFunction.run_numeralCode]
      | rw [PRFunction.run_successor]
      | rw [PRFunction.run_pair])

macro "evaluate_current_process_tag" : tactic =>
  `(tactic|
    rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
      PRFunction.run_unaryIn, PRFunction.run_predecessor,
      PRFunction.run_projection, NatVector.get_cons_zero])

/-- The five-input term program implements the numeric term step exactly. -/
theorem PRFunction.run_machineProcessTermStep
    (code depth work results value : Nat) :
    PRFunction.machineProcessTermStep.run
        (NatVector.cons code
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons value NatVector.nil))))) =
      substitutionProcessTermStep code depth work results value := by
  cases code with
  | zero =>
      rw [substitutionProcessTermStep.eq_1]
      unfold PRFunction.machineProcessTermStep
      normalize_active_machine_program
      rfl
  | succ encoded =>
      rw [substitutionProcessTermStep.eq_2]
      unfold PRFunction.machineProcessTermStep
      dsimp only
      rw [PRFunction.run_select]
      rw [PRFunction.run_projection, NatVector.get_cons_zero]
      rw [natIfZero_succ_clean]
      change (PRFunction.selectTag _ 0 _ _).run _ = _
      rw [PRFunction.run_selectTag]
      rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
        PRFunction.run_unaryIn, PRFunction.run_predecessor,
        PRFunction.run_projection, NatVector.get_cons_zero]
      have predecessor : (encoded + 1).pred = encoded := rfl
      rw [predecessor]
      cases tagValue : natUnpairLeft encoded with
      | zero =>
          rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
          change (PRFunction.select _ _ _).run _ = _
          normalize_active_machine_program
          rw [predecessor]
          by_cases bounded : natUnpairRight encoded < depth
          · rw [natLessBit_eq_one_of_lt bounded,
              natIfZero_succ_clean, if_pos bounded]
            rfl
          · rw [natLessBit_eq_zero_of_not_lt bounded,
              natIfZero_zero_clean, if_neg bounded]
            rfl
      | succ tag =>
          repeat rw [Nat.add_one]
          rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
          cases tag with
          | zero =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_current_process_tag
              rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
              rw [natEqualBit_succ_succ_clean,
                natEqualBit_zero_zero_clean, natIfZero_succ_clean]
              normalize_active_machine_program
              rfl
          | succ tag =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_current_process_tag
              rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
              rw [natEqualBit_succ_succ_clean,
                natEqualBit_succ_zero_clean, natIfZero_zero_clean]
              cases tag with
              | zero =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_current_process_tag
                  rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                  rw [natEqualBit_succ_succ_clean,
                    natEqualBit_succ_succ_clean,
                    natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                  normalize_active_machine_program
                  rfl
              | succ tag =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_current_process_tag
                  rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                  rw [natEqualBit_succ_succ_clean,
                    natEqualBit_succ_succ_clean,
                    natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                  cases tag with
                  | zero =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_current_process_tag
                      rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                      rw [natEqualBit_succ_succ_clean,
                        natEqualBit_succ_succ_clean,
                        natEqualBit_succ_succ_clean,
                        natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                      normalize_active_machine_program
                      rfl
                  | succ tag =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_current_process_tag
                      rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                      rw [natEqualBit_succ_succ_clean,
                        natEqualBit_succ_succ_clean,
                        natEqualBit_succ_succ_clean,
                        natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                      cases tag with
                      | zero =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_current_process_tag
                          rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                          rw [natEqualBit_succ_succ_clean,
                            natEqualBit_succ_succ_clean,
                            natEqualBit_succ_succ_clean,
                            natEqualBit_succ_succ_clean,
                            natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                          normalize_active_machine_program
                          rfl
                      | succ tag =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_current_process_tag
                          rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                          rw [natEqualBit_succ_succ_clean,
                            natEqualBit_succ_succ_clean,
                            natEqualBit_succ_succ_clean,
                            natEqualBit_succ_succ_clean,
                            natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                          normalize_active_machine_program
                          rfl

/-- The five-input formula program implements the numeric formula step exactly. -/
theorem PRFunction.run_machineProcessFormulaStep
    (code depth work results value : Nat) :
    PRFunction.machineProcessFormulaStep.run
        (NatVector.cons code
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons value NatVector.nil))))) =
      substitutionProcessFormulaStep code depth work results value := by
  cases code with
  | zero =>
      rw [substitutionProcessFormulaStep.eq_1]
      unfold PRFunction.machineProcessFormulaStep
      normalize_active_machine_program
      rfl
  | succ encoded =>
      rw [substitutionProcessFormulaStep.eq_2]
      unfold PRFunction.machineProcessFormulaStep
      dsimp only
      rw [PRFunction.run_select]
      rw [PRFunction.run_projection, NatVector.get_cons_zero]
      rw [natIfZero_succ_clean]
      change (PRFunction.selectTag _ 0 _ _).run _ = _
      rw [PRFunction.run_selectTag]
      rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
        PRFunction.run_unaryIn, PRFunction.run_predecessor,
        PRFunction.run_projection, NatVector.get_cons_zero]
      have predecessor : (encoded + 1).pred = encoded := rfl
      rw [predecessor]
      cases tagValue : natUnpairLeft encoded with
      | zero =>
          rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
          normalize_active_machine_program
          rfl
      | succ tag =>
          repeat rw [Nat.add_one]
          rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
          cases tag with
          | zero =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_current_process_tag
              rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
              repeat rw [natEqualBit_succ_succ_clean]
              rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
              normalize_active_machine_program
              rfl
          | succ tag =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_current_process_tag
              rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
              repeat rw [natEqualBit_succ_succ_clean]
              rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
              cases tag with
              | zero =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_current_process_tag
                  rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                  repeat rw [natEqualBit_succ_succ_clean]
                  rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                  normalize_active_machine_program
                  rfl
              | succ tag =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_current_process_tag
                  rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                  repeat rw [natEqualBit_succ_succ_clean]
                  rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                  cases tag with
                  | zero =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_current_process_tag
                      rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                      repeat rw [natEqualBit_succ_succ_clean]
                      rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                      normalize_active_machine_program
                      rfl
                  | succ tag =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_current_process_tag
                      rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                      repeat rw [natEqualBit_succ_succ_clean]
                      rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                      cases tag with
                      | zero =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_current_process_tag
                          rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                          repeat rw [natEqualBit_succ_succ_clean]
                          rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                          normalize_active_machine_program
                          rfl
                      | succ tag =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_current_process_tag
                          rw [show (Nat.succ encoded).pred = encoded from rfl, tagValue]
                          repeat rw [natEqualBit_succ_succ_clean]
                          rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                          cases tag with
                          | zero =>
                              change (PRFunction.selectTag _ 5 _ _).run _ = _
                              rw [PRFunction.run_selectTag]
                              evaluate_current_process_tag
                              rw [show (Nat.succ encoded).pred = encoded from rfl,
                                tagValue]
                              repeat rw [natEqualBit_succ_succ_clean]
                              rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                              normalize_active_machine_program
                              rfl
                          | succ tag =>
                              change (PRFunction.selectTag _ 5 _ _).run _ = _
                              rw [PRFunction.run_selectTag]
                              evaluate_current_process_tag
                              rw [show (Nat.succ encoded).pred = encoded from rfl,
                                tagValue]
                              repeat rw [natEqualBit_succ_succ_clean]
                              rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                              cases tag with
                              | zero =>
                                  change (PRFunction.selectTag _ 6 _ _).run _ = _
                                  rw [PRFunction.run_selectTag]
                                  evaluate_current_process_tag
                                  rw [show (Nat.succ encoded).pred = encoded from rfl,
                                    tagValue]
                                  repeat rw [natEqualBit_succ_succ_clean]
                                  rw [natEqualBit_zero_zero_clean, natIfZero_succ_clean]
                                  normalize_active_machine_program
                                  rfl

                              | succ tag =>
                                  change (PRFunction.selectTag _ 6 _ _).run _ = _
                                  rw [PRFunction.run_selectTag]
                                  evaluate_current_process_tag
                                  rw [show (Nat.succ encoded).pred = encoded from rfl,
                                    tagValue]
                                  repeat rw [natEqualBit_succ_succ_clean]
                                  rw [natEqualBit_succ_zero_clean, natIfZero_zero_clean]
                                  normalize_active_machine_program
                                  rfl

@[simp] theorem PRFunction.run_machineProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results value :
      PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineProcessTermDispatchIn processCode processDepth
        remainingWork results value).run inputs =
      substitutionProcessTermStep
        (processCode.run inputs) (processDepth.run inputs)
        (remainingWork.run inputs) (results.run inputs) (value.run inputs) := by
  unfold PRFunction.machineProcessTermDispatchIn
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_machineProcessTermStep]

@[simp] theorem PRFunction.run_machineProcessFormulaDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results value :
      PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.machineProcessFormulaDispatchIn processCode processDepth
        remainingWork results value).run inputs =
      substitutionProcessFormulaStep
        (processCode.run inputs) (processDepth.run inputs)
        (remainingWork.run inputs) (results.run inputs) (value.run inputs) := by
  unfold PRFunction.machineProcessFormulaDispatchIn
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_machineProcessFormulaStep]

private theorem substitutionMachineStep_zero_work_clean
    (state value : Nat)
    (stateWork : natUnpairLeft state = 0) :
    substitutionMachineStep state value = state := by
  unfold substitutionMachineStep
  rw [stateWork]

private theorem substitutionMachineStep_succ_work_clean
    (state value encodedWork results : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results) :
    substitutionMachineStep state value =
      substitutionExecuteTask
        (natUnpairLeft encodedWork)
        (natUnpairRight encodedWork)
        results value := by
  unfold substitutionMachineStep
  rw [stateWork, stateResults]

macro "rewrite_machine_step_once" : tactic =>
  `(tactic|
    first
    | rw [PRFunction.run_select]
    | rw [PRFunction.run_selectTag]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_predecessor]
    | rw [PRFunction.run_unpairLeft]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunctionVector.run_nil]
    | rw [PRFunction.run_machineStateIn]
    | rw [PRFunction.run_machineProcessTermStep]
    | rw [PRFunction.run_machineProcessFormulaStep]
    | rw [PRFunction.run_machineProcessTermDispatchIn]
    | rw [PRFunction.run_machineProcessFormulaDispatchIn]
    | rw [PRFunction.run_machineBuildUnaryIn]
    | rw [PRFunction.run_machineBuildBinaryIn]
    | rw [natIfZero_zero_clean]
    | rw [natIfZero_succ_clean]
    | rw [natEqualBit_zero_zero_clean]
    | rw [natEqualBit_succ_zero_clean]
    | rw [natEqualBit_succ_succ_clean]
    | rw [Nat.add_one]
    | rw [Nat.pred_succ]
    | rw [PRFunction.machineStep]
    | rw [substitutionExecuteTask]
    | rw [substitutionMachineState])

macro "close_machine_step_branch_one" "[" rule:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_machine_step_once
      | rw [($rule)]
      | rfl)

macro "close_machine_step_branch_four"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_machine_step_once
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rfl)

macro "close_machine_step_branch_six"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "," ruleFive:ident "," ruleSix:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_machine_step_once
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rw [($ruleFive)]
      | rw [($ruleSix)]
      | rfl)

private theorem run_machineStep_zero_work_clean
    (state value : Nat)
    (stateWork : natUnpairLeft state = 0) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_zero_work_clean state value stateWork]
  close_machine_step_branch_one [stateWork]

private theorem run_machineStep_zero_task_clean
    (state value encodedWork results remainingWork : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = 0)
    (_workRemaining : natUnpairRight encodedWork = remainingWork) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_four
    [stateWork, stateResults, workTask, _workRemaining]

private theorem run_machineStep_tag_zero_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 0)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_one_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 1)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_two_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 2)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_three_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 3)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_four_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 4)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_five_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 5)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_six_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 6)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_seven_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 7)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_eight_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 8)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_nine_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 9)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_machineStep_tag_ten_clean
    (state value encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 10)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  rw [substitutionMachineStep_succ_work_clean state value encodedWork results
    stateWork stateResults]
  close_machine_step_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

set_option maxHeartbeats 2000000 in
/-- The two-input positive program implements one complete machine step. -/
theorem PRFunction.run_machineStep (state value : Nat) :
    PRFunction.machineStep.run
        (NatVector.cons state (NatVector.cons value NatVector.nil)) =
      substitutionMachineStep state value := by
  cases stateComponents : (natUnpairLeft state, natUnpairRight state) with
  | mk work results =>
      have stateWork : natUnpairLeft state = work := by
        exact congrArg Prod.fst stateComponents
      have stateResults : natUnpairRight state = results := by
        exact congrArg Prod.snd stateComponents
      cases work with
      | zero =>
          exact run_machineStep_zero_work_clean state value stateWork
      | succ encodedWork =>
          have stateWorkSucc :
              natUnpairLeft state = Nat.succ encodedWork := by
            rw [Nat.add_one] at stateWork
            exact stateWork
          cases workComponents :
              (natUnpairLeft encodedWork, natUnpairRight encodedWork) with
          | mk task remainingWork =>
              have workTask : natUnpairLeft encodedWork = task := by
                exact congrArg Prod.fst workComponents
              have workRemaining : natUnpairRight encodedWork = remainingWork := by
                exact congrArg Prod.snd workComponents
              cases task with
              | zero =>
                  exact run_machineStep_zero_task_clean state value encodedWork
                    results remainingWork stateWorkSucc stateResults workTask
                    workRemaining
              | succ encodedTask =>
                  have workTaskSucc :
                      natUnpairLeft encodedWork = Nat.succ encodedTask := by
                    rw [Nat.add_one] at workTask
                    exact workTask
                  cases taskComponents :
                      (natUnpairLeft encodedTask, natUnpairRight encodedTask) with
                  | mk tag payload =>
                      have taskTag : natUnpairLeft encodedTask = tag := by
                        exact congrArg Prod.fst taskComponents
                      have taskPayload : natUnpairRight encodedTask = payload := by
                        exact congrArg Prod.snd taskComponents
                      cases tag with
                      | zero =>
                          exact run_machineStep_tag_zero_clean state value
                            encodedWork results encodedTask remainingWork payload
                            stateWorkSucc stateResults workTaskSucc workRemaining
                            taskTag taskPayload
                      | succ tag =>
                          cases tag with
                          | zero =>
                              exact run_machineStep_tag_one_clean state value
                                encodedWork results encodedTask remainingWork payload
                                stateWorkSucc stateResults workTaskSucc workRemaining
                                taskTag taskPayload
                          | succ tag =>
                              cases tag with
                              | zero =>
                                  exact run_machineStep_tag_two_clean state value
                                    encodedWork results encodedTask remainingWork payload
                                    stateWorkSucc stateResults workTaskSucc workRemaining
                                    taskTag taskPayload
                              | succ tag =>
                                  cases tag with
                                  | zero =>
                                      exact run_machineStep_tag_three_clean state value
                                        encodedWork results encodedTask remainingWork
                                        payload stateWorkSucc stateResults workTaskSucc
                                        workRemaining taskTag taskPayload
                                  | succ tag =>
                                      cases tag with
                                      | zero =>
                                          exact run_machineStep_tag_four_clean state value
                                            encodedWork results encodedTask remainingWork
                                            payload stateWorkSucc stateResults workTaskSucc
                                            workRemaining taskTag taskPayload
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact run_machineStep_tag_five_clean state value
                                                encodedWork results encodedTask remainingWork
                                                payload stateWorkSucc stateResults workTaskSucc
                                                workRemaining taskTag taskPayload
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact run_machineStep_tag_six_clean state value
                                                    encodedWork results encodedTask
                                                    remainingWork payload stateWorkSucc
                                                    stateResults workTaskSucc workRemaining
                                                    taskTag taskPayload
                                              | succ tag =>
                                                  cases tag with
                                                  | zero =>
                                                      exact run_machineStep_tag_seven_clean
                                                        state value encodedWork results
                                                        encodedTask remainingWork payload
                                                        stateWorkSucc stateResults workTaskSucc
                                                        workRemaining taskTag taskPayload
                                                  | succ tag =>
                                                      cases tag with
                                                      | zero =>
                                                          exact run_machineStep_tag_eight_clean
                                                            state value encodedWork results
                                                            encodedTask remainingWork payload
                                                            stateWorkSucc stateResults
                                                            workTaskSucc workRemaining taskTag
                                                            taskPayload
                                                      | succ tag =>
                                                          cases tag with
                                                          | zero =>
                                                              exact run_machineStep_tag_nine_clean
                                                                state value encodedWork results
                                                                encodedTask remainingWork payload
                                                                stateWorkSucc stateResults
                                                                workTaskSucc workRemaining taskTag
                                                                taskPayload
                                                          | succ tag =>
                                                              cases tag with
                                                              | zero =>
                                                                  exact run_machineStep_tag_ten_clean
                                                                    state value encodedWork results
                                                                    encodedTask remainingWork payload
                                                                    stateWorkSucc stateResults
                                                                    workTaskSucc workRemaining taskTag
                                                                    taskPayload
                                                              | succ tag =>
                                                                  rw [substitutionMachineStep_succ_work_clean
                                                                    state value encodedWork results
                                                                    stateWorkSucc stateResults]
                                                                  close_machine_step_branch_six
                                                                    [stateWorkSucc, stateResults,
                                                                      workTaskSucc,
                                                                      workRemaining, taskTag, taskPayload]

@[simp] theorem PRFunction.run_machineIterationArguments
    (counter previous state value : Nat) :
    PRFunction.machineIterationArguments.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons value NatVector.nil)))) =
      NatVector.cons previous (NatVector.cons value NatVector.nil) := by
  rfl

@[simp] theorem PRFunction.run_machineIterationStep
    (counter previous state value : Nat) :
    PRFunction.machineIterationStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons value NatVector.nil)))) =
      substitutionMachineStep previous value := by
  calc
    _ = PRFunction.machineStep.run
        (PRFunction.machineIterationArguments.run
          (NatVector.cons counter
            (NatVector.cons previous
              (NatVector.cons state
                (NatVector.cons value NatVector.nil))))) :=
      PRFunction.run_composition
        PRFunction.machineStep PRFunction.machineIterationArguments _
    _ = PRFunction.machineStep.run
        (NatVector.cons previous (NatVector.cons value NatVector.nil)) :=
      congrArg PRFunction.machineStep.run
        (PRFunction.run_machineIterationArguments
          counter previous state value)
    _ = substitutionMachineStep previous value :=
      PRFunction.run_machineStep previous value

/-- The primitive-recursion iterator is exactly the semantic machine run. -/
theorem PRFunction.run_machineRun
    (steps state value : Nat) :
    PRFunction.machineRun.run
        (NatVector.cons steps
          (NatVector.cons state
            (NatVector.cons value NatVector.nil))) =
      substitutionMachineRun steps state value := by
  induction steps with
  | zero =>
      unfold PRFunction.machineRun
      rw [PRFunction.run_primitive_zero, PRFunction.run_projection]
      rfl
  | succ steps inductionHypothesis =>
      unfold PRFunction.machineRun
      rw [PRFunction.run_primitive_succ]
      rw [show
        (PRFunction.primitiveRecursion
          (PRFunction.projection 2 0 indexZero_lt_two)
          PRFunction.machineIterationStep).run
            (NatVector.cons steps
              (NatVector.cons state
                (NatVector.cons value NatVector.nil))) =
          PRFunction.machineRun.run
            (NatVector.cons steps
              (NatVector.cons state
                (NatVector.cons value NatVector.nil))) from rfl]
      rw [PRFunction.run_machineIterationStep, inductionHypothesis]
      rw [← substitutionMachineRun_one]
      exact (substitutionMachineRun_add steps 1 state value).symm

@[simp] theorem PRFunction.run_machineInitialState (formulaCode : Nat) :
    PRFunction.machineInitialState.run
        (NatVector.cons formulaCode NatVector.nil) =
      substitutionMachineInitialState formulaCode := by
  unfold PRFunction.machineInitialState
  normalize_active_machine_program
  rw [PRFunction.run_identity]
  rfl

/-- The explicit binary program computes the verified code substitution. -/
theorem PRFunction.run_machineSubstituteNumeral
    (formulaCode value : Nat) :
    PRFunction.machineSubstituteNumeral.run
        (NatVector.cons formulaCode
          (NatVector.cons value NatVector.nil)) =
      machineSubstituteNumeralCode formulaCode value := by
  unfold PRFunction.machineSubstituteNumeral
  repeat
    first
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunctionVector.run_nil]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_double]
    | rw [PRFunction.run_machineInitialState]
    | rw [PRFunction.run_machineRun]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_machineStackHead]
    | rfl

/-- Positive execution certificate for substitution on every genuine code. -/
theorem PRFunction.machineSubstituteNumeral_evaluates_code
    (formula : RawFormula)
    (value : Nat) :
    PRFunction.Evaluates PRFunction.machineSubstituteNumeral
        (NatVector.cons formula.code
          (NatVector.cons value NatVector.nil))
        (formula.instantiateNumeral value).code := by
  have evaluation := PRFunction.machineSubstituteNumeral.run_evaluates
    (NatVector.cons formula.code
      (NatVector.cons value NatVector.nil))
  rw [PRFunction.run_machineSubstituteNumeral,
    machineSubstituteNumeralCode_code] at evaluation
  exact evaluation

/-- The unary diagonal program computes capture-avoiding self-substitution. -/
theorem PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code
    (formula : RawFormula) :
    PRFunction.Evaluates PRFunction.captureAvoidingDiagonalSubstitution
        (NatVector.cons formula.code NatVector.nil)
        (formula.instantiateNumeral formula.code).code := by
  apply PRFunction.Evaluates.composition
  · exact PRFunctionVector.Evaluates.cons
      (PRFunction.Evaluates.projection
        0 (Nat.zero_lt_succ 0)
        (NatVector.cons formula.code NatVector.nil))
      (PRFunctionVector.Evaluates.cons
        (PRFunction.Evaluates.projection
          0 (Nat.zero_lt_succ 0)
          (NatVector.cons formula.code NatVector.nil))
        (PRFunctionVector.Evaluates.nil
          (NatVector.cons formula.code NatVector.nil)))
  · exact PRFunction.machineSubstituteNumeral_evaluates_code
      formula formula.code

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineProcessFormulaStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineRun
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineSubstituteNumeral
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.captureAvoidingDiagonalSubstitution
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_machineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_machineIterationStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_machineRun
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code
/- AXIOM_AUDIT_END -/
