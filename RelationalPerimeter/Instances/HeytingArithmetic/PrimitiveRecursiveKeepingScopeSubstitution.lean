import RelationalPerimeter.Instances.HeytingArithmetic.KeepingScopeSubstitutionMachine
import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveFormulaRaising

/-!
# Primitive-recursive induction-step substitution

This is the compiled counterpart of `KeepingScopeSubstitutionMachine`.  It is
needed to recognize the full parameterized induction scheme numerically.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

private theorem keepIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem keepIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem keepIndexOne_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)
private theorem keepIndexZero_lt_five : 0 < 5 := Nat.zero_lt_succ 4
private theorem keepIndexOne_lt_five : 1 < 5 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 3)
private theorem keepIndexTwo_lt_five : 2 < 5 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
private theorem keepIndexThree_lt_five : 3 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
private theorem keepIndexFour_lt_five : 4 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

/-- The only term-code action specific to keeping-scope substitution. -/
def PRFunction.keepingScopeVariableCode : PRFunction 2 :=
  let payload := PRFunction.projection 2 0 keepIndexZero_lt_two
  let depth := PRFunction.projection 2 1 keepIndexOne_lt_two
  let unchanged := PRFunction.unaryIn PRFunction.successor
    (PRFunction.binaryIn PRFunction.pair
      (PRFunction.constant 2 0) payload)
  let shiftedAtDepth := PRFunction.unaryIn PRFunction.termSuccessorCode
    (PRFunction.unaryIn PRFunction.successor
      (PRFunction.binaryIn PRFunction.pair
        (PRFunction.constant 2 0) depth))
  PRFunction.select
    (PRFunction.binaryIn PRFunction.equalBit payload depth)
    unchanged shiftedAtDepth

def PRFunction.keepingScopeProcessTermStep : PRFunction 5 :=
  let code := PRFunction.projection 5 0 keepIndexZero_lt_five
  let depth := PRFunction.projection 5 1 keepIndexOne_lt_five
  let work := PRFunction.projection 5 2 keepIndexTwo_lt_five
  let results := PRFunction.projection 5 3 keepIndexThree_lt_five
  let encoded := PRFunction.unaryIn PRFunction.predecessor code
  let tag := PRFunction.unaryIn PRFunction.unpairLeft encoded
  let payload := PRFunction.unaryIn PRFunction.unpairRight encoded
  let fallback := PRFunction.machinePushResultIn work results
    (PRFunction.constant 5 RawTerm.zero.code)
  let variableCode := PRFunction.composition
    PRFunction.keepingScopeVariableCode
    (PRFunctionVector.cons payload (PRFunctionVector.singleton depth))
  let variableBranch := PRFunction.machinePushResultIn
    work results variableCode
  let genericBranch := PRFunction.composition
    PRFunction.formulaRaisingProcessTermStep
    (PRFunctionVector.cons code
      (PRFunctionVector.cons depth
        (PRFunctionVector.cons work
          (PRFunctionVector.cons results
            (PRFunctionVector.singleton (PRFunction.constant 5 0))))))
  let nodeBranch := PRFunction.selectTag tag 0 variableBranch genericBranch
  PRFunction.select code fallback nodeBranch

private theorem formulaRaisingProcessTermStep_zeroAmount_eq_keeping_of_positive_tag
    (encoded depth work results parameter tag : Nat)
    (tagValue : natUnpairLeft encoded = Nat.succ tag) :
    formulaRaisingProcessTermStep
        (Nat.succ encoded) depth work results 0 =
      keepingScopeProcessTermStep
        (Nat.succ encoded) depth work results parameter := by
  unfold formulaRaisingProcessTermStep keepingScopeProcessTermStep
  dsimp only
  rw [tagValue]
  cases tag with
  | zero => rfl
  | succ tag =>
      cases tag with
      | zero => rfl
      | succ tag =>
          cases tag with
          | zero => rfl
          | succ tag =>
              cases tag with
              | zero => rfl
              | succ tag => rfl

private theorem keepingScopeProcessTermStep_of_zero_tag
    (encoded depth work results parameter : Nat)
    (tagValue : natUnpairLeft encoded = 0) :
    keepingScopeProcessTermStep
        (Nat.succ encoded) depth work results parameter =
      if natUnpairRight encoded = depth then
        substitutionPushResult work results
          (RawTerm.succ (RawTerm.bvar depth)).code
      else
        substitutionPushResult work results
          (RawTerm.bvar (natUnpairRight encoded)).code := by
  unfold keepingScopeProcessTermStep
  dsimp only
  rw [tagValue]
  change
    (if natUnpairRight encoded < depth then
        substitutionPushResult work results
          (RawTerm.bvar (natUnpairRight encoded)).code
      else if natUnpairRight encoded = depth then
        substitutionPushResult work results
          (RawTerm.succ (RawTerm.bvar depth)).code
      else
        substitutionPushResult work results
          (RawTerm.bvar (natUnpairRight encoded)).code) =
      if natUnpairRight encoded = depth then
        substitutionPushResult work results
          (RawTerm.succ (RawTerm.bvar depth)).code
      else
        substitutionPushResult work results
          (RawTerm.bvar (natUnpairRight encoded)).code
  by_cases equal : natUnpairRight encoded = depth
  · have notBelow : ¬ natUnpairRight encoded < depth := by
      rw [equal]
      exact Nat.lt_irrefl depth
    rw [if_neg notBelow, if_pos equal]
  · rw [if_neg equal]
    by_cases below : natUnpairRight encoded < depth
    · rw [if_pos below]
    · rw [if_neg below]

private theorem apply_if_then_else
    {alpha beta : Type}
    (function : alpha → beta)
    (condition : Prop)
    [Decidable condition]
    (whenTrue whenFalse : alpha) :
    function (if condition then whenTrue else whenFalse) =
      if condition then function whenTrue else function whenFalse := by
  by_cases holds : condition
  · rw [if_pos holds, if_pos holds]
  · rw [if_neg holds, if_neg holds]

private theorem keepIfZero_zero (whenZero whenPositive : Nat) :
    natIfZero 0 whenZero whenPositive = whenZero := rfl
private theorem keepIfZero_succ (n whenZero whenPositive : Nat) :
    natIfZero (Nat.succ n) whenZero whenPositive = whenPositive := rfl
private theorem keepEqual_zero_zero : natEqualBit 0 0 = 1 := rfl
private theorem keepEqual_succ_zero (n : Nat) :
    natEqualBit (Nat.succ n) 0 = 0 := by
  unfold natEqualBit natIsZero
  rw [Nat.sub_zero, Nat.zero_sub, Nat.add_zero]
private theorem keepEqual_succ_succ (left right : Nat) :
    natEqualBit (Nat.succ left) (Nat.succ right) =
      natEqualBit left right := by
  unfold natEqualBit
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
private theorem keepEqual_self (value : Nat) :
    natEqualBit value value = 1 := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [keepEqual_succ_succ]
      exact inductionHypothesis
private theorem keepEqual_zero_of_ne
    {left right : Nat} (different : left = right -> False) :
    natEqualBit left right = 0 := by
  induction left generalizing right with
  | zero => cases right with
    | zero => exact (different rfl).elim
    | succ right => rfl
  | succ left inductionHypothesis => cases right with
    | zero => exact keepEqual_succ_zero left
    | succ right =>
        rw [keepEqual_succ_succ]
        exact inductionHypothesis (fun equality =>
          different (congrArg Nat.succ equality))

@[simp] theorem PRFunction.run_keepingScopeVariableCode
    (payload depth : Nat) :
    PRFunction.keepingScopeVariableCode.run
        (NatVector.cons payload (NatVector.cons depth NatVector.nil)) =
      if payload = depth then
        (RawTerm.succ (RawTerm.bvar depth)).code
      else
        (RawTerm.bvar payload).code := by
  unfold PRFunction.keepingScopeVariableCode
  dsimp only
  rw [PRFunction.run_select, PRFunction.run_binaryIn,
    PRFunction.run_equalBit,
    PRFunction.run_projection, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_zero]
  by_cases equal : payload = depth
  · rw [equal, keepEqual_self, keepIfZero_succ, if_pos rfl]
    rw [PRFunction.run_unaryIn,
      PRFunction.run_termSuccessorCode, PRFunction.run_unaryIn,
      PRFunction.run_successor,
      PRFunction.run_binaryIn, PRFunction.run_pair,
      PRFunction.run_constant, PRFunction.run_projection,
      NatVector.get_cons_succ, NatVector.get_cons_zero]
    rfl
  · rw [keepEqual_zero_of_ne equal, keepIfZero_zero, if_neg equal]
    rw [PRFunction.run_unaryIn, PRFunction.run_successor,
      PRFunction.run_binaryIn, PRFunction.run_pair,
      PRFunction.run_constant, PRFunction.run_projection,
      NatVector.get_cons_zero]
    rfl

macro "normalize_keep_term" : tactic =>
  `(tactic|
    simp only [PRFunction.run_select, PRFunction.run_selectTag,
      PRFunction.run_projection, NatVector.get_cons_zero,
      NatVector.get_cons_succ, PRFunction.run_machinePushResultIn,
      PRFunction.run_machineStateIn, PRFunction.run_machineStackPushIn,
      PRFunction.run_machineProcessTaskIn, PRFunction.run_constant,
      PRFunction.run_unaryIn, PRFunction.run_binaryIn,
      PRFunction.run_composition, PRFunctionVector.run_cons,
      PRFunctionVector.run_singleton, PRFunction.run_predecessor,
      PRFunction.run_unpairLeft, PRFunction.run_unpairRight,
      PRFunction.run_lessBit, PRFunction.run_equalBit,
      PRFunction.run_successor, PRFunction.run_pair,
      PRFunction.run_termSuccessorCode,
      PRFunction.run_formulaRaisingProcessTermStep,
      PRFunction.run_keepingScopeVariableCode])

macro "evaluate_keep_tag" : tactic =>
  `(tactic|
    rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
      PRFunction.run_unaryIn, PRFunction.run_predecessor,
      PRFunction.run_projection, NatVector.get_cons_zero])

private theorem run_keepingScopeProcessTermStep_zero
    (depth work results parameter : Nat) :
    PRFunction.keepingScopeProcessTermStep.run
        (NatVector.cons 0
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons parameter NatVector.nil))))) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep
        0 depth work results parameter := by
  rw [_root_.RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep]
  unfold PRFunction.keepingScopeProcessTermStep
  dsimp only
  rw [PRFunction.run_select, PRFunction.run_projection,
    NatVector.get_cons_zero, keepIfZero_zero]
  rw [PRFunction.run_machinePushResultIn,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_succ,
    NatVector.get_cons_zero,
    PRFunction.run_constant]

private theorem run_keepingScopeProcessTermStep_variable
    (encoded depth work results parameter : Nat)
    (tagValue : natUnpairLeft encoded = 0) :
    PRFunction.keepingScopeProcessTermStep.run
        (NatVector.cons (Nat.succ encoded)
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons parameter NatVector.nil))))) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep
        (Nat.succ encoded) depth work results parameter := by
  unfold PRFunction.keepingScopeProcessTermStep
  dsimp only
  rw [PRFunction.run_select, PRFunction.run_projection,
    NatVector.get_cons_zero, keepIfZero_succ]
  rw [PRFunction.run_selectTag]
  evaluate_keep_tag
  have predecessor : (Nat.succ encoded).pred = encoded := rfl
  rw [predecessor, tagValue]
  rw [keepingScopeProcessTermStep_of_zero_tag
    encoded depth work results parameter tagValue]
  rw [keepEqual_zero_zero, keepIfZero_succ]
  rw [PRFunction.run_machinePushResultIn,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_succ,
    NatVector.get_cons_zero,
    PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_keepingScopeVariableCode,
    PRFunction.run_unaryIn, PRFunction.run_unpairRight,
    PRFunction.run_unaryIn, PRFunction.run_predecessor,
    PRFunction.run_projection, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_zero,
    predecessor]
  exact apply_if_then_else
    (substitutionPushResult work results)
    (natUnpairRight encoded = depth)
    (RawTerm.succ (RawTerm.bvar depth)).code
    (RawTerm.bvar (natUnpairRight encoded)).code

private theorem run_keepingScopeProcessTermStep_positive_tag
    (encoded depth work results parameter tag : Nat)
    (tagValue : natUnpairLeft encoded = Nat.succ tag) :
    PRFunction.keepingScopeProcessTermStep.run
        (NatVector.cons (Nat.succ encoded)
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons parameter NatVector.nil))))) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep
        (Nat.succ encoded) depth work results parameter := by
  unfold PRFunction.keepingScopeProcessTermStep
  dsimp only
  rw [PRFunction.run_select, PRFunction.run_projection,
    NatVector.get_cons_zero, keepIfZero_succ]
  rw [PRFunction.run_selectTag]
  evaluate_keep_tag
  have predecessor : (Nat.succ encoded).pred = encoded := rfl
  rw [predecessor, tagValue, keepEqual_succ_zero, keepIfZero_zero]
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_formulaRaisingProcessTermStep,
    PRFunction.run_projection, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_succ,
    NatVector.get_cons_zero,
    PRFunction.run_constant]
  exact
    formulaRaisingProcessTermStep_zeroAmount_eq_keeping_of_positive_tag
      encoded depth work results parameter tag tagValue

theorem PRFunction.run_keepingScopeProcessTermStep
    (code depth work results parameter : Nat) :
    PRFunction.keepingScopeProcessTermStep.run
        (NatVector.cons code
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons parameter NatVector.nil))))) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep
        code depth work results parameter := by
  cases code with
  | zero =>
      exact run_keepingScopeProcessTermStep_zero
        depth work results parameter
  | succ encoded =>
      cases tagValue : natUnpairLeft encoded with
      | zero =>
          exact run_keepingScopeProcessTermStep_variable
            encoded depth work results parameter tagValue
      | succ tag =>
          exact run_keepingScopeProcessTermStep_positive_tag
            encoded depth work results parameter tag tagValue

/-! ## Reuse the generic dispatcher shape with the custom term program. -/

/-- Embed the keeping-scope term program in a shared input context. -/
def PRFunction.keepingScopeProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results parameter :
      PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.keepingScopeProcessTermStep
    (PRFunctionVector.cons processCode
      (PRFunctionVector.cons processDepth
        (PRFunctionVector.cons remainingWork
          (PRFunctionVector.cons results
            (PRFunctionVector.singleton parameter)))))

def PRFunction.keepingScopeMachineStep : PRFunction 2 :=
  let state := PRFunction.projection 2 0 keepIndexZero_lt_two
  let parameter := PRFunction.projection 2 1 keepIndexOne_lt_two
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
  let processTerm := PRFunction.keepingScopeProcessTermDispatchIn
    processCode processDepth remainingWork results parameter
  let dispatch := PRFunction.selectTag tag 0 processTerm PRFunction.machineStep
  PRFunction.select work state
    (PRFunction.select task PRFunction.machineStep dispatch)

@[simp] theorem PRFunction.run_keepingScopeProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results parameter :
      PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.keepingScopeProcessTermDispatchIn processCode processDepth
        remainingWork results parameter).run inputs =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep
        (processCode.run inputs) (processDepth.run inputs)
        (remainingWork.run inputs) (results.run inputs)
        (parameter.run inputs) := by
  unfold PRFunction.keepingScopeProcessTermDispatchIn
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_keepingScopeProcessTermStep]

private theorem keepingStep_zero_work
    (state parameter : Nat) (work : natUnpairLeft state = 0) :
    keepingScopeMachineStep state parameter = state := by
  unfold keepingScopeMachineStep
  rw [work]

private theorem keepingStep_succ_work
    (state parameter encodedWork results : Nat)
    (work : natUnpairLeft state = Nat.succ encodedWork)
    (result : natUnpairRight state = results) :
    keepingScopeMachineStep state parameter =
      keepingScopeExecuteTask
        (natUnpairLeft encodedWork) (natUnpairRight encodedWork)
        results parameter := by
  unfold keepingScopeMachineStep
  rw [work, result]

macro "rewrite_keep_step" : tactic =>
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
    | rw [PRFunction.run_keepingScopeProcessTermStep]
    | rw [PRFunction.run_machineProcessFormulaStep]
    | rw [PRFunction.run_keepingScopeProcessTermDispatchIn]
    | rw [PRFunction.run_machineProcessFormulaDispatchIn]
    | rw [PRFunction.run_machineBuildUnaryIn]
    | rw [PRFunction.run_machineBuildBinaryIn]
    | rw [PRFunction.run_machineStep]
    | rw [keepIfZero_zero]
    | rw [keepIfZero_succ]
    | rw [keepEqual_zero_zero]
    | rw [keepEqual_succ_zero]
    | rw [keepEqual_succ_succ]
    | rw [Nat.add_one]
    | rw [Nat.pred_succ]
    | rw [PRFunction.keepingScopeMachineStep]
    | rw [keepingScopeExecuteTask]
    | rw [substitutionMachineStep]
    | rw [substitutionExecuteTask]
    | rw [substitutionMachineState])

macro "close_keep_four"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_keep_step
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rfl)
macro "close_keep_six"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "," ruleFive:ident "," ruleSix:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_keep_step
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rw [($ruleFive)]
      | rw [($ruleSix)]
      | rfl)

set_option maxHeartbeats 3000000 in
theorem PRFunction.run_keepingScopeMachineStep
    (state parameter : Nat) :
    PRFunction.keepingScopeMachineStep.run
        (NatVector.cons state (NatVector.cons parameter NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeMachineStep
        state parameter := by
  cases components : (natUnpairLeft state, natUnpairRight state) with
  | mk work results =>
      have stateWork : natUnpairLeft state = work := congrArg Prod.fst components
      have stateResults : natUnpairRight state = results :=
        congrArg Prod.snd components
      cases work with
      | zero =>
          rw [keepingStep_zero_work state parameter stateWork]
          repeat first | rewrite_keep_step | rw [stateWork] | rfl
      | succ encodedWork =>
          have stateWorkSucc :
              natUnpairLeft state = Nat.succ encodedWork := by
            rw [Nat.add_one] at stateWork
            exact stateWork
          cases workParts :
              (natUnpairLeft encodedWork, natUnpairRight encodedWork) with
          | mk task remainingWork =>
              have workTask : natUnpairLeft encodedWork = task :=
                congrArg Prod.fst workParts
              have workRemaining : natUnpairRight encodedWork = remainingWork :=
                congrArg Prod.snd workParts
              cases task with
              | zero =>
                  rw [keepingStep_succ_work state parameter encodedWork results
                    stateWorkSucc stateResults]
                  close_keep_four
                    [stateWorkSucc, stateResults, workTask, workRemaining]
                  dsimp only
                  rw [workTask, workRemaining]
                  rfl
              | succ encodedTask =>
                  have workTaskSucc :
                      natUnpairLeft encodedWork = Nat.succ encodedTask := by
                    rw [Nat.add_one] at workTask
                    exact workTask
                  cases taskParts :
                      (natUnpairLeft encodedTask,
                        natUnpairRight encodedTask) with
                  | mk tag payload =>
                      have taskTag : natUnpairLeft encodedTask = tag :=
                        congrArg Prod.fst taskParts
                      have taskPayload : natUnpairRight encodedTask = payload :=
                        congrArg Prod.snd taskParts
                      cases tag with
                      | zero =>
                          rw [keepingStep_succ_work state parameter encodedWork
                            results stateWorkSucc stateResults]
                          close_keep_six
                            [stateWorkSucc, stateResults, workTaskSucc,
                              workRemaining, taskTag, taskPayload]
                      | succ tag =>
                          rw [keepingStep_succ_work state parameter encodedWork
                            results stateWorkSucc stateResults]
                          close_keep_six
                            [stateWorkSucc, stateResults, workTaskSucc,
                              workRemaining, taskTag, taskPayload]
                          dsimp only
                          rw [workTaskSucc, workRemaining]
                          unfold substitutionExecuteTask
                          dsimp only
                          rw [taskTag, taskPayload]
                          rfl

def PRFunction.keepingScopeIterationStep : PRFunction 3 :=
  PRFunction.binaryIn PRFunction.keepingScopeMachineStep
    (PRFunction.projection 3 1 keepIndexOne_lt_three)
    (PRFunction.constant 3 0)

def PRFunction.keepingScopeMachineRun : PRFunction 2 :=
  PRFunction.primitiveRecursion PRFunction.identity
    PRFunction.keepingScopeIterationStep

def PRFunction.successorInstanceCode : PRFunction 1 :=
  let code := PRFunction.identity
  let fuel := PRFunction.unaryIn PRFunction.double code
  let initial := PRFunction.unaryIn PRFunction.machineInitialState code
  let finalState := PRFunction.composition PRFunction.keepingScopeMachineRun
    (PRFunctionVector.cons fuel (PRFunctionVector.singleton initial))
  PRFunction.unaryIn PRFunction.machineStackHead
    (PRFunction.unaryIn PRFunction.unpairRight finalState)

@[simp] theorem PRFunction.run_keepingScopeIterationStep
    (counter previous state : Nat) :
    PRFunction.keepingScopeIterationStep.run
        (NatVector.cons counter
          (NatVector.cons previous (NatVector.cons state NatVector.nil))) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeMachineStep
        previous 0 := by
  unfold PRFunction.keepingScopeIterationStep
  rw [PRFunction.run_binaryIn, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_constant,
    PRFunction.run_keepingScopeMachineStep]

theorem PRFunction.run_keepingScopeMachineRun
    (steps state : Nat) :
    PRFunction.keepingScopeMachineRun.run
        (NatVector.cons steps (NatVector.cons state NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeMachineRun
        steps state 0 := by
  induction steps with
  | zero =>
      unfold PRFunction.keepingScopeMachineRun
      rw [PRFunction.run_primitive_zero, PRFunction.run_identity]
      rfl
  | succ steps inductionHypothesis =>
      unfold PRFunction.keepingScopeMachineRun
      rw [PRFunction.run_primitive_succ]
      rw [show
        (PRFunction.primitiveRecursion PRFunction.identity
          PRFunction.keepingScopeIterationStep).run
            (NatVector.cons steps (NatVector.cons state NatVector.nil)) =
          PRFunction.keepingScopeMachineRun.run
            (NatVector.cons steps (NatVector.cons state NatVector.nil)) from rfl]
      rw [PRFunction.run_keepingScopeIterationStep, inductionHypothesis]
      rw [_root_.RelationalPerimeter.HeytingArithmetic.keepingScopeMachineRun_add,
        _root_.RelationalPerimeter.HeytingArithmetic.keepingScopeMachineRun_one]

@[simp] theorem PRFunction.run_successorInstanceCode (formulaCode : Nat) :
    PRFunction.successorInstanceCode.run
        (NatVector.cons formulaCode NatVector.nil) =
      machineSuccessorInstanceCode formulaCode := by
  unfold PRFunction.successorInstanceCode machineSuccessorInstanceCode
  repeat first
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_identity]
    | rw [PRFunction.run_double]
    | rw [PRFunction.run_machineInitialState]
    | rw [PRFunction.run_keepingScopeMachineRun]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_machineStackHead]

theorem PRFunction.successorInstanceCode_evaluates
    (formula : RawFormula) :
    PRFunction.Evaluates PRFunction.successorInstanceCode
      (NatVector.cons formula.code NatVector.nil)
      (formula.substitute
        ScopedFormula.replaceNewestKeepingScopeSubstitution).code := by
  have evaluation := PRFunction.successorInstanceCode.run_evaluates
    (NatVector.cons formula.code NatVector.nil)
  unfold PRFunction.Evaluates at evaluation ⊢
  rw [PRFunction.run_successorInstanceCode,
    machineSuccessorInstanceCode_code] at evaluation
  exact evaluation

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.keepingScopeProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_keepingScopeProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.keepingScopeMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_keepingScopeMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.successorInstanceCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.successorInstanceCode_evaluates
/- AXIOM_AUDIT_END -/
