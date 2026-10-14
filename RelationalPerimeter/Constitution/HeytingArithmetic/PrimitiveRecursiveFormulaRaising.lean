import RelationalPerimeter.Constitution.HeytingArithmetic.FormulaRaisingMachine
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveSubstitutionMachine

/-!
# Positive primitive-recursive formula raising

This file compiles `FormulaRaisingMachine` into the intrinsic `PRFunction`
language.  The resulting binary tree computes the exact code of capture-free
raising on every genuine formula code.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

private theorem raisingIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem raisingIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem raisingIndexOne_lt_four : 1 < 4 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 2)
private theorem raisingIndexThree_lt_four : 3 < 4 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
private theorem raisingIndexZero_lt_five : 0 < 5 := Nat.zero_lt_succ 4
private theorem raisingIndexOne_lt_five : 1 < 5 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 3)
private theorem raisingIndexTwo_lt_five : 2 < 5 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
private theorem raisingIndexThree_lt_five : 3 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
private theorem raisingIndexFour_lt_five : 4 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

/-! ## Custom term step -/

def PRFunction.formulaRaisingProcessTermStep : PRFunction 5 :=
  let code := PRFunction.projection 5 0 raisingIndexZero_lt_five
  let depth := PRFunction.projection 5 1 raisingIndexOne_lt_five
  let work := PRFunction.projection 5 2 raisingIndexTwo_lt_five
  let results := PRFunction.projection 5 3 raisingIndexThree_lt_five
  let amount := PRFunction.projection 5 4 raisingIndexFour_lt_five
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
  let raisedVariable := PRFunction.machinePushResultIn
    work results
    (PRFunction.unaryIn PRFunction.successor
      (PRFunction.binaryIn PRFunction.pair
        (PRFunction.constant 5 0)
        (PRFunction.binaryIn PRFunction.add payload amount)))
  let variableBranch := PRFunction.select
    (PRFunction.binaryIn PRFunction.lessBit payload depth)
    raisedVariable boundVariable
  let unaryBranch := PRFunction.machineStateIn
    (PRFunction.machineStackPushIn
      (PRFunction.machineProcessTaskIn
        (PRFunction.constant 5 0) payload depth)
      (PRFunction.machineStackPushIn
        (PRFunction.constant 5 substitutionBuildTermSuccTask) work))
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
    (PRFunction.selectTag tag 1 fallback
      (PRFunction.selectTag tag 2 unaryBranch
        (PRFunction.selectTag tag 3
          (binaryBranch substitutionBuildTermAddTask)
          (PRFunction.selectTag tag 4
            (binaryBranch substitutionBuildTermMulTask) fallback))))
  PRFunction.select code fallback nodeBranch

private theorem raisingNatIfZero_zero (whenZero whenPositive : Nat) :
    natIfZero 0 whenZero whenPositive = whenZero := rfl

private theorem raisingNatIfZero_succ
    (selector whenZero whenPositive : Nat) :
    natIfZero (Nat.succ selector) whenZero whenPositive = whenPositive := rfl

private theorem raisingNatEqualBit_zero_zero : natEqualBit 0 0 = 1 := rfl

private theorem raisingNatEqualBit_succ_zero (value : Nat) :
    natEqualBit (Nat.succ value) 0 = 0 := by
  unfold natEqualBit natIsZero
  rw [Nat.sub_zero, Nat.zero_sub, Nat.add_zero]

private theorem raisingNatEqualBit_succ_succ (left right : Nat) :
    natEqualBit (Nat.succ left) (Nat.succ right) =
      natEqualBit left right := by
  unfold natEqualBit
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]

private theorem run_add_formula_raising (left right : Nat) :
    PRFunction.add.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      left + right :=
  (PRFunction.add_evaluates left right).symm

macro "normalize_formula_raising_term_program" : tactic =>
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
      | rw [PRFunction.run_composition]
      | rw [PRFunctionVector.run_cons]
      | rw [PRFunctionVector.run_singleton]
      | rw [PRFunction.run_predecessor]
      | rw [PRFunction.run_unpairLeft]
      | rw [PRFunction.run_unpairRight]
      | rw [PRFunction.run_lessBit]
      | rw [PRFunction.run_successor]
      | rw [PRFunction.run_pair]
      | rw [run_add_formula_raising])

macro "evaluate_formula_raising_current_tag" : tactic =>
  `(tactic|
    rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
      PRFunction.run_unaryIn, PRFunction.run_predecessor,
      PRFunction.run_projection, NatVector.get_cons_zero])

theorem PRFunction.run_formulaRaisingProcessTermStep
    (code depth work results amount : Nat) :
    PRFunction.formulaRaisingProcessTermStep.run
        (NatVector.cons code
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons amount NatVector.nil))))) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingProcessTermStep
        code depth work results amount := by
  cases code with
  | zero =>
      unfold _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingProcessTermStep
      unfold PRFunction.formulaRaisingProcessTermStep
      normalize_formula_raising_term_program
      rfl
  | succ encoded =>
      unfold _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingProcessTermStep
      unfold PRFunction.formulaRaisingProcessTermStep
      dsimp only
      rw [PRFunction.run_select, PRFunction.run_projection,
        NatVector.get_cons_zero, raisingNatIfZero_succ]
      change (PRFunction.selectTag _ 0 _ _).run _ = _
      rw [PRFunction.run_selectTag]
      evaluate_formula_raising_current_tag
      have predecessor : (Nat.succ encoded).pred = encoded := rfl
      rw [predecessor]
      cases tagValue : natUnpairLeft encoded with
      | zero =>
          rw [raisingNatEqualBit_zero_zero, raisingNatIfZero_succ]
          change (PRFunction.select _ _ _).run _ = _
          normalize_formula_raising_term_program
          rw [predecessor]
          by_cases bounded : natUnpairRight encoded < depth
          · rw [natLessBit_eq_one_of_lt bounded,
              raisingNatIfZero_succ, if_pos bounded]
            rfl
          · rw [natLessBit_eq_zero_of_not_lt bounded,
              raisingNatIfZero_zero, if_neg bounded]
            rfl
      | succ tag =>
          rw [raisingNatEqualBit_succ_zero, raisingNatIfZero_zero]
          cases tag with
          | zero =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_formula_raising_current_tag
              rw [predecessor, tagValue, raisingNatEqualBit_succ_succ,
                raisingNatEqualBit_zero_zero, raisingNatIfZero_succ]
              normalize_formula_raising_term_program
              rfl
          | succ tag =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_formula_raising_current_tag
              rw [predecessor, tagValue, raisingNatEqualBit_succ_succ,
                raisingNatEqualBit_succ_zero, raisingNatIfZero_zero]
              cases tag with
              | zero =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_formula_raising_current_tag
                  rw [predecessor, tagValue]
                  repeat rw [raisingNatEqualBit_succ_succ]
                  rw [raisingNatEqualBit_zero_zero, raisingNatIfZero_succ]
                  normalize_formula_raising_term_program
                  rfl
              | succ tag =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_formula_raising_current_tag
                  rw [predecessor, tagValue]
                  repeat rw [raisingNatEqualBit_succ_succ]
                  rw [raisingNatEqualBit_succ_zero, raisingNatIfZero_zero]
                  cases tag with
                  | zero =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_formula_raising_current_tag
                      rw [predecessor, tagValue]
                      repeat rw [raisingNatEqualBit_succ_succ]
                      rw [raisingNatEqualBit_zero_zero, raisingNatIfZero_succ]
                      normalize_formula_raising_term_program
                      rw [Nat.add_one, Nat.pred_succ]
                      rfl
                  | succ tag =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_formula_raising_current_tag
                      rw [predecessor, tagValue]
                      repeat rw [raisingNatEqualBit_succ_succ]
                      rw [raisingNatEqualBit_succ_zero, raisingNatIfZero_zero]
                      cases tag with
                      | zero =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_formula_raising_current_tag
                          rw [predecessor, tagValue]
                          repeat rw [raisingNatEqualBit_succ_succ]
                          rw [raisingNatEqualBit_zero_zero,
                            raisingNatIfZero_succ]
                          normalize_formula_raising_term_program
                          rw [Nat.add_one, Nat.pred_succ]
                          rfl
                      | succ tag =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_formula_raising_current_tag
                          rw [predecessor, tagValue]
                          repeat rw [raisingNatEqualBit_succ_succ]
                          rw [raisingNatEqualBit_succ_zero,
                            raisingNatIfZero_zero]
                          normalize_formula_raising_term_program
                          rw [Nat.add_one]
                          rfl

/-! ## Complete compiled dispatcher -/

/-- Embed the raising term-processing program in a shared input context. -/
def PRFunction.formulaRaisingProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results amount :
      PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.formulaRaisingProcessTermStep
    (PRFunctionVector.cons processCode
      (PRFunctionVector.cons processDepth
        (PRFunctionVector.cons remainingWork
          (PRFunctionVector.cons results
            (PRFunctionVector.singleton amount)))))

def PRFunction.formulaRaisingMachineStep : PRFunction 2 :=
  let state := PRFunction.projection 2 0 raisingIndexZero_lt_two
  let amount := PRFunction.projection 2 1 raisingIndexOne_lt_two
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
  let processTerm := PRFunction.formulaRaisingProcessTermDispatchIn
    processCode processDepth remainingWork results amount
  let processFormula := PRFunction.machineProcessFormulaDispatchIn
    processCode processDepth remainingWork results amount
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
  PRFunction.select work state (PRFunction.select task dropInvalid dispatch)

@[simp] theorem PRFunction.run_formulaRaisingProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results amount :
      PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.formulaRaisingProcessTermDispatchIn processCode processDepth
        remainingWork results amount).run inputs =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingProcessTermStep
        (processCode.run inputs) (processDepth.run inputs)
        (remainingWork.run inputs) (results.run inputs) (amount.run inputs) := by
  unfold PRFunction.formulaRaisingProcessTermDispatchIn
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_formulaRaisingProcessTermStep]

private theorem formulaRaisingStep_zero_work
    (state amount : Nat)
    (stateWork : natUnpairLeft state = 0) :
    formulaRaisingMachineStep state amount = state := by
  unfold formulaRaisingMachineStep
  rw [stateWork]

private theorem formulaRaisingStep_succ_work
    (state amount encodedWork results : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results) :
    formulaRaisingMachineStep state amount =
      formulaRaisingExecuteTask
        (natUnpairLeft encodedWork) (natUnpairRight encodedWork)
        results amount := by
  unfold formulaRaisingMachineStep
  rw [stateWork, stateResults]

macro "rewrite_formula_raising_step_once" : tactic =>
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
    | rw [PRFunction.run_formulaRaisingProcessTermStep]
    | rw [PRFunction.run_machineProcessFormulaStep]
    | rw [PRFunction.run_formulaRaisingProcessTermDispatchIn]
    | rw [PRFunction.run_machineProcessFormulaDispatchIn]
    | rw [PRFunction.run_machineBuildUnaryIn]
    | rw [PRFunction.run_machineBuildBinaryIn]
    | rw [raisingNatIfZero_zero]
    | rw [raisingNatIfZero_succ]
    | rw [raisingNatEqualBit_zero_zero]
    | rw [raisingNatEqualBit_succ_zero]
    | rw [raisingNatEqualBit_succ_succ]
    | rw [Nat.add_one]
    | rw [Nat.pred_succ]
    | rw [PRFunction.formulaRaisingMachineStep]
    | rw [formulaRaisingExecuteTask]
    | rw [substitutionExecuteTask]
    | rw [substitutionMachineState])

macro "close_formula_raising_branch_four"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_formula_raising_step_once
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rfl)

macro "close_formula_raising_branch_six"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "," ruleFive:ident "," ruleSix:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_formula_raising_step_once
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rw [($ruleFive)]
      | rw [($ruleSix)]
      | rfl)

private theorem run_formulaRaisingMachineStep_zero_work
    (state amount : Nat)
    (stateWork : natUnpairLeft state = 0) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_zero_work state amount stateWork]
  repeat first
    | rewrite_formula_raising_step_once
    | rw [stateWork]
    | rfl

private theorem run_formulaRaisingMachineStep_zero_task
    (state amount encodedWork results remainingWork : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = 0)
    (_workRemaining : natUnpairRight encodedWork = remainingWork) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_four
    [stateWork, stateResults, workTask, _workRemaining]

private theorem run_formulaRaisingMachineStep_tag_zero
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 0)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_one
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 1)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_two
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 2)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_three
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 3)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_four
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 4)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_five
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 5)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_six
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 6)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_seven
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 7)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_eight
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 8)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_nine
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 9)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_formulaRaisingMachineStep_tag_ten
    (state amount encodedWork results encodedTask remainingWork payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 10)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  rw [formulaRaisingStep_succ_work state amount encodedWork results
    stateWork stateResults]
  close_formula_raising_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]


set_option maxHeartbeats 3000000 in
theorem PRFunction.run_formulaRaisingMachineStep
    (state amount : Nat) :
    PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons state (NatVector.cons amount NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        state amount := by
  cases stateComponents : (natUnpairLeft state, natUnpairRight state) with
  | mk work results =>
      have stateWork : natUnpairLeft state = work :=
        congrArg Prod.fst stateComponents
      have stateResults : natUnpairRight state = results :=
        congrArg Prod.snd stateComponents
      cases work with
      | zero =>
          exact run_formulaRaisingMachineStep_zero_work
            state amount stateWork
      | succ encodedWork =>
          have stateWorkSucc :
              natUnpairLeft state = Nat.succ encodedWork := by
            rw [Nat.add_one] at stateWork
            exact stateWork
          cases workComponents :
              (natUnpairLeft encodedWork, natUnpairRight encodedWork) with
          | mk task remainingWork =>
              have workTask : natUnpairLeft encodedWork = task :=
                congrArg Prod.fst workComponents
              have workRemaining : natUnpairRight encodedWork = remainingWork :=
                congrArg Prod.snd workComponents
              cases task with
              | zero =>
                  exact run_formulaRaisingMachineStep_zero_task state amount
                    encodedWork results remainingWork stateWorkSucc stateResults
                    workTask workRemaining
              | succ encodedTask =>
                  have workTaskSucc :
                      natUnpairLeft encodedWork = Nat.succ encodedTask := by
                    rw [Nat.add_one] at workTask
                    exact workTask
                  cases taskComponents :
                      (natUnpairLeft encodedTask,
                        natUnpairRight encodedTask) with
                  | mk tag payload =>
                      have taskTag : natUnpairLeft encodedTask = tag :=
                        congrArg Prod.fst taskComponents
                      have taskPayload : natUnpairRight encodedTask = payload :=
                        congrArg Prod.snd taskComponents
                      cases tag with
                      | zero =>
                          exact run_formulaRaisingMachineStep_tag_zero state
                            amount encodedWork results encodedTask remainingWork
                            payload stateWorkSucc stateResults workTaskSucc
                            workRemaining taskTag taskPayload
                      | succ tag =>
                          cases tag with
                          | zero =>
                              exact run_formulaRaisingMachineStep_tag_one state
                                amount encodedWork results encodedTask remainingWork
                                payload stateWorkSucc stateResults workTaskSucc
                                workRemaining taskTag taskPayload
                          | succ tag =>
                              cases tag with
                              | zero =>
                                  exact run_formulaRaisingMachineStep_tag_two state
                                    amount encodedWork results encodedTask
                                    remainingWork payload stateWorkSucc stateResults
                                    workTaskSucc workRemaining taskTag taskPayload
                              | succ tag =>
                                  cases tag with
                                  | zero =>
                                      exact run_formulaRaisingMachineStep_tag_three
                                        state amount encodedWork results encodedTask
                                        remainingWork payload stateWorkSucc stateResults
                                        workTaskSucc workRemaining taskTag taskPayload
                                  | succ tag =>
                                      cases tag with
                                      | zero =>
                                          exact run_formulaRaisingMachineStep_tag_four
                                            state amount encodedWork results encodedTask
                                            remainingWork payload stateWorkSucc
                                            stateResults workTaskSucc workRemaining
                                            taskTag taskPayload
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact run_formulaRaisingMachineStep_tag_five
                                                state amount encodedWork results
                                                encodedTask remainingWork payload
                                                stateWorkSucc stateResults workTaskSucc
                                                workRemaining taskTag taskPayload
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact
                                                    run_formulaRaisingMachineStep_tag_six
                                                      state amount encodedWork results
                                                      encodedTask remainingWork payload
                                                      stateWorkSucc stateResults
                                                      workTaskSucc workRemaining taskTag
                                                      taskPayload
                                              | succ tag =>
                                                  cases tag with
                                                  | zero =>
                                                      exact
                                                        run_formulaRaisingMachineStep_tag_seven
                                                          state amount encodedWork results
                                                          encodedTask remainingWork payload
                                                          stateWorkSucc stateResults
                                                          workTaskSucc workRemaining taskTag
                                                          taskPayload
                                                  | succ tag =>
                                                      cases tag with
                                                      | zero =>
                                                          exact
                                                            run_formulaRaisingMachineStep_tag_eight
                                                              state amount encodedWork results
                                                              encodedTask remainingWork payload
                                                              stateWorkSucc stateResults
                                                              workTaskSucc workRemaining taskTag
                                                              taskPayload
                                                      | succ tag =>
                                                          cases tag with
                                                          | zero =>
                                                              exact
                                                                run_formulaRaisingMachineStep_tag_nine
                                                                  state amount encodedWork results
                                                                  encodedTask remainingWork payload
                                                                  stateWorkSucc stateResults
                                                                  workTaskSucc workRemaining taskTag
                                                                  taskPayload
                                                          | succ tag =>
                                                              cases tag with
                                                              | zero =>
                                                                  exact
                                                                    run_formulaRaisingMachineStep_tag_ten
                                                                      state amount encodedWork results
                                                                      encodedTask remainingWork payload
                                                                      stateWorkSucc stateResults
                                                                      workTaskSucc workRemaining taskTag
                                                                      taskPayload
                                                              | succ tag =>
                                                                  rw [formulaRaisingStep_succ_work
                                                                    state amount encodedWork results
                                                                    stateWorkSucc stateResults]
                                                                  close_formula_raising_branch_six
                                                                    [stateWorkSucc,
                                                                      stateResults,
                                                                      workTaskSucc,
                                                                      workRemaining,
                                                                      taskTag,
                                                                      taskPayload]

/-! ## Iteration and exported program -/

def PRFunction.formulaRaisingIterationArguments : PRFunctionVector 4 2 :=
  PRFunctionVector.cons
    (PRFunction.projection 4 1 raisingIndexOne_lt_four)
    (PRFunctionVector.singleton
      (PRFunction.projection 4 3 raisingIndexThree_lt_four))

def PRFunction.formulaRaisingIterationStep : PRFunction 4 :=
  PRFunction.composition PRFunction.formulaRaisingMachineStep
    PRFunction.formulaRaisingIterationArguments

def PRFunction.formulaRaisingMachineRun : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 raisingIndexZero_lt_two)
    PRFunction.formulaRaisingIterationStep

/-- Binary primitive-recursive program for formula raising. -/
def PRFunction.raiseFormulaCode : PRFunction 2 :=
  let code := PRFunction.projection 2 0 raisingIndexZero_lt_two
  let amount := PRFunction.projection 2 1 raisingIndexOne_lt_two
  let fuel := PRFunction.unaryIn PRFunction.double code
  let initial := PRFunction.unaryIn PRFunction.machineInitialState code
  let finalState := PRFunction.composition PRFunction.formulaRaisingMachineRun
    (PRFunctionVector.cons fuel
      (PRFunctionVector.cons initial (PRFunctionVector.singleton amount)))
  PRFunction.unaryIn PRFunction.machineStackHead
    (PRFunction.unaryIn PRFunction.unpairRight finalState)

@[simp] theorem PRFunction.run_formulaRaisingIterationArguments
    (counter previous state amount : Nat) :
    PRFunction.formulaRaisingIterationArguments.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons amount NatVector.nil)))) =
      NatVector.cons previous (NatVector.cons amount NatVector.nil) := by
  rfl

@[simp] theorem PRFunction.run_formulaRaisingIterationStep
    (counter previous state amount : Nat) :
    PRFunction.formulaRaisingIterationStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons amount NatVector.nil)))) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
        previous amount := by
  calc
    _ = PRFunction.formulaRaisingMachineStep.run
        (PRFunction.formulaRaisingIterationArguments.run
          (NatVector.cons counter
            (NatVector.cons previous
              (NatVector.cons state
                (NatVector.cons amount NatVector.nil))))) :=
      PRFunction.run_composition PRFunction.formulaRaisingMachineStep
        PRFunction.formulaRaisingIterationArguments _
    _ = PRFunction.formulaRaisingMachineStep.run
        (NatVector.cons previous (NatVector.cons amount NatVector.nil)) :=
      congrArg PRFunction.formulaRaisingMachineStep.run
        (PRFunction.run_formulaRaisingIterationArguments
          counter previous state amount)
    _ = _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
          previous amount :=
      PRFunction.run_formulaRaisingMachineStep previous amount

theorem PRFunction.run_formulaRaisingMachineRun
    (steps state amount : Nat) :
    PRFunction.formulaRaisingMachineRun.run
        (NatVector.cons steps
          (NatVector.cons state (NatVector.cons amount NatVector.nil))) =
      _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineRun
        steps state amount := by
  induction steps with
  | zero =>
      unfold PRFunction.formulaRaisingMachineRun
      rw [PRFunction.run_primitive_zero, PRFunction.run_projection]
      rfl
  | succ steps inductionHypothesis =>
      unfold PRFunction.formulaRaisingMachineRun
      rw [PRFunction.run_primitive_succ]
      rw [show
        (PRFunction.primitiveRecursion
          (PRFunction.projection 2 0 raisingIndexZero_lt_two)
          PRFunction.formulaRaisingIterationStep).run
            (NatVector.cons steps
              (NatVector.cons state
                (NatVector.cons amount NatVector.nil))) =
          PRFunction.formulaRaisingMachineRun.run
            (NatVector.cons steps
              (NatVector.cons state
                (NatVector.cons amount NatVector.nil))) from rfl]
      rw [PRFunction.run_formulaRaisingIterationStep, inductionHypothesis]
      rw [_root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineRun_add,
        _root_.RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineRun_one]

@[simp] theorem PRFunction.run_raiseFormulaCode
    (formulaCode amount : Nat) :
    PRFunction.raiseFormulaCode.run
        (NatVector.cons formulaCode
          (NatVector.cons amount NatVector.nil)) =
      machineRaiseFormulaCode formulaCode amount := by
  unfold PRFunction.raiseFormulaCode machineRaiseFormulaCode
  repeat first
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_double]
    | rw [PRFunction.run_machineInitialState]
    | rw [PRFunction.run_formulaRaisingMachineRun]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_machineStackHead]

theorem PRFunction.raiseFormulaCode_evaluates_code
    (formula : RawFormula)
    (amount : Nat) :
    PRFunction.Evaluates PRFunction.raiseFormulaCode
      (NatVector.cons formula.code
        (NatVector.cons amount NatVector.nil))
      (formula.raiseFreeVariables amount).code := by
  have evaluation := PRFunction.raiseFormulaCode.run_evaluates
    (NatVector.cons formula.code
      (NatVector.cons amount NatVector.nil))
  unfold PRFunction.Evaluates at evaluation ⊢
  rw [PRFunction.run_raiseFormulaCode,
    machineRaiseFormulaCode_code] at evaluation
  exact evaluation

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaRaisingProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_formulaRaisingProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaRaisingMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_formulaRaisingMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_formulaRaisingIterationStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_formulaRaisingMachineRun
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseFormulaCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseFormulaCode_evaluates_code
/- AXIOM_AUDIT_END -/
