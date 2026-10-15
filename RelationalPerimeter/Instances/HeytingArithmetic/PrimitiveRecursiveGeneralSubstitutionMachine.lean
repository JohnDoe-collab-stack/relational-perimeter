import RelationalPerimeter.Instances.HeytingArithmetic.GeneralSubstitutionMachine
import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveSubstitutionMachine

/-!
# Positive program for general capture-avoiding instantiation

This module compiles `GeneralSubstitutionMachine` into the intrinsic
`PRFunction` language.  The formula dispatcher, stacks, and constructor
programs are reused from the verified numeral machine.  The term-variable
branch additionally performs numeric equality with the binder depth,
primitive-recursive predecessor, and the certified coded term raising.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

private theorem generalIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem generalIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem generalIndexOne_lt_four : 1 < 4 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 2)
private theorem generalIndexThree_lt_four : 3 < 4 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
private theorem generalIndexZero_lt_five : 0 < 5 := Nat.zero_lt_succ 4
private theorem generalIndexOne_lt_five : 1 < 5 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 3)
private theorem generalIndexTwo_lt_five : 2 < 5 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
private theorem generalIndexThree_lt_five : 3 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
private theorem generalIndexFour_lt_five : 4 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

/-! ## General term-processing program -/

def PRFunction.generalMachineProcessTermStep : PRFunction 5 :=
  let code := PRFunction.projection 5 0 generalIndexZero_lt_five
  let depth := PRFunction.projection 5 1 generalIndexOne_lt_five
  let work := PRFunction.projection 5 2 generalIndexTwo_lt_five
  let results := PRFunction.projection 5 3 generalIndexThree_lt_five
  let replacementCode :=
    PRFunction.projection 5 4 generalIndexFour_lt_five
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
  let loweredVariable := PRFunction.machinePushResultIn
    work results
    (PRFunction.unaryIn PRFunction.successor
      (PRFunction.binaryIn PRFunction.pair
        (PRFunction.constant 5 0)
        (PRFunction.unaryIn PRFunction.predecessor payload)))
  let raisedReplacement := PRFunction.machinePushResultIn
    work results
    (PRFunction.composition PRFunction.raiseTermCode
      (PRFunctionVector.cons replacementCode
        (PRFunctionVector.singleton depth)))
  let outsideBinder := PRFunction.select
    (PRFunction.binaryIn PRFunction.equalBit payload depth)
    loweredVariable raisedReplacement
  let variableBranch := PRFunction.select
    (PRFunction.binaryIn PRFunction.lessBit payload depth)
    outsideBinder boundVariable
  let zeroBranch := fallback
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
    (PRFunction.selectTag tag 1 zeroBranch
      (PRFunction.selectTag tag 2 unaryBranch
        (PRFunction.selectTag tag 3
          (binaryBranch substitutionBuildTermAddTask)
          (PRFunction.selectTag tag 4
            (binaryBranch substitutionBuildTermMulTask)
            fallback))))
  PRFunction.select code fallback nodeBranch

private theorem generalNatIfZero_zero (whenZero whenPositive : Nat) :
    natIfZero 0 whenZero whenPositive = whenZero := rfl

private theorem generalNatIfZero_succ
    (selector whenZero whenPositive : Nat) :
    natIfZero (Nat.succ selector) whenZero whenPositive = whenPositive := rfl

private theorem generalNatEqualBit_zero_zero : natEqualBit 0 0 = 1 := rfl

private theorem generalNatEqualBit_succ_zero (value : Nat) :
    natEqualBit (Nat.succ value) 0 = 0 := by
  unfold natEqualBit natIsZero
  rw [Nat.sub_zero, Nat.zero_sub, Nat.add_zero]

private theorem generalNatEqualBit_succ_succ (left right : Nat) :
    natEqualBit (Nat.succ left) (Nat.succ right) =
      natEqualBit left right := by
  unfold natEqualBit
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]

private theorem generalNatEqualBit_self (value : Nat) :
    natEqualBit value value = 1 := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [generalNatEqualBit_succ_succ, inductionHypothesis]

private theorem generalNatEqualBit_zero_of_ne
    {left right : Nat}
    (different : left = right -> False) :
    natEqualBit left right = 0 := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => exact (different rfl).elim
      | succ right => rfl
  | succ left inductionHypothesis =>
      cases right with
      | zero => exact generalNatEqualBit_succ_zero left
      | succ right =>
          rw [generalNatEqualBit_succ_succ]
          exact inductionHypothesis fun equality =>
            different (congrArg Nat.succ equality)

macro "normalize_general_term_program" : tactic =>
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
      | rw [PRFunction.run_equalBit]
      | rw [PRFunction.run_successor]
      | rw [PRFunction.run_pair])

macro "evaluate_general_current_tag" : tactic =>
  `(tactic|
    rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
      PRFunction.run_unaryIn, PRFunction.run_predecessor,
      PRFunction.run_projection, NatVector.get_cons_zero])

/-- The five-input positive program implements the general term step. -/
theorem PRFunction.run_generalMachineProcessTermStep
    (code depth work results replacementCode : Nat) :
    PRFunction.generalMachineProcessTermStep.run
        (NatVector.cons code
          (NatVector.cons depth
            (NatVector.cons work
              (NatVector.cons results
                (NatVector.cons replacementCode NatVector.nil))))) =
      generalSubstitutionProcessTermStep
        code depth work results replacementCode := by
  cases code with
  | zero =>
      rw [generalSubstitutionProcessTermStep.eq_1]
      unfold PRFunction.generalMachineProcessTermStep
      normalize_general_term_program
      rfl
  | succ encoded =>
      rw [generalSubstitutionProcessTermStep.eq_2]
      unfold PRFunction.generalMachineProcessTermStep
      dsimp only
      rw [PRFunction.run_select]
      rw [PRFunction.run_projection, NatVector.get_cons_zero]
      rw [generalNatIfZero_succ]
      change (PRFunction.selectTag _ 0 _ _).run _ = _
      rw [PRFunction.run_selectTag]
      evaluate_general_current_tag
      have predecessor : (Nat.succ encoded).pred = encoded := rfl
      rw [predecessor]
      cases tagValue : natUnpairLeft encoded with
      | zero =>
          rw [generalNatEqualBit_zero_zero, generalNatIfZero_succ]
          change (PRFunction.select _ _ _).run _ = _
          normalize_general_term_program
          rw [predecessor]
          by_cases bounded : natUnpairRight encoded < depth
          · rw [natLessBit_eq_one_of_lt bounded,
              generalNatIfZero_succ, if_pos bounded]
            rfl
          · rw [natLessBit_eq_zero_of_not_lt bounded,
              generalNatIfZero_zero, if_neg bounded]
            by_cases equal : natUnpairRight encoded = depth
            · have equalBit :
                  natEqualBit (natUnpairRight encoded) depth = 1 := by
                rw [equal]
                exact generalNatEqualBit_self depth
              rw [equalBit]
              rw [generalNatIfZero_succ, if_pos equal]
              rfl
            · rw [generalNatEqualBit_zero_of_ne equal]
              rw [generalNatIfZero_zero, if_neg equal]
              rfl
      | succ tag =>
          rw [generalNatEqualBit_succ_zero, generalNatIfZero_zero]
          cases tag with
          | zero =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_general_current_tag
              rw [predecessor, tagValue]
              rw [generalNatEqualBit_succ_succ,
                generalNatEqualBit_zero_zero, generalNatIfZero_succ]
              normalize_general_term_program
              rfl
          | succ tag =>
              change (PRFunction.selectTag _ 1 _ _).run _ = _
              rw [PRFunction.run_selectTag]
              evaluate_general_current_tag
              rw [predecessor, tagValue]
              rw [generalNatEqualBit_succ_succ,
                generalNatEqualBit_succ_zero, generalNatIfZero_zero]
              cases tag with
              | zero =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_general_current_tag
                  rw [predecessor, tagValue]
                  rw [generalNatEqualBit_succ_succ,
                    generalNatEqualBit_succ_succ,
                    generalNatEqualBit_zero_zero, generalNatIfZero_succ]
                  normalize_general_term_program
                  rfl
              | succ tag =>
                  change (PRFunction.selectTag _ 2 _ _).run _ = _
                  rw [PRFunction.run_selectTag]
                  evaluate_general_current_tag
                  rw [predecessor, tagValue]
                  rw [generalNatEqualBit_succ_succ,
                    generalNatEqualBit_succ_succ,
                    generalNatEqualBit_succ_zero, generalNatIfZero_zero]
                  cases tag with
                  | zero =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_general_current_tag
                      rw [predecessor, tagValue]
                      rw [generalNatEqualBit_succ_succ,
                        generalNatEqualBit_succ_succ,
                        generalNatEqualBit_succ_succ,
                        generalNatEqualBit_zero_zero, generalNatIfZero_succ]
                      normalize_general_term_program
                      rfl
                  | succ tag =>
                      change (PRFunction.selectTag _ 3 _ _).run _ = _
                      rw [PRFunction.run_selectTag]
                      evaluate_general_current_tag
                      rw [predecessor, tagValue]
                      rw [generalNatEqualBit_succ_succ,
                        generalNatEqualBit_succ_succ,
                        generalNatEqualBit_succ_succ,
                        generalNatEqualBit_succ_zero, generalNatIfZero_zero]
                      cases tag with
                      | zero =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_general_current_tag
                          rw [predecessor, tagValue]
                          rw [generalNatEqualBit_self,
                            generalNatIfZero_succ]
                          normalize_general_term_program
                          rfl
                      | succ tag =>
                          change (PRFunction.selectTag _ 4 _ _).run _ = _
                          rw [PRFunction.run_selectTag]
                          evaluate_general_current_tag
                          rw [predecessor, tagValue]
                          repeat rw [generalNatEqualBit_succ_succ]
                          rw [generalNatEqualBit_succ_zero,
                            generalNatIfZero_zero]
                          normalize_general_term_program
                          rfl

/-! ## Complete general dispatcher -/

/-- Embed the general term-processing program in a shared input context. -/
def PRFunction.generalMachineProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results replacementCode :
      PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.generalMachineProcessTermStep
    (PRFunctionVector.cons processCode
      (PRFunctionVector.cons processDepth
        (PRFunctionVector.cons remainingWork
          (PRFunctionVector.cons results
            (PRFunctionVector.singleton replacementCode)))))

def PRFunction.generalMachineStep : PRFunction 2 :=
  let state := PRFunction.projection 2 0 generalIndexZero_lt_two
  let replacementCode :=
    PRFunction.projection 2 1 generalIndexOne_lt_two
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
  let processTerm := PRFunction.generalMachineProcessTermDispatchIn
    processCode processDepth remainingWork results replacementCode
  let processFormula := PRFunction.machineProcessFormulaDispatchIn
    processCode processDepth remainingWork results replacementCode
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

@[simp] theorem PRFunction.run_generalMachineProcessTermDispatchIn
    {arity : Nat}
    (processCode processDepth remainingWork results replacementCode :
      PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.generalMachineProcessTermDispatchIn processCode processDepth
        remainingWork results replacementCode).run inputs =
      generalSubstitutionProcessTermStep
        (processCode.run inputs) (processDepth.run inputs)
        (remainingWork.run inputs) (results.run inputs)
        (replacementCode.run inputs) := by
  unfold PRFunction.generalMachineProcessTermDispatchIn
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_generalMachineProcessTermStep]

private theorem generalMachineStep_zero_work_clean
    (state replacementCode : Nat)
    (stateWork : natUnpairLeft state = 0) :
    generalSubstitutionMachineStep state replacementCode = state := by
  unfold generalSubstitutionMachineStep
  rw [stateWork]

private theorem generalMachineStep_succ_work_clean
    (state replacementCode encodedWork results : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results) :
    generalSubstitutionMachineStep state replacementCode =
      generalSubstitutionExecuteTask
        (natUnpairLeft encodedWork)
        (natUnpairRight encodedWork)
        results replacementCode := by
  unfold generalSubstitutionMachineStep
  rw [stateWork, stateResults]

macro "rewrite_general_machine_step_once" : tactic =>
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
    | rw [PRFunction.run_generalMachineProcessTermStep]
    | rw [PRFunction.run_machineProcessFormulaStep]
    | rw [PRFunction.run_generalMachineProcessTermDispatchIn]
    | rw [PRFunction.run_machineProcessFormulaDispatchIn]
    | rw [PRFunction.run_machineBuildUnaryIn]
    | rw [PRFunction.run_machineBuildBinaryIn]
    | rw [generalNatIfZero_zero]
    | rw [generalNatIfZero_succ]
    | rw [generalNatEqualBit_zero_zero]
    | rw [generalNatEqualBit_succ_zero]
    | rw [generalNatEqualBit_succ_succ]
    | rw [Nat.add_one]
    | rw [Nat.pred_succ]
    | rw [PRFunction.generalMachineStep]
    | rw [generalSubstitutionExecuteTask]
    | rw [substitutionExecuteTask]
    | rw [substitutionMachineState])

macro "close_general_machine_branch_one" "[" rule:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_general_machine_step_once
      | rw [($rule)]
      | rfl)

macro "close_general_machine_branch_four"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_general_machine_step_once
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rfl)

macro "close_general_machine_branch_six"
    "[" ruleOne:ident "," ruleTwo:ident "," ruleThree:ident ","
      ruleFour:ident "," ruleFive:ident "," ruleSix:ident "]" : tactic =>
  `(tactic|
    repeat
      first
      | rewrite_general_machine_step_once
      | rw [($ruleOne)]
      | rw [($ruleTwo)]
      | rw [($ruleThree)]
      | rw [($ruleFour)]
      | rw [($ruleFive)]
      | rw [($ruleSix)]
      | rfl)

private theorem run_generalMachineStep_zero_work_clean
    (state replacementCode : Nat)
    (stateWork : natUnpairLeft state = 0) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_zero_work_clean state replacementCode stateWork]
  close_general_machine_branch_one [stateWork]

private theorem run_generalMachineStep_zero_task_clean
    (state replacementCode encodedWork results remainingWork : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = 0)
    (_workRemaining : natUnpairRight encodedWork = remainingWork) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_four
    [stateWork, stateResults, workTask, _workRemaining]

private theorem run_generalMachineStep_tag_zero_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 0)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_one_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 1)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_two_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 2)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_three_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 3)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_four_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 4)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_five_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 5)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_six_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 6)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_seven_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 7)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_eight_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 8)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_nine_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 9)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]

private theorem run_generalMachineStep_tag_ten_clean
    (state replacementCode encodedWork results encodedTask remainingWork
      payload : Nat)
    (stateWork : natUnpairLeft state = Nat.succ encodedWork)
    (stateResults : natUnpairRight state = results)
    (workTask : natUnpairLeft encodedWork = Nat.succ encodedTask)
    (workRemaining : natUnpairRight encodedWork = remainingWork)
    (taskTag : natUnpairLeft encodedTask = 10)
    (taskPayload : natUnpairRight encodedTask = payload) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  rw [generalMachineStep_succ_work_clean state replacementCode encodedWork
    results stateWork stateResults]
  close_general_machine_branch_six
    [stateWork, stateResults, workTask, workRemaining, taskTag, taskPayload]


set_option maxHeartbeats 3000000 in
/-- The binary positive program implements one complete general machine step. -/
theorem PRFunction.run_generalMachineStep
    (state replacementCode : Nat) :
    PRFunction.generalMachineStep.run
        (NatVector.cons state
          (NatVector.cons replacementCode NatVector.nil)) =
      generalSubstitutionMachineStep state replacementCode := by
  cases stateComponents : (natUnpairLeft state, natUnpairRight state) with
  | mk work results =>
      have stateWork : natUnpairLeft state = work :=
        congrArg Prod.fst stateComponents
      have stateResults : natUnpairRight state = results :=
        congrArg Prod.snd stateComponents
      cases work with
      | zero =>
          exact run_generalMachineStep_zero_work_clean
            state replacementCode stateWork
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
                  exact run_generalMachineStep_zero_task_clean state
                    replacementCode encodedWork results remainingWork
                    stateWorkSucc stateResults workTask workRemaining
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
                          exact run_generalMachineStep_tag_zero_clean state
                            replacementCode encodedWork results encodedTask
                            remainingWork payload stateWorkSucc stateResults
                            workTaskSucc workRemaining taskTag taskPayload
                      | succ tag =>
                          cases tag with
                          | zero =>
                              exact run_generalMachineStep_tag_one_clean state
                                replacementCode encodedWork results encodedTask
                                remainingWork payload stateWorkSucc stateResults
                                workTaskSucc workRemaining taskTag taskPayload
                          | succ tag =>
                              cases tag with
                              | zero =>
                                  exact run_generalMachineStep_tag_two_clean state
                                    replacementCode encodedWork results encodedTask
                                    remainingWork payload stateWorkSucc stateResults
                                    workTaskSucc workRemaining taskTag taskPayload
                              | succ tag =>
                                  cases tag with
                                  | zero =>
                                      exact run_generalMachineStep_tag_three_clean
                                        state replacementCode encodedWork results
                                        encodedTask remainingWork payload stateWorkSucc
                                        stateResults workTaskSucc workRemaining taskTag
                                        taskPayload
                                  | succ tag =>
                                      cases tag with
                                      | zero =>
                                          exact run_generalMachineStep_tag_four_clean
                                            state replacementCode encodedWork results
                                            encodedTask remainingWork payload stateWorkSucc
                                            stateResults workTaskSucc workRemaining taskTag
                                            taskPayload
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact run_generalMachineStep_tag_five_clean
                                                state replacementCode encodedWork results
                                                encodedTask remainingWork payload
                                                stateWorkSucc stateResults workTaskSucc
                                                workRemaining taskTag taskPayload
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact run_generalMachineStep_tag_six_clean
                                                    state replacementCode encodedWork results
                                                    encodedTask remainingWork payload
                                                    stateWorkSucc stateResults workTaskSucc
                                                    workRemaining taskTag taskPayload
                                              | succ tag =>
                                                  cases tag with
                                                  | zero =>
                                                      exact
                                                        run_generalMachineStep_tag_seven_clean
                                                          state replacementCode encodedWork
                                                          results encodedTask remainingWork
                                                          payload stateWorkSucc stateResults
                                                          workTaskSucc workRemaining taskTag
                                                          taskPayload
                                                  | succ tag =>
                                                      cases tag with
                                                      | zero =>
                                                          exact
                                                            run_generalMachineStep_tag_eight_clean
                                                              state replacementCode encodedWork
                                                              results encodedTask remainingWork
                                                              payload stateWorkSucc stateResults
                                                              workTaskSucc workRemaining taskTag
                                                              taskPayload
                                                      | succ tag =>
                                                          cases tag with
                                                          | zero =>
                                                              exact
                                                                run_generalMachineStep_tag_nine_clean
                                                                  state replacementCode encodedWork
                                                                  results encodedTask remainingWork
                                                                  payload stateWorkSucc stateResults
                                                                  workTaskSucc workRemaining taskTag
                                                                  taskPayload
                                                          | succ tag =>
                                                              cases tag with
                                                              | zero =>
                                                                  exact
                                                                    run_generalMachineStep_tag_ten_clean
                                                                      state replacementCode
                                                                      encodedWork results encodedTask
                                                                      remainingWork payload stateWorkSucc
                                                                      stateResults workTaskSucc
                                                                      workRemaining taskTag taskPayload
                                                              | succ tag =>
                                                                  rw [generalMachineStep_succ_work_clean
                                                                    state replacementCode encodedWork
                                                                    results stateWorkSucc stateResults]
                                                                  close_general_machine_branch_six
                                                                    [stateWorkSucc, stateResults,
                                                                      workTaskSucc, workRemaining,
                                                                      taskTag, taskPayload]

/-! ## Iteration and exported instantiation program -/

def PRFunction.generalMachineIterationArguments : PRFunctionVector 4 2 :=
  PRFunctionVector.cons
    (PRFunction.projection 4 1 generalIndexOne_lt_four)
    (PRFunctionVector.singleton
      (PRFunction.projection 4 3 generalIndexThree_lt_four))

def PRFunction.generalMachineIterationStep : PRFunction 4 :=
  PRFunction.composition PRFunction.generalMachineStep
    PRFunction.generalMachineIterationArguments

def PRFunction.generalMachineRun : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 generalIndexZero_lt_two)
    PRFunction.generalMachineIterationStep

/-- Binary program for capture-avoiding formula instantiation by a term code. -/
def PRFunction.machineInstantiateTerm : PRFunction 2 :=
  let code := PRFunction.projection 2 0 generalIndexZero_lt_two
  let replacementCode :=
    PRFunction.projection 2 1 generalIndexOne_lt_two
  let fuel := PRFunction.unaryIn PRFunction.double code
  let initial := PRFunction.unaryIn PRFunction.machineInitialState code
  let finalState := PRFunction.composition PRFunction.generalMachineRun
    (PRFunctionVector.cons fuel
      (PRFunctionVector.cons initial
        (PRFunctionVector.singleton replacementCode)))
  PRFunction.unaryIn PRFunction.machineStackHead
    (PRFunction.unaryIn PRFunction.unpairRight finalState)

@[simp] theorem PRFunction.run_generalMachineIterationArguments
    (counter previous state replacementCode : Nat) :
    PRFunction.generalMachineIterationArguments.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons replacementCode NatVector.nil)))) =
      NatVector.cons previous
        (NatVector.cons replacementCode NatVector.nil) := by
  rfl

@[simp] theorem PRFunction.run_generalMachineIterationStep
    (counter previous state replacementCode : Nat) :
    PRFunction.generalMachineIterationStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons replacementCode NatVector.nil)))) =
      generalSubstitutionMachineStep previous replacementCode := by
  calc
    _ = PRFunction.generalMachineStep.run
        (PRFunction.generalMachineIterationArguments.run
          (NatVector.cons counter
            (NatVector.cons previous
              (NatVector.cons state
                (NatVector.cons replacementCode NatVector.nil))))) :=
      PRFunction.run_composition PRFunction.generalMachineStep
        PRFunction.generalMachineIterationArguments _
    _ = PRFunction.generalMachineStep.run
        (NatVector.cons previous
          (NatVector.cons replacementCode NatVector.nil)) :=
      congrArg PRFunction.generalMachineStep.run
        (PRFunction.run_generalMachineIterationArguments
          counter previous state replacementCode)
    _ = generalSubstitutionMachineStep previous replacementCode :=
      PRFunction.run_generalMachineStep previous replacementCode

/-- Primitive-recursion iteration is exactly the semantic general run. -/
theorem PRFunction.run_generalMachineRun
    (steps state replacementCode : Nat) :
    PRFunction.generalMachineRun.run
        (NatVector.cons steps
          (NatVector.cons state
            (NatVector.cons replacementCode NatVector.nil))) =
      generalSubstitutionMachineRun steps state replacementCode := by
  induction steps with
  | zero =>
      unfold PRFunction.generalMachineRun
      rw [PRFunction.run_primitive_zero, PRFunction.run_projection]
      rfl
  | succ steps inductionHypothesis =>
      unfold PRFunction.generalMachineRun
      rw [PRFunction.run_primitive_succ]
      rw [show
        (PRFunction.primitiveRecursion
          (PRFunction.projection 2 0 generalIndexZero_lt_two)
          PRFunction.generalMachineIterationStep).run
            (NatVector.cons steps
              (NatVector.cons state
                (NatVector.cons replacementCode NatVector.nil))) =
          PRFunction.generalMachineRun.run
            (NatVector.cons steps
              (NatVector.cons state
                (NatVector.cons replacementCode NatVector.nil))) from rfl]
      rw [PRFunction.run_generalMachineIterationStep, inductionHypothesis]
      rw [← generalSubstitutionMachineRun_one]
      exact
        (generalSubstitutionMachineRun_add
          steps 1 state replacementCode).symm

/-- The exported program computes the verified total numeric operation. -/
theorem PRFunction.run_machineInstantiateTerm
    (formulaCode replacementCode : Nat) :
    PRFunction.machineInstantiateTerm.run
        (NatVector.cons formulaCode
          (NatVector.cons replacementCode NatVector.nil)) =
      machineInstantiateTermCode formulaCode replacementCode := by
  unfold PRFunction.machineInstantiateTerm
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
    | rw [PRFunction.run_generalMachineRun]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_machineStackHead]
    | rfl

/-- Positive execution certificate on every genuine formula and term code. -/
theorem PRFunction.machineInstantiateTerm_evaluates_code
    (formula : RawFormula)
    (replacement : RawTerm) :
    PRFunction.Evaluates PRFunction.machineInstantiateTerm
        (NatVector.cons formula.code
          (NatVector.cons replacement.code NatVector.nil))
        (formula.instantiateTerm replacement).code := by
  have evaluation := PRFunction.machineInstantiateTerm.run_evaluates
    (NatVector.cons formula.code
      (NatVector.cons replacement.code NatVector.nil))
  rw [PRFunction.run_machineInstantiateTerm,
    machineInstantiateTermCode_code] at evaluation
  exact evaluation
end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.generalMachineProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_generalMachineProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.generalMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_generalMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.generalMachineRun
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_generalMachineRun
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineInstantiateTerm
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.machineInstantiateTerm_evaluates_code
/- AXIOM_AUDIT_END -/
