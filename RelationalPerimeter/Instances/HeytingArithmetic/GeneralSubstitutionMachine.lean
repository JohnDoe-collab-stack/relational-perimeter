import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveTermRaising
import RelationalPerimeter.Instances.HeytingArithmetic.SubstitutionMachine

/-!
# Stack machine for general first-order instantiation

This machine reuses the positive stacks, tasks, constructor tasks, and exact
syntax costs of the numeral-substitution machine.  Only term-processing tag
zero is replaced.  At binder depth `d` it implements the exact De Bruijn law:

* indices below `d` remain bound;
* index `d` is replaced by the replacement term raised through `d` binders;
* indices above `d` are lowered by one.

All formula and build tasks are literally delegated to the already verified
machine operations.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! ## Constructive index separation -/

theorem natLtOfNotLtNotEq
    {index depth : Nat}
    (notBelow : index < depth -> False)
    (notEqual : index = depth -> False) :
    depth < index := by
  induction depth generalizing index with
  | zero =>
      cases index with
      | zero => exact (notEqual rfl).elim
      | succ index => exact Nat.zero_lt_succ index
  | succ depth inductionHypothesis =>
      cases index with
      | zero => exact (notBelow (Nat.zero_lt_succ depth)).elim
      | succ index =>
          exact Nat.succ_lt_succ
            (inductionHypothesis
              (fun below => notBelow (Nat.succ_lt_succ below))
              (fun equality => notEqual (congrArg Nat.succ equality)))

theorem termSubstitutionAtDepth_of_gt
    (replacement : RawTerm)
    (depth index : Nat)
    (greater : depth < index) :
    termSubstitutionAtDepth replacement depth index =
      RawTerm.bvar index.pred := by
  induction depth generalizing index with
  | zero =>
      cases index with
      | zero => exact (Nat.lt_irrefl 0 greater).elim
      | succ index => rfl
  | succ depth inductionHypothesis =>
      cases index with
      | zero => exact (Nat.not_lt_zero (Nat.succ depth) greater).elim
      | succ index =>
          have innerGreater : depth < index :=
            Nat.lt_of_succ_lt_succ greater
          cases index with
          | zero => exact (Nat.not_lt_zero depth innerGreater).elim
          | succ index =>
              change
                (termSubstitutionAtDepth replacement depth
                  (Nat.succ index)).rename Nat.succ =
                  RawTerm.bvar (Nat.succ index)
              rw [inductionHypothesis (Nat.succ index) innerGreater]
              rfl

/-! ## One general term task -/

/-- Process a term node using a genuine replacement-term code. -/
def generalSubstitutionProcessTermStep
    (code depth work results replacementCode : Nat) : Nat :=
  match code with
  | 0 => substitutionPushResult work results RawTerm.zero.code
  | Nat.succ encoded =>
      let tag := natUnpairLeft encoded
      let payload := natUnpairRight encoded
      match tag with
      | 0 =>
          if payload < depth then
            substitutionPushResult work results
              (RawTerm.bvar payload).code
          else if payload = depth then
            substitutionPushResult work results
              (PRFunction.raiseTermCode.run
                (NatVector.cons replacementCode
                  (NatVector.cons depth NatVector.nil)))
          else
            substitutionPushResult work results
              (RawTerm.bvar payload.pred).code
      | 1 => substitutionPushResult work results RawTerm.zero.code
      | 2 =>
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessTermTask payload depth)
              (substitutionStackPush substitutionBuildTermSuccTask work))
            results
      | 3 =>
          let left := natUnpairLeft payload
          let right := natUnpairRight payload
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessTermTask left depth)
              (substitutionStackPush
                (substitutionProcessTermTask right depth)
                (substitutionStackPush substitutionBuildTermAddTask work)))
            results
      | 4 =>
          let left := natUnpairLeft payload
          let right := natUnpairRight payload
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessTermTask left depth)
              (substitutionStackPush
                (substitutionProcessTermTask right depth)
                (substitutionStackPush substitutionBuildTermMulTask work)))
            results
      | _ => substitutionPushResult work results RawTerm.zero.code

/-!
Only process-term tasks have tag zero.  Every positive task tag is delegated
definitionally to the old executor, whose formula and build actions do not use
the numeral parameter.
-/
def generalSubstitutionExecuteTask
    (task remainingWork results replacementCode : Nat) : Nat :=
  match task with
  | 0 => substitutionMachineState remainingWork results
  | Nat.succ encodedTask =>
      if natUnpairLeft encodedTask = 0 then
        let payload := natUnpairRight encodedTask
        generalSubstitutionProcessTermStep
          (natUnpairLeft payload)
          (natUnpairRight payload)
          remainingWork results replacementCode
      else
        substitutionExecuteTask task remainingWork results replacementCode

/-- Execute one work-stack task; completed states remain fixed. -/
def generalSubstitutionMachineStep
    (state replacementCode : Nat) : Nat :=
  let work := natUnpairLeft state
  let results := natUnpairRight state
  match work with
  | 0 => state
  | Nat.succ encodedWork =>
      generalSubstitutionExecuteTask
        (natUnpairLeft encodedWork)
        (natUnpairRight encodedWork)
        results replacementCode

/-- Iterate the general substitution machine. -/
def generalSubstitutionMachineRun : Nat -> Nat -> Nat -> Nat
  | 0, state, _replacementCode => state
  | Nat.succ steps, state, replacementCode =>
      generalSubstitutionMachineRun steps
        (generalSubstitutionMachineStep state replacementCode)
        replacementCode

theorem generalSubstitutionMachineRun_succ
    (steps state replacementCode : Nat) :
    generalSubstitutionMachineRun (Nat.succ steps) state replacementCode =
      generalSubstitutionMachineRun steps
        (generalSubstitutionMachineStep state replacementCode)
        replacementCode := rfl

theorem generalSubstitutionMachineRun_one
    (state replacementCode : Nat) :
    generalSubstitutionMachineRun 1 state replacementCode =
      generalSubstitutionMachineStep state replacementCode := rfl

theorem generalSubstitutionMachineRun_add
    (first second state replacementCode : Nat) :
    generalSubstitutionMachineRun (first + second) state replacementCode =
      generalSubstitutionMachineRun second
        (generalSubstitutionMachineRun first state replacementCode)
        replacementCode := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add]
      change
        generalSubstitutionMachineRun (first + second)
            (generalSubstitutionMachineStep state replacementCode)
            replacementCode =
          generalSubstitutionMachineRun second
            (generalSubstitutionMachineRun first
              (generalSubstitutionMachineStep state replacementCode)
              replacementCode)
            replacementCode
      exact inductionHypothesis
        (generalSubstitutionMachineStep state replacementCode)

/-! ## Dispatch and delegation -/

theorem generalSubstitutionMachineStep_pushedTask
    (task work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush task work) results)
        replacementCode =
      generalSubstitutionExecuteTask task work results replacementCode := by
  unfold generalSubstitutionMachineStep substitutionMachineState
    substitutionStackPush
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  change
    generalSubstitutionExecuteTask
        (natUnpairLeft (natPair task work))
        (natUnpairRight (natPair task work))
        results replacementCode = _
  rw [natUnpairLeft_pair, natUnpairRight_pair]

theorem generalSubstitutionMachineStep_processTermTask
    (code depth work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask code depth) work)
          results)
        replacementCode =
      generalSubstitutionProcessTermStep
        code depth work results replacementCode := by
  rw [generalSubstitutionMachineStep_pushedTask]
  unfold substitutionProcessTermTask substitutionTask
    generalSubstitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  rw [if_pos rfl, natUnpairLeft_pair, natUnpairRight_pair]

theorem generalSubstitutionExecuteTask_positiveTag
    (tag payload work results replacementCode : Nat)
    (positive : 0 < tag) :
    generalSubstitutionExecuteTask
        (substitutionTask tag payload) work results replacementCode =
      substitutionExecuteTask
        (substitutionTask tag payload) work results replacementCode := by
  unfold substitutionTask generalSubstitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair]
  exact if_neg (Nat.ne_of_gt positive)

/-- Every positive-tag canonical task has exactly the old machine action. -/
theorem generalSubstitutionMachineStep_positiveTask
    (tag payload work results replacementCode : Nat)
    (positive : 0 < tag) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush (substitutionTask tag payload) work)
          results)
        replacementCode =
      substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush (substitutionTask tag payload) work)
          results)
        replacementCode := by
  rw [generalSubstitutionMachineStep_pushedTask,
    substitutionMachineStep_pushedTask]
  exact generalSubstitutionExecuteTask_positiveTag
    tag payload work results replacementCode positive

/-- Formula dispatch and all constructor tasks inherit the old exact actions. -/
theorem generalSubstitutionMachineStep_processFormulaTask
    (code depth work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask code depth) work)
          results)
        replacementCode =
      substitutionProcessFormulaStep
        code depth work results replacementCode :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      1 (natPair code depth) work results replacementCode
      (Nat.zero_lt_succ 0))
    (substitutionMachineStep_processFormulaTask
      code depth work results replacementCode)

theorem generalSubstitutionMachineStep_buildTermSucc
    (child work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermSuccTask work)
          (substitutionStackPush child results)) replacementCode =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 2 child)) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      2 0 work (substitutionStackPush child results) replacementCode
      (Nat.zero_lt_succ 1))
    (substitutionMachineStep_buildTermSucc
      child work results replacementCode)

theorem generalSubstitutionMachineStep_buildTermAdd
    (left right work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermAddTask work)
          (substitutionStackPush right
            (substitutionStackPush left results))) replacementCode =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 3 (natPair left right))) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      3 0 work
      (substitutionStackPush right (substitutionStackPush left results))
      replacementCode (Nat.zero_lt_succ 2))
    (substitutionMachineStep_buildTermAdd
      left right work results replacementCode)

theorem generalSubstitutionMachineStep_buildTermMul
    (left right work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermMulTask work)
          (substitutionStackPush right
            (substitutionStackPush left results))) replacementCode =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 4 (natPair left right))) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      4 0 work
      (substitutionStackPush right (substitutionStackPush left results))
      replacementCode (Nat.zero_lt_succ 3))
    (substitutionMachineStep_buildTermMul
      left right work results replacementCode)

theorem generalSubstitutionMachineStep_buildFormulaEqual
    (left right work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaEqualTask work)
          (substitutionStackPush right
            (substitutionStackPush left results))) replacementCode =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 1 (natPair left right))) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      5 0 work
      (substitutionStackPush right (substitutionStackPush left results))
      replacementCode (Nat.zero_lt_succ 4))
    (substitutionMachineStep_buildFormulaEqual
      left right work results replacementCode)

theorem generalSubstitutionMachineStep_buildFormulaConj
    (left right work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaConjTask work)
          (substitutionStackPush right
            (substitutionStackPush left results))) replacementCode =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 2 (natPair left right))) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      6 0 work
      (substitutionStackPush right (substitutionStackPush left results))
      replacementCode (Nat.zero_lt_succ 5))
    (substitutionMachineStep_buildFormulaConj
      left right work results replacementCode)

theorem generalSubstitutionMachineStep_buildFormulaDisj
    (left right work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaDisjTask work)
          (substitutionStackPush right
            (substitutionStackPush left results))) replacementCode =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 3 (natPair left right))) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      7 0 work
      (substitutionStackPush right (substitutionStackPush left results))
      replacementCode (Nat.zero_lt_succ 6))
    (substitutionMachineStep_buildFormulaDisj
      left right work results replacementCode)

theorem generalSubstitutionMachineStep_buildFormulaImpl
    (left right work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaImplTask work)
          (substitutionStackPush right
            (substitutionStackPush left results))) replacementCode =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 4 (natPair left right))) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      8 0 work
      (substitutionStackPush right (substitutionStackPush left results))
      replacementCode (Nat.zero_lt_succ 7))
    (substitutionMachineStep_buildFormulaImpl
      left right work results replacementCode)

theorem generalSubstitutionMachineStep_buildFormulaAll
    (body work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaAllTask work)
          (substitutionStackPush body results)) replacementCode =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 5 body)) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      9 0 work (substitutionStackPush body results)
      replacementCode (Nat.zero_lt_succ 8))
    (substitutionMachineStep_buildFormulaAll
      body work results replacementCode)

theorem generalSubstitutionMachineStep_buildFormulaEx
    (body work results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaExTask work)
          (substitutionStackPush body results)) replacementCode =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 6 body)) results) :=
  Eq.trans
    (generalSubstitutionMachineStep_positiveTask
      10 0 work (substitutionStackPush body results)
      replacementCode (Nat.zero_lt_succ 9))
    (substitutionMachineStep_buildFormulaEx
      body work results replacementCode)

/-! ## Exact syntax correctness -/

/-- One genuine term task consumes exactly its existing structural cost. -/
theorem RawTerm.generalSubstitutionMachineRun_correct
    (term replacement : RawTerm)
    (depth work results : Nat) :
    generalSubstitutionMachineRun term.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask term.code depth) work)
          results)
        replacement.code =
      substitutionMachineState work
        (substitutionStackPush
          (term.substitute
            (termSubstitutionAtDepth replacement depth)).code
          results) := by
  induction term generalizing depth work results with
  | bvar index =>
      rw [RawTerm.substitutionCost, generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_processTermTask]
      simp only [generalSubstitutionProcessTermStep, RawTerm.code,
        RawTerm.substitute, natUnpairLeft_pair, natUnpairRight_pair]
      by_cases bounded : index < depth
      · rw [if_pos bounded,
          termSubstitutionAtDepth_of_lt replacement depth index bounded]
        rfl
      · rw [if_neg bounded]
        by_cases equal : index = depth
        · rw [if_pos equal, equal,
            termSubstitutionAtDepth_at,
            PRFunction.raiseTermCode_run]
          rfl
        · rw [if_neg equal]
          have greater := natLtOfNotLtNotEq bounded equal
          rw [termSubstitutionAtDepth_of_gt
            replacement depth index greater]
          rfl
  | zero =>
      rw [RawTerm.substitutionCost, generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_processTermTask]
      simp only [generalSubstitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair]
      rfl
  | succ body inductionHypothesis =>
      rw [RawTerm.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processTermTask]
      simp only [generalSubstitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [generalSubstitutionMachineRun_add]
      rw [inductionHypothesis depth
        (substitutionStackPush substitutionBuildTermSuccTask work)
        results]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildTermSucc]
      rfl
  | add left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processTermTask]
      simp only [generalSubstitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [generalSubstitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessTermTask right.code depth)
          (substitutionStackPush substitutionBuildTermAddTask work))
        results]
      rw [generalSubstitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildTermAddTask work)]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildTermAdd]
      rfl
  | mul left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processTermTask]
      simp only [generalSubstitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [generalSubstitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessTermTask right.code depth)
          (substitutionStackPush substitutionBuildTermMulTask work))
        results]
      rw [generalSubstitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildTermMulTask work)]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildTermMul]
      rfl

/-- One genuine formula task consumes exactly its existing structural cost. -/
theorem RawFormula.generalSubstitutionMachineRun_correct
    (formula : RawFormula)
    (replacement : RawTerm)
    (depth work results : Nat) :
    generalSubstitutionMachineRun formula.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask formula.code depth) work)
          results)
        replacement.code =
      substitutionMachineState work
        (substitutionStackPush
          (formula.substitute
            (termSubstitutionAtDepth replacement depth)).code
          results) := by
  induction formula generalizing depth work results with
  | falsum =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair]
      rfl
  | equal left right =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [generalSubstitutionMachineRun_add left.substitutionCost]
      rw [left.generalSubstitutionMachineRun_correct replacement depth
        (substitutionStackPush
          (substitutionProcessTermTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaEqualTask work))
        results]
      rw [generalSubstitutionMachineRun_add right.substitutionCost 1]
      rw [right.generalSubstitutionMachineRun_correct replacement depth
        (substitutionStackPush substitutionBuildFormulaEqualTask work)]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildFormulaEqual]
      rfl
  | conj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [generalSubstitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessFormulaTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaConjTask work))
        results]
      rw [generalSubstitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildFormulaConjTask work)]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildFormulaConj]
      rfl
  | disj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [generalSubstitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessFormulaTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaDisjTask work))
        results]
      rw [generalSubstitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildFormulaDisjTask work)]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildFormulaDisj]
      rfl
  | impl left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [generalSubstitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessFormulaTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaImplTask work))
        results]
      rw [generalSubstitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildFormulaImplTask work)]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildFormulaImpl]
      rfl
  | all body inductionHypothesis =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [generalSubstitutionMachineRun_add]
      rw [inductionHypothesis (Nat.succ depth)
        (substitutionStackPush substitutionBuildFormulaAllTask work)
        results]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildFormulaAll]
      rfl
  | ex body inductionHypothesis =>
      rw [RawFormula.substitutionCost, generalSubstitutionMachineRun_succ]
      rw [generalSubstitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [generalSubstitutionMachineRun_add]
      rw [inductionHypothesis (Nat.succ depth)
        (substitutionStackPush substitutionBuildFormulaExTask work)
        results]
      rw [generalSubstitutionMachineRun_one]
      rw [generalSubstitutionMachineStep_buildFormulaEx]
      rfl

/-! ## Total code operation -/

theorem generalSubstitutionMachineStep_completed
    (results replacementCode : Nat) :
    generalSubstitutionMachineStep
        (substitutionMachineState 0 results) replacementCode =
      substitutionMachineState 0 results := by
  unfold generalSubstitutionMachineStep substitutionMachineState
  rw [natUnpairLeft_pair, natUnpairRight_pair]

theorem generalSubstitutionMachineRun_completed
    (steps results replacementCode : Nat) :
    generalSubstitutionMachineRun steps
        (substitutionMachineState 0 results) replacementCode =
      substitutionMachineState 0 results := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change
        generalSubstitutionMachineRun steps
          (generalSubstitutionMachineStep
            (substitutionMachineState 0 results) replacementCode)
          replacementCode = _
      rw [generalSubstitutionMachineStep_completed, inductionHypothesis]

/-- Total code-level instantiation computed with code-derived fuel. -/
def machineInstantiateTermCode
    (formulaCode replacementCode : Nat) : Nat :=
  substitutionStackHead
    (natUnpairRight
      (generalSubstitutionMachineRun
        (natDouble formulaCode)
        (substitutionMachineInitialState formulaCode)
        replacementCode))

/-- The machine computes general capture-avoiding formula instantiation. -/
theorem machineInstantiateTermCode_code
    (formula : RawFormula)
    (replacement : RawTerm) :
    machineInstantiateTermCode formula.code replacement.code =
      (formula.instantiateTerm replacement).code := by
  cases natExistsEqAddOfLe formula.substitutionCost_le_doubleCode with
  | intro extra fuelEquality =>
      unfold machineInstantiateTermCode
      rw [fuelEquality, generalSubstitutionMachineRun_add]
      have exactRun :=
        formula.generalSubstitutionMachineRun_correct replacement 0 0 0
      unfold RawFormula.instantiateTerm at *
      unfold substitutionMachineInitialState
      rw [exactRun, generalSubstitutionMachineRun_completed]
      unfold substitutionMachineState
      rw [natUnpairRight_pair, substitutionStackHead_push]
      rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.generalSubstitutionMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.generalSubstitutionMachineRun
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.generalSubstitutionMachineRun_correct
#print axioms RelationalPerimeter.HeytingArithmetic.machineInstantiateTermCode_code
/- AXIOM_AUDIT_END -/
