import RelationalPerimeter.Instances.HeytingArithmetic.SubstitutionMachine

/-!
# Stack machine for raising free variables in coded formulas

The existing substitution machine already supplies the positive work stack,
result stack, formula dispatcher, constructor tasks, and exact structural
cost.  Raising changes only the variable branch of a term task.  At binder
depth `d`, indices below `d` remain bound and every other index is increased
by the requested amount.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! ## Syntactic operation implemented by the machine -/

/-- Renaming which raises precisely the variables free at the given depth. -/
def raisingRenamingAtDepth (amount : Nat) : Nat -> Renaming
  | 0 => fun index => index + amount
  | Nat.succ depth => liftRenaming (raisingRenamingAtDepth amount depth)

theorem raisingRenamingAtDepth_of_lt
    (amount depth index : Nat)
    (bounded : index < depth) :
    raisingRenamingAtDepth amount depth index = index := by
  induction depth generalizing index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change Nat.succ (raisingRenamingAtDepth amount depth index) =
            Nat.succ index
          exact congrArg Nat.succ
            (inductionHypothesis index (Nat.lt_of_succ_lt_succ bounded))

theorem raisingRenamingAtDepth_of_not_lt
    (amount depth index : Nat)
    (unbounded : index < depth -> False) :
    raisingRenamingAtDepth amount depth index = index + amount := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth inductionHypothesis =>
      cases index with
      | zero => exact (unbounded (Nat.zero_lt_succ depth)).elim
      | succ index =>
          change Nat.succ (raisingRenamingAtDepth amount depth index) =
            Nat.succ index + amount
          rw [inductionHypothesis index (fun bounded =>
            unbounded (Nat.succ_lt_succ bounded))]
          exact (Nat.succ_add index amount).symm.trans rfl

/-- Raise all free variables of a formula by an explicit amount. -/
def RawFormula.raiseFreeVariables
    (formula : RawFormula)
    (amount : Nat) : RawFormula :=
  formula.rename (raisingRenamingAtDepth amount 0)

private theorem binaryCongrConstructive
    {alpha beta gamma : Type}
    (operation : alpha -> beta -> gamma)
    {left₁ left₂ : alpha}
    {right₁ right₂ : beta}
    (leftEqual : left₁ = left₂)
    (rightEqual : right₁ = right₂) :
    operation left₁ right₁ = operation left₂ right₂ := by
  cases leftEqual
  cases rightEqual
  rfl

theorem RawTerm.rename_eq_of_pointwise
    (term : RawTerm)
    (left right : Renaming)
    (agree : (index : Nat) -> left index = right index) :
    term.rename left = term.rename right := by
  induction term with
  | bvar index => exact congrArg RawTerm.bvar (agree index)
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add first second firstHypothesis secondHypothesis =>
      exact binaryCongrConstructive RawTerm.add
        firstHypothesis secondHypothesis
  | mul first second firstHypothesis secondHypothesis =>
      exact binaryCongrConstructive RawTerm.mul
        firstHypothesis secondHypothesis

theorem RawFormula.rename_eq_of_pointwise
    (formula : RawFormula)
    (left right : Renaming)
    (agree : (index : Nat) -> left index = right index) :
    formula.rename left = formula.rename right := by
  induction formula generalizing left right with
  | falsum => rfl
  | equal first second =>
      exact binaryCongrConstructive RawFormula.equal
        (first.rename_eq_of_pointwise left right agree)
        (second.rename_eq_of_pointwise left right agree)
  | conj first second firstHypothesis secondHypothesis =>
      exact binaryCongrConstructive RawFormula.conj
        (firstHypothesis left right agree)
        (secondHypothesis left right agree)
  | disj first second firstHypothesis secondHypothesis =>
      exact binaryCongrConstructive RawFormula.disj
        (firstHypothesis left right agree)
        (secondHypothesis left right agree)
  | impl first second firstHypothesis secondHypothesis =>
      exact binaryCongrConstructive RawFormula.impl
        (firstHypothesis left right agree)
        (secondHypothesis left right agree)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis
      intro index
      cases index with
      | zero => rfl
      | succ index => exact congrArg Nat.succ (agree index)
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis
      intro index
      cases index with
      | zero => rfl
      | succ index => exact congrArg Nat.succ (agree index)

theorem RawFormula.raiseFreeVariables_one
    (formula : RawFormula) :
    formula.raiseFreeVariables 1 = formula.rename Nat.succ := by
  unfold RawFormula.raiseFreeVariables
  apply formula.rename_eq_of_pointwise
  intro index
  exact Nat.add_one index

/-! ## Numeric machine -/

/-- Custom term action for formula raising. -/
def formulaRaisingProcessTermStep
    (code depth work results amount : Nat) : Nat :=
  match code with
  | 0 => substitutionPushResult work results RawTerm.zero.code
  | Nat.succ encoded =>
      let tag := natUnpairLeft encoded
      let payload := natUnpairRight encoded
      match tag with
      | 0 =>
          if payload < depth then
            substitutionPushResult work results (RawTerm.bvar payload).code
          else
            substitutionPushResult work results
              (RawTerm.bvar (payload + amount)).code
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

/-- Only tag zero differs from the already verified substitution executor. -/
def formulaRaisingExecuteTask
    (task remainingWork results amount : Nat) : Nat :=
  match task with
  | 0 => substitutionMachineState remainingWork results
  | Nat.succ encodedTask =>
      if natUnpairLeft encodedTask = 0 then
        let payload := natUnpairRight encodedTask
        formulaRaisingProcessTermStep
          (natUnpairLeft payload)
          (natUnpairRight payload)
          remainingWork results amount
      else
        substitutionExecuteTask task remainingWork results amount

/-- Execute one raising task.  Completed states remain fixed. -/
def formulaRaisingMachineStep (state amount : Nat) : Nat :=
  let work := natUnpairLeft state
  let results := natUnpairRight state
  match work with
  | 0 => state
  | Nat.succ encodedWork =>
      formulaRaisingExecuteTask
        (natUnpairLeft encodedWork)
        (natUnpairRight encodedWork)
        results amount

def formulaRaisingMachineRun : Nat -> Nat -> Nat -> Nat
  | 0, state, _amount => state
  | Nat.succ steps, state, amount =>
      formulaRaisingMachineRun steps
        (formulaRaisingMachineStep state amount) amount

theorem formulaRaisingMachineRun_succ
    (steps state amount : Nat) :
    formulaRaisingMachineRun (Nat.succ steps) state amount =
      formulaRaisingMachineRun steps
        (formulaRaisingMachineStep state amount) amount := rfl

theorem formulaRaisingMachineRun_one (state amount : Nat) :
    formulaRaisingMachineRun 1 state amount =
      formulaRaisingMachineStep state amount := rfl

theorem formulaRaisingMachineRun_add
    (first second state amount : Nat) :
    formulaRaisingMachineRun (first + second) state amount =
      formulaRaisingMachineRun second
        (formulaRaisingMachineRun first state amount) amount := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add]
      change formulaRaisingMachineRun (first + second)
          (formulaRaisingMachineStep state amount) amount = _
      exact inductionHypothesis (formulaRaisingMachineStep state amount)

/-! ## Exact canonical task equations -/

theorem formulaRaisingMachineStep_pushedTask
    (task work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush task work) results) amount =
      formulaRaisingExecuteTask task work results amount := by
  unfold formulaRaisingMachineStep substitutionMachineState
    substitutionStackPush
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  change formulaRaisingExecuteTask
      (natUnpairLeft (natPair task work))
      (natUnpairRight (natPair task work)) results amount = _
  rw [natUnpairLeft_pair, natUnpairRight_pair]

theorem formulaRaisingMachineStep_processTermTask
    (code depth work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask code depth) work) results) amount =
      formulaRaisingProcessTermStep code depth work results amount := by
  rw [formulaRaisingMachineStep_pushedTask]
  unfold substitutionProcessTermTask substitutionTask
    formulaRaisingExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair, if_pos rfl,
    natUnpairLeft_pair, natUnpairRight_pair]

theorem formulaRaisingExecuteTask_positiveTag
    (tag payload work results amount : Nat)
    (positive : 0 < tag) :
    formulaRaisingExecuteTask (substitutionTask tag payload)
        work results amount =
      substitutionExecuteTask (substitutionTask tag payload)
        work results amount := by
  unfold substitutionTask formulaRaisingExecuteTask
  dsimp only
  rw [natUnpairLeft_pair]
  exact if_neg (Nat.ne_of_gt positive)

theorem formulaRaisingMachineStep_positiveTask
    (tag payload work results amount : Nat)
    (positive : 0 < tag) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush (substitutionTask tag payload) work)
          results) amount =
      substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush (substitutionTask tag payload) work)
          results) amount := by
  rw [formulaRaisingMachineStep_pushedTask,
    substitutionMachineStep_pushedTask]
  exact formulaRaisingExecuteTask_positiveTag
    tag payload work results amount positive

theorem formulaRaisingMachineStep_processFormulaTask
    (code depth work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask code depth) work) results) amount =
      substitutionProcessFormulaStep code depth work results amount := by
  unfold substitutionProcessFormulaTask
  rw [formulaRaisingMachineStep_positiveTask 1
    (natPair code depth) work results amount (Nat.zero_lt_succ 0)]
  exact substitutionMachineStep_processFormulaTask
    code depth work results amount

private theorem formulaRaisingMachineStep_buildTermSucc
    (child work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermSuccTask work)
          (substitutionStackPush child results)) amount =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 2 child)) results) := by
  unfold substitutionBuildTermSuccTask
  rw [formulaRaisingMachineStep_positiveTask 2 0 work
    (substitutionStackPush child results) amount (Nat.zero_lt_succ 1)]
  exact substitutionMachineStep_buildTermSucc child work results amount

private theorem formulaRaisingMachineStep_buildTermAdd
    (left right work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermAddTask work)
          (substitutionStackPush right (substitutionStackPush left results)))
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 3 (natPair left right))) results) := by
  unfold substitutionBuildTermAddTask
  rw [formulaRaisingMachineStep_positiveTask 3 0 work
    (substitutionStackPush right (substitutionStackPush left results)) amount
    (Nat.zero_lt_succ 2)]
  exact substitutionMachineStep_buildTermAdd left right work results amount

private theorem formulaRaisingMachineStep_buildTermMul
    (left right work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermMulTask work)
          (substitutionStackPush right (substitutionStackPush left results)))
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 4 (natPair left right))) results) := by
  unfold substitutionBuildTermMulTask
  rw [formulaRaisingMachineStep_positiveTask 4 0 work
    (substitutionStackPush right (substitutionStackPush left results)) amount
    (Nat.zero_lt_succ 3)]
  exact substitutionMachineStep_buildTermMul left right work results amount

private theorem formulaRaisingMachineStep_buildFormulaEqual
    (left right work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaEqualTask work)
          (substitutionStackPush right (substitutionStackPush left results)))
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 1 (natPair left right))) results) := by
  unfold substitutionBuildFormulaEqualTask
  rw [formulaRaisingMachineStep_positiveTask 5 0 work
    (substitutionStackPush right (substitutionStackPush left results)) amount
    (Nat.zero_lt_succ 4)]
  exact substitutionMachineStep_buildFormulaEqual left right work results amount

private theorem formulaRaisingMachineStep_buildFormulaConj
    (left right work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaConjTask work)
          (substitutionStackPush right (substitutionStackPush left results)))
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 2 (natPair left right))) results) := by
  unfold substitutionBuildFormulaConjTask
  rw [formulaRaisingMachineStep_positiveTask 6 0 work
    (substitutionStackPush right (substitutionStackPush left results)) amount
    (Nat.zero_lt_succ 5)]
  exact substitutionMachineStep_buildFormulaConj left right work results amount

private theorem formulaRaisingMachineStep_buildFormulaDisj
    (left right work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaDisjTask work)
          (substitutionStackPush right (substitutionStackPush left results)))
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 3 (natPair left right))) results) := by
  unfold substitutionBuildFormulaDisjTask
  rw [formulaRaisingMachineStep_positiveTask 7 0 work
    (substitutionStackPush right (substitutionStackPush left results)) amount
    (Nat.zero_lt_succ 6)]
  exact substitutionMachineStep_buildFormulaDisj left right work results amount

private theorem formulaRaisingMachineStep_buildFormulaImpl
    (left right work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaImplTask work)
          (substitutionStackPush right (substitutionStackPush left results)))
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 4 (natPair left right))) results) := by
  unfold substitutionBuildFormulaImplTask
  rw [formulaRaisingMachineStep_positiveTask 8 0 work
    (substitutionStackPush right (substitutionStackPush left results)) amount
    (Nat.zero_lt_succ 7)]
  exact substitutionMachineStep_buildFormulaImpl left right work results amount

private theorem formulaRaisingMachineStep_buildFormulaAll
    (body work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaAllTask work)
          (substitutionStackPush body results)) amount =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 5 body)) results) := by
  unfold substitutionBuildFormulaAllTask
  rw [formulaRaisingMachineStep_positiveTask 9 0 work
    (substitutionStackPush body results) amount (Nat.zero_lt_succ 8)]
  exact substitutionMachineStep_buildFormulaAll body work results amount

private theorem formulaRaisingMachineStep_buildFormulaEx
    (body work results amount : Nat) :
    formulaRaisingMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaExTask work)
          (substitutionStackPush body results)) amount =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 6 body)) results) := by
  unfold substitutionBuildFormulaExTask
  rw [formulaRaisingMachineStep_positiveTask 10 0 work
    (substitutionStackPush body results) amount (Nat.zero_lt_succ 9)]
  exact substitutionMachineStep_buildFormulaEx body work results amount

/-! ## Structural correctness -/

theorem RawTerm.formulaRaisingMachineRun_correct
    (term : RawTerm)
    (depth work results amount : Nat) :
    formulaRaisingMachineRun term.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask term.code depth) work) results)
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (term.rename (raisingRenamingAtDepth amount depth)).code results) := by
  induction term generalizing depth work results with
  | bvar index =>
      rw [RawTerm.substitutionCost, formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_processTermTask]
      simp only [formulaRaisingProcessTermStep, RawTerm.code,
        RawTerm.rename, natUnpairLeft_pair, natUnpairRight_pair]
      by_cases bounded : index < depth
      · rw [if_pos bounded,
          raisingRenamingAtDepth_of_lt amount depth index bounded]
        rfl
      · rw [if_neg bounded,
          raisingRenamingAtDepth_of_not_lt amount depth index bounded]
        rfl
  | zero =>
      rw [RawTerm.substitutionCost, formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_processTermTask]
      rfl
  | succ body inductionHypothesis =>
      rw [RawTerm.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processTermTask]
      simp only [formulaRaisingProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [formulaRaisingMachineRun_add,
        inductionHypothesis depth
          (substitutionStackPush substitutionBuildTermSuccTask work) results,
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildTermSucc]
      rfl
  | add left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processTermTask]
      simp only [formulaRaisingProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, formulaRaisingMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessTermTask right.code depth)
            (substitutionStackPush substitutionBuildTermAddTask work)) results,
        formulaRaisingMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildTermAddTask work),
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildTermAdd]
      rfl
  | mul left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processTermTask]
      simp only [formulaRaisingProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, formulaRaisingMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessTermTask right.code depth)
            (substitutionStackPush substitutionBuildTermMulTask work)) results,
        formulaRaisingMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildTermMulTask work),
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildTermMul]
      rfl

theorem RawFormula.formulaRaisingMachineRun_correct
    (formula : RawFormula)
    (depth work results amount : Nat) :
    formulaRaisingMachineRun formula.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask formula.code depth) work) results)
        amount =
      substitutionMachineState work
        (substitutionStackPush
          (formula.rename (raisingRenamingAtDepth amount depth)).code results) := by
  induction formula generalizing depth work results with
  | falsum =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_processFormulaTask]
      rfl
  | equal left right =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, formulaRaisingMachineRun_add left.substitutionCost,
        left.formulaRaisingMachineRun_correct depth
          (substitutionStackPush
            (substitutionProcessTermTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaEqualTask work)) results,
        formulaRaisingMachineRun_add right.substitutionCost 1,
        right.formulaRaisingMachineRun_correct depth
          (substitutionStackPush substitutionBuildFormulaEqualTask work),
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildFormulaEqual]
      rfl
  | conj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, formulaRaisingMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessFormulaTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaConjTask work)) results,
        formulaRaisingMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildFormulaConjTask work),
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildFormulaConj]
      rfl
  | disj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, formulaRaisingMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessFormulaTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaDisjTask work)) results,
        formulaRaisingMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildFormulaDisjTask work),
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildFormulaDisj]
      rfl
  | impl left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, formulaRaisingMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessFormulaTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaImplTask work)) results,
        formulaRaisingMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildFormulaImplTask work),
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildFormulaImpl]
      rfl
  | all body inductionHypothesis =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [formulaRaisingMachineRun_add,
        inductionHypothesis (Nat.succ depth)
          (substitutionStackPush substitutionBuildFormulaAllTask work) results,
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildFormulaAll]
      rfl
  | ex body inductionHypothesis =>
      rw [RawFormula.substitutionCost, formulaRaisingMachineRun_succ,
        formulaRaisingMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [formulaRaisingMachineRun_add,
        inductionHypothesis (Nat.succ depth)
          (substitutionStackPush substitutionBuildFormulaExTask work) results,
        formulaRaisingMachineRun_one,
        formulaRaisingMachineStep_buildFormulaEx]
      rfl

theorem formulaRaisingMachineStep_completed
    (results amount : Nat) :
    formulaRaisingMachineStep (substitutionMachineState 0 results) amount =
      substitutionMachineState 0 results := by
  unfold formulaRaisingMachineStep substitutionMachineState
  rw [natUnpairLeft_pair, natUnpairRight_pair]

theorem formulaRaisingMachineRun_completed
    (steps results amount : Nat) :
    formulaRaisingMachineRun steps
        (substitutionMachineState 0 results) amount =
      substitutionMachineState 0 results := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change formulaRaisingMachineRun steps
        (formulaRaisingMachineStep
          (substitutionMachineState 0 results) amount) amount = _
      rw [formulaRaisingMachineStep_completed, inductionHypothesis]

/-- Total numeric implementation, before compilation to `PRFunction`. -/
def machineRaiseFormulaCode (formulaCode amount : Nat) : Nat :=
  substitutionStackHead
    (natUnpairRight
      (formulaRaisingMachineRun
        (natDouble formulaCode)
        (substitutionMachineInitialState formulaCode) amount))

theorem machineRaiseFormulaCode_code
    (formula : RawFormula)
    (amount : Nat) :
    machineRaiseFormulaCode formula.code amount =
      (formula.raiseFreeVariables amount).code := by
  cases natExistsEqAddOfLe formula.substitutionCost_le_doubleCode with
  | intro extra fuelEquality =>
      unfold machineRaiseFormulaCode RawFormula.raiseFreeVariables
      rw [fuelEquality, formulaRaisingMachineRun_add]
      have exactRun := formula.formulaRaisingMachineRun_correct
        0 0 0 amount
      unfold substitutionMachineInitialState at exactRun
      unfold substitutionMachineInitialState
      rw [exactRun, formulaRaisingMachineRun_completed]
      unfold substitutionMachineState
      rw [natUnpairRight_pair, substitutionStackHead_push]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.raiseFreeVariables
#print axioms RelationalPerimeter.HeytingArithmetic.formulaRaisingMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.formulaRaisingMachineRun_correct
#print axioms RelationalPerimeter.HeytingArithmetic.machineRaiseFormulaCode
#print axioms RelationalPerimeter.HeytingArithmetic.machineRaiseFormulaCode_code
/- AXIOM_AUDIT_END -/
