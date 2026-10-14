import RelationalPerimeter.Constitution.HeytingArithmetic.SubstitutionMachine
import RelationalPerimeter.Constitution.HeytingArithmetic.ProofCalculus

/-!
# Stack machine for replacement without scope contraction

The induction step replaces the newest ambient variable by its successor but
keeps every later ambient variable at the same index.  This is distinct from
ordinary instantiation, which removes one variable.  The machine below reuses
the verified positive task language and changes only the variable action.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def keepingScopeSubstitutionAtDepth : Nat -> Substitution
  | 0 => ScopedFormula.replaceNewestKeepingScopeSubstitution
  | Nat.succ depth => liftSubstitution (keepingScopeSubstitutionAtDepth depth)

theorem keepingScopeSubstitutionAtDepth_of_lt
    (depth index : Nat)
    (bounded : index < depth) :
    keepingScopeSubstitutionAtDepth depth index = RawTerm.bvar index := by
  induction depth generalizing index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change (keepingScopeSubstitutionAtDepth depth index).rename Nat.succ =
            RawTerm.bvar (Nat.succ index)
          rw [inductionHypothesis index (Nat.lt_of_succ_lt_succ bounded)]
          rfl

theorem keepingScopeSubstitutionAtDepth_at
    (depth : Nat) :
    keepingScopeSubstitutionAtDepth depth depth =
      RawTerm.succ (RawTerm.bvar depth) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change (keepingScopeSubstitutionAtDepth depth depth).rename Nat.succ =
        RawTerm.succ (RawTerm.bvar (Nat.succ depth))
      rw [inductionHypothesis]
      rfl

theorem keepingScopeSubstitutionAtDepth_after
    (depth offset : Nat) :
    keepingScopeSubstitutionAtDepth depth (depth + Nat.succ offset) =
      RawTerm.bvar (depth + Nat.succ offset) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [Nat.succ_add]
      change
        (keepingScopeSubstitutionAtDepth depth
          (depth + Nat.succ offset)).rename Nat.succ =
        RawTerm.bvar (Nat.succ (depth + Nat.succ offset))
      rw [inductionHypothesis]
      rfl

theorem keepingScopeSubstitutionAtDepth_of_gt
    (depth index : Nat)
    (above : depth < index) :
    keepingScopeSubstitutionAtDepth depth index = RawTerm.bvar index := by
  induction depth generalizing index with
  | zero =>
      cases index with
      | zero => exact (Nat.lt_irrefl 0 above).elim
      | succ index => rfl
  | succ depth inductionHypothesis =>
      cases index with
      | zero => exact (Nat.not_succ_le_zero depth (Nat.le_of_lt above)).elim
      | succ index =>
          change (keepingScopeSubstitutionAtDepth depth index).rename Nat.succ =
            RawTerm.bvar (Nat.succ index)
          rw [inductionHypothesis index (Nat.lt_of_succ_lt_succ above)]
          rfl

def keepingScopeProcessTermStep
    (code depth work results _parameter : Nat) : Nat :=
  match code with
  | 0 => substitutionPushResult work results RawTerm.zero.code
  | Nat.succ encoded =>
      let tag := natUnpairLeft encoded
      let payload := natUnpairRight encoded
      match tag with
      | 0 =>
          if payload < depth then
            substitutionPushResult work results (RawTerm.bvar payload).code
          else if payload = depth then
            substitutionPushResult work results
              (RawTerm.succ (RawTerm.bvar depth)).code
          else
            substitutionPushResult work results (RawTerm.bvar payload).code
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

def keepingScopeExecuteTask
    (task remainingWork results parameter : Nat) : Nat :=
  match task with
  | 0 => substitutionMachineState remainingWork results
  | Nat.succ encodedTask =>
      if natUnpairLeft encodedTask = 0 then
        let payload := natUnpairRight encodedTask
        keepingScopeProcessTermStep
          (natUnpairLeft payload) (natUnpairRight payload)
          remainingWork results parameter
      else
        substitutionExecuteTask task remainingWork results parameter

def keepingScopeMachineStep (state parameter : Nat) : Nat :=
  let work := natUnpairLeft state
  let results := natUnpairRight state
  match work with
  | 0 => state
  | Nat.succ encodedWork =>
      keepingScopeExecuteTask
        (natUnpairLeft encodedWork) (natUnpairRight encodedWork)
        results parameter

def keepingScopeMachineRun : Nat -> Nat -> Nat -> Nat
  | 0, state, _parameter => state
  | Nat.succ steps, state, parameter =>
      keepingScopeMachineRun steps
        (keepingScopeMachineStep state parameter) parameter

theorem keepingScopeMachineRun_succ
    (steps state parameter : Nat) :
    keepingScopeMachineRun (Nat.succ steps) state parameter =
      keepingScopeMachineRun steps
        (keepingScopeMachineStep state parameter) parameter := rfl

theorem keepingScopeMachineRun_one (state parameter : Nat) :
    keepingScopeMachineRun 1 state parameter =
      keepingScopeMachineStep state parameter := rfl

theorem keepingScopeMachineRun_add
    (first second state parameter : Nat) :
    keepingScopeMachineRun (first + second) state parameter =
      keepingScopeMachineRun second
        (keepingScopeMachineRun first state parameter) parameter := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add]
      change keepingScopeMachineRun (first + second)
        (keepingScopeMachineStep state parameter) parameter = _
      exact inductionHypothesis (keepingScopeMachineStep state parameter)

theorem keepingScopeMachineStep_pushedTask
    (task work results parameter : Nat) :
    keepingScopeMachineStep
        (substitutionMachineState (substitutionStackPush task work) results)
        parameter =
      keepingScopeExecuteTask task work results parameter := by
  unfold keepingScopeMachineStep substitutionMachineState
    substitutionStackPush
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  change keepingScopeExecuteTask
    (natUnpairLeft (natPair task work))
    (natUnpairRight (natPair task work)) results parameter = _
  rw [natUnpairLeft_pair, natUnpairRight_pair]

theorem keepingScopeMachineStep_processTermTask
    (code depth work results parameter : Nat) :
    keepingScopeMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask code depth) work) results) parameter =
      keepingScopeProcessTermStep code depth work results parameter := by
  rw [keepingScopeMachineStep_pushedTask]
  unfold substitutionProcessTermTask substitutionTask keepingScopeExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair, if_pos rfl,
    natUnpairLeft_pair, natUnpairRight_pair]

theorem keepingScopeExecuteTask_positiveTag
    (tag payload work results parameter : Nat)
    (positive : 0 < tag) :
    keepingScopeExecuteTask (substitutionTask tag payload)
        work results parameter =
      substitutionExecuteTask (substitutionTask tag payload)
        work results parameter := by
  unfold substitutionTask keepingScopeExecuteTask
  dsimp only
  rw [natUnpairLeft_pair]
  exact if_neg (Nat.ne_of_gt positive)

theorem keepingScopeMachineStep_positiveTask
    (tag payload work results parameter : Nat)
    (positive : 0 < tag) :
    keepingScopeMachineStep
        (substitutionMachineState
          (substitutionStackPush (substitutionTask tag payload) work) results)
        parameter =
      substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush (substitutionTask tag payload) work) results)
        parameter := by
  rw [keepingScopeMachineStep_pushedTask,
    substitutionMachineStep_pushedTask]
  exact keepingScopeExecuteTask_positiveTag
    tag payload work results parameter positive

theorem keepingScopeMachineStep_processFormulaTask
    (code depth work results parameter : Nat) :
    keepingScopeMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask code depth) work) results) parameter =
      substitutionProcessFormulaStep code depth work results parameter := by
  unfold substitutionProcessFormulaTask
  rw [keepingScopeMachineStep_positiveTask 1 (natPair code depth)
    work results parameter (Nat.zero_lt_succ 0)]
  exact substitutionMachineStep_processFormulaTask
    code depth work results parameter

/-! The exact recursive execution uses the already verified constructor tasks
    after each positive-tag equality. -/

theorem RawTerm.keepingScopeMachineRun_correct
    (term : RawTerm)
    (depth work results parameter : Nat) :
    keepingScopeMachineRun term.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask term.code depth) work) results)
        parameter =
      substitutionMachineState work
        (substitutionStackPush
          (term.substitute (keepingScopeSubstitutionAtDepth depth)).code
          results) := by
  induction term generalizing depth work results with
  | bvar index =>
      rw [RawTerm.substitutionCost, keepingScopeMachineRun_one,
        keepingScopeMachineStep_processTermTask]
      simp only [keepingScopeProcessTermStep, RawTerm.code,
        RawTerm.substitute, natUnpairLeft_pair, natUnpairRight_pair]
      by_cases below : index < depth
      · rw [if_pos below,
          keepingScopeSubstitutionAtDepth_of_lt depth index below]
        rfl
      · rw [if_neg below]
        by_cases equal : index = depth
        · rw [if_pos equal, equal,
            keepingScopeSubstitutionAtDepth_at depth]
          rfl
        · rw [if_neg equal]
          have above : depth < index := by
            exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt below) (Ne.symm equal)
          rw [keepingScopeSubstitutionAtDepth_of_gt depth index above]
          rfl
  | zero =>
      rw [RawTerm.substitutionCost, keepingScopeMachineRun_one,
        keepingScopeMachineStep_processTermTask]
      rfl
  | succ body inductionHypothesis =>
      rw [RawTerm.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processTermTask]
      simp only [keepingScopeProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [keepingScopeMachineRun_add,
        inductionHypothesis depth
          (substitutionStackPush substitutionBuildTermSuccTask work) results,
        keepingScopeMachineRun_one]
      unfold substitutionBuildTermSuccTask
      rw [keepingScopeMachineStep_positiveTask 2 0 work
        (substitutionStackPush
          ((body.substitute
            (keepingScopeSubstitutionAtDepth depth)).code) results)
        parameter (Nat.zero_lt_succ 1)]
      have built := substitutionMachineStep_buildTermSucc
        ((body.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildTermSuccTask at built
      rw [built]
      rfl
  | add left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processTermTask]
      simp only [keepingScopeProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, keepingScopeMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessTermTask right.code depth)
            (substitutionStackPush substitutionBuildTermAddTask work)) results,
        keepingScopeMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildTermAddTask work),
        keepingScopeMachineRun_one]
      unfold substitutionBuildTermAddTask
      rw [keepingScopeMachineStep_positiveTask 3 0 work
          (substitutionStackPush
            ((right.substitute
              (keepingScopeSubstitutionAtDepth depth)).code)
            (substitutionStackPush
              ((left.substitute
                (keepingScopeSubstitutionAtDepth depth)).code) results))
          parameter (Nat.zero_lt_succ 2)]
      have built := substitutionMachineStep_buildTermAdd
        ((left.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        ((right.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildTermAddTask at built
      rw [built]
      rfl
  | mul left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processTermTask]
      simp only [keepingScopeProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, keepingScopeMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessTermTask right.code depth)
            (substitutionStackPush substitutionBuildTermMulTask work)) results,
        keepingScopeMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildTermMulTask work),
        keepingScopeMachineRun_one]
      unfold substitutionBuildTermMulTask
      rw [keepingScopeMachineStep_positiveTask 4 0 work
          (substitutionStackPush
            ((right.substitute
              (keepingScopeSubstitutionAtDepth depth)).code)
            (substitutionStackPush
              ((left.substitute
                (keepingScopeSubstitutionAtDepth depth)).code) results))
          parameter (Nat.zero_lt_succ 3)]
      have built := substitutionMachineStep_buildTermMul
        ((left.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        ((right.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildTermMulTask at built
      rw [built]
      rfl

theorem RawFormula.keepingScopeMachineRun_correct
    (formula : RawFormula)
    (depth work results parameter : Nat) :
    keepingScopeMachineRun formula.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask formula.code depth) work) results)
        parameter =
      substitutionMachineState work
        (substitutionStackPush
          (formula.substitute (keepingScopeSubstitutionAtDepth depth)).code
          results) := by
  induction formula generalizing depth work results with
  | falsum =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_one,
        keepingScopeMachineStep_processFormulaTask]
      rfl
  | equal left right =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, keepingScopeMachineRun_add left.substitutionCost,
        left.keepingScopeMachineRun_correct depth
          (substitutionStackPush
            (substitutionProcessTermTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaEqualTask work)) results,
        keepingScopeMachineRun_add right.substitutionCost 1,
        right.keepingScopeMachineRun_correct depth
          (substitutionStackPush substitutionBuildFormulaEqualTask work),
        keepingScopeMachineRun_one]
      unfold substitutionBuildFormulaEqualTask
      rw [keepingScopeMachineStep_positiveTask 5 0 work
          (substitutionStackPush
            ((right.substitute
              (keepingScopeSubstitutionAtDepth depth)).code)
            (substitutionStackPush
              ((left.substitute
                (keepingScopeSubstitutionAtDepth depth)).code) results))
          parameter (Nat.zero_lt_succ 4)]
      have built := substitutionMachineStep_buildFormulaEqual
        ((left.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        ((right.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildFormulaEqualTask at built
      rw [built]
      rfl
  | conj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, keepingScopeMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessFormulaTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaConjTask work)) results,
        keepingScopeMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildFormulaConjTask work),
        keepingScopeMachineRun_one]
      unfold substitutionBuildFormulaConjTask
      rw [keepingScopeMachineStep_positiveTask 6 0 work
          (substitutionStackPush
            ((right.substitute
              (keepingScopeSubstitutionAtDepth depth)).code)
            (substitutionStackPush
              ((left.substitute
                (keepingScopeSubstitutionAtDepth depth)).code) results))
          parameter (Nat.zero_lt_succ 5)]
      have built := substitutionMachineStep_buildFormulaConj
        ((left.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        ((right.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildFormulaConjTask at built
      rw [built]
      rfl
  | disj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, keepingScopeMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessFormulaTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaDisjTask work)) results,
        keepingScopeMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildFormulaDisjTask work),
        keepingScopeMachineRun_one]
      unfold substitutionBuildFormulaDisjTask
      rw [keepingScopeMachineStep_positiveTask 7 0 work
          (substitutionStackPush
            ((right.substitute
              (keepingScopeSubstitutionAtDepth depth)).code)
            (substitutionStackPush
              ((left.substitute
                (keepingScopeSubstitutionAtDepth depth)).code) results))
          parameter (Nat.zero_lt_succ 6)]
      have built := substitutionMachineStep_buildFormulaDisj
        ((left.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        ((right.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildFormulaDisjTask at built
      rw [built]
      rfl
  | impl left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc, keepingScopeMachineRun_add left.substitutionCost,
        leftHypothesis depth
          (substitutionStackPush
            (substitutionProcessFormulaTask right.code depth)
            (substitutionStackPush substitutionBuildFormulaImplTask work)) results,
        keepingScopeMachineRun_add right.substitutionCost 1,
        rightHypothesis depth
          (substitutionStackPush substitutionBuildFormulaImplTask work),
        keepingScopeMachineRun_one]
      unfold substitutionBuildFormulaImplTask
      rw [keepingScopeMachineStep_positiveTask 8 0 work
          (substitutionStackPush
            ((right.substitute
              (keepingScopeSubstitutionAtDepth depth)).code)
            (substitutionStackPush
              ((left.substitute
                (keepingScopeSubstitutionAtDepth depth)).code) results))
          parameter (Nat.zero_lt_succ 7)]
      have built := substitutionMachineStep_buildFormulaImpl
        ((left.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        ((right.substitute (keepingScopeSubstitutionAtDepth depth)).code)
        work results parameter
      unfold substitutionBuildFormulaImplTask at built
      rw [built]
      rfl
  | all body inductionHypothesis =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [keepingScopeMachineRun_add,
        inductionHypothesis (Nat.succ depth)
          (substitutionStackPush substitutionBuildFormulaAllTask work) results,
        keepingScopeMachineRun_one]
      unfold substitutionBuildFormulaAllTask
      rw [keepingScopeMachineStep_positiveTask 9 0 work
          (substitutionStackPush
            ((body.substitute
              (keepingScopeSubstitutionAtDepth (Nat.succ depth))).code)
            results) parameter (Nat.zero_lt_succ 8)]
      have built := substitutionMachineStep_buildFormulaAll
        ((body.substitute
          (keepingScopeSubstitutionAtDepth (Nat.succ depth))).code)
        work results parameter
      unfold substitutionBuildFormulaAllTask at built
      rw [built]
      rfl
  | ex body inductionHypothesis =>
      rw [RawFormula.substitutionCost, keepingScopeMachineRun_succ,
        keepingScopeMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [keepingScopeMachineRun_add,
        inductionHypothesis (Nat.succ depth)
          (substitutionStackPush substitutionBuildFormulaExTask work) results,
        keepingScopeMachineRun_one]
      unfold substitutionBuildFormulaExTask
      rw [keepingScopeMachineStep_positiveTask 10 0 work
          (substitutionStackPush
            ((body.substitute
              (keepingScopeSubstitutionAtDepth (Nat.succ depth))).code)
            results) parameter (Nat.zero_lt_succ 9)]
      have built := substitutionMachineStep_buildFormulaEx
        ((body.substitute
          (keepingScopeSubstitutionAtDepth (Nat.succ depth))).code)
        work results parameter
      unfold substitutionBuildFormulaExTask at built
      rw [built]
      rfl

theorem keepingScopeMachineStep_completed
    (results parameter : Nat) :
    keepingScopeMachineStep (substitutionMachineState 0 results) parameter =
      substitutionMachineState 0 results := by
  unfold keepingScopeMachineStep substitutionMachineState
  rw [natUnpairLeft_pair, natUnpairRight_pair]

theorem keepingScopeMachineRun_completed
    (steps results parameter : Nat) :
    keepingScopeMachineRun steps
        (substitutionMachineState 0 results) parameter =
      substitutionMachineState 0 results := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change keepingScopeMachineRun steps
        (keepingScopeMachineStep
          (substitutionMachineState 0 results) parameter) parameter = _
      rw [keepingScopeMachineStep_completed, inductionHypothesis]

def machineSuccessorInstanceCode (formulaCode : Nat) : Nat :=
  substitutionStackHead
    (natUnpairRight
      (keepingScopeMachineRun (natDouble formulaCode)
        (substitutionMachineInitialState formulaCode) 0))

theorem machineSuccessorInstanceCode_code
    (formula : RawFormula) :
    machineSuccessorInstanceCode formula.code =
      (formula.substitute
        ScopedFormula.replaceNewestKeepingScopeSubstitution).code := by
  cases natExistsEqAddOfLe formula.substitutionCost_le_doubleCode with
  | intro extra fuelEquality =>
      unfold machineSuccessorInstanceCode
      rw [fuelEquality, keepingScopeMachineRun_add]
      have exactRun := formula.keepingScopeMachineRun_correct 0 0 0 0
      unfold keepingScopeSubstitutionAtDepth at exactRun
      unfold substitutionMachineInitialState
      rw [exactRun, keepingScopeMachineRun_completed]
      unfold substitutionMachineState
      rw [natUnpairRight_pair, substitutionStackHead_push]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.keepingScopeSubstitutionAtDepth
#print axioms RelationalPerimeter.HeytingArithmetic.keepingScopeProcessTermStep
#print axioms RelationalPerimeter.HeytingArithmetic.keepingScopeMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.keepingScopeMachineRun_correct
#print axioms RelationalPerimeter.HeytingArithmetic.machineSuccessorInstanceCode
#print axioms RelationalPerimeter.HeytingArithmetic.machineSuccessorInstanceCode_code
/- AXIOM_AUDIT_END -/
