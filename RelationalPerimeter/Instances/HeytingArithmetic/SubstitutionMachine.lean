import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveCodeSubstitution

/-!
# Capture-avoiding substitution machine

The machine carries the current De Bruijn depth in every processing task.
Bound variables are therefore preserved and only free variables are replaced
by the quoted numeral.  Work and result stacks are positive prefix-pair codes;
no semantic oracle occurs in the machine state.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## Iterated lifted numeral substitution -/

/-- The constant numeral substitution lifted below `depth` binders. -/
def numeralSubstitutionAtDepth (value : Nat) : Nat -> Substitution
  | 0 => fun _index => RawTerm.numeral value
  | Nat.succ depth => liftSubstitution (numeralSubstitutionAtDepth value depth)

/-- Renaming does not change a closed numeral. -/
theorem RawTerm.numeral_rename_succ (value : Nat) :
    (RawTerm.numeral value).rename Nat.succ = RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change RawTerm.succ ((RawTerm.numeral value).rename Nat.succ) = _
      rw [inductionHypothesis]
      rw [Nat.add_one]
      rfl

/-- Below the current depth, the lifted substitution preserves bound indices. -/
theorem numeralSubstitutionAtDepth_of_lt
    (value depth index : Nat)
    (bounded : index < depth) :
    numeralSubstitutionAtDepth value depth index = RawTerm.bvar index := by
  induction depth generalizing index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            (numeralSubstitutionAtDepth value depth index).rename Nat.succ =
              RawTerm.bvar (Nat.succ index)
          rw [inductionHypothesis index (Nat.lt_of_succ_lt_succ bounded)]
          rfl

/-- At and above the current depth, every free index becomes the numeral. -/
theorem numeralSubstitutionAtDepth_of_not_lt
    (value depth index : Nat)
    (unbounded : index < depth -> False) :
    numeralSubstitutionAtDepth value depth index = RawTerm.numeral value := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth inductionHypothesis =>
      cases index with
      | zero => exact (unbounded (Nat.zero_lt_succ depth)).elim
      | succ index =>
          change
            (numeralSubstitutionAtDepth value depth index).rename Nat.succ =
              RawTerm.numeral value
          rw [inductionHypothesis index (fun bounded =>
            unbounded (Nat.succ_lt_succ bounded))]
          exact RawTerm.numeral_rename_succ value

/-- At depth zero this is exactly the public numeral instantiation. -/
theorem RawFormula.substitute_numeralAtDepth_zero
    (formula : RawFormula)
    (value : Nat) :
    formula.substitute (numeralSubstitutionAtDepth value 0) =
      formula.instantiateNumeral value :=
  rfl

/-! ## Positive numeric stacks, tasks, and states -/

/-- Positive stack cell; zero is reserved for the empty stack. -/
def substitutionStackPush (item stack : Nat) : Nat :=
  Nat.succ (natPair item stack)

/-- Total head and tail operations for a positive stack. -/
def substitutionStackHead : Nat -> Nat
  | 0 => 0
  | Nat.succ encoded => natUnpairLeft encoded

def substitutionStackTail : Nat -> Nat
  | 0 => 0
  | Nat.succ encoded => natUnpairRight encoded

theorem substitutionStackHead_push (item stack : Nat) :
    substitutionStackHead (substitutionStackPush item stack) = item :=
  natUnpairLeft_pair item stack

theorem substitutionStackTail_push (item stack : Nat) :
    substitutionStackTail (substitutionStackPush item stack) = stack :=
  natUnpairRight_pair item stack

/-- Task code with a positive outer marker. -/
def substitutionTask (tag payload : Nat) : Nat :=
  Nat.succ (natPair tag payload)

/-- Processing tasks carry `(syntaxCode, depth)`. -/
def substitutionProcessTermTask (code depth : Nat) : Nat :=
  substitutionTask 0 (natPair code depth)

def substitutionProcessFormulaTask (code depth : Nat) : Nat :=
  substitutionTask 1 (natPair code depth)

/-! Build-task tags. -/

def substitutionBuildTermSuccTask : Nat := substitutionTask 2 0
def substitutionBuildTermAddTask : Nat := substitutionTask 3 0
def substitutionBuildTermMulTask : Nat := substitutionTask 4 0
def substitutionBuildFormulaEqualTask : Nat := substitutionTask 5 0
def substitutionBuildFormulaConjTask : Nat := substitutionTask 6 0
def substitutionBuildFormulaDisjTask : Nat := substitutionTask 7 0
def substitutionBuildFormulaImplTask : Nat := substitutionTask 8 0
def substitutionBuildFormulaAllTask : Nat := substitutionTask 9 0
def substitutionBuildFormulaExTask : Nat := substitutionTask 10 0

/-- A machine state pairs its work and result stacks. -/
def substitutionMachineState (work results : Nat) : Nat :=
  natPair work results

/-- Initial state for substitution in a formula at the outermost depth. -/
def substitutionMachineInitialState (formulaCode : Nat) : Nat :=
  substitutionMachineState
    (substitutionStackPush
      (substitutionProcessFormulaTask formulaCode 0)
      0)
    0

/-! ## Numeric constructor actions -/

/-- Push one transformed code on the result stack. -/
def substitutionPushResult (work results result : Nat) : Nat :=
  substitutionMachineState work (substitutionStackPush result results)

/-- Rebuild a unary node from the top result. -/
def substitutionBuildUnary
    (tag work results : Nat) : Nat :=
  substitutionPushResult
    work
    (substitutionStackTail results)
    (Nat.succ
      (natPair tag (substitutionStackHead results)))

/-- Rebuild a binary node from the two top results, right child first. -/
def substitutionBuildBinary
    (tag work results : Nat) : Nat :=
  let right := substitutionStackHead results
  let afterRight := substitutionStackTail results
  let left := substitutionStackHead afterRight
  let afterLeft := substitutionStackTail afterRight
  substitutionPushResult
    work
    afterLeft
    (Nat.succ (natPair tag (natPair left right)))

/-! ## One deterministic machine step -/

/-- Process one raw term node, expanding children into work-stack tasks. -/
def substitutionProcessTermStep
    (code depth work results value : Nat) : Nat :=
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
          else
            substitutionPushResult work results
              (RawTerm.numeral value).code
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

/-- Process one raw formula node with the same explicit binder depth. -/
def substitutionProcessFormulaStep
    (code depth work results _value : Nat) : Nat :=
  match code with
  | 0 => substitutionPushResult work results RawFormula.falsum.code
  | Nat.succ encoded =>
      let tag := natUnpairLeft encoded
      let payload := natUnpairRight encoded
      match tag with
      | 0 => substitutionPushResult work results RawFormula.falsum.code
      | 1 =>
          let left := natUnpairLeft payload
          let right := natUnpairRight payload
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessTermTask left depth)
              (substitutionStackPush
                (substitutionProcessTermTask right depth)
                (substitutionStackPush substitutionBuildFormulaEqualTask work)))
            results
      | 2 =>
          let left := natUnpairLeft payload
          let right := natUnpairRight payload
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessFormulaTask left depth)
              (substitutionStackPush
                (substitutionProcessFormulaTask right depth)
                (substitutionStackPush substitutionBuildFormulaConjTask work)))
            results
      | 3 =>
          let left := natUnpairLeft payload
          let right := natUnpairRight payload
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessFormulaTask left depth)
              (substitutionStackPush
                (substitutionProcessFormulaTask right depth)
                (substitutionStackPush substitutionBuildFormulaDisjTask work)))
            results
      | 4 =>
          let left := natUnpairLeft payload
          let right := natUnpairRight payload
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessFormulaTask left depth)
              (substitutionStackPush
                (substitutionProcessFormulaTask right depth)
                (substitutionStackPush substitutionBuildFormulaImplTask work)))
            results
      | 5 =>
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessFormulaTask payload (Nat.succ depth))
              (substitutionStackPush substitutionBuildFormulaAllTask work))
            results
      | 6 =>
          substitutionMachineState
            (substitutionStackPush
              (substitutionProcessFormulaTask payload (Nat.succ depth))
              (substitutionStackPush substitutionBuildFormulaExTask work))
            results
      | _ => substitutionPushResult work results RawFormula.falsum.code

/-- Execute one already separated work-stack task. -/
def substitutionExecuteTask
    (task remainingWork results value : Nat) : Nat :=
  match task with
  | 0 => substitutionMachineState remainingWork results
  | Nat.succ encodedTask =>
      let tag := natUnpairLeft encodedTask
      let payload := natUnpairRight encodedTask
      match tag with
      | 0 =>
          substitutionProcessTermStep
            (natUnpairLeft payload)
            (natUnpairRight payload)
            remainingWork results value
      | 1 =>
          substitutionProcessFormulaStep
            (natUnpairLeft payload)
            (natUnpairRight payload)
            remainingWork results value
      | 2 => substitutionBuildUnary 2 remainingWork results
      | 3 => substitutionBuildBinary 3 remainingWork results
      | 4 => substitutionBuildBinary 4 remainingWork results
      | 5 => substitutionBuildBinary 1 remainingWork results
      | 6 => substitutionBuildBinary 2 remainingWork results
      | 7 => substitutionBuildBinary 3 remainingWork results
      | 8 => substitutionBuildBinary 4 remainingWork results
      | 9 => substitutionBuildUnary 5 remainingWork results
      | 10 => substitutionBuildUnary 6 remainingWork results
      | _ => substitutionMachineState remainingWork results

/-- Execute one work-stack task; completed states remain fixed. -/
def substitutionMachineStep (state value : Nat) : Nat :=
  let work := natUnpairLeft state
  let results := natUnpairRight state
  match work with
  | 0 => state
  | Nat.succ encodedWork =>
      substitutionExecuteTask
        (natUnpairLeft encodedWork)
        (natUnpairRight encodedWork)
        results value

/-- Iterate the deterministic machine for an explicit number of steps. -/
def substitutionMachineRun : Nat -> Nat -> Nat -> Nat
  | 0, state, _value => state
  | Nat.succ steps, state, value =>
      substitutionMachineRun steps
        (substitutionMachineStep state value)
        value

/-- One positive iteration exposes exactly one machine step. -/
theorem substitutionMachineRun_succ
    (steps state value : Nat) :
    substitutionMachineRun (Nat.succ steps) state value =
      substitutionMachineRun steps (substitutionMachineStep state value) value :=
  rfl

/-- A singleton run is one machine step. -/
theorem substitutionMachineRun_one (state value : Nat) :
    substitutionMachineRun 1 state value = substitutionMachineStep state value :=
  rfl

/-! ## Exact structural cost -/

def RawTerm.substitutionCost : RawTerm -> Nat
  | RawTerm.bvar _index => 1
  | RawTerm.zero => 1
  | RawTerm.succ body => Nat.succ (Nat.succ body.substitutionCost)
  | RawTerm.add left right =>
      Nat.succ (left.substitutionCost + right.substitutionCost + 1)
  | RawTerm.mul left right =>
      Nat.succ (left.substitutionCost + right.substitutionCost + 1)

def RawFormula.substitutionCost : RawFormula -> Nat
  | RawFormula.falsum => 1
  | RawFormula.equal left right =>
      Nat.succ (left.substitutionCost + right.substitutionCost + 1)
  | RawFormula.conj left right =>
      Nat.succ (left.substitutionCost + right.substitutionCost + 1)
  | RawFormula.disj left right =>
      Nat.succ (left.substitutionCost + right.substitutionCost + 1)
  | RawFormula.impl left right =>
      Nat.succ (left.substitutionCost + right.substitutionCost + 1)
  | RawFormula.all body => Nat.succ (Nat.succ body.substitutionCost)
  | RawFormula.ex body => Nat.succ (Nat.succ body.substitutionCost)

/-! ## Exact execution of canonical tasks -/

/-- A pushed task is separated from the two numeric stacks in one step. -/
theorem substitutionMachineStep_pushedTask
    (task work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState (substitutionStackPush task work) results)
        value =
      substitutionExecuteTask task work results value := by
  unfold substitutionMachineStep substitutionMachineState substitutionStackPush
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  change
    substitutionExecuteTask
        (natUnpairLeft (natPair task work))
        (natUnpairRight (natPair task work))
        results value =
      substitutionExecuteTask task work results value
  rw [natUnpairLeft_pair, natUnpairRight_pair]

/-- Splitting an iteration count executes the two blocks consecutively. -/
theorem substitutionMachineRun_add
    (first second state value : Nat) :
    substitutionMachineRun (first + second) state value =
      substitutionMachineRun second
        (substitutionMachineRun first state value)
        value := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add]
      change
        substitutionMachineRun (first + second)
            (substitutionMachineStep state value) value =
          substitutionMachineRun second
            (substitutionMachineRun first
              (substitutionMachineStep state value) value)
            value
      exact inductionHypothesis (substitutionMachineStep state value)

/-- A canonical term-processing task dispatches to the term step. -/
theorem substitutionMachineStep_processTermTask
    (code depth work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask code depth)
            work)
          results)
        value =
      substitutionProcessTermStep code depth work results value := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionProcessTermTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  rfl

/-- A canonical formula-processing task dispatches to the formula step. -/
theorem substitutionMachineStep_processFormulaTask
    (code depth work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask code depth)
            work)
          results)
        value =
      substitutionProcessFormulaStep code depth work results value := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionProcessFormulaTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  rfl

/-! Canonical build tasks, stated directly on their concrete result stacks. -/

theorem substitutionMachineStep_buildTermSucc
    (child work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermSuccTask work)
          (substitutionStackPush child results)) value =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 2 child)) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildTermSuccTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildUnary substitutionPushResult
  rw [substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildTermAdd
    (left right work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermAddTask work)
          (substitutionStackPush right (substitutionStackPush left results))) value =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 3 (natPair left right))) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildTermAddTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildBinary substitutionPushResult
  dsimp only
  rw [substitutionStackHead_push, substitutionStackTail_push,
    substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildTermMul
    (left right work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildTermMulTask work)
          (substitutionStackPush right (substitutionStackPush left results))) value =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 4 (natPair left right))) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildTermMulTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildBinary substitutionPushResult
  dsimp only
  rw [substitutionStackHead_push, substitutionStackTail_push,
    substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildFormulaEqual
    (left right work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaEqualTask work)
          (substitutionStackPush right (substitutionStackPush left results))) value =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 1 (natPair left right))) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildFormulaEqualTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildBinary substitutionPushResult
  dsimp only
  rw [substitutionStackHead_push, substitutionStackTail_push,
    substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildFormulaConj
    (left right work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaConjTask work)
          (substitutionStackPush right (substitutionStackPush left results))) value =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 2 (natPair left right))) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildFormulaConjTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildBinary substitutionPushResult
  dsimp only
  rw [substitutionStackHead_push, substitutionStackTail_push,
    substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildFormulaDisj
    (left right work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaDisjTask work)
          (substitutionStackPush right (substitutionStackPush left results))) value =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 3 (natPair left right))) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildFormulaDisjTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildBinary substitutionPushResult
  dsimp only
  rw [substitutionStackHead_push, substitutionStackTail_push,
    substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildFormulaImpl
    (left right work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaImplTask work)
          (substitutionStackPush right (substitutionStackPush left results))) value =
      substitutionMachineState work
        (substitutionStackPush
          (Nat.succ (natPair 4 (natPair left right))) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildFormulaImplTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildBinary substitutionPushResult
  dsimp only
  rw [substitutionStackHead_push, substitutionStackTail_push,
    substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildFormulaAll
    (body work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaAllTask work)
          (substitutionStackPush body results)) value =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 5 body)) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildFormulaAllTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildUnary substitutionPushResult
  rw [substitutionStackHead_push, substitutionStackTail_push]
  rfl

theorem substitutionMachineStep_buildFormulaEx
    (body work results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState
          (substitutionStackPush substitutionBuildFormulaExTask work)
          (substitutionStackPush body results)) value =
      substitutionMachineState work
        (substitutionStackPush (Nat.succ (natPair 6 body)) results) := by
  rw [substitutionMachineStep_pushedTask]
  unfold substitutionBuildFormulaExTask substitutionTask substitutionExecuteTask
  dsimp only
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  unfold substitutionBuildUnary substitutionPushResult
  rw [substitutionStackHead_push, substitutionStackTail_push]
  rfl

/-- One term task consumes exactly its structural cost. -/
theorem RawTerm.substitutionMachineRun_correct
    (term : RawTerm)
    (depth work results value : Nat) :
    substitutionMachineRun term.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessTermTask term.code depth)
            work)
          results)
        value =
      substitutionMachineState work
        (substitutionStackPush
          (term.substitute (numeralSubstitutionAtDepth value depth)).code
          results) := by
  induction term generalizing depth work results with
  | bvar index =>
      rw [RawTerm.substitutionCost, substitutionMachineRun_one]
      rw [substitutionMachineStep_processTermTask]
      simp only [substitutionProcessTermStep, RawTerm.code,
        RawTerm.substitute, natUnpairLeft_pair, natUnpairRight_pair]
      by_cases bounded : index < depth
      · rw [if_pos bounded,
          numeralSubstitutionAtDepth_of_lt value depth index bounded]
        rfl
      · rw [if_neg bounded,
          numeralSubstitutionAtDepth_of_not_lt value depth index bounded]
        rfl
  | zero =>
      rw [RawTerm.substitutionCost, substitutionMachineRun_one]
      rw [substitutionMachineStep_processTermTask]
      simp only [substitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair]
      rfl
  | succ body inductionHypothesis =>
      rw [RawTerm.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processTermTask]
      simp only [substitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [substitutionMachineRun_add]
      rw [inductionHypothesis depth
        (substitutionStackPush substitutionBuildTermSuccTask work)
        results]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildTermSucc]
      rfl
  | add left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processTermTask]
      simp only [substitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [substitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessTermTask right.code depth)
          (substitutionStackPush substitutionBuildTermAddTask work))
        results]
      rw [substitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildTermAddTask work)]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildTermAdd]
      rfl
  | mul left right leftHypothesis rightHypothesis =>
      rw [RawTerm.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processTermTask]
      simp only [substitutionProcessTermStep, RawTerm.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [substitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessTermTask right.code depth)
          (substitutionStackPush substitutionBuildTermMulTask work))
        results]
      rw [substitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildTermMulTask work)]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildTermMul]
      rfl

/-- One formula task consumes exactly its structural cost. -/
theorem RawFormula.substitutionMachineRun_correct
    (formula : RawFormula)
    (depth work results value : Nat) :
    substitutionMachineRun formula.substitutionCost
        (substitutionMachineState
          (substitutionStackPush
            (substitutionProcessFormulaTask formula.code depth)
            work)
          results)
        value =
      substitutionMachineState work
        (substitutionStackPush
          (formula.substitute
            (numeralSubstitutionAtDepth value depth)).code
          results) := by
  induction formula generalizing depth work results with
  | falsum =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_one]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair]
      rfl
  | equal left right =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [substitutionMachineRun_add left.substitutionCost]
      rw [left.substitutionMachineRun_correct depth
        (substitutionStackPush
          (substitutionProcessTermTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaEqualTask work))
        results]
      rw [substitutionMachineRun_add right.substitutionCost 1]
      rw [right.substitutionMachineRun_correct depth
        (substitutionStackPush substitutionBuildFormulaEqualTask work)]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildFormulaEqual]
      rfl
  | conj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [substitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessFormulaTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaConjTask work))
        results]
      rw [substitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildFormulaConjTask work)]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildFormulaConj]
      rfl
  | disj left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [substitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessFormulaTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaDisjTask work))
        results]
      rw [substitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildFormulaDisjTask work)]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildFormulaDisj]
      rfl
  | impl left right leftHypothesis rightHypothesis =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [Nat.add_assoc]
      rw [substitutionMachineRun_add left.substitutionCost]
      rw [leftHypothesis depth
        (substitutionStackPush
          (substitutionProcessFormulaTask right.code depth)
          (substitutionStackPush substitutionBuildFormulaImplTask work))
        results]
      rw [substitutionMachineRun_add right.substitutionCost 1]
      rw [rightHypothesis depth
        (substitutionStackPush substitutionBuildFormulaImplTask work)]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildFormulaImpl]
      rfl
  | all body inductionHypothesis =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [substitutionMachineRun_add]
      rw [inductionHypothesis (Nat.succ depth)
        (substitutionStackPush substitutionBuildFormulaAllTask work)
        results]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildFormulaAll]
      rfl
  | ex body inductionHypothesis =>
      rw [RawFormula.substitutionCost, substitutionMachineRun_succ]
      rw [substitutionMachineStep_processFormulaTask]
      simp only [substitutionProcessFormulaStep, RawFormula.code,
        natUnpairLeft_pair, natUnpairRight_pair]
      rw [substitutionMachineRun_add]
      rw [inductionHypothesis (Nat.succ depth)
        (substitutionStackPush substitutionBuildFormulaExTask work)
        results]
      rw [substitutionMachineRun_one]
      rw [substitutionMachineStep_buildFormulaEx]
      rfl

/-! ## A code-computable uniform fuel bound -/

/-- Prefix pairing dominates the sum of its two components. -/
theorem nat_add_le_natPair (left right : Nat) :
    left + right <= natPair left right := by
  induction left with
  | zero =>
      rw [Nat.zero_add]
      exact nat_le_natDouble right
  | succ left inductionHypothesis =>
      rw [Nat.succ_add]
      change Nat.succ (left + right) <=
        Nat.succ (natDouble (natPair left right))
      exact Nat.succ_le_succ
        (Nat.le_trans inductionHypothesis
          (nat_le_natDouble (natPair left right)))

/-- Structural doubling is monotone. -/
theorem natDouble_mono
    {left right : Nat}
    (bounded : left <= right) :
    natDouble left <= natDouble right := by
  rw [← nat_add_self_eq_natDouble, ← nat_add_self_eq_natDouble]
  exact Nat.add_le_add bounded bounded

/-- A positive pairing tag places the successor of its payload below the pair. -/
theorem nat_succ_le_natPair_succ (tag payload : Nat) :
    Nat.succ payload <= natPair (Nat.succ tag) payload := by
  change Nat.succ payload <= Nat.succ (natDouble (natPair tag payload))
  exact Nat.succ_le_succ
    (Nat.le_trans (natPair_right_le tag payload)
      (nat_le_natDouble (natPair tag payload)))

/-- Every term task costs at most its own positive syntax code. -/
theorem RawTerm.substitutionCost_le_code (term : RawTerm) :
    term.substitutionCost <= term.code := by
  induction term with
  | bvar index =>
      change 1 <= Nat.succ (natPair 0 index)
      exact Nat.succ_le_succ (Nat.zero_le (natPair 0 index))
  | zero =>
      change 1 <= Nat.succ (natPair 1 0)
      exact Nat.succ_le_succ (Nat.zero_le (natPair 1 0))
  | succ body inductionHypothesis =>
      change Nat.succ (Nat.succ body.substitutionCost) <=
        Nat.succ (natPair 2 body.code)
      apply Nat.succ_le_succ
      exact Nat.le_trans (Nat.succ_le_succ inductionHypothesis)
        (nat_succ_le_natPair_succ 1 body.code)
  | add left right leftHypothesis rightHypothesis =>
      have childrenPacking :
          left.code + right.code <= natPair left.code right.code :=
        nat_add_le_natPair left.code right.code
      change Nat.succ
          (left.substitutionCost + right.substitutionCost + 1) <=
        Nat.succ (natPair 3 (natPair left.code right.code))
      apply Nat.succ_le_succ
      rw [Nat.add_one]
      exact Nat.le_trans
        (Nat.succ_le_succ
          (Nat.le_trans
            (Nat.add_le_add leftHypothesis rightHypothesis)
            childrenPacking))
        (nat_succ_le_natPair_succ 2 (natPair left.code right.code))
  | mul left right leftHypothesis rightHypothesis =>
      have childrenPacking :
          left.code + right.code <= natPair left.code right.code :=
        nat_add_le_natPair left.code right.code
      change Nat.succ
          (left.substitutionCost + right.substitutionCost + 1) <=
        Nat.succ (natPair 4 (natPair left.code right.code))
      apply Nat.succ_le_succ
      rw [Nat.add_one]
      exact Nat.le_trans
        (Nat.succ_le_succ
          (Nat.le_trans
            (Nat.add_le_add leftHypothesis rightHypothesis)
            childrenPacking))
        (nat_succ_le_natPair_succ 3 (natPair left.code right.code))

/-- Every formula task costs at most its own positive syntax code. -/
theorem RawFormula.substitutionCost_le_code (formula : RawFormula) :
    formula.substitutionCost <= formula.code := by
  induction formula with
  | falsum =>
      change 1 <= Nat.succ (natPair 0 0)
      exact Nat.succ_le_succ (Nat.zero_le (natPair 0 0))
  | equal left right =>
      have leftBound := left.substitutionCost_le_code
      have rightBound := right.substitutionCost_le_code
      have childrenPacking := nat_add_le_natPair left.code right.code
      change Nat.succ
          (left.substitutionCost + right.substitutionCost + 1) <=
        Nat.succ (natPair 1 (natPair left.code right.code))
      apply Nat.succ_le_succ
      rw [Nat.add_one]
      exact Nat.le_trans
        (Nat.succ_le_succ
          (Nat.le_trans (Nat.add_le_add leftBound rightBound)
            childrenPacking))
        (nat_succ_le_natPair_succ 0 (natPair left.code right.code))
  | conj left right leftHypothesis rightHypothesis =>
      have childrenPacking := nat_add_le_natPair left.code right.code
      change Nat.succ
          (left.substitutionCost + right.substitutionCost + 1) <=
        Nat.succ (natPair 2 (natPair left.code right.code))
      apply Nat.succ_le_succ
      rw [Nat.add_one]
      exact Nat.le_trans
        (Nat.succ_le_succ
          (Nat.le_trans
            (Nat.add_le_add leftHypothesis rightHypothesis)
            childrenPacking))
        (nat_succ_le_natPair_succ 1 (natPair left.code right.code))
  | disj left right leftHypothesis rightHypothesis =>
      have childrenPacking := nat_add_le_natPair left.code right.code
      change Nat.succ
          (left.substitutionCost + right.substitutionCost + 1) <=
        Nat.succ (natPair 3 (natPair left.code right.code))
      apply Nat.succ_le_succ
      rw [Nat.add_one]
      exact Nat.le_trans
        (Nat.succ_le_succ
          (Nat.le_trans
            (Nat.add_le_add leftHypothesis rightHypothesis)
            childrenPacking))
        (nat_succ_le_natPair_succ 2 (natPair left.code right.code))
  | impl left right leftHypothesis rightHypothesis =>
      have childrenPacking := nat_add_le_natPair left.code right.code
      change Nat.succ
          (left.substitutionCost + right.substitutionCost + 1) <=
        Nat.succ (natPair 4 (natPair left.code right.code))
      apply Nat.succ_le_succ
      rw [Nat.add_one]
      exact Nat.le_trans
        (Nat.succ_le_succ
          (Nat.le_trans
            (Nat.add_le_add leftHypothesis rightHypothesis)
            childrenPacking))
        (nat_succ_le_natPair_succ 3 (natPair left.code right.code))
  | all body inductionHypothesis =>
      change Nat.succ (Nat.succ body.substitutionCost) <=
        Nat.succ (natPair 5 body.code)
      apply Nat.succ_le_succ
      exact Nat.le_trans (Nat.succ_le_succ inductionHypothesis)
        (nat_succ_le_natPair_succ 4 body.code)
  | ex body inductionHypothesis =>
      change Nat.succ (Nat.succ body.substitutionCost) <=
        Nat.succ (natPair 6 body.code)
      apply Nat.succ_le_succ
      exact Nat.le_trans (Nat.succ_le_succ inductionHypothesis)
        (nat_succ_le_natPair_succ 5 body.code)

/-- The previous sharper bound implies the code-computable double bound. -/
theorem RawTerm.substitutionCost_le_doubleCode (term : RawTerm) :
    term.substitutionCost <= natDouble term.code :=
  Nat.le_trans term.substitutionCost_le_code (nat_le_natDouble term.code)

/-- The previous sharper bound implies the code-computable double bound. -/
theorem RawFormula.substitutionCost_le_doubleCode (formula : RawFormula) :
    formula.substitutionCost <= natDouble formula.code :=
  Nat.le_trans formula.substitutionCost_le_code
    (nat_le_natDouble formula.code)

/-- A completed machine state is fixed by every further step. -/
theorem substitutionMachineStep_completed
    (results value : Nat) :
    substitutionMachineStep
        (substitutionMachineState 0 results)
        value =
      substitutionMachineState 0 results := by
  unfold substitutionMachineStep substitutionMachineState
  rw [natUnpairLeft_pair, natUnpairRight_pair]

/-- A completed machine state is fixed by every further run. -/
theorem substitutionMachineRun_completed
    (steps results value : Nat) :
    substitutionMachineRun steps
        (substitutionMachineState 0 results)
        value =
      substitutionMachineState 0 results := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change substitutionMachineRun steps
        (substitutionMachineStep
          (substitutionMachineState 0 results) value) value = _
      rw [substitutionMachineStep_completed, inductionHypothesis]

/-- Total code-level substitution computed by the verified stack machine. -/
def machineSubstituteNumeralCode (formulaCode value : Nat) : Nat :=
  substitutionStackHead
    (natUnpairRight
      (substitutionMachineRun
        (natDouble formulaCode)
        (substitutionMachineInitialState formulaCode)
        value))

/-- The machine commutes exactly with syntax on every genuine formula code. -/
theorem machineSubstituteNumeralCode_code
    (formula : RawFormula)
    (value : Nat) :
    machineSubstituteNumeralCode formula.code value =
      (formula.instantiateNumeral value).code := by
  cases natExistsEqAddOfLe formula.substitutionCost_le_doubleCode with
  | intro extra fuelEquality =>
      unfold machineSubstituteNumeralCode
      rw [fuelEquality, substitutionMachineRun_add]
      have exactRun := formula.substitutionMachineRun_correct 0 0 0 value
      rw [RawFormula.substitute_numeralAtDepth_zero] at exactRun
      unfold substitutionMachineInitialState
      rw [exactRun, substitutionMachineRun_completed]
      unfold substitutionMachineState
      rw [natUnpairRight_pair, substitutionStackHead_push]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.numeralSubstitutionAtDepth
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionProcessFormulaStep
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineRun
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep_pushedTask
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep_processTermTask
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep_processFormulaTask
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep_buildTermSucc
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep_buildTermAdd
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineStep_buildFormulaAll
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionMachineRun_add
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.substitutionCost
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitutionCost
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.substitutionCost_le_code
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitutionCost_le_code
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.substitutionMachineRun_correct
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitutionMachineRun_correct
#print axioms RelationalPerimeter.HeytingArithmetic.machineSubstituteNumeralCode_code
/- AXIOM_AUDIT_END -/
