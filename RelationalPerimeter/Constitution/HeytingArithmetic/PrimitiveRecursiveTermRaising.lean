import RelationalPerimeter.Constitution.HeytingArithmetic.GeneralInstantiation
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveCodeSubstitution

/-!
# Primitive-recursive raising of coded terms

Instantiation below binders must insert a raised copy of the replacement term.
This module compiles that raising operation as a positive course-of-values
`PRFunction`.  Each genuine term constructor refers only to smaller positive
codes, so the newest-first trace supplies the already transformed children.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem PRFunction.run_add_raising (left right : Nat) :
    PRFunction.add.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      left + right :=
  (PRFunction.add_evaluates left right).symm

/-! ## Program tree -/

def PRFunction.raisingCounter : PRFunction 3 :=
  PRFunction.projection 3 0 (Nat.zero_lt_succ 2)

def PRFunction.raisingHistory : PRFunction 3 :=
  PRFunction.projection 3 1
    (Nat.succ_lt_succ (Nat.zero_lt_succ 1))

def PRFunction.raisingAmount : PRFunction 3 :=
  PRFunction.projection 3 2
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

def PRFunction.raisingCurrentCode : PRFunction 3 :=
  PRFunction.composition PRFunction.successor
    (PRFunctionVector.singleton PRFunction.raisingCounter)

def PRFunction.raisingTag : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairLeft
    (PRFunctionVector.singleton PRFunction.raisingCounter)

def PRFunction.raisingPayload : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairRight
    (PRFunctionVector.singleton PRFunction.raisingCounter)

def PRFunction.raisingPayloadLeft : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairLeft
    (PRFunctionVector.singleton PRFunction.raisingPayload)

def PRFunction.raisingPayloadRight : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairRight
    (PRFunctionVector.singleton PRFunction.raisingPayload)

def PRFunction.raisingLookup
    (child : PRFunction 3) : PRFunction 3 :=
  PRFunction.composition PRFunction.traceLookupCode
    (PRFunctionVector.cons PRFunction.raisingCurrentCode
      (PRFunctionVector.cons child
        (PRFunctionVector.singleton PRFunction.raisingHistory)))

/-- Add the raising amount to the current variable index. -/
def PRFunction.raisingVariableIndex : PRFunction 3 :=
  PRFunction.composition PRFunction.add
    (PRFunctionVector.cons PRFunction.raisingPayload
      (PRFunctionVector.singleton PRFunction.raisingAmount))

/-- Rebuild one term code after its children have been raised. -/
def PRFunction.raisingTermAt : PRFunction 3 :=
  PRFunction.selectTag PRFunction.raisingTag 0
    (PRFunction.composition PRFunction.boundVariableCode
      (PRFunctionVector.singleton PRFunction.raisingVariableIndex))
    (PRFunction.selectTag PRFunction.raisingTag 1
      (PRFunction.termZeroCode 3)
      (PRFunction.selectTag PRFunction.raisingTag 2
        (PRFunction.substitutionUnary
          PRFunction.termSuccessorCode
          (PRFunction.raisingLookup PRFunction.raisingPayload))
        (PRFunction.selectTag PRFunction.raisingTag 3
          (PRFunction.substitutionBinary
            PRFunction.termAddCode
            (PRFunction.raisingLookup PRFunction.raisingPayloadLeft)
            (PRFunction.raisingLookup PRFunction.raisingPayloadRight))
          (PRFunction.selectTag PRFunction.raisingTag 4
            (PRFunction.substitutionBinary
              PRFunction.termMultiplyCode
              (PRFunction.raisingLookup PRFunction.raisingPayloadLeft)
              (PRFunction.raisingLookup PRFunction.raisingPayloadRight))
            (PRFunction.termZeroCode 3)))))

/-- Newest-first trace of raised readings for all codes up to the input. -/
def PRFunction.raisingTrace : PRFunction 2 :=
  PRFunction.traceBuilder PRFunction.raisingTermAt

/-- Primitive-recursive raising of a coded term by an explicit amount. -/
def PRFunction.raiseTermCode : PRFunction 2 :=
  PRFunction.composition PRFunction.unpairLeft
    (PRFunctionVector.singleton PRFunction.raisingTrace)

/-! ## Numeric execution equations -/

@[simp] theorem PRFunction.run_raisingCounter
    (counter history amount : Nat) :
    PRFunction.raisingCounter.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = counter := rfl

@[simp] theorem PRFunction.run_raisingHistory
    (counter history amount : Nat) :
    PRFunction.raisingHistory.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = history := rfl

@[simp] theorem PRFunction.run_raisingAmount
    (counter history amount : Nat) :
    PRFunction.raisingAmount.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = amount := rfl

@[simp] theorem PRFunction.run_raisingCurrentCode
    (counter history amount : Nat) :
    PRFunction.raisingCurrentCode.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = Nat.succ counter := rfl

@[simp] theorem PRFunction.run_raisingTag
    (counter history amount : Nat) :
    PRFunction.raisingTag.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      natUnpairLeft counter := by
  change PRFunction.unpairLeft.run
    (NatVector.cons counter NatVector.nil) = _
  exact PRFunction.run_unpairLeft counter

@[simp] theorem PRFunction.run_raisingPayload
    (counter history amount : Nat) :
    PRFunction.raisingPayload.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      natUnpairRight counter := by
  change PRFunction.unpairRight.run
    (NatVector.cons counter NatVector.nil) = _
  exact PRFunction.run_unpairRight counter

@[simp] theorem PRFunction.run_raisingPayloadLeft
    (counter history amount : Nat) :
    PRFunction.raisingPayloadLeft.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      natUnpairLeft (natUnpairRight counter) := by
  unfold PRFunction.raisingPayloadLeft
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_raisingPayload, PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_raisingPayloadRight
    (counter history amount : Nat) :
    PRFunction.raisingPayloadRight.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      natUnpairRight (natUnpairRight counter) := by
  unfold PRFunction.raisingPayloadRight
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_raisingPayload, PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_raisingLookup
    (child : PRFunction 3)
    (counter history amount : Nat) :
    (PRFunction.raisingLookup child).run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      natTraceLookupCode
        (Nat.succ counter)
        (child.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons amount NatVector.nil))))
        history := by
  unfold PRFunction.raisingLookup
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_raisingCurrentCode, PRFunction.run_raisingHistory,
    PRFunction.run_traceLookupCode]

@[simp] theorem PRFunction.run_raisingVariableIndex
    (counter history amount : Nat) :
    PRFunction.raisingVariableIndex.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      natUnpairRight counter + amount := by
  unfold PRFunction.raisingVariableIndex
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_raisingPayload,
    PRFunction.run_raisingAmount, PRFunction.run_add_raising]

/-! ## Canonical trace -/

/-- Numeric newest-first trace computed by the raising program. -/
def raisingTraceValue : Nat -> Nat -> Nat
  | 0, _amount => 0
  | Nat.succ counter, amount =>
      natPair
        (PRFunction.raisingTermAt.run
          (NatVector.cons counter
            (NatVector.cons (raisingTraceValue counter amount)
              (NatVector.cons amount NatVector.nil))))
        (raisingTraceValue counter amount)

/-- Numeric entry assigned to a positive syntax code. -/
def raisingEntryAt (code amount : Nat) : Nat :=
  match code with
  | 0 => 0
  | Nat.succ counter =>
      PRFunction.raisingTermAt.run
        (NatVector.cons counter
          (NatVector.cons (raisingTraceValue counter amount)
            (NatVector.cons amount NatVector.nil)))

theorem raisingTraceValue_succ (counter amount : Nat) :
    raisingTraceValue (Nat.succ counter) amount =
      natPair
        (raisingEntryAt (Nat.succ counter) amount)
        (raisingTraceValue counter amount) := rfl

theorem raisingTraceValue_lookup
    (code offset amount : Nat)
    (positive : 0 < code) :
    natTraceLookup offset (raisingTraceValue (code + offset) amount) =
      raisingEntryAt code amount := by
  induction offset with
  | zero =>
      rw [Nat.add_zero]
      cases code with
      | zero => exact (Nat.lt_irrefl 0 positive).elim
      | succ code =>
          rw [raisingTraceValue_succ, natTraceLookup_zero_pair]
  | succ offset inductionHypothesis =>
      rw [Nat.add_succ]
      change natTraceLookup (Nat.succ offset)
          (raisingTraceValue (Nat.succ (code + offset)) amount) = _
      rw [raisingTraceValue_succ, natTraceLookup_succ_pair]
      exact inductionHypothesis

/-- Local structural zero-addition, avoiding algebraic library bridges. -/
theorem natZeroAddConstructive (right : Nat) : 0 + right = right := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      change Nat.succ (0 + right) = Nat.succ right
      exact congrArg Nat.succ inductionHypothesis

/-- Local structural successor-addition. -/
theorem natSuccAddConstructive (left right : Nat) :
    Nat.succ left + right = Nat.succ (left + right) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      change
        Nat.succ (Nat.succ left + right) =
          Nat.succ (Nat.succ (left + right))
      exact congrArg Nat.succ inductionHypothesis

/-- Local constructive cancellation for the trace offset calculation. -/
theorem natAddSubCancelLeftConstructive (left right : Nat) :
    (left + right) - left = right := by
  induction left with
  | zero =>
      rw [natZeroAddConstructive]
      rfl
  | succ left inductionHypothesis =>
      rw [natSuccAddConstructive]
      rw [show left + 1 = Nat.succ left by rfl]
      rw [Nat.succ_sub_succ_eq_sub]
      exact inductionHypothesis

theorem raisingTraceValue_lookupCode
    (current child amount : Nat)
    (childPositive : 0 < child)
    (childEarlier : child < current) :
    natTraceLookupCode current child
        (raisingTraceValue current.pred amount) =
      raisingEntryAt child amount := by
  cases current with
  | zero => exact (Nat.not_lt_zero child childEarlier).elim
  | succ current =>
      have bounded : child <= current := Nat.le_of_lt_succ childEarlier
      cases natExistsEqAddOfLe bounded with
      | intro offset equality =>
          change
            natTraceLookupCode (Nat.succ current) child
                (raisingTraceValue current amount) =
              raisingEntryAt child amount
          unfold natTraceLookupCode
          rw [equality, Nat.pred_succ,
            natAddSubCancelLeftConstructive]
          exact raisingTraceValue_lookup child offset amount childPositive

/-- The positive trace-builder computes the named numeric trace. -/
theorem PRFunction.raisingTrace_run (code amount : Nat) :
    PRFunction.raisingTrace.run
        (NatVector.cons code (NatVector.cons amount NatVector.nil)) =
      raisingTraceValue code amount := by
  induction code with
  | zero => rfl
  | succ code inductionHypothesis =>
      change
        (PRFunction.prependToPrevious PRFunction.raisingTermAt).run
            (NatVector.cons code
              (NatVector.cons
                (PRFunction.raisingTrace.run
                  (NatVector.cons code
                    (NatVector.cons amount NatVector.nil)))
                (NatVector.cons amount NatVector.nil))) = _
      rw [inductionHypothesis]
      simp only [PRFunction.prependToPrevious,
        PRFunction.run_composition, PRFunctionVector.run_cons,
        PRFunctionVector.run_singleton, PRFunction.run_projection,
        PRFunction.run_pair]
      rfl

/-! ## Correctness on genuine term codes -/

theorem RawTerm.raise_bvar (index amount : Nat) :
    (RawTerm.bvar index).raise amount =
      RawTerm.bvar (index + amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      change
        ((RawTerm.bvar index).raise amount).rename Nat.succ =
          RawTerm.bvar (index + Nat.succ amount)
      rw [inductionHypothesis, Nat.add_succ]
      rfl

theorem RawTerm.raise_zero (amount : Nat) :
    RawTerm.zero.raise amount = RawTerm.zero := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      change (RawTerm.zero.raise amount).rename Nat.succ = RawTerm.zero
      rw [inductionHypothesis]
      rfl

theorem RawTerm.raise_succ (term : RawTerm) (amount : Nat) :
    (RawTerm.succ term).raise amount = RawTerm.succ (term.raise amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      change
        ((RawTerm.succ term).raise amount).rename Nat.succ =
          RawTerm.succ ((term.raise amount).rename Nat.succ)
      rw [inductionHypothesis]
      rfl

theorem RawTerm.raise_add (left right : RawTerm) (amount : Nat) :
    (RawTerm.add left right).raise amount =
      RawTerm.add (left.raise amount) (right.raise amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      change
        ((RawTerm.add left right).raise amount).rename Nat.succ =
          RawTerm.add
            ((left.raise amount).rename Nat.succ)
            ((right.raise amount).rename Nat.succ)
      rw [inductionHypothesis]
      rfl

theorem RawTerm.raise_mul (left right : RawTerm) (amount : Nat) :
    (RawTerm.mul left right).raise amount =
      RawTerm.mul (left.raise amount) (right.raise amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      change
        ((RawTerm.mul left right).raise amount).rename Nat.succ =
          RawTerm.mul
            ((left.raise amount).rename Nat.succ)
            ((right.raise amount).rename Nat.succ)
      rw [inductionHypothesis]
      rfl

private theorem termChildEarlierUnary
    (tag : Nat) (child : RawTerm) :
    child.code < Nat.succ (natPair tag child.code) :=
  Nat.lt_succ_of_le (natPair_right_le tag child.code)

private theorem termChildEarlierBinaryLeft
    (tag : Nat) (left right : RawTerm) :
    left.code < Nat.succ (natPair tag (natPair left.code right.code)) :=
  Nat.lt_succ_of_le
    (Nat.le_trans
      (natPair_left_le left.code right.code)
      (natPair_right_le tag (natPair left.code right.code)))

private theorem termChildEarlierBinaryRight
    (tag : Nat) (left right : RawTerm) :
    right.code < Nat.succ (natPair tag (natPair left.code right.code)) :=
  Nat.lt_succ_of_le
    (Nat.le_trans
      (natPair_right_le left.code right.code)
      (natPair_right_le tag (natPair left.code right.code)))

theorem PRFunction.raisingTermAt_bvar
    (index history amount : Nat) :
    PRFunction.raisingTermAt.run
        (NatVector.cons (natPair 0 index)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      (RawTerm.bvar (index + amount)).code := by
  unfold PRFunction.raisingTermAt
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.composition PRFunction.boundVariableCode
      (PRFunctionVector.singleton PRFunction.raisingVariableIndex)).run
        (NatVector.cons (natPair 0 index)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.run_raisingVariableIndex]
  rw [natUnpairRight_pair]
  change
    (PRFunction.taggedUnaryCode 0).run
        (NatVector.cons (index + amount) NatVector.nil) =
      Nat.succ (natPair 0 (index + amount))
  exact PRFunction.run_taggedUnaryCode 0 (index + amount)

theorem PRFunction.raisingTermAt_zero
    (payload history amount : Nat) :
    PRFunction.raisingTermAt.run
        (NatVector.cons (natPair 1 payload)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      RawTerm.zero.code := by
  unfold PRFunction.raisingTermAt
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 1
      (PRFunction.termZeroCode 3)
      _).run
        (NatVector.cons (natPair 1 payload)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  exact PRFunction.run_termZeroCode 3
    (NatVector.cons (natPair 1 payload)
      (NatVector.cons history
        (NatVector.cons amount NatVector.nil)))

theorem PRFunction.raisingTermAt_succ
    (child history amount : Nat) :
    PRFunction.raisingTermAt.run
        (NatVector.cons (natPair 2 child)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      Nat.succ
        (natPair 2
          (natTraceLookupCode
            (Nat.succ (natPair 2 child)) child history)) := by
  unfold PRFunction.raisingTermAt
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 1
      (PRFunction.termZeroCode 3) _).run
        (NatVector.cons (natPair 2 child)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 2
      (PRFunction.substitutionUnary PRFunction.termSuccessorCode
        (PRFunction.raisingLookup PRFunction.raisingPayload)) _).run
        (NatVector.cons (natPair 2 child)
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  rw [show natEqualBit 2 2 = 1 by rfl]
  rw [PRFunction.run_substitutionUnary,
    PRFunction.run_raisingLookup, PRFunction.run_raisingPayload,
    natUnpairRight_pair, PRFunction.run_termSuccessorCode]
  rfl

theorem PRFunction.raisingTermAt_add
    (left right history amount : Nat) :
    PRFunction.raisingTermAt.run
        (NatVector.cons (natPair 3 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      Nat.succ
        (natPair 3
          (natPair
            (natTraceLookupCode
              (Nat.succ (natPair 3 (natPair left right))) left history)
            (natTraceLookupCode
              (Nat.succ (natPair 3 (natPair left right))) right history))) := by
  unfold PRFunction.raisingTermAt
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 1
      (PRFunction.termZeroCode 3) _).run
        (NatVector.cons (natPair 3 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 2 _ _).run
        (NatVector.cons (natPair 3 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 3
      (PRFunction.substitutionBinary PRFunction.termAddCode
        (PRFunction.raisingLookup PRFunction.raisingPayloadLeft)
        (PRFunction.raisingLookup PRFunction.raisingPayloadRight)) _).run
        (NatVector.cons (natPair 3 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  rw [show natEqualBit 3 3 = 1 by rfl]
  rw [PRFunction.run_substitutionBinary]
  rw [PRFunction.run_raisingLookup,
    PRFunction.run_raisingPayloadLeft,
    natUnpairRight_pair, natUnpairLeft_pair]
  rw [PRFunction.run_raisingLookup,
    PRFunction.run_raisingPayloadRight,
    natUnpairRight_pair, natUnpairRight_pair]
  rw [PRFunction.run_termAddCode]
  rfl

theorem PRFunction.raisingTermAt_mul
    (left right history amount : Nat) :
    PRFunction.raisingTermAt.run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) =
      Nat.succ
        (natPair 4
          (natPair
            (natTraceLookupCode
              (Nat.succ (natPair 4 (natPair left right))) left history)
            (natTraceLookupCode
              (Nat.succ (natPair 4 (natPair left right))) right history))) := by
  unfold PRFunction.raisingTermAt
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 1
      (PRFunction.termZeroCode 3) _).run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 2 _ _).run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 3 _ _).run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  change
    (PRFunction.selectTag PRFunction.raisingTag 4
      (PRFunction.substitutionBinary PRFunction.termMultiplyCode
        (PRFunction.raisingLookup PRFunction.raisingPayloadLeft)
        (PRFunction.raisingLookup PRFunction.raisingPayloadRight)) _).run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons amount NatVector.nil))) = _
  rw [PRFunction.run_selectTag, PRFunction.run_raisingTag,
    natUnpairLeft_pair]
  rw [show natEqualBit 4 4 = 1 by rfl]
  rw [PRFunction.run_substitutionBinary]
  rw [PRFunction.run_raisingLookup,
    PRFunction.run_raisingPayloadLeft,
    natUnpairRight_pair, natUnpairLeft_pair]
  rw [PRFunction.run_raisingLookup,
    PRFunction.run_raisingPayloadRight,
    natUnpairRight_pair, natUnpairRight_pair]
  rw [PRFunction.run_termMultiplyCode]
  rfl

/-- Every genuine term entry is exactly the code of its raised syntax. -/
theorem raisingEntryAt_term_code
    (term : RawTerm)
    (amount : Nat) :
    raisingEntryAt term.code amount = (term.raise amount).code := by
  induction term with
  | bvar index =>
      change
        PRFunction.raisingTermAt.run
            (NatVector.cons (natPair 0 index)
              (NatVector.cons
                (raisingTraceValue (natPair 0 index) amount)
                (NatVector.cons amount NatVector.nil))) = _
      rw [PRFunction.raisingTermAt_bvar, RawTerm.raise_bvar]
  | zero =>
      change
        PRFunction.raisingTermAt.run
            (NatVector.cons (natPair 1 0)
              (NatVector.cons
                (raisingTraceValue (natPair 1 0) amount)
                (NatVector.cons amount NatVector.nil))) = _
      rw [PRFunction.raisingTermAt_zero, RawTerm.raise_zero]
  | succ child inductionHypothesis =>
      change
        PRFunction.raisingTermAt.run
            (NatVector.cons (natPair 2 child.code)
              (NatVector.cons
                (raisingTraceValue (natPair 2 child.code) amount)
                (NatVector.cons amount NatVector.nil))) = _
      rw [PRFunction.raisingTermAt_succ]
      have childLookup := raisingTraceValue_lookupCode
        (Nat.succ (natPair 2 child.code))
        child.code
        amount
        (child.code_pos)
        (termChildEarlierUnary 2 child)
      simp only [Nat.pred_succ] at childLookup
      rw [childLookup]
      rw [inductionHypothesis, RawTerm.raise_succ]
      rfl
  | add left right leftHypothesis rightHypothesis =>
      change
        PRFunction.raisingTermAt.run
            (NatVector.cons (natPair 3 (natPair left.code right.code))
              (NatVector.cons
                (raisingTraceValue
                  (natPair 3 (natPair left.code right.code)) amount)
                (NatVector.cons amount NatVector.nil))) = _
      rw [PRFunction.raisingTermAt_add]
      have leftLookup := raisingTraceValue_lookupCode
        (Nat.succ (natPair 3 (natPair left.code right.code)))
        left.code amount
        left.code_pos (termChildEarlierBinaryLeft 3 left right)
      have rightLookup := raisingTraceValue_lookupCode
        (Nat.succ (natPair 3 (natPair left.code right.code)))
        right.code amount
        right.code_pos (termChildEarlierBinaryRight 3 left right)
      simp only [Nat.pred_succ] at leftLookup rightLookup
      rw [leftLookup, rightLookup]
      rw [leftHypothesis, rightHypothesis, RawTerm.raise_add]
      rfl
  | mul left right leftHypothesis rightHypothesis =>
      change
        PRFunction.raisingTermAt.run
            (NatVector.cons (natPair 4 (natPair left.code right.code))
              (NatVector.cons
                (raisingTraceValue
                  (natPair 4 (natPair left.code right.code)) amount)
                (NatVector.cons amount NatVector.nil))) = _
      rw [PRFunction.raisingTermAt_mul]
      have leftLookup := raisingTraceValue_lookupCode
        (Nat.succ (natPair 4 (natPair left.code right.code)))
        left.code amount
        left.code_pos (termChildEarlierBinaryLeft 4 left right)
      have rightLookup := raisingTraceValue_lookupCode
        (Nat.succ (natPair 4 (natPair left.code right.code)))
        right.code amount
        right.code_pos (termChildEarlierBinaryRight 4 left right)
      simp only [Nat.pred_succ] at leftLookup rightLookup
      rw [leftLookup, rightLookup]
      rw [leftHypothesis, rightHypothesis, RawTerm.raise_mul]
      rfl

/-- The compiled raising program is exact on every genuine term code. -/
theorem PRFunction.raiseTermCode_run
    (term : RawTerm)
    (amount : Nat) :
    PRFunction.raiseTermCode.run
        (NatVector.cons term.code
          (NatVector.cons amount NatVector.nil)) =
      (term.raise amount).code := by
  unfold PRFunction.raiseTermCode
  rw [PRFunction.run_composition, PRFunctionVector.run_singleton,
    PRFunction.raisingTrace_run, PRFunction.run_unpairLeft]
  change
    natTraceLookup 0 (raisingTraceValue term.code amount) =
      (term.raise amount).code
  exact (by
    simpa only [Nat.add_zero] using
      (Eq.trans
        (raisingTraceValue_lookup term.code 0 amount term.code_pos)
        (raisingEntryAt_term_code term amount)))

/-- Positive execution certificate for coded term raising. -/
theorem PRFunction.raiseTermCode_evaluates
    (term : RawTerm)
    (amount : Nat) :
    PRFunction.Evaluates
      PRFunction.raiseTermCode
      (NatVector.cons term.code
        (NatVector.cons amount NatVector.nil))
      ((term.raise amount).code) := by
  unfold PRFunction.Evaluates
  exact (PRFunction.raiseTermCode_run term amount).symm

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseTermCode
#print axioms RelationalPerimeter.HeytingArithmetic.raisingEntryAt_term_code
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseTermCode_run
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.raiseTermCode_evaluates
/- AXIOM_AUDIT_END -/
