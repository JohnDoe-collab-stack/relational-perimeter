import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveBoolean
import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveTrace
import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveSubstitutionMachine
import RelationalPerimeter.Instances.HeytingArithmetic.ProofDecoding

/-!
# Strict course-of-values recognition of canonical syntax codes

Each positive code receives a pair `(termBit,formulaBit)`.  Child codes are
strictly smaller than their constructor code, so their bits are already in the
newest-first trace.  Unlike the permissive raw decoder, the recognizer also
checks canonical payloads for nullary constructors.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem syntaxIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem syntaxIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)

def PRFunction.syntaxCounter : PRFunction 2 :=
  PRFunction.projection 2 0 syntaxIndexZero_lt_two
def PRFunction.syntaxHistory : PRFunction 2 :=
  PRFunction.projection 2 1 syntaxIndexOne_lt_two
def PRFunction.syntaxCurrentCode : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.successor PRFunction.syntaxCounter
def PRFunction.syntaxCurrentTag : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.unpairLeft PRFunction.syntaxCounter
def PRFunction.syntaxCurrentPayload : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.unpairRight PRFunction.syntaxCounter
def PRFunction.syntaxCurrentLeft : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.unpairLeft PRFunction.syntaxCurrentPayload
def PRFunction.syntaxCurrentRight : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.unpairRight PRFunction.syntaxCurrentPayload

def PRFunction.syntaxLookup (child : PRFunction 2) : PRFunction 2 :=
  PRFunction.composition PRFunction.traceLookupCode
    (PRFunctionVector.cons PRFunction.syntaxCurrentCode
      (PRFunctionVector.cons child
        (PRFunctionVector.singleton PRFunction.syntaxHistory)))

def PRFunction.syntaxTermLookup (child : PRFunction 2) : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.unpairLeft
    (PRFunction.syntaxLookup child)

def PRFunction.syntaxFormulaLookup (child : PRFunction 2) : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.unpairRight
    (PRFunction.syntaxLookup child)

def PRFunction.syntaxBoth
    (left right : PRFunction 2) : PRFunction 2 :=
  PRFunction.conjoin left right

def PRFunction.syntaxTermBitAt : PRFunction 2 :=
  let tag := PRFunction.syntaxCurrentTag
  let payload := PRFunction.syntaxCurrentPayload
  let left := PRFunction.syntaxCurrentLeft
  let right := PRFunction.syntaxCurrentRight
  let canonicalZero := PRFunction.binaryIn PRFunction.equalBit
    payload (PRFunction.constant 2 0)
  PRFunction.selectTag tag 0 (PRFunction.constant 2 1)
    (PRFunction.selectTag tag 1 canonicalZero
      (PRFunction.selectTag tag 2 (PRFunction.syntaxTermLookup payload)
        (PRFunction.selectTag tag 3
          (PRFunction.syntaxBoth
            (PRFunction.syntaxTermLookup left)
            (PRFunction.syntaxTermLookup right))
          (PRFunction.selectTag tag 4
            (PRFunction.syntaxBoth
              (PRFunction.syntaxTermLookup left)
              (PRFunction.syntaxTermLookup right))
            (PRFunction.constant 2 0)))))

def PRFunction.syntaxFormulaBitAt : PRFunction 2 :=
  let tag := PRFunction.syntaxCurrentTag
  let payload := PRFunction.syntaxCurrentPayload
  let left := PRFunction.syntaxCurrentLeft
  let right := PRFunction.syntaxCurrentRight
  let canonicalFalsum := PRFunction.binaryIn PRFunction.equalBit
    payload (PRFunction.constant 2 0)
  PRFunction.selectTag tag 0 canonicalFalsum
    (PRFunction.selectTag tag 1
      (PRFunction.syntaxBoth
        (PRFunction.syntaxTermLookup left)
        (PRFunction.syntaxTermLookup right))
      (PRFunction.selectTag tag 2
        (PRFunction.syntaxBoth
          (PRFunction.syntaxFormulaLookup left)
          (PRFunction.syntaxFormulaLookup right))
        (PRFunction.selectTag tag 3
          (PRFunction.syntaxBoth
            (PRFunction.syntaxFormulaLookup left)
            (PRFunction.syntaxFormulaLookup right))
          (PRFunction.selectTag tag 4
            (PRFunction.syntaxBoth
              (PRFunction.syntaxFormulaLookup left)
              (PRFunction.syntaxFormulaLookup right))
            (PRFunction.selectTag tag 5
              (PRFunction.syntaxFormulaLookup payload)
              (PRFunction.selectTag tag 6
                (PRFunction.syntaxFormulaLookup payload)
                (PRFunction.constant 2 0)))))))

def PRFunction.syntaxEntry : PRFunction 2 :=
  PRFunction.binaryIn PRFunction.pair
    PRFunction.syntaxTermBitAt PRFunction.syntaxFormulaBitAt

def PRFunction.syntaxTrace : PRFunction 1 :=
  PRFunction.traceBuilder PRFunction.syntaxEntry

def PRFunction.strictTermCode : PRFunction 1 :=
  PRFunction.unaryIn PRFunction.unpairLeft
    (PRFunction.unaryIn PRFunction.unpairLeft PRFunction.syntaxTrace)

def PRFunction.strictFormulaCode : PRFunction 1 :=
  PRFunction.unaryIn PRFunction.unpairRight
    (PRFunction.unaryIn PRFunction.unpairLeft PRFunction.syntaxTrace)

/-! ## Numeric trace semantics -/

def syntaxTraceValue : Nat -> Nat
  | 0 => 0
  | Nat.succ counter =>
      natPair
        (PRFunction.syntaxEntry.run
          (NatVector.cons counter
            (NatVector.cons (syntaxTraceValue counter) NatVector.nil)))
        (syntaxTraceValue counter)

def syntaxEntryAt : Nat -> Nat
  | 0 => 0
  | Nat.succ counter =>
      PRFunction.syntaxEntry.run
        (NatVector.cons counter
          (NatVector.cons (syntaxTraceValue counter) NatVector.nil))

theorem syntaxTraceValue_succ (counter : Nat) :
    syntaxTraceValue (Nat.succ counter) =
      natPair (syntaxEntryAt (Nat.succ counter))
        (syntaxTraceValue counter) := rfl

theorem syntaxTraceValue_lookup
    (code offset : Nat)
    (positive : 0 < code) :
    natTraceLookup offset (syntaxTraceValue (code + offset)) =
      syntaxEntryAt code := by
  induction offset with
  | zero =>
      rw [Nat.add_zero]
      cases code with
      | zero => exact (Nat.lt_irrefl 0 positive).elim
      | succ code =>
          rw [syntaxTraceValue_succ, natTraceLookup_zero_pair]
  | succ offset inductionHypothesis =>
      rw [Nat.add_succ]
      change natTraceLookup (Nat.succ offset)
          (syntaxTraceValue (Nat.succ (code + offset))) = _
      rw [syntaxTraceValue_succ, natTraceLookup_succ_pair]
      exact inductionHypothesis

private theorem syntaxAddSubCancelLeft (left right : Nat) :
    left + right - left = right := by
  induction left with
  | zero =>
      induction right with
      | zero => rfl
      | succ right inductionHypothesis =>
          exact congrArg Nat.succ inductionHypothesis
  | succ left inductionHypothesis =>
      rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub,
        inductionHypothesis]

theorem syntaxTraceValue_lookupCode
    (current child : Nat)
    (childPositive : 0 < child)
    (childEarlier : child < current) :
    natTraceLookupCode current child (syntaxTraceValue current.pred) =
      syntaxEntryAt child := by
  cases current with
  | zero => exact (Nat.not_lt_zero child childEarlier).elim
  | succ previous =>
      unfold natTraceLookupCode
      have bounded : child <= previous :=
        Nat.le_of_lt_succ childEarlier
      have decomposition := natExistsEqAddOfLe bounded
      cases decomposition with
      | intro extra equality =>
          rw [equality, Nat.add_one, Nat.pred_succ,
            syntaxAddSubCancelLeft]
          exact syntaxTraceValue_lookup child extra childPositive

@[simp] theorem PRFunction.run_syntaxCounter (counter history : Nat) :
    PRFunction.syntaxCounter.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) = counter :=
  rfl

@[simp] theorem PRFunction.run_syntaxHistory (counter history : Nat) :
    PRFunction.syntaxHistory.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) = history :=
  rfl

@[simp] theorem PRFunction.run_syntaxCurrentCode (counter history : Nat) :
    PRFunction.syntaxCurrentCode.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      Nat.succ counter := by
  unfold PRFunction.syntaxCurrentCode
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxCounter,
    PRFunction.run_successor]

@[simp] theorem PRFunction.run_syntaxCurrentTag (counter history : Nat) :
    PRFunction.syntaxCurrentTag.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natUnpairLeft counter := by
  unfold PRFunction.syntaxCurrentTag
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxCounter,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_syntaxCurrentPayload (counter history : Nat) :
    PRFunction.syntaxCurrentPayload.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natUnpairRight counter := by
  unfold PRFunction.syntaxCurrentPayload
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxCounter,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_syntaxCurrentLeft (counter history : Nat) :
    PRFunction.syntaxCurrentLeft.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natUnpairLeft (natUnpairRight counter) := by
  unfold PRFunction.syntaxCurrentLeft
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxCurrentPayload,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_syntaxCurrentRight (counter history : Nat) :
    PRFunction.syntaxCurrentRight.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natUnpairRight (natUnpairRight counter) := by
  unfold PRFunction.syntaxCurrentRight
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxCurrentPayload,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_syntaxLookup
    (child : PRFunction 2)
    (counter history : Nat) :
    (PRFunction.syntaxLookup child).run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natTraceLookupCode (Nat.succ counter)
        (child.run
          (NatVector.cons counter (NatVector.cons history NatVector.nil)))
        history := by
  unfold PRFunction.syntaxLookup
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_syntaxCurrentCode, PRFunction.run_syntaxHistory,
    PRFunction.run_traceLookupCode]

@[simp] theorem PRFunction.run_syntaxTermLookup
    (child : PRFunction 2)
    (counter history : Nat) :
    (PRFunction.syntaxTermLookup child).run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natUnpairLeft
        (natTraceLookupCode (Nat.succ counter)
          (child.run
            (NatVector.cons counter (NatVector.cons history NatVector.nil)))
          history) := by
  unfold PRFunction.syntaxTermLookup
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxLookup,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_syntaxFormulaLookup
    (child : PRFunction 2)
    (counter history : Nat) :
    (PRFunction.syntaxFormulaLookup child).run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natUnpairRight
        (natTraceLookupCode (Nat.succ counter)
          (child.run
            (NatVector.cons counter (NatVector.cons history NatVector.nil)))
          history) := by
  unfold PRFunction.syntaxFormulaLookup
  rw [PRFunction.run_unaryIn, PRFunction.run_syntaxLookup,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_syntaxBoth
    (left right : PRFunction 2)
    (counter history : Nat) :
    (PRFunction.syntaxBoth left right).run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natAndBit
        (left.run (NatVector.cons counter (NatVector.cons history NatVector.nil)))
        (right.run
          (NatVector.cons counter (NatVector.cons history NatVector.nil))) := by
  unfold PRFunction.syntaxBoth
  rw [PRFunction.run_conjoin]

@[simp] theorem PRFunction.run_syntaxEntry
    (counter history : Nat) :
    PRFunction.syntaxEntry.run
        (NatVector.cons counter (NatVector.cons history NatVector.nil)) =
      natPair
        (PRFunction.syntaxTermBitAt.run
          (NatVector.cons counter (NatVector.cons history NatVector.nil)))
        (PRFunction.syntaxFormulaBitAt.run
          (NatVector.cons counter (NatVector.cons history NatVector.nil))) := by
  unfold PRFunction.syntaxEntry
  rw [PRFunction.run_binaryIn, PRFunction.run_pair]

theorem PRFunction.run_syntaxTrace (code : Nat) :
    PRFunction.syntaxTrace.run (NatVector.cons code NatVector.nil) =
      syntaxTraceValue code := by
  induction code with
  | zero => rfl
  | succ code inductionHypothesis =>
      change (PRFunction.prependToPrevious PRFunction.syntaxEntry).run
        (NatVector.cons code
          (NatVector.cons
            (PRFunction.syntaxTrace.run (NatVector.cons code NatVector.nil))
            NatVector.nil)) = _
      unfold PRFunction.prependToPrevious
      rw [PRFunction.run_composition, PRFunctionVector.run_cons,
        PRFunctionVector.run_singleton,
        PRFunction.run_syntaxEntry, PRFunction.run_projection,
        NatVector.get_cons_succ, NatVector.get_cons_zero,
        PRFunction.run_pair, inductionHypothesis]
      rw [Nat.add_one, syntaxTraceValue_succ]
      rw [syntaxEntryAt, PRFunction.run_syntaxEntry]

@[simp] theorem PRFunction.run_strictTermCode (code : Nat) :
    PRFunction.strictTermCode.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft (syntaxEntryAt code) := by
  unfold PRFunction.strictTermCode
  rw [PRFunction.run_unaryIn, PRFunction.run_unaryIn,
    PRFunction.run_syntaxTrace]
  cases code with
  | zero => rfl
  | succ code =>
      rw [syntaxTraceValue_succ, PRFunction.run_unpairLeft,
        PRFunction.run_unpairLeft, natUnpairLeft_pair]

@[simp] theorem PRFunction.run_strictFormulaCode (code : Nat) :
    PRFunction.strictFormulaCode.run (NatVector.cons code NatVector.nil) =
      natUnpairRight (syntaxEntryAt code) := by
  unfold PRFunction.strictFormulaCode
  rw [PRFunction.run_unaryIn, PRFunction.run_unaryIn,
    PRFunction.run_syntaxTrace]
  cases code with
  | zero => rfl
  | succ code =>
      rw [syntaxTraceValue_succ, PRFunction.run_unpairLeft,
        PRFunction.run_unpairRight, natUnpairLeft_pair]

/-! ## Lookup equations used by canonical-syntax correctness -/

theorem syntaxTermLookupCode_current
    (current child : Nat)
    (childPositive : 0 < child)
    (childEarlier : child < current) :
    natUnpairLeft
        (natTraceLookupCode current child (syntaxTraceValue current.pred)) =
      natUnpairLeft (syntaxEntryAt child) :=
  congrArg natUnpairLeft
    (syntaxTraceValue_lookupCode current child childPositive childEarlier)

theorem syntaxFormulaLookupCode_current
    (current child : Nat)
    (childPositive : 0 < child)
    (childEarlier : child < current) :
    natUnpairRight
        (natTraceLookupCode current child (syntaxTraceValue current.pred)) =
      natUnpairRight (syntaxEntryAt child) :=
  congrArg natUnpairRight
    (syntaxTraceValue_lookupCode current child childPositive childEarlier)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.syntaxTrace
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.strictTermCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.strictFormulaCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_strictFormulaCode
#print axioms RelationalPerimeter.HeytingArithmetic.syntaxTermLookupCode_current
#print axioms RelationalPerimeter.HeytingArithmetic.syntaxFormulaLookupCode_current
/- AXIOM_AUDIT_END -/
