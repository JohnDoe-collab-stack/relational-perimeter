import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveComparison
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveUnpair

/-!
# Pair-coded primitive-recursive traces

A finite trace is stored newest-first as repeated `natPair result history`.
Lookup drops a bounded number of tails with `unpairRight`, then reads the head
with `unpairLeft`.  This is the trace representation used for course-of-values
transformations of syntax codes.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Iteration of the total right-component operation. -/
def natIterateUnpairRight : Nat -> Nat -> Nat
  | 0, history => history
  | Nat.succ offset, history =>
      natUnpairRight (natIterateUnpairRight offset history)

/-- Apply `unpairRight` to the previous iteration result. -/
def PRFunction.unpairRightOfPrevious : PRFunction 3 :=
  PRFunction.composition
    PRFunction.unpairRight
    (PRFunctionVector.singleton
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

/-- Primitive-recursive iteration of pair-coded trace tails. -/
def PRFunction.iterateUnpairRight : PRFunction 2 :=
  PRFunction.primitiveRecursion
    PRFunction.identity
    PRFunction.unpairRightOfPrevious

/-- The explicit tail iterator computes `natIterateUnpairRight`. -/
theorem PRFunction.iterateUnpairRight_evaluates
    (offset history : Nat) :
    PRFunction.Evaluates
      PRFunction.iterateUnpairRight
      (NatVector.cons offset
        (NatVector.cons history NatVector.nil))
      (natIterateUnpairRight offset history) := by
  induction offset with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.projection
          0
          (Nat.zero_lt_succ 0)
          (NatVector.cons history NatVector.nil))
  | succ offset inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
            (NatVector.cons offset
              (NatVector.cons (natIterateUnpairRight offset history)
                (NatVector.cons history NatVector.nil)))
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons offset
              (NatVector.cons (natIterateUnpairRight offset history)
                (NatVector.cons history NatVector.nil)))
      · exact PRFunction.unpairRight_evaluates
          (natIterateUnpairRight offset history)

/-- Read the trace entry at a newest-first offset. -/
def natTraceLookup (offset history : Nat) : Nat :=
  natUnpairLeft (natIterateUnpairRight offset history)

/-- The trace tail selected by a two-input `(offset, history)` context. -/
def PRFunction.traceTailAt : PRFunction 2 :=
  PRFunction.iterateUnpairRight

/-- Primitive-recursive newest-first trace lookup. -/
def PRFunction.traceLookup : PRFunction 2 :=
  PRFunction.composition
    PRFunction.unpairLeft
    (PRFunctionVector.singleton PRFunction.traceTailAt)

/-- The explicit lookup program computes `natTraceLookup`. -/
theorem PRFunction.traceLookup_evaluates (offset history : Nat) :
    PRFunction.Evaluates
      PRFunction.traceLookup
      (NatVector.cons offset
        (NatVector.cons history NatVector.nil))
      (natTraceLookup offset history) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact PRFunction.iterateUnpairRight_evaluates offset history
    · exact PRFunctionVector.Evaluates.nil
        (NatVector.cons offset
          (NatVector.cons history NatVector.nil))
  · exact PRFunction.unpairLeft_evaluates
      (natIterateUnpairRight offset history)

/-- Read a child-code result from the trace preceding `currentCode`. -/
def natTraceLookupCode
    (currentCode childCode history : Nat) :
    Nat :=
  natTraceLookup (currentCode.pred - childCode) history

/-- Predecessor of the current code in a `(current, child, history)` context. -/
def PRFunction.traceCurrentPredecessor : PRFunction 3 :=
  PRFunction.composition
    PRFunction.predecessor
    (PRFunctionVector.singleton
      (PRFunction.projection 3 0 (Nat.zero_lt_succ 2)))

/-- Newest-first offset corresponding to an earlier absolute child code. -/
def PRFunction.traceCodeOffset : PRFunction 3 :=
  PRFunction.composition
    PRFunction.subtract
    (PRFunctionVector.cons
      PRFunction.traceCurrentPredecessor
      (PRFunctionVector.singleton
        (PRFunction.projection 3 1
          (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))))

/-- Primitive-recursive lookup by current and child syntax codes. -/
def PRFunction.traceLookupCode : PRFunction 3 :=
  PRFunction.composition
    PRFunction.traceLookup
    (PRFunctionVector.cons
      PRFunction.traceCodeOffset
      (PRFunctionVector.singleton
        (PRFunction.projection 3 2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))

/-- The absolute-code lookup program computes `natTraceLookupCode`. -/
theorem PRFunction.traceLookupCode_evaluates
    (currentCode childCode history : Nat) :
    PRFunction.Evaluates
      PRFunction.traceLookupCode
      (NatVector.cons currentCode
        (NatVector.cons childCode
          (NatVector.cons history NatVector.nil)))
      (natTraceLookupCode currentCode childCode history) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · apply PRFunction.Evaluates.composition
          · apply PRFunctionVector.Evaluates.cons
            · exact PRFunction.Evaluates.projection
                0
                (Nat.zero_lt_succ 2)
                (NatVector.cons currentCode
                  (NatVector.cons childCode
                    (NatVector.cons history NatVector.nil)))
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons currentCode
                  (NatVector.cons childCode
                    (NatVector.cons history NatVector.nil)))
          · exact PRFunction.predecessor_evaluates currentCode
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              1
              (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
              (NatVector.cons currentCode
                (NatVector.cons childCode
                  (NatVector.cons history NatVector.nil)))
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons currentCode
                (NatVector.cons childCode
                  (NatVector.cons history NatVector.nil)))
      · exact PRFunction.subtract_evaluates currentCode.pred childCode
    · apply PRFunctionVector.Evaluates.cons
      · exact PRFunction.Evaluates.projection
          2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
          (NatVector.cons currentCode
            (NatVector.cons childCode
              (NatVector.cons history NatVector.nil)))
      · exact PRFunctionVector.Evaluates.nil
          (NatVector.cons currentCode
            (NatVector.cons childCode
              (NatVector.cons history NatVector.nil)))
  · exact PRFunction.traceLookup_evaluates
      (currentCode.pred - childCode)
      history

/-- Moving one iteration outside is extensionally the same tail operation. -/
theorem natIterateUnpairRight_succ (offset history : Nat) :
    natIterateUnpairRight (Nat.succ offset) history =
      natIterateUnpairRight offset (natUnpairRight history) := by
  induction offset with
  | zero => rfl
  | succ offset inductionHypothesis =>
      change
        natUnpairRight
          (natIterateUnpairRight (Nat.succ offset) history) =
        natUnpairRight
          (natIterateUnpairRight offset (natUnpairRight history))
      rw [inductionHypothesis]

/-- Offset zero reads the newest result. -/
theorem natTraceLookup_zero_pair (head history : Nat) :
    natTraceLookup 0 (natPair head history) = head := by
  change natUnpairLeft (natPair head history) = head
  exact natUnpairLeft_pair head history

/-- A positive offset skips the newest result. -/
theorem natTraceLookup_succ_pair (offset head history : Nat) :
    natTraceLookup (Nat.succ offset) (natPair head history) =
      natTraceLookup offset history := by
  change
    natUnpairLeft
      (natIterateUnpairRight (Nat.succ offset)
        (natPair head history)) =
      natUnpairLeft (natIterateUnpairRight offset history)
  rw [natIterateUnpairRight_succ]
  rw [natUnpairRight_pair]

/-- Prepend an element program's result to the previous trace. -/
def PRFunction.prependToPrevious
    {parameterArity : Nat}
    (element : PRFunction (Nat.succ (Nat.succ parameterArity))) :
    PRFunction (Nat.succ (Nat.succ parameterArity)) :=
  PRFunction.composition
    PRFunction.pair
    (PRFunctionVector.cons
      element
      (PRFunctionVector.singleton
        (PRFunction.projection
          (Nat.succ (Nat.succ parameterArity))
          1
          (Nat.succ_lt_succ
            (Nat.zero_lt_succ parameterArity)))))

/-- Prepending executes to the pair of the new result and previous trace. -/
theorem PRFunction.prependToPrevious_evaluates
    {parameterArity : Nat}
    (element : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (inputs : NatVector (Nat.succ (Nat.succ parameterArity)))
    (elementOutput : Nat)
    (elementEvaluation :
      PRFunction.Evaluates element inputs elementOutput) :
    PRFunction.Evaluates
      (PRFunction.prependToPrevious element)
      inputs
      (natPair elementOutput
        (inputs.get 1
          (Nat.succ_lt_succ
            (Nat.zero_lt_succ parameterArity)))) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact elementEvaluation
    · apply PRFunctionVector.Evaluates.cons
      · exact PRFunction.Evaluates.projection
          1
          (Nat.succ_lt_succ
            (Nat.zero_lt_succ parameterArity))
          inputs
      · exact PRFunctionVector.Evaluates.nil inputs
  · exact PRFunction.pair_evaluates
      elementOutput
      (inputs.get 1
        (Nat.succ_lt_succ
          (Nat.zero_lt_succ parameterArity)))

/-- Build a newest-first trace by ordinary primitive recursion. -/
def PRFunction.traceBuilder
    {parameterArity : Nat}
    (element : PRFunction (Nat.succ (Nat.succ parameterArity))) :
    PRFunction (Nat.succ parameterArity) :=
  PRFunction.primitiveRecursion
    PRFunction.zero
    (PRFunction.prependToPrevious element)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.iterateUnpairRight
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.iterateUnpairRight_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.traceLookup
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.traceLookup_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.traceLookupCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.traceLookupCode_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.natTraceLookup_zero_pair
#print axioms RelationalPerimeter.HeytingArithmetic.natTraceLookup_succ_pair
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.prependToPrevious
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.prependToPrevious_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.traceBuilder
/- AXIOM_AUDIT_END -/
