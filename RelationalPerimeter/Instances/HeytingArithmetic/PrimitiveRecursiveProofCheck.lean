import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveProofLineChecking

/-!
# Primitive-recursive verification of a complete proof archive

The fold is bounded by the line count stored in the archive.  Its recursive
state is only the accumulated acceptance bit; chronological references are
checked by `checkProofLine`.  The terminal test requires a nonempty archive
whose last line is a closed proof of the requested sentence in the empty local
context.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem checkIndexZero_lt_three : 0 < 3 := Nat.zero_lt_succ 2
private theorem checkIndexOne_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)
private theorem checkIndexTwo_lt_three : 2 < 3 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
private theorem checkIndexOne_lt_five : 1 < 5 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 3)
private theorem checkIndexTwo_lt_five : 2 < 5 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
private theorem checkIndexThree_lt_five : 3 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
private theorem checkIndexFour_lt_five : 4 < 5 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

def proofCheckFold : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, accepted, _historyCode, _proofCode => accepted
  | Nat.succ index, accepted, historyCode, proofCode =>
      natAndBit (proofCheckFold index accepted historyCode proofCode)
        (PRFunction.checkProofLine.run
          (NatVector.cons historyCode
            (NatVector.cons proofCode
              (NatVector.cons index NatVector.nil))))

def PRFunction.proofCheckIterationStep : PRFunction 5 :=
  let index := PRFunction.projection 5 0 (Nat.zero_lt_succ 4)
  let previous := PRFunction.projection 5 1 checkIndexOne_lt_five
  let history := PRFunction.projection 5 3 checkIndexThree_lt_five
  let proof := PRFunction.projection 5 4 checkIndexFour_lt_five
  let current := PRFunction.composition PRFunction.checkProofLine
    (PRFunctionVector.cons history
      (PRFunctionVector.cons proof (PRFunctionVector.singleton index)))
  PRFunction.binaryIn PRFunction.andBit previous current

def PRFunction.proofCheckFold : PRFunction 4 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 3 0 checkIndexZero_lt_three)
    PRFunction.proofCheckIterationStep

def proofCheckBit (historyCode proofCode sentenceCode : Nat) : Nat :=
  let lineCount := natUnpairLeft proofCode
  let accepted := _root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
    lineCount 1 historyCode proofCode
  let lastLine := betaComponent
    (natUnpairLeft (natUnpairRight proofCode))
    (natUnpairRight (natUnpairRight proofCode)) lineCount.pred
  natAndBit (natPositiveBit lineCount)
    (natAndBit accepted
      (natAndBit (natEqualBit (natUnpairLeft (natUnpairRight lastLine)) 0)
        (natAndBit
          (natEqualBit
            (natUnpairLeft (natUnpairRight (natUnpairRight lastLine))) 0)
          (natAndBit
            (natEqualBit
              (natUnpairLeft
                (natUnpairRight
                  (natUnpairRight (natUnpairRight lastLine))))
              sentenceCode)
            (natAndBit
              (PRFunction.isScopedFormulaCode.run
      (NatVector.cons 0
                  (NatVector.cons sentenceCode NatVector.nil))) 1)))))

/-! Named terminal-checker components keep evaluation opaque at module scale. -/

def PRFunction.proofCheckLineCount : PRFunction 3 :=
  PRFunction.unaryIn PRFunction.archiveLineCount
    PRFunction.proofCheckArchive

def PRFunction.proofCheckAccepted : PRFunction 3 :=
  PRFunction.composition PRFunction.proofCheckFold
    (PRFunctionVector.cons PRFunction.proofCheckLineCount
      (PRFunctionVector.cons (PRFunction.constant 3 1)
        (PRFunctionVector.cons PRFunction.proofCheckHistory
          (PRFunctionVector.singleton PRFunction.proofCheckArchive))))

def PRFunction.proofCheckLastIndex : PRFunction 3 :=
  PRFunction.unaryIn PRFunction.predecessor
    PRFunction.proofCheckLineCount

def PRFunction.proofCheckLastLine : PRFunction 3 :=
  PRFunction.lineAtIn PRFunction.proofCheckArchive
    PRFunction.proofCheckLastIndex

def PRFunction.proofCheckLastBound : PRFunction 3 :=
  PRFunction.lineBoundIn PRFunction.proofCheckLastLine

def PRFunction.proofCheckLastContext : PRFunction 3 :=
  PRFunction.lineContextIn PRFunction.proofCheckLastLine

def PRFunction.proofCheckLastConclusion : PRFunction 3 :=
  PRFunction.lineConclusionIn PRFunction.proofCheckLastLine

def PRFunction.proofCheckLineCountPositive : PRFunction 3 :=
  PRFunction.unaryIn PRFunction.positiveBit
    PRFunction.proofCheckLineCount

def PRFunction.proofCheckLastBoundZero : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckLastBound
    (PRFunction.constant 3 0)

def PRFunction.proofCheckLastContextZero : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckLastContext
    (PRFunction.constant 3 0)

def PRFunction.proofCheckLastConclusionExact : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckLastConclusion
    PRFunction.proofCheckIndex

def PRFunction.proofCheckSentenceScoped : PRFunction 3 :=
  PRFunction.composition PRFunction.isScopedFormulaCode
    (PRFunctionVector.cons (PRFunction.constant 3 0)
      (PRFunctionVector.singleton PRFunction.proofCheckIndex))

/-- The terminal three-input proof verifier. -/
def PRFunction.proofCheck : PRFunction 3 :=
  PRFunction.allBits [
    PRFunction.proofCheckLineCountPositive,
    PRFunction.proofCheckAccepted,
    PRFunction.proofCheckLastBoundZero,
    PRFunction.proofCheckLastContextZero,
    PRFunction.proofCheckLastConclusionExact,
    PRFunction.proofCheckSentenceScoped]

@[simp] theorem PRFunction.run_proofCheckIterationStep
    (index previous initialAccepted history proof : Nat) :
    PRFunction.proofCheckIterationStep.run
        (NatVector.cons index
          (NatVector.cons previous
            (NatVector.cons initialAccepted
              (NatVector.cons history
                (NatVector.cons proof NatVector.nil))))) =
      natAndBit previous
        (PRFunction.checkProofLine.run
          (NatVector.cons history
            (NatVector.cons proof
              (NatVector.cons index NatVector.nil)))) := by
  unfold PRFunction.proofCheckIterationStep
  rw [PRFunction.run_binaryIn, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_succ,
    NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_succ,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_zero,
    PRFunction.run_andBit]

@[simp] theorem PRFunction.run_positiveBit (value : Nat) :
    PRFunction.positiveBit.run (NatVector.cons value NatVector.nil) =
      natPositiveBit value :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.positiveBit_evaluates value)

private theorem PRFunction.run_proofCheckFold_zero
    (accepted history proof : Nat) :
    PRFunction.proofCheckFold.run
        (NatVector.cons 0
          (NatVector.cons accepted
            (NatVector.cons history
              (NatVector.cons proof NatVector.nil)))) = accepted := by
  unfold PRFunction.proofCheckFold
  exact (PRFunction.Evaluates.runCore_primitive_zero
    (PRFunction.projection 3 0 checkIndexZero_lt_three)
    PRFunction.proofCheckIterationStep
    (NatVector.cons accepted
      (NatVector.cons history
        (NatVector.cons proof NatVector.nil)))).trans rfl

private theorem PRFunction.run_proofCheckFold_succ
    (lineCount accepted history proof : Nat) :
    PRFunction.proofCheckFold.run
        (NatVector.cons (Nat.succ lineCount)
          (NatVector.cons accepted
            (NatVector.cons history
              (NatVector.cons proof NatVector.nil)))) =
      PRFunction.proofCheckIterationStep.run
        (NatVector.cons lineCount
          (NatVector.cons
            (PRFunction.proofCheckFold.run
              (NatVector.cons lineCount
                (NatVector.cons accepted
                  (NatVector.cons history
                    (NatVector.cons proof NatVector.nil)))))
            (NatVector.cons accepted
              (NatVector.cons history
                (NatVector.cons proof NatVector.nil))))) := by
  unfold PRFunction.proofCheckFold
  exact PRFunction.Evaluates.runCore_primitive_succ
    (PRFunction.projection 3 0 checkIndexZero_lt_three)
    PRFunction.proofCheckIterationStep lineCount
    (NatVector.cons accepted
      (NatVector.cons history
        (NatVector.cons proof NatVector.nil)))

theorem PRFunction.run_proofCheckFold
    (lineCount accepted history proof : Nat) :
    PRFunction.proofCheckFold.run
        (NatVector.cons lineCount
          (NatVector.cons accepted
            (NatVector.cons history
              (NatVector.cons proof NatVector.nil)))) =
      RelationalPerimeter.HeytingArithmetic.proofCheckFold
        lineCount accepted history proof := by
  induction lineCount with
  | zero =>
      exact PRFunction.run_proofCheckFold_zero accepted history proof
  | succ lineCount inductionHypothesis =>
      rw [PRFunction.run_proofCheckFold_succ,
        PRFunction.run_proofCheckIterationStep, inductionHypothesis]
      rfl

/-!
`PRFunction.proofCheckFold` has constant base one, so its exact public equation
is stated at that canonical initial bit.  No other initial value is used by the
terminal checker.
-/
theorem PRFunction.run_proofCheckFold_one
    (lineCount history proof : Nat) :
    PRFunction.proofCheckFold.run
        (NatVector.cons lineCount
          (NatVector.cons 1
            (NatVector.cons history
              (NatVector.cons proof NatVector.nil)))) =
      RelationalPerimeter.HeytingArithmetic.proofCheckFold
        lineCount 1 history proof := by
  exact PRFunction.run_proofCheckFold lineCount 1 history proof

private theorem PRFunction.run_proofCheckHistory_terminal
    (history proof sentence : Nat) :
    PRFunction.proofCheckHistory.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) = history := by
  rfl

private theorem PRFunction.run_proofCheckArchive_terminal
    (history proof sentence : Nat) :
    PRFunction.proofCheckArchive.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) = proof := by
  rfl

private theorem PRFunction.run_proofCheckIndex_terminal
    (history proof sentence : Nat) :
    PRFunction.proofCheckIndex.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) = sentence := by
  rfl

@[simp] private theorem PRFunction.run_proofCheckLineCount
    (history proof sentence : Nat) :
    PRFunction.proofCheckLineCount.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natUnpairLeft proof := by
  unfold PRFunction.proofCheckLineCount
  rw [PRFunction.run_unaryIn, PRFunction.run_archiveLineCount,
    PRFunction.run_proofCheckArchive_terminal]

@[simp] private theorem PRFunction.run_proofCheckAccepted
    (history proof sentence : Nat) :
    PRFunction.proofCheckAccepted.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      RelationalPerimeter.HeytingArithmetic.proofCheckFold
        (natUnpairLeft proof) 1 history proof := by
  unfold PRFunction.proofCheckAccepted
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_proofCheckLineCount, PRFunction.run_constant,
    PRFunction.run_proofCheckHistory_terminal,
    PRFunction.run_proofCheckArchive_terminal,
    PRFunction.run_proofCheckFold_one]

@[simp] private theorem PRFunction.run_proofCheckLastIndex
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastIndex.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      (natUnpairLeft proof).pred := by
  unfold PRFunction.proofCheckLastIndex
  rw [PRFunction.run_unaryIn, PRFunction.run_proofCheckLineCount,
    PRFunction.run_predecessor]

@[simp] private theorem PRFunction.run_proofCheckLastLine
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastLine.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      betaComponent
        (natUnpairLeft (natUnpairRight proof))
        (natUnpairRight (natUnpairRight proof))
        (natUnpairLeft proof).pred := by
  unfold PRFunction.proofCheckLastLine PRFunction.lineAtIn
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_proofCheckArchive_terminal,
    PRFunction.run_proofCheckLastIndex,
    PRFunction.run_archiveLineCode]

@[simp] private theorem PRFunction.run_proofCheckLastBound
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastBound.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natUnpairLeft (natUnpairRight
        (betaComponent
          (natUnpairLeft (natUnpairRight proof))
          (natUnpairRight (natUnpairRight proof))
          (natUnpairLeft proof).pred)) := by
  unfold PRFunction.proofCheckLastBound PRFunction.lineBoundIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofCheckLastLine,
    PRFunction.run_proofLineBound]

@[simp] private theorem PRFunction.run_proofCheckLastContext
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastContext.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natUnpairLeft (natUnpairRight (natUnpairRight
        (betaComponent
          (natUnpairLeft (natUnpairRight proof))
          (natUnpairRight (natUnpairRight proof))
          (natUnpairLeft proof).pred))) := by
  unfold PRFunction.proofCheckLastContext PRFunction.lineContextIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofCheckLastLine,
    PRFunction.run_proofLineContext]

@[simp] private theorem PRFunction.run_proofCheckLastConclusion
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastConclusion.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natUnpairLeft (natUnpairRight (natUnpairRight (natUnpairRight
        (betaComponent
          (natUnpairLeft (natUnpairRight proof))
          (natUnpairRight (natUnpairRight proof))
          (natUnpairLeft proof).pred)))) := by
  unfold PRFunction.proofCheckLastConclusion PRFunction.lineConclusionIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofCheckLastLine,
    PRFunction.run_proofLineConclusion]

@[simp] private theorem PRFunction.run_proofCheckLineCountPositive
    (history proof sentence : Nat) :
    PRFunction.proofCheckLineCountPositive.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natPositiveBit (natUnpairLeft proof) := by
  unfold PRFunction.proofCheckLineCountPositive
  rw [PRFunction.run_unaryIn, PRFunction.run_proofCheckLineCount,
    PRFunction.run_positiveBit]

@[simp] private theorem PRFunction.run_proofCheckLastBoundZero
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastBoundZero.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natEqualBit
        (natUnpairLeft (natUnpairRight
          (betaComponent
            (natUnpairLeft (natUnpairRight proof))
            (natUnpairRight (natUnpairRight proof))
            (natUnpairLeft proof).pred))) 0 := by
  unfold PRFunction.proofCheckLastBoundZero PRFunction.sameIn
  rw [PRFunction.run_binaryIn, PRFunction.run_proofCheckLastBound,
    PRFunction.run_constant, PRFunction.run_equalBit]

@[simp] private theorem PRFunction.run_proofCheckLastContextZero
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastContextZero.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natEqualBit
        (natUnpairLeft (natUnpairRight (natUnpairRight
          (betaComponent
            (natUnpairLeft (natUnpairRight proof))
            (natUnpairRight (natUnpairRight proof))
            (natUnpairLeft proof).pred)))) 0 := by
  unfold PRFunction.proofCheckLastContextZero PRFunction.sameIn
  rw [PRFunction.run_binaryIn, PRFunction.run_proofCheckLastContext,
    PRFunction.run_constant, PRFunction.run_equalBit]

@[simp] private theorem PRFunction.run_proofCheckLastConclusionExact
    (history proof sentence : Nat) :
    PRFunction.proofCheckLastConclusionExact.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      natEqualBit
        (natUnpairLeft (natUnpairRight (natUnpairRight (natUnpairRight
          (betaComponent
            (natUnpairLeft (natUnpairRight proof))
            (natUnpairRight (natUnpairRight proof))
            (natUnpairLeft proof).pred))))) sentence := by
  unfold PRFunction.proofCheckLastConclusionExact PRFunction.sameIn
  rw [PRFunction.run_binaryIn, PRFunction.run_proofCheckLastConclusion,
    PRFunction.run_proofCheckIndex_terminal, PRFunction.run_equalBit]

@[simp] private theorem PRFunction.run_proofCheckSentenceScoped
    (history proof sentence : Nat) :
    PRFunction.proofCheckSentenceScoped.run
        (NatVector.cons history
          (NatVector.cons proof
            (NatVector.cons sentence NatVector.nil))) =
      PRFunction.isScopedFormulaCode.run
        (NatVector.cons 0 (NatVector.cons sentence NatVector.nil)) := by
  unfold PRFunction.proofCheckSentenceScoped
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_constant,
    PRFunction.run_proofCheckIndex_terminal]

private theorem PRFunction.run_allBits
    {arity : Nat}
    (checks : List (PRFunction arity))
    (inputs : NatVector arity) :
    (PRFunction.allBits checks).run inputs =
      checks.foldr (fun check tail => natAndBit (check.run inputs) tail) 1 := by
  induction checks with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact (PRFunction.run_conjoin head (PRFunction.allBits tail) inputs).trans
        (congrArg (natAndBit (head.run inputs)) inductionHypothesis)

theorem PRFunction.run_proofCheck
    (historyCode proofCode sentenceCode : Nat) :
    PRFunction.proofCheck.run
        (NatVector.cons historyCode
          (NatVector.cons proofCode
            (NatVector.cons sentenceCode NatVector.nil))) =
      proofCheckBit historyCode proofCode sentenceCode := by
  let inputs := NatVector.cons historyCode
    (NatVector.cons proofCode
      (NatVector.cons sentenceCode NatVector.nil))
  let lineCount := natUnpairLeft proofCode
  let lastLine := betaComponent
    (natUnpairLeft (natUnpairRight proofCode))
    (natUnpairRight (natUnpairRight proofCode)) lineCount.pred
  have positiveExact := PRFunction.run_proofCheckLineCountPositive
    historyCode proofCode sentenceCode
  have acceptedExact := PRFunction.run_proofCheckAccepted
    historyCode proofCode sentenceCode
  have boundExact := PRFunction.run_proofCheckLastBoundZero
    historyCode proofCode sentenceCode
  have contextExact := PRFunction.run_proofCheckLastContextZero
    historyCode proofCode sentenceCode
  have conclusionExact := PRFunction.run_proofCheckLastConclusionExact
    historyCode proofCode sentenceCode
  have scopedExact := PRFunction.run_proofCheckSentenceScoped
    historyCode proofCode sentenceCode
  change (PRFunction.allBits [
    PRFunction.proofCheckLineCountPositive,
    PRFunction.proofCheckAccepted,
    PRFunction.proofCheckLastBoundZero,
    PRFunction.proofCheckLastContextZero,
    PRFunction.proofCheckLastConclusionExact,
    PRFunction.proofCheckSentenceScoped]).run inputs = _
  calc
    _ = natAndBit (PRFunction.proofCheckLineCountPositive.run inputs)
        (natAndBit (PRFunction.proofCheckAccepted.run inputs)
          (natAndBit (PRFunction.proofCheckLastBoundZero.run inputs)
            (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
              (natAndBit
                (PRFunction.proofCheckLastConclusionExact.run inputs)
                (natAndBit
                  (PRFunction.proofCheckSentenceScoped.run inputs) 1))))) :=
      PRFunction.run_allBits _ inputs
    _ = natAndBit (natPositiveBit lineCount)
        (natAndBit (PRFunction.proofCheckAccepted.run inputs)
          (natAndBit (PRFunction.proofCheckLastBoundZero.run inputs)
            (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
              (natAndBit
                (PRFunction.proofCheckLastConclusionExact.run inputs)
                (natAndBit
                  (PRFunction.proofCheckSentenceScoped.run inputs) 1))))) :=
      congrArg
        (fun value => natAndBit value
          (natAndBit (PRFunction.proofCheckAccepted.run inputs)
            (natAndBit (PRFunction.proofCheckLastBoundZero.run inputs)
              (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
                (natAndBit
                  (PRFunction.proofCheckLastConclusionExact.run inputs)
                  (natAndBit
                    (PRFunction.proofCheckSentenceScoped.run inputs) 1))))))
        positiveExact
    _ = natAndBit (natPositiveBit lineCount)
        (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
          lineCount 1 historyCode proofCode)
          (natAndBit (PRFunction.proofCheckLastBoundZero.run inputs)
            (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
              (natAndBit
                (PRFunction.proofCheckLastConclusionExact.run inputs)
                (natAndBit
                  (PRFunction.proofCheckSentenceScoped.run inputs) 1))))) :=
      congrArg (natAndBit (natPositiveBit lineCount))
        (congrArg
          (fun value => natAndBit value
            (natAndBit (PRFunction.proofCheckLastBoundZero.run inputs)
              (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
                (natAndBit
                  (PRFunction.proofCheckLastConclusionExact.run inputs)
                  (natAndBit
                    (PRFunction.proofCheckSentenceScoped.run inputs) 1)))))
          acceptedExact)
    _ = natAndBit (natPositiveBit lineCount)
        (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
          lineCount 1 historyCode proofCode)
          (natAndBit (natEqualBit (natUnpairLeft
            (natUnpairRight lastLine)) 0)
            (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
              (natAndBit
                (PRFunction.proofCheckLastConclusionExact.run inputs)
                (natAndBit
                  (PRFunction.proofCheckSentenceScoped.run inputs) 1))))) :=
      congrArg
        (fun value => natAndBit (natPositiveBit lineCount)
          (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
            lineCount 1 historyCode proofCode)
            (natAndBit value
              (natAndBit (PRFunction.proofCheckLastContextZero.run inputs)
                (natAndBit
                  (PRFunction.proofCheckLastConclusionExact.run inputs)
                  (natAndBit
                    (PRFunction.proofCheckSentenceScoped.run inputs) 1))))))
        boundExact
    _ = natAndBit (natPositiveBit lineCount)
        (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
          lineCount 1 historyCode proofCode)
          (natAndBit (natEqualBit (natUnpairLeft
            (natUnpairRight lastLine)) 0)
            (natAndBit (natEqualBit (natUnpairLeft
              (natUnpairRight (natUnpairRight lastLine))) 0)
              (natAndBit
                (PRFunction.proofCheckLastConclusionExact.run inputs)
                (natAndBit
                  (PRFunction.proofCheckSentenceScoped.run inputs) 1))))) :=
      congrArg
        (fun value => natAndBit (natPositiveBit lineCount)
          (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
            lineCount 1 historyCode proofCode)
            (natAndBit (natEqualBit (natUnpairLeft
              (natUnpairRight lastLine)) 0)
              (natAndBit value
                (natAndBit
                  (PRFunction.proofCheckLastConclusionExact.run inputs)
                  (natAndBit
                    (PRFunction.proofCheckSentenceScoped.run inputs) 1))))))
        contextExact
    _ = natAndBit (natPositiveBit lineCount)
        (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
          lineCount 1 historyCode proofCode)
          (natAndBit (natEqualBit (natUnpairLeft
            (natUnpairRight lastLine)) 0)
            (natAndBit (natEqualBit (natUnpairLeft
              (natUnpairRight (natUnpairRight lastLine))) 0)
              (natAndBit (natEqualBit (natUnpairLeft
                (natUnpairRight (natUnpairRight
                  (natUnpairRight lastLine)))) sentenceCode)
                (natAndBit
                  (PRFunction.proofCheckSentenceScoped.run inputs) 1))))) :=
      congrArg
        (fun value => natAndBit (natPositiveBit lineCount)
          (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
            lineCount 1 historyCode proofCode)
            (natAndBit (natEqualBit (natUnpairLeft
              (natUnpairRight lastLine)) 0)
              (natAndBit (natEqualBit (natUnpairLeft
                (natUnpairRight (natUnpairRight lastLine))) 0)
                (natAndBit value
                  (natAndBit
                    (PRFunction.proofCheckSentenceScoped.run inputs) 1))))))
        conclusionExact
    _ = proofCheckBit historyCode proofCode sentenceCode := by
      unfold proofCheckBit
      exact congrArg
        (fun value => natAndBit (natPositiveBit lineCount)
          (natAndBit (_root_.RelationalPerimeter.HeytingArithmetic.proofCheckFold
            lineCount 1 historyCode proofCode)
            (natAndBit (natEqualBit (natUnpairLeft
              (natUnpairRight lastLine)) 0)
              (natAndBit (natEqualBit (natUnpairLeft
                (natUnpairRight (natUnpairRight lastLine))) 0)
                (natAndBit (natEqualBit (natUnpairLeft
                  (natUnpairRight (natUnpairRight
                    (natUnpairRight lastLine)))) sentenceCode)
                  (natAndBit value 1))))))
        scopedExact

theorem PRFunction.proofCheck_evaluates
    (historyCode proofCode sentenceCode : Nat) :
    PRFunction.Evaluates PRFunction.proofCheck
      (NatVector.cons historyCode
        (NatVector.cons proofCode
          (NatVector.cons sentenceCode NatVector.nil)))
      (proofCheckBit historyCode proofCode sentenceCode) := by
  have evaluation := PRFunction.proofCheck.run_evaluates
    (NatVector.cons historyCode
      (NatVector.cons proofCode
        (NatVector.cons sentenceCode NatVector.nil)))
  unfold PRFunction.Evaluates at evaluation ⊢
  rw [PRFunction.run_proofCheck] at evaluation
  exact evaluation

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.proofCheck
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_proofCheck
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.proofCheck_evaluates
/- AXIOM_AUDIT_END -/
