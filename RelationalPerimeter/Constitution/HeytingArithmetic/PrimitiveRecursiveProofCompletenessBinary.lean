import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveProofCompletenessUnary

/-!
# Binary infrastructure for primitive-recursive proof completeness

Canonical two-premise archives expose both terminal premise frames and prove
that both references precede the newly emitted line.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

theorem encodeHistoryDerivation_binaryFirstFrame
    {history : TheoryHistory}
    {firstBound secondBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    let firstArchive := encodeHistoryDerivation first
    let combined :=
      firstArchive.appendRebased (encodeHistoryDerivation second)
    let archiveCode :=
      (embeddedArchive prefixLines (combined.finish line)
        suffixLines).quote
    let reference := prefixLines.length + firstArchive.lastIndex
    numericLineBound
        (numericArchiveLine archiveCode reference) = firstBound ∧
    numericLineContext
        (numericArchiveLine archiveCode reference) =
      firstContext.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode reference) =
      firstConclusion.raw.code := by
  dsimp only
  let firstArchive := encodeHistoryDerivation first
  let secondArchive := encodeHistoryDerivation second
  let combined := firstArchive.appendRebased secondArchive
  let futureLines :=
    (secondArchive.rebase
      (prefixLines.length + firstArchive.lineCount)).lines ++
      line.rebase prefixLines.length :: suffixLines
  have archiveEquation :
      embeddedArchive prefixLines (combined.finish line) suffixLines =
        embeddedArchive prefixLines firstArchive futureLines :=
    (embeddedArchive_finish prefixLines suffixLines combined line).trans
      (embeddedArchive_appendRebased_left prefixLines
        (line.rebase prefixLines.length :: suffixLines)
        firstArchive secondArchive)
  have archiveCodeEquation :=
    congrArg ProofArchive.quote archiveEquation
  have frame :=
    encodeHistoryDerivation_embeddedTerminalFrame first
      prefixLines futureLines
  rw [← archiveCodeEquation] at frame
  exact frame

theorem encodeHistoryDerivation_binarySecondFrame
    {history : TheoryHistory}
    {firstBound secondBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    let firstArchive := encodeHistoryDerivation first
    let secondArchive := encodeHistoryDerivation second
    let combined := firstArchive.appendRebased secondArchive
    let archiveCode :=
      (embeddedArchive prefixLines (combined.finish line)
        suffixLines).quote
    let reference := prefixLines.length + combined.lastIndex
    numericLineBound
        (numericArchiveLine archiveCode reference) = secondBound ∧
    numericLineContext
        (numericArchiveLine archiveCode reference) =
      secondContext.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode reference) =
      secondConclusion.raw.code := by
  dsimp only
  let firstArchive := encodeHistoryDerivation first
  let secondArchive := encodeHistoryDerivation second
  let combined := firstArchive.appendRebased secondArchive
  let secondPrefix :=
    prefixLines ++ (firstArchive.rebase prefixLines.length).lines
  have archiveEquation :
      embeddedArchive prefixLines (combined.finish line) suffixLines =
        embeddedArchive secondPrefix secondArchive
          (line.rebase prefixLines.length :: suffixLines) :=
    (embeddedArchive_finish prefixLines suffixLines combined line).trans
      (embeddedArchive_appendRebased_right prefixLines
        (line.rebase prefixLines.length :: suffixLines)
        firstArchive secondArchive)
  have archiveCodeEquation :=
    congrArg ProofArchive.quote archiveEquation
  have frame :=
    encodeHistoryDerivation_embeddedTerminalFrame second
      secondPrefix
      (line.rebase prefixLines.length :: suffixLines)
  rw [← archiveCodeEquation] at frame
  have secondPositive :=
    encodeHistoryDerivation_lineCount_positive_early second
  have secondPrefixLength :
      secondPrefix.length =
        prefixLines.length + firstArchive.lineCount := by
    unfold secondPrefix
    rw [listLengthAppendConstructive]
    change prefixLines.length +
        (firstArchive.rebase prefixLines.length).lineCount =
      prefixLines.length + firstArchive.lineCount
    rw [ProofArchive.lineCount_rebase]
  have combinedLastIndex :
      combined.lastIndex =
        firstArchive.lineCount + secondArchive.lastIndex := by
    unfold combined
    exact ProofArchive.lastIndex_appendRebased_of_positive
      firstArchive secondArchive secondPositive
  have referenceEquation :
      secondPrefix.length + secondArchive.lastIndex =
        prefixLines.length + combined.lastIndex := by
    rw [secondPrefixLength, combinedLastIndex]
    exact natAddAssocConstructive prefixLines.length
      firstArchive.lineCount secondArchive.lastIndex
  rw [referenceEquation] at frame
  exact frame

theorem encodeHistoryDerivation_binaryFirstChronologyBit
    {history : TheoryHistory}
    {firstBound secondBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength + (encodeHistoryDerivation first).lastIndex)
        (prefixLength +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lineCount) = 1 := by
  apply natLessBit_eq_one_of_lt
  apply Nat.add_lt_add_left
  exact Nat.lt_of_lt_of_le
    (by
      unfold ProofArchive.lastIndex
      exact Nat.pred_lt
        (Nat.ne_of_gt
          (encodeHistoryDerivation_lineCount_positive_early first)))
    (by
      rw [ProofArchive.lineCount_appendRebased]
      exact Nat.le_add_right _ _)

theorem encodeHistoryDerivation_binarySecondChronologyBit
    {history : TheoryHistory}
    {firstBound secondBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lastIndex)
        (prefixLength +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lineCount) = 1 := by
  apply natLessBit_eq_one_of_lt
  apply Nat.add_lt_add_left
  unfold ProofArchive.lastIndex
  apply Nat.pred_lt
  rw [ProofArchive.lineCount_appendRebased]
  exact Nat.ne_of_gt
    (Nat.add_pos_right _
      (encodeHistoryDerivation_lineCount_positive_early second))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_binaryFirstFrame
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_binarySecondFrame
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_binaryFirstChronologyBit
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_binarySecondChronologyBit
/- AXIOM_AUDIT_END -/
