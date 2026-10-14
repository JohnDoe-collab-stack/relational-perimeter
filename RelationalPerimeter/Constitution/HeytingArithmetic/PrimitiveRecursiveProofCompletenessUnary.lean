import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveProofCompletenessCore

/-!
# Unary infrastructure for primitive-recursive proof completeness

This module isolates the frame normalizer and the canonical embedding of a
single premise so later rule-by-rule completeness proofs reuse an opaque,
constructively audited interface.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open Lean.Parser.Tactic

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def EncodedTerminalLineAccepted
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) : Prop :=
    forall (prefixLines suffixLines : List ProofLine),
      numericCheckProofLine history.quote
        (embeddedArchive prefixLines
          (encodeHistoryDerivation proof) suffixLines).quote
        (prefixLines.length +
          (encodeHistoryDerivation proof).lastIndex) = 1

macro "close_encoded_terminal_line" : tactic =>
  `(tactic|
    unfold EncodedTerminalLineAccepted <;>
    intro prefixLines suffixLines <;>
    simp [proofCheckFold,
      PRFunction.checkProofLine, PRFunction.checkProofLineFrame,
      PRFunction.checkProofLineRules, PRFunction.checkProofLineRuleChecks,
      encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
      ProofLine.quote, proofLine, PRFunction.allBits, PRFunction.anyBits,
      unaryArchive, binaryArchive, ternaryArchive,
      List.map_append, List.append_assoc] <;>
    normalize_line_program <;>
    simp [ProofLine.rebase] <;>
    try simp [PRFunction.checkProofLineRuleBody,
      PRFunction.checkProofLineRuleBodies] <;>
    normalize_line_program <;>
    try simp [PRFunction.isContextCode_accepts,
      PRFunction.isScopedFormulaCode_accepts,
      PRFunction.isScopedTermCode_accepts,
      PRFunction.isHistoryAxiomCode_accepts_arithmetic,
      PRFunction.isHistoryAxiomCode_accepts_added])

@[simp] theorem PRFunction.run_checkProofLineFrame_numeric
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.checkProofLineFrame.run
        (proofCheckInputs historyCode archiveCode lineIndex) =
      natAndBit
        (natLessBit lineIndex (numericArchiveLineCount archiveCode))
        (natAndBit
          (PRFunction.isContextCode.run
            (NatVector.cons
              (numericLineBound
                (numericArchiveLine archiveCode lineIndex))
              (NatVector.cons
                (numericLineContext
                  (numericArchiveLine archiveCode lineIndex))
                NatVector.nil)))
          (natAndBit
            (PRFunction.isScopedFormulaCode.run
              (NatVector.cons
                (numericLineBound
                  (numericArchiveLine archiveCode lineIndex))
                (NatVector.cons
                  (numericLineConclusion
                    (numericArchiveLine archiveCode lineIndex))
                  NatVector.nil)))
            1)) := by
  unfold PRFunction.checkProofLineFrame PRFunction.allBits
    PRFunction.lessIn PRFunction.lineAtIn PRFunction.lineBoundIn
    PRFunction.lineContextIn PRFunction.lineConclusionIn proofCheckInputs
  repeat unfold PRFunction.allBits
  repeat first
    | rw [PRFunction.run_conjoin]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_lessBit]
    | rw [PRFunction.run_archiveLineCode_numeric]
    | rw [PRFunction.run_archiveLineCount_numeric]
    | rw [PRFunction.run_proofLineBound_numeric]
    | rw [PRFunction.run_proofLineContext_numeric]
    | rw [PRFunction.run_proofLineConclusion_numeric]

theorem encodeHistoryDerivation_unaryPremiseFrame
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    let premiseArchive := encodeHistoryDerivation premise
    let archiveCode :=
      (embeddedArchive prefixLines
        (premiseArchive.finish line) suffixLines).quote
    let reference := prefixLines.length + premiseArchive.lastIndex
    numericLineBound
        (numericArchiveLine archiveCode reference) = bound ∧
    numericLineContext
        (numericArchiveLine archiveCode reference) = context.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode reference) =
      conclusion.raw.code := by
  dsimp only
  have archiveCodeEquation :
      (embeddedArchive prefixLines
        ((encodeHistoryDerivation premise).finish line)
        suffixLines).quote =
      (embeddedArchive prefixLines (encodeHistoryDerivation premise)
        (line.rebase prefixLines.length :: suffixLines)).quote :=
    congrArg ProofArchive.quote
      (embeddedArchive_finish prefixLines suffixLines
        (encodeHistoryDerivation premise) line)
  have terminal :=
    encodeHistoryDerivation_embeddedTerminalFrame premise
      prefixLines (line.rebase prefixLines.length :: suffixLines)
  rw [← archiveCodeEquation] at terminal
  exact terminal

theorem encodeHistoryDerivation_lineCount_positive_early
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    0 < (encodeHistoryDerivation proof).lineCount :=
  @encodeDerivationWithAxiomParameters_lineCount_positive
    LogicMode.intuitionistic history.theory historyAxiomParameters
    bound context conclusion proof

theorem encodeHistoryDerivation_globalLastIndex_lt_finishIndex
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLength : Nat) :
    prefixLength + (encodeHistoryDerivation premise).lastIndex <
      prefixLength + (encodeHistoryDerivation premise).lineCount := by
  apply Nat.add_lt_add_left
  unfold ProofArchive.lastIndex
  exact Nat.pred_lt
    (Nat.ne_of_gt
      (encodeHistoryDerivation_lineCount_positive_early premise))

theorem encodeHistoryDerivation_unaryPremiseBound
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    numericLineBound
        (numericArchiveLine
          (embeddedArchive prefixLines
            ((encodeHistoryDerivation premise).finish line)
            suffixLines).quote
          (prefixLines.length +
            (encodeHistoryDerivation premise).lastIndex)) =
      bound :=
  (encodeHistoryDerivation_unaryPremiseFrame premise line
    prefixLines suffixLines).1

theorem encodeHistoryDerivation_unaryPremiseContext
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    numericLineContext
        (numericArchiveLine
          (embeddedArchive prefixLines
            ((encodeHistoryDerivation premise).finish line)
            suffixLines).quote
          (prefixLines.length +
            (encodeHistoryDerivation premise).lastIndex)) =
      context.quote :=
  (encodeHistoryDerivation_unaryPremiseFrame premise line
    prefixLines suffixLines).2.1

theorem encodeHistoryDerivation_unaryPremiseConclusion
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    numericLineConclusion
        (numericArchiveLine
          (embeddedArchive prefixLines
            ((encodeHistoryDerivation premise).finish line)
            suffixLines).quote
          (prefixLines.length +
            (encodeHistoryDerivation premise).lastIndex)) =
      conclusion.raw.code :=
  (encodeHistoryDerivation_unaryPremiseFrame premise line
    prefixLines suffixLines).2.2

theorem encodeHistoryDerivation_unaryChronologyBit
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength + (encodeHistoryDerivation premise).lastIndex)
        (prefixLength + (encodeHistoryDerivation premise).lineCount) = 1 :=
  natLessBit_eq_one_of_lt
    (encodeHistoryDerivation_globalLastIndex_lt_finishIndex
      premise prefixLength)

theorem encodeHistoryDerivation_unaryPremiseBound_transparent
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    numericLineBound
        (numericArchiveLine
          (embeddedArchive prefixLines
            ((encodeDerivationWithAxiomParameters
              historyAxiomParameters premise).finish line)
            suffixLines).quote
          (prefixLines.length +
            (encodeDerivationWithAxiomParameters
              historyAxiomParameters premise).lastIndex)) =
      bound :=
  encodeHistoryDerivation_unaryPremiseBound premise line
    prefixLines suffixLines

theorem encodeHistoryDerivation_unaryPremiseContext_transparent
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    numericLineContext
        (numericArchiveLine
          (embeddedArchive prefixLines
            ((encodeDerivationWithAxiomParameters
              historyAxiomParameters premise).finish line)
            suffixLines).quote
          (prefixLines.length +
            (encodeDerivationWithAxiomParameters
              historyAxiomParameters premise).lastIndex)) =
      context.quote :=
  encodeHistoryDerivation_unaryPremiseContext premise line
    prefixLines suffixLines

theorem encodeHistoryDerivation_unaryPremiseConclusion_transparent
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    numericLineConclusion
        (numericArchiveLine
          (embeddedArchive prefixLines
            ((encodeDerivationWithAxiomParameters
              historyAxiomParameters premise).finish line)
            suffixLines).quote
          (prefixLines.length +
            (encodeDerivationWithAxiomParameters
              historyAxiomParameters premise).lastIndex)) =
      conclusion.raw.code :=
  encodeHistoryDerivation_unaryPremiseConclusion premise line
    prefixLines suffixLines

theorem encodeHistoryDerivation_unaryChronologyBit_transparent
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength +
          (encodeDerivationWithAxiomParameters
            historyAxiomParameters premise).lastIndex)
        (prefixLength +
          (encodeDerivationWithAxiomParameters
            historyAxiomParameters premise).lineCount) = 1 :=
  encodeHistoryDerivation_unaryChronologyBit premise prefixLength

theorem ProofArchive.lastIndex_appendRebased_of_positive
    (earlier later : ProofArchive)
    (positive : 0 < later.lineCount) :
    (earlier.appendRebased later).lastIndex =
      earlier.lineCount + later.lastIndex := by
  unfold ProofArchive.lastIndex
  rw [ProofArchive.lineCount_appendRebased]
  cases countEquation : later.lineCount with
  | zero =>
      rw [countEquation] at positive
      exact (Nat.not_lt_zero 0 positive).elim
  | succ count =>
      rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_checkProofLineFrame_numeric
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_unaryPremiseFrame
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_lineCount_positive_early
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_unaryChronologyBit
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchive.lastIndex_appendRebased_of_positive
/- AXIOM_AUDIT_END -/
