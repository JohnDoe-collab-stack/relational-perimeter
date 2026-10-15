import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveProofCompletenessBinary

/-!
# Completeness of the primitive-recursive proof verifier

Every typed derivation is accepted by its canonical chronological archive.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open Lean.Parser.Tactic

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

theorem encodeHistoryDerivation_ternaryFirstFrame
    {history : TheoryHistory}
    {firstBound secondBound thirdBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {thirdContext : FormulaContext thirdBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    {thirdConclusion : ScopedFormula thirdBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (third :
      Derivation LogicMode.intuitionistic history.theory
        thirdContext thirdConclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    let firstArchive := encodeHistoryDerivation first
    let secondArchive := encodeHistoryDerivation second
    let thirdArchive := encodeHistoryDerivation third
    let firstSecond := firstArchive.appendRebased secondArchive
    let combined := firstSecond.appendRebased thirdArchive
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
  rw [embeddedArchive_finish, embeddedArchive_appendRebased_left,
    embeddedArchive_appendRebased_left]
  exact encodeHistoryDerivation_embeddedTerminalFrame first
    prefixLines
    (((encodeHistoryDerivation second).rebase
        (prefixLines.length +
          (encodeHistoryDerivation first).lineCount)).lines ++
      (((encodeHistoryDerivation third).rebase
        (prefixLines.length +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lineCount)).lines ++
        line.rebase prefixLines.length :: suffixLines))

theorem encodeHistoryDerivation_ternarySecondFrame
    {history : TheoryHistory}
    {firstBound secondBound thirdBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {thirdContext : FormulaContext thirdBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    {thirdConclusion : ScopedFormula thirdBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (third :
      Derivation LogicMode.intuitionistic history.theory
        thirdContext thirdConclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    let firstArchive := encodeHistoryDerivation first
    let secondArchive := encodeHistoryDerivation second
    let thirdArchive := encodeHistoryDerivation third
    let firstSecond := firstArchive.appendRebased secondArchive
    let combined := firstSecond.appendRebased thirdArchive
    let archiveCode :=
      (embeddedArchive prefixLines (combined.finish line)
        suffixLines).quote
    let reference := prefixLines.length + firstSecond.lastIndex
    numericLineBound
        (numericArchiveLine archiveCode reference) = secondBound ∧
    numericLineContext
        (numericArchiveLine archiveCode reference) =
      secondContext.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode reference) =
      secondConclusion.raw.code := by
  dsimp only
  rw [embeddedArchive_finish, embeddedArchive_appendRebased_left,
    embeddedArchive_appendRebased_right]
  have frame :=
    encodeHistoryDerivation_embeddedTerminalFrame second
      (prefixLines ++
        ((encodeHistoryDerivation first).rebase
          prefixLines.length).lines)
      ((((encodeHistoryDerivation third).rebase
        (prefixLines.length +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lineCount)).lines ++
        line.rebase prefixLines.length :: suffixLines))
  have secondPositive :=
    encodeHistoryDerivation_lineCount_positive_early second
  have secondPrefixLength :
      (prefixLines ++
          ((encodeHistoryDerivation first).rebase
            prefixLines.length).lines).length =
        prefixLines.length +
          (encodeHistoryDerivation first).lineCount := by
    rw [listLengthAppendConstructive]
    change prefixLines.length +
        ((encodeHistoryDerivation first).rebase
          prefixLines.length).lineCount =
      prefixLines.length +
        (encodeHistoryDerivation first).lineCount
    rw [ProofArchive.lineCount_rebase]
  have firstSecondLastIndex :
      ((encodeHistoryDerivation first).appendRebased
          (encodeHistoryDerivation second)).lastIndex =
        (encodeHistoryDerivation first).lineCount +
          (encodeHistoryDerivation second).lastIndex :=
    ProofArchive.lastIndex_appendRebased_of_positive
      (encodeHistoryDerivation first)
      (encodeHistoryDerivation second) secondPositive
  have referenceEquation :
      (prefixLines ++
          ((encodeHistoryDerivation first).rebase
            prefixLines.length).lines).length +
            (encodeHistoryDerivation second).lastIndex =
        prefixLines.length +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lastIndex := by
    rw [secondPrefixLength, firstSecondLastIndex]
    exact natAddAssocConstructive prefixLines.length
      (encodeHistoryDerivation first).lineCount
      (encodeHistoryDerivation second).lastIndex
  rw [referenceEquation] at frame
  exact frame

theorem encodeHistoryDerivation_ternaryThirdFrame
    {history : TheoryHistory}
    {firstBound secondBound thirdBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {thirdContext : FormulaContext thirdBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    {thirdConclusion : ScopedFormula thirdBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (third :
      Derivation LogicMode.intuitionistic history.theory
        thirdContext thirdConclusion)
    (line : ProofLine)
    (prefixLines suffixLines : List ProofLine) :
    let firstArchive := encodeHistoryDerivation first
    let secondArchive := encodeHistoryDerivation second
    let thirdArchive := encodeHistoryDerivation third
    let firstSecond := firstArchive.appendRebased secondArchive
    let combined := firstSecond.appendRebased thirdArchive
    let archiveCode :=
      (embeddedArchive prefixLines (combined.finish line)
        suffixLines).quote
    let reference := prefixLines.length + combined.lastIndex
    numericLineBound
        (numericArchiveLine archiveCode reference) = thirdBound ∧
    numericLineContext
        (numericArchiveLine archiveCode reference) =
      thirdContext.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode reference) =
      thirdConclusion.raw.code := by
  dsimp only
  rw [embeddedArchive_finish, embeddedArchive_appendRebased_right]
  have frame :=
    encodeHistoryDerivation_embeddedTerminalFrame third
      (prefixLines ++
        (((encodeHistoryDerivation first).appendRebased
          (encodeHistoryDerivation second)).rebase
          prefixLines.length).lines)
      (line.rebase prefixLines.length :: suffixLines)
  have thirdPositive :=
    encodeHistoryDerivation_lineCount_positive_early third
  have thirdPrefixLength :
      (prefixLines ++
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).rebase
            prefixLines.length).lines).length =
        prefixLines.length +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lineCount := by
    rw [listLengthAppendConstructive]
    change prefixLines.length +
        (((encodeHistoryDerivation first).appendRebased
          (encodeHistoryDerivation second)).rebase
          prefixLines.length).lineCount =
      prefixLines.length +
        ((encodeHistoryDerivation first).appendRebased
          (encodeHistoryDerivation second)).lineCount
    rw [ProofArchive.lineCount_rebase]
  have combinedLastIndex :
      (((encodeHistoryDerivation first).appendRebased
          (encodeHistoryDerivation second)).appendRebased
          (encodeHistoryDerivation third)).lastIndex =
        ((encodeHistoryDerivation first).appendRebased
          (encodeHistoryDerivation second)).lineCount +
          (encodeHistoryDerivation third).lastIndex :=
    ProofArchive.lastIndex_appendRebased_of_positive
      ((encodeHistoryDerivation first).appendRebased
        (encodeHistoryDerivation second))
      (encodeHistoryDerivation third) thirdPositive
  have referenceEquation :
      (prefixLines ++
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).rebase
            prefixLines.length).lines).length +
            (encodeHistoryDerivation third).lastIndex =
        prefixLines.length +
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).appendRebased
            (encodeHistoryDerivation third)).lastIndex := by
    rw [thirdPrefixLength, combinedLastIndex]
    exact natAddAssocConstructive prefixLines.length
      ((encodeHistoryDerivation first).appendRebased
        (encodeHistoryDerivation second)).lineCount
      (encodeHistoryDerivation third).lastIndex
  rw [referenceEquation] at frame
  exact frame

theorem encodeHistoryDerivation_ternaryFirstChronologyBit
    {history : TheoryHistory}
    {firstBound secondBound thirdBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {thirdContext : FormulaContext thirdBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    {thirdConclusion : ScopedFormula thirdBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (third :
      Derivation LogicMode.intuitionistic history.theory
        thirdContext thirdConclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength + (encodeHistoryDerivation first).lastIndex)
        (prefixLength +
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).appendRebased
              (encodeHistoryDerivation third)).lineCount) = 1 := by
  apply natLessBit_eq_one_of_lt
  apply Nat.add_lt_add_left
  exact Nat.lt_of_lt_of_le
    (by
      unfold ProofArchive.lastIndex
      exact Nat.pred_lt
        (Nat.ne_of_gt
          (encodeHistoryDerivation_lineCount_positive_early first)))
    (by
      repeat rw [ProofArchive.lineCount_appendRebased]
      exact Nat.le_trans
        (Nat.le_add_right _ _)
        (Nat.le_add_right _ _))

theorem encodeHistoryDerivation_ternarySecondChronologyBit
    {history : TheoryHistory}
    {firstBound secondBound thirdBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {thirdContext : FormulaContext thirdBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    {thirdConclusion : ScopedFormula thirdBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (third :
      Derivation LogicMode.intuitionistic history.theory
        thirdContext thirdConclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength +
          ((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).lastIndex)
        (prefixLength +
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).appendRebased
              (encodeHistoryDerivation third)).lineCount) = 1 := by
  apply natLessBit_eq_one_of_lt
  apply Nat.add_lt_add_left
  exact Nat.lt_of_lt_of_le
    (by
      unfold ProofArchive.lastIndex
      apply Nat.pred_lt
      rw [ProofArchive.lineCount_appendRebased]
      exact Nat.ne_of_gt
        (Nat.add_pos_right _
          (encodeHistoryDerivation_lineCount_positive_early second)))
    (by
      repeat rw [ProofArchive.lineCount_appendRebased]
      exact Nat.le_add_right _ _)

theorem encodeHistoryDerivation_ternaryThirdChronologyBit
    {history : TheoryHistory}
    {firstBound secondBound thirdBound : Nat}
    {firstContext : FormulaContext firstBound}
    {secondContext : FormulaContext secondBound}
    {thirdContext : FormulaContext thirdBound}
    {firstConclusion : ScopedFormula firstBound}
    {secondConclusion : ScopedFormula secondBound}
    {thirdConclusion : ScopedFormula thirdBound}
    (first :
      Derivation LogicMode.intuitionistic history.theory
        firstContext firstConclusion)
    (second :
      Derivation LogicMode.intuitionistic history.theory
        secondContext secondConclusion)
    (third :
      Derivation LogicMode.intuitionistic history.theory
        thirdContext thirdConclusion)
    (prefixLength : Nat) :
    natLessBit
        (prefixLength +
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).appendRebased
              (encodeHistoryDerivation third)).lastIndex)
        (prefixLength +
          (((encodeHistoryDerivation first).appendRebased
            (encodeHistoryDerivation second)).appendRebased
              (encodeHistoryDerivation third)).lineCount) = 1 := by
  apply natLessBit_eq_one_of_lt
  apply Nat.add_lt_add_left
  unfold ProofArchive.lastIndex
  apply Nat.pred_lt
  rw [ProofArchive.lineCount_appendRebased]
  exact Nat.ne_of_gt
    (Nat.add_pos_right _
      (encodeHistoryDerivation_lineCount_positive_early third))

theorem encodeHistoryDerivation_terminalFrameAccepted
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLines suffixLines : List ProofLine) :
    PRFunction.checkProofLineFrame.run
        (proofCheckInputs history.quote
          (embeddedArchive prefixLines
            (encodeHistoryDerivation proof) suffixLines).quote
          (prefixLines.length +
            (encodeHistoryDerivation proof).lastIndex)) = 1 := by
  let archive := encodeHistoryDerivation proof
  have positive : 0 < archive.lineCount :=
    encodeHistoryDerivation_lineCount_positive_early proof
  have lastBounded : archive.lastIndex < archive.lineCount := by
    unfold ProofArchive.lastIndex
    exact Nat.pred_lt (Nat.ne_of_gt positive)
  have globalBounded :
      prefixLines.length + archive.lastIndex <
        prefixLines.length + archive.lineCount + suffixLines.length := by
    have inside :
        prefixLines.length + archive.lastIndex <
          prefixLines.length + archive.lineCount :=
      Nat.add_lt_add_left lastBounded prefixLines.length
    exact Nat.lt_of_lt_of_le inside
      (Nat.le_add_right
        (prefixLines.length + archive.lineCount) suffixLines.length)
  have terminal :=
    encodeHistoryDerivation_embeddedTerminalFrame proof
      prefixLines suffixLines
  change
    PRFunction.checkProofLineFrame.run
        (proofCheckInputs history.quote
          (embeddedArchive prefixLines archive suffixLines).quote
          (prefixLines.length + archive.lastIndex)) = 1
  rw [PRFunction.run_checkProofLineFrame_numeric]
  rw [numericArchiveLineCount_archiveQuote,
    embeddedArchive_lineCount]
  rw [natLessBit_eq_one_of_lt globalBounded]
  dsimp only at terminal
  rw [terminal.1, terminal.2.1, terminal.2.2,
    PRFunction.isContextCode_accepts context,
    PRFunction.isScopedFormulaCode_accepts conclusion]
  rfl

theorem PRFunction.checkProofLineRuleChecks_accept_selected
    (expected : Nat)
    (expectedRules : List Nat)
    (historyCode archiveCode lineIndex : Nat)
    (member : expected ∈ expectedRules)
    (tagExact :
      proofCheckRuleValue archiveCode lineIndex = expected)
    (bodyAccepted :
      (PRFunction.checkProofLineRuleBody expected).run
        (proofCheckInputs historyCode archiveCode lineIndex) = 1) :
    (PRFunction.checkProofLineRuleChecks expectedRules).run
        (proofCheckInputs historyCode archiveCode lineIndex) = 1 := by
  induction expectedRules with
  | nil =>
      cases member
  | cons head tail inductionHypothesis =>
      unfold PRFunction.checkProofLineRuleChecks
      rw [PRFunction.run_binaryIn, PRFunction.run_orBit]
      cases member with
      | head =>
          rw [PRFunction.run_checkProofLineRuleCheck_inputs,
            tagExact,
            (natEqualBit_eq_one_iff expected expected).mpr rfl,
            bodyAccepted]
          rfl
      | tail _ tailMember =>
          rw [inductionHypothesis tailMember]
          cases (PRFunction.checkProofLineRuleCheck head).run
            (proofCheckInputs historyCode archiveCode lineIndex) <;> rfl

theorem PRFunction.checkProofLineRules_accept_selected
    (expected historyCode archiveCode lineIndex : Nat)
    (member :
      expected ∈ intuitionisticProofRuleTags)
    (tagExact :
      proofCheckRuleValue archiveCode lineIndex = expected)
    (bodyAccepted :
      (PRFunction.checkProofLineRuleBody expected).run
        (proofCheckInputs historyCode archiveCode lineIndex) = 1) :
    PRFunction.checkProofLineRules.run
        (proofCheckInputs historyCode archiveCode lineIndex) = 1 := by
  unfold PRFunction.checkProofLineRules
  exact PRFunction.checkProofLineRuleChecks_accept_selected
    expected _ historyCode archiveCode lineIndex
    member tagExact bodyAccepted

@[simp] theorem proofCheckRuleValue_numeric
    (archiveCode lineIndex : Nat) :
    proofCheckRuleValue archiveCode lineIndex =
      numericLineRule (numericArchiveLine archiveCode lineIndex) := by
  unfold proofCheckRuleValue
  rw [PRFunction.run_proofLineRule_numeric,
    PRFunction.run_archiveLineCode_numeric]

theorem encodeHistoryDerivation_terminalRuleTag
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLines suffixLines : List ProofLine) :
    proofCheckRuleValue
        (embeddedArchive prefixLines
          (encodeHistoryDerivation proof) suffixLines).quote
      (prefixLines.length +
          (encodeHistoryDerivation proof).lastIndex) =
      (derivationRuleTag proof).code := by
  let terminal := encodeHistoryDerivation_terminalDecomposition proof
  rw [terminal.encoding, ProofArchive.lastIndex_finish,
    proofCheckRuleValue_numeric,
    numericArchiveLine_embeddedFinish,
    numericLineRule_quote]
  exact congrArg ProofRuleTag.code terminal.ruleEquation

def EncodedTerminalRuleBodyAccepted
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    Prop :=
  forall (prefixLines suffixLines : List ProofLine),
    (PRFunction.checkProofLineRuleBody
      (derivationRuleTag proof).code).run
      (proofCheckInputs history.quote
        (embeddedArchive prefixLines
          (encodeHistoryDerivation proof) suffixLines).quote
        (prefixLines.length +
          (encodeHistoryDerivation proof).lastIndex)) = 1

def ContextMember.toCodeContains
    {bound : Nat}
    {formula : ScopedFormula bound}
    {context : FormulaContext bound}
    (member : ContextMember formula context) :
    ListCodeContains formula.raw.code context.rawCodes :=
  match member with
  | .here => ListCodeContains.here rfl
  | .there earlier =>
      ListCodeContains.there earlier.toCodeContains

theorem FormulaContext.member_implies_numeric
    {bound : Nat}
    {formula : ScopedFormula bound}
    {context : FormulaContext bound}
    (member : ContextMember formula context) :
    PRFunction.theoryHistoryContains.run
        (NatVector.cons context.quote
          (NatVector.cons formula.raw.code NatVector.nil)) = 1 := by
  rw [PRFunction.run_theoryHistoryContains,
    FormulaContext.quote_eq_quoteNatList_rawCodes,
    theoryHistoryContainsBit_quoteNatList]
  exact listContainsFrom_of_contains member.toCodeContains

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_theoryAxiom
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (witness : history.theory.Axiom bound conclusion) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.theoryAxiom witness :
        Derivation LogicMode.intuitionistic history.theory context conclusion) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  cases witness with
  | arithmetic arithmeticWitness =>
    simp [derivationRuleTag, ProofRuleTag.code,
      PRFunction.checkProofLineRuleBody,
      PRFunction.checkProofLineRuleBodies,
      encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
      historyAxiomParameters, proofLine]
    normalize_line_program
    simp only [numericArchiveLine_embeddedSingleton,
      numericLinePremises_quote, numericLineBound_quote,
      numericLineConclusion_quote, numericLineParameters_quote,
      ProofLine.rebase]
    rw [PRFunction.isHistoryAxiomCode_accepts_arithmetic
      history arithmeticWitness]
    simp only [List.map, quoteNatList]
    rw [(natEqualBit_eq_one_iff 0 0).mpr rfl]
    rfl
  | added evidence =>
    simp [derivationRuleTag, ProofRuleTag.code,
      PRFunction.checkProofLineRuleBody,
      PRFunction.checkProofLineRuleBodies,
      encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
      historyAxiomParameters, proofLine]
    normalize_line_program
    simp only [numericArchiveLine_embeddedSingleton,
      numericLinePremises_quote, numericLineBound_quote,
      numericLineConclusion_quote, numericLineParameters_quote,
      ProofLine.rebase]
    rw [PRFunction.isHistoryAxiomCode_accepts_added evidence bound]
    simp only [List.map, quoteNatList]
    rw [(natEqualBit_eq_one_iff 0 0).mpr rfl]
    rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_hypothesis
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (member : ContextMember conclusion context) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.hypothesis member :
        Derivation LogicMode.intuitionistic history.theory context conclusion) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedSingleton,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineContext_quote, numericLineConclusion_quote,
    ProofLine.rebase, List.map, quoteNatList_nil]
  have memberAccepted :=
    FormulaContext.member_implies_numeric member
  rw [PRFunction.run_theoryHistoryContains] at memberAccepted
  rw [memberAccepted]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_equalityReflexivity
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    (term : ScopedTerm bound) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.equalityReflexivity term :
        Derivation LogicMode.intuitionistic history.theory context
          (ScopedFormula.equal term term)) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedSingleton,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineConclusion_quote,
    ProofLine.rebase, List.map, quoteNatList_nil,
    codedListEntry_quoteNatList_zero]
  have scopedAccepted :=
    PRFunction.isScopedTermCode_accepts term
  rw [PRFunction.run_isScopedTermCode] at scopedAccepted
  normalize_line_program at scopedAccepted
  rw [scopedAccepted]
  rw [show
    (ScopedFormula.equal term term).raw.code =
      Nat.succ (natPair 1 (natPair term.raw.code term.raw.code)) by
    rfl]
  simp only [natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_weaken
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (extra : ScopedFormula bound)
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.weaken extra premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let premiseArchive := encodeHistoryDerivation premise
  let currentLine :=
    proofLine ProofRuleTag.weaken bound
      (FormulaContext.cons extra context).quote
      conclusion.raw.code [premiseArchive.lastIndex] [extra.raw.code]
  have premiseFrame :=
    encodeHistoryDerivation_unaryPremiseFrame premise currentLine
      prefixLines suffixLines
  have chronological :=
    encodeHistoryDerivation_globalLastIndex_lt_finishIndex
      premise prefixLines.length
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero]
  unfold currentLine premiseArchive at premiseFrame
  simp only [encodeHistoryDerivation, proofLine] at premiseFrame
  unfold encodeHistoryDerivation at chronological
  rw [premiseFrame.1, premiseFrame.2.1, premiseFrame.2.2]
  rw [natLessBit_eq_one_of_lt chronological]
  have extraAccepted :=
    PRFunction.isScopedFormulaCode_accepts extra
  rw [PRFunction.run_isScopedFormulaCode] at extraAccepted
  rw [extraAccepted]
  simp [quoteNatList, natEqualBit_refl,
    FormulaContext.quote]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_implicationIntroduction
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory
        (FormulaContext.cons left context) right) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.implicationIntroduction premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [FormulaContext.quote, ScopedFormula.impl, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_conjunctionEliminationLeft
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.conj left right)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.conjunctionEliminationLeft premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [ScopedFormula.conj, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_conjunctionEliminationRight
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.conj left right)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.conjunctionEliminationRight premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [ScopedFormula.conj, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_disjunctionIntroductionLeft
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context left) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.disjunctionIntroductionLeft
        (right := right) premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [ScopedFormula.disj, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_disjunctionIntroductionRight
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context right) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.disjunctionIntroductionRight
        (left := left) premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [ScopedFormula.disj, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_falsumElimination
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.falsum bound)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.falsumElimination
        (conclusion := conclusion) premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [ScopedFormula.falsum, RawFormula.code, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_equalitySymmetry
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedTerm bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.equal left right)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.equalitySymmetry premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  simp [ScopedFormula.equal, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_implicationElimination
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (implication :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.impl left right))
    (argument :
      Derivation LogicMode.intuitionistic history.theory context left) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.implicationElimination implication argument) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let firstArchive := encodeHistoryDerivation implication
  let secondArchive := encodeHistoryDerivation argument
  let combined := firstArchive.appendRebased secondArchive
  let currentLine :=
    proofLine ProofRuleTag.implicationElimination bound context.quote
      right.raw.code [firstArchive.lastIndex, combined.lastIndex] []
  have firstFrame :=
    encodeHistoryDerivation_binaryFirstFrame implication argument
      currentLine prefixLines suffixLines
  have secondFrame :=
    encodeHistoryDerivation_binarySecondFrame implication argument
      currentLine prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    binaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero,
    codedListEntry_quoteNatList_succ, quoteNatList_nil]
  unfold currentLine combined secondArchive firstArchive
    encodeHistoryDerivation proofLine at firstFrame secondFrame
  have firstChronology :=
    encodeHistoryDerivation_binaryFirstChronologyBit
      implication argument prefixLines.length
  have secondChronology :=
    encodeHistoryDerivation_binarySecondChronologyBit
      implication argument prefixLines.length
  unfold encodeHistoryDerivation at firstChronology secondChronology
  rw [firstChronology, secondChronology]
  rw [firstFrame.1, firstFrame.2.1, firstFrame.2.2,
    secondFrame.1, secondFrame.2.1, secondFrame.2.2]
  simp [ScopedFormula.impl, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_conjunctionIntroduction
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (leftProof :
      Derivation LogicMode.intuitionistic history.theory context left)
    (rightProof :
      Derivation LogicMode.intuitionistic history.theory context right) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.conjunctionIntroduction leftProof rightProof) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let firstArchive := encodeHistoryDerivation leftProof
  let secondArchive := encodeHistoryDerivation rightProof
  let combined := firstArchive.appendRebased secondArchive
  let currentLine :=
    proofLine ProofRuleTag.conjunctionIntroduction bound context.quote
      (ScopedFormula.conj left right).raw.code
      [firstArchive.lastIndex, combined.lastIndex] []
  have firstFrame :=
    encodeHistoryDerivation_binaryFirstFrame leftProof rightProof
      currentLine prefixLines suffixLines
  have secondFrame :=
    encodeHistoryDerivation_binarySecondFrame leftProof rightProof
      currentLine prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    binaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero,
    codedListEntry_quoteNatList_succ, quoteNatList_nil]
  unfold currentLine combined secondArchive firstArchive
    encodeHistoryDerivation proofLine at firstFrame secondFrame
  have firstChronology :=
    encodeHistoryDerivation_binaryFirstChronologyBit
      leftProof rightProof prefixLines.length
  have secondChronology :=
    encodeHistoryDerivation_binarySecondChronologyBit
      leftProof rightProof prefixLines.length
  unfold encodeHistoryDerivation at firstChronology secondChronology
  rw [firstChronology, secondChronology]
  rw [firstFrame.1, firstFrame.2.1, firstFrame.2.2,
    secondFrame.1, secondFrame.2.1, secondFrame.2.2]
  simp [ScopedFormula.conj, RawFormula.code, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_equalityTransitivity
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left middle right : ScopedTerm bound}
    (firstProof :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.equal left middle))
    (secondProof :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.equal middle right)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.equalityTransitivity firstProof secondProof) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let firstArchive := encodeHistoryDerivation firstProof
  let secondArchive := encodeHistoryDerivation secondProof
  let combined := firstArchive.appendRebased secondArchive
  let currentLine :=
    proofLine ProofRuleTag.equalityTransitivity bound context.quote
      (ScopedFormula.equal left right).raw.code
      [firstArchive.lastIndex, combined.lastIndex] []
  have firstFrame :=
    encodeHistoryDerivation_binaryFirstFrame firstProof secondProof
      currentLine prefixLines suffixLines
  have secondFrame :=
    encodeHistoryDerivation_binarySecondFrame firstProof secondProof
      currentLine prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    binaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero,
    codedListEntry_quoteNatList_succ, quoteNatList_nil]
  unfold currentLine combined secondArchive firstArchive
    encodeHistoryDerivation proofLine at firstFrame secondFrame
  have firstChronology :=
    encodeHistoryDerivation_binaryFirstChronologyBit
      firstProof secondProof prefixLines.length
  have secondChronology :=
    encodeHistoryDerivation_binarySecondChronologyBit
      firstProof secondProof prefixLines.length
  unfold encodeHistoryDerivation at firstChronology secondChronology
  rw [firstChronology, secondChronology]
  rw [firstFrame.1, firstFrame.2.1, firstFrame.2.2,
    secondFrame.1, secondFrame.2.1, secondFrame.2.2]
  simp [ScopedFormula.equal, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_disjunctionElimination
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right conclusion : ScopedFormula bound}
    (disjunction :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.disj left right))
    (leftBranch :
      Derivation LogicMode.intuitionistic history.theory
        (FormulaContext.cons left context) conclusion)
    (rightBranch :
      Derivation LogicMode.intuitionistic history.theory
        (FormulaContext.cons right context) conclusion) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.disjunctionElimination
        disjunction leftBranch rightBranch) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let firstArchive := encodeHistoryDerivation disjunction
  let secondArchive := encodeHistoryDerivation leftBranch
  let thirdArchive := encodeHistoryDerivation rightBranch
  let firstSecond := firstArchive.appendRebased secondArchive
  let combined := firstSecond.appendRebased thirdArchive
  let currentLine :=
    proofLine ProofRuleTag.disjunctionElimination bound context.quote
      conclusion.raw.code
      [firstArchive.lastIndex, firstSecond.lastIndex,
        combined.lastIndex] []
  have firstFrame :=
    encodeHistoryDerivation_ternaryFirstFrame
      disjunction leftBranch rightBranch
      currentLine prefixLines suffixLines
  have secondFrame :=
    encodeHistoryDerivation_ternarySecondFrame
      disjunction leftBranch rightBranch
      currentLine prefixLines suffixLines
  have thirdFrame :=
    encodeHistoryDerivation_ternaryThirdFrame
      disjunction leftBranch rightBranch
      currentLine prefixLines suffixLines
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    ternaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero,
    codedListEntry_quoteNatList_succ, quoteNatList_nil]
  unfold currentLine combined firstSecond thirdArchive secondArchive firstArchive encodeHistoryDerivation proofLine at firstFrame secondFrame thirdFrame
  have firstChronology :=
    encodeHistoryDerivation_ternaryFirstChronologyBit
      disjunction leftBranch rightBranch prefixLines.length
  have secondChronology :=
    encodeHistoryDerivation_ternarySecondChronologyBit
      disjunction leftBranch rightBranch prefixLines.length
  have thirdChronology :=
    encodeHistoryDerivation_ternaryThirdChronologyBit
      disjunction leftBranch rightBranch prefixLines.length
  unfold encodeHistoryDerivation at firstChronology secondChronology thirdChronology
  rw [firstChronology, secondChronology, thirdChronology]
  rw [firstFrame.1, firstFrame.2.1, firstFrame.2.2,
    secondFrame.1, secondFrame.2.1, secondFrame.2.2,
    thirdFrame.1, thirdFrame.2.1, thirdFrame.2.2]
  simp [FormulaContext.quote, ScopedFormula.disj, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_universalIntroduction
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {body : ScopedFormula (Nat.succ bound)}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context.lift body) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.universalIntroduction premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  have liftedContext := PRFunction.raiseContextCode_lift context
  rw [PRFunction.run_raiseContextCode] at liftedContext
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  rw [liftedContext]
  simp [ScopedFormula.all, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_universalElimination
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {body : ScopedFormula (Nat.succ bound)}
    (term : ScopedTerm bound)
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.all body)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.universalElimination term premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  have termAccepted := PRFunction.isScopedTermCode_accepts term
  rw [PRFunction.run_isScopedTermCode] at termAccepted
  normalize_line_program at termAccepted
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  rw [termAccepted]
  simp only [ScopedFormula.all, RawFormula.code, Nat.pred_succ,
    natUnpairLeft_pair, natUnpairRight_pair]
  rw [machineInstantiateTermCode_code]
  simp [ScopedFormula.instantiate, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_existentialIntroduction
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {body : ScopedFormula (Nat.succ bound)}
    (term : ScopedTerm bound)
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (body.instantiate term)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.existentialIntroduction term premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  have termAccepted := PRFunction.isScopedTermCode_accepts term
  rw [PRFunction.run_isScopedTermCode] at termAccepted
  normalize_line_program at termAccepted
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  rw [termAccepted]
  simp only [ScopedFormula.ex, RawFormula.code, Nat.pred_succ,
    natUnpairLeft_pair, natUnpairRight_pair]
  rw [machineInstantiateTermCode_code]
  simp [ScopedFormula.instantiate, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_liftVariables
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.liftVariables premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  have liftedContext := PRFunction.raiseContextCode_lift context
  rw [PRFunction.run_raiseContextCode] at liftedContext
  have liftedConclusion := ScopedFormula.lift_code conclusion
  rw [PRFunction.run_raiseFormulaCode] at liftedConclusion
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero, quoteNatList_nil]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  rw [liftedContext, liftedConclusion]
  simp [natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_freeInstantiation
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext (Nat.succ bound)}
    {conclusion : ScopedFormula (Nat.succ bound)}
    (replacement : ScopedTerm bound)
    (premise :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.freeInstantiation replacement premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  have replacementAccepted :=
    PRFunction.isScopedTermCode_accepts replacement
  rw [PRFunction.run_isScopedTermCode] at replacementAccepted
  normalize_line_program at replacementAccepted
  have instantiatedContext :=
    PRFunction.instantiateContextTermCode_code replacement context
  rw [PRFunction.run_instantiateContextTermCode] at instantiatedContext
  have instantiatedConclusion :=
    machineInstantiateTermCode_code conclusion.raw replacement.raw
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    unaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero]
  rw [encodeHistoryDerivation_unaryChronologyBit_transparent
    premise prefixLines.length]
  rw [encodeHistoryDerivation_unaryPremiseBound_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseContext_transparent
    premise _ prefixLines suffixLines]
  rw [encodeHistoryDerivation_unaryPremiseConclusion_transparent
    premise _ prefixLines suffixLines]
  rw [replacementAccepted, instantiatedContext, instantiatedConclusion]
  simp [ScopedFormula.instantiate, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_existentialElimination
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {body : ScopedFormula (Nat.succ bound)}
    {conclusion : ScopedFormula bound}
    (existential :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.ex body))
    (branch :
      Derivation LogicMode.intuitionistic history.theory
        (FormulaContext.cons body context.lift)
        conclusion.lift) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.existentialElimination existential branch) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let firstArchive := encodeHistoryDerivation existential
  let secondArchive := encodeHistoryDerivation branch
  let combined := firstArchive.appendRebased secondArchive
  let currentLine :=
    proofLine ProofRuleTag.existentialElimination bound context.quote
      conclusion.raw.code [firstArchive.lastIndex, combined.lastIndex] []
  have firstFrame :=
    encodeHistoryDerivation_binaryFirstFrame existential branch
      currentLine prefixLines suffixLines
  have secondFrame :=
    encodeHistoryDerivation_binarySecondFrame existential branch
      currentLine prefixLines suffixLines
  have liftedContext := PRFunction.raiseContextCode_lift context
  rw [PRFunction.run_raiseContextCode] at liftedContext
  have liftedConclusion := ScopedFormula.lift_code conclusion
  rw [PRFunction.run_raiseFormulaCode] at liftedConclusion
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    binaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero,
    codedListEntry_quoteNatList_succ, quoteNatList_nil]
  unfold currentLine combined secondArchive firstArchive
    encodeHistoryDerivation proofLine at firstFrame secondFrame
  have firstChronology :=
    encodeHistoryDerivation_binaryFirstChronologyBit
      existential branch prefixLines.length
  have secondChronology :=
    encodeHistoryDerivation_binarySecondChronologyBit
      existential branch prefixLines.length
  unfold encodeHistoryDerivation at firstChronology secondChronology
  rw [firstChronology, secondChronology]
  rw [firstFrame.1, firstFrame.2.1, firstFrame.2.2,
    secondFrame.1, secondFrame.2.1, secondFrame.2.2]
  rw [liftedContext, liftedConclusion]
  simp [FormulaContext.quote, ScopedFormula.ex, RawFormula.code,
    natUnpairLeft_pair, natUnpairRight_pair, natEqualBit_refl]
  rfl

set_option maxHeartbeats 10000000 in
theorem encodedTerminalRuleBodyAccepted_equalitySubstitution
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedTerm bound}
    (body : ScopedFormula (Nat.succ bound))
    (equality :
      Derivation LogicMode.intuitionistic history.theory context
        (ScopedFormula.equal left right))
    (premise :
      Derivation LogicMode.intuitionistic history.theory context
        (body.instantiate left)) :
    EncodedTerminalRuleBodyAccepted
      (Derivation.equalitySubstitution body equality premise) := by
  unfold EncodedTerminalRuleBodyAccepted
  intro prefixLines suffixLines
  let firstArchive := encodeHistoryDerivation equality
  let secondArchive := encodeHistoryDerivation premise
  let combined := firstArchive.appendRebased secondArchive
  let currentLine :=
    proofLine ProofRuleTag.equalitySubstitution bound context.quote
      (body.instantiate right).raw.code
      [firstArchive.lastIndex, combined.lastIndex] [body.raw.code]
  have firstFrame :=
    encodeHistoryDerivation_binaryFirstFrame equality premise
      currentLine prefixLines suffixLines
  have secondFrame :=
    encodeHistoryDerivation_binarySecondFrame equality premise
      currentLine prefixLines suffixLines
  have bodyAccepted := PRFunction.isScopedFormulaCode_accepts body
  rw [PRFunction.run_isScopedFormulaCode] at bodyAccepted
  have leftInstance :=
    machineInstantiateTermCode_code body.raw left.raw
  have rightInstance :=
    machineInstantiateTermCode_code body.raw right.raw
  simp [derivationRuleTag, ProofRuleTag.code,
    PRFunction.checkProofLineRuleBody,
    PRFunction.checkProofLineRuleBodies,
    encodeHistoryDerivation, encodeDerivationWithAxiomParameters,
    binaryArchive, proofLine]
  normalize_line_program
  simp only [numericArchiveLine_embeddedFinish,
    numericLinePremises_quote, numericLineParameters_quote,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote, ProofLine.rebase, List.map,
    codedListEntry_quoteNatList_zero,
    codedListEntry_quoteNatList_succ]
  unfold currentLine combined secondArchive firstArchive
    encodeHistoryDerivation proofLine at firstFrame secondFrame
  have firstChronology :=
    encodeHistoryDerivation_binaryFirstChronologyBit
      equality premise prefixLines.length
  have secondChronology :=
    encodeHistoryDerivation_binarySecondChronologyBit
      equality premise prefixLines.length
  unfold encodeHistoryDerivation at firstChronology secondChronology
  rw [firstChronology, secondChronology]
  rw [firstFrame.1, firstFrame.2.1, firstFrame.2.2,
    secondFrame.1, secondFrame.2.1, secondFrame.2.2]
  rw [bodyAccepted]
  simp only [ScopedFormula.equal, RawFormula.code, Nat.pred_succ,
    natUnpairLeft_pair, natUnpairRight_pair]
  rw [leftInstance, rightInstance]
  simp [ScopedFormula.instantiate, natEqualBit_refl]
  rfl

theorem encodedTerminalRuleBodyAccepted
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    EncodedTerminalRuleBodyAccepted proof := by
  cases proof with
  | theoryAxiom witness =>
      exact encodedTerminalRuleBodyAccepted_theoryAxiom witness
  | hypothesis member =>
      exact encodedTerminalRuleBodyAccepted_hypothesis member
  | weaken extra premise =>
      exact encodedTerminalRuleBodyAccepted_weaken extra premise
  | implicationIntroduction premise =>
      exact encodedTerminalRuleBodyAccepted_implicationIntroduction premise
  | implicationElimination implication argument =>
      exact encodedTerminalRuleBodyAccepted_implicationElimination
        implication argument
  | conjunctionIntroduction leftProof rightProof =>
      exact encodedTerminalRuleBodyAccepted_conjunctionIntroduction
        leftProof rightProof
  | conjunctionEliminationLeft premise =>
      exact encodedTerminalRuleBodyAccepted_conjunctionEliminationLeft premise
  | conjunctionEliminationRight premise =>
      exact encodedTerminalRuleBodyAccepted_conjunctionEliminationRight premise
  | disjunctionIntroductionLeft premise =>
      exact encodedTerminalRuleBodyAccepted_disjunctionIntroductionLeft premise
  | disjunctionIntroductionRight premise =>
      exact encodedTerminalRuleBodyAccepted_disjunctionIntroductionRight premise
  | disjunctionElimination disjunction leftBranch rightBranch =>
      exact encodedTerminalRuleBodyAccepted_disjunctionElimination
        disjunction leftBranch rightBranch
  | falsumElimination premise =>
      exact encodedTerminalRuleBodyAccepted_falsumElimination premise
  | universalIntroduction premise =>
      exact encodedTerminalRuleBodyAccepted_universalIntroduction premise
  | universalElimination term premise =>
      exact encodedTerminalRuleBodyAccepted_universalElimination term premise
  | existentialIntroduction term premise =>
      exact encodedTerminalRuleBodyAccepted_existentialIntroduction term premise
  | existentialElimination existential branch =>
      exact encodedTerminalRuleBodyAccepted_existentialElimination
        existential branch
  | equalityReflexivity term =>
      exact encodedTerminalRuleBodyAccepted_equalityReflexivity term
  | equalitySymmetry premise =>
      exact encodedTerminalRuleBodyAccepted_equalitySymmetry premise
  | equalityTransitivity firstProof secondProof =>
      exact encodedTerminalRuleBodyAccepted_equalityTransitivity
        firstProof secondProof
  | equalitySubstitution body equality premise =>
      exact encodedTerminalRuleBodyAccepted_equalitySubstitution
        body equality premise
  | liftVariables premise =>
      exact encodedTerminalRuleBodyAccepted_liftVariables premise
  | freeInstantiation replacement premise =>
      exact encodedTerminalRuleBodyAccepted_freeInstantiation
        replacement premise
  | doubleNegationElimination permission _premise =>
      exact nomatch permission

theorem derivationRuleTag_code_mem
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    (derivationRuleTag proof).code ∈ intuitionisticProofRuleTags := by
  unfold intuitionisticProofRuleTags intuitionisticRuleTags
  cases proof <;>
    repeat' first
      | exact List.Mem.head _
      | apply List.Mem.tail
      | assumption
  case doubleNegationElimination permission _ =>
    exact nomatch permission

theorem encodeHistoryDerivation_terminalLineAccepted
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    EncodedTerminalLineAccepted proof := by
  unfold EncodedTerminalLineAccepted
  intro prefixLines suffixLines
  unfold numericCheckProofLine PRFunction.checkProofLine
  rw [PRFunction.run_conjoin]
  have frameAccepted :=
    encodeHistoryDerivation_terminalFrameAccepted
      proof prefixLines suffixLines
  unfold proofCheckInputs at frameAccepted
  rw [frameAccepted]
  have rulesAccepted :=
    PRFunction.checkProofLineRules_accept_selected
      (derivationRuleTag proof).code history.quote
      (embeddedArchive prefixLines
        (encodeHistoryDerivation proof) suffixLines).quote
      (prefixLines.length +
        (encodeHistoryDerivation proof).lastIndex)
      (derivationRuleTag_code_mem proof)
      (encodeHistoryDerivation_terminalRuleTag
        proof prefixLines suffixLines)
      (encodedTerminalRuleBodyAccepted proof
        prefixLines suffixLines)
  unfold proofCheckInputs at rulesAccepted
  rw [rulesAccepted]
  rfl

theorem ArchiveSegmentAccepted.finishEncoded
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (archive : ProofArchive)
    (line : ProofLine)
    (encoding :
      encodeHistoryDerivation proof = archive.finish line)
    (acceptedArchive : ArchiveSegmentAccepted history archive) :
    ArchiveSegmentAccepted history (encodeHistoryDerivation proof) := by
  rw [encoding]
  apply acceptedArchive.finish line
  intro prefixLines suffixLines
  have terminal :=
    encodeHistoryDerivation_terminalLineAccepted proof
      prefixLines suffixLines
  rw [encoding] at terminal
  simpa only [ProofArchive.lastIndex_finish] using terminal

theorem encodeHistoryDerivation_segmentAccepted
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    ArchiveSegmentAccepted history (encodeHistoryDerivation proof) := by
  induction proof with
  | theoryAxiom witness =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.theoryAxiom witness)
        (archive := ProofArchive.empty)
        (line := proofLine ProofRuleTag.theoryAxiom _ _ _ []
          (historyAxiomParameters witness))
        (encoding := rfl)
        (ArchiveSegmentAccepted.empty history)
  | hypothesis member =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.hypothesis member)
        (archive := ProofArchive.empty)
        (line := proofLine ProofRuleTag.hypothesis _ _ _ [] [])
        (encoding := rfl)
        (ArchiveSegmentAccepted.empty history)
  | weaken extra premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.weaken extra premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.weaken _ _ _
          [(encodeHistoryDerivation premise).lastIndex]
          [extra.raw.code])
        (encoding := rfl)
        inductionHypothesis

  | implicationIntroduction premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.implicationIntroduction premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.implicationIntroduction _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | implicationElimination implication argument
      implicationInduction argumentInduction =>
      let combined :=
        (encodeHistoryDerivation implication).appendRebased
          (encodeHistoryDerivation argument)
      apply ArchiveSegmentAccepted.finishEncoded
        (proof :=
          Derivation.implicationElimination implication argument)
        (archive := combined)
        (line := proofLine ProofRuleTag.implicationElimination _ _ _
          [(encodeHistoryDerivation implication).lastIndex,
            combined.lastIndex] [])
        (encoding := rfl)
        (implicationInduction.appendRebased argumentInduction)
  | conjunctionIntroduction leftProof rightProof
      leftInduction rightInduction =>
      let combined :=
        (encodeHistoryDerivation leftProof).appendRebased
          (encodeHistoryDerivation rightProof)
      apply ArchiveSegmentAccepted.finishEncoded
        (proof :=
          Derivation.conjunctionIntroduction leftProof rightProof)
        (archive := combined)
        (line := proofLine ProofRuleTag.conjunctionIntroduction _ _ _
          [(encodeHistoryDerivation leftProof).lastIndex,
            combined.lastIndex] [])
        (encoding := rfl)
        (leftInduction.appendRebased rightInduction)
  | conjunctionEliminationLeft premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.conjunctionEliminationLeft premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.conjunctionEliminationLeft _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | conjunctionEliminationRight premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.conjunctionEliminationRight premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.conjunctionEliminationRight _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | disjunctionIntroductionLeft premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.disjunctionIntroductionLeft premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.disjunctionIntroductionLeft _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | disjunctionIntroductionRight premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.disjunctionIntroductionRight premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.disjunctionIntroductionRight _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | disjunctionElimination disjunction leftBranch rightBranch
      disjunctionInduction leftInduction rightInduction =>
      let firstSecond :=
        (encodeHistoryDerivation disjunction).appendRebased
          (encodeHistoryDerivation leftBranch)
      let combined :=
        firstSecond.appendRebased
          (encodeHistoryDerivation rightBranch)
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.disjunctionElimination
          disjunction leftBranch rightBranch)
        (archive := combined)
        (line := proofLine ProofRuleTag.disjunctionElimination _ _ _
          [(encodeHistoryDerivation disjunction).lastIndex,
            firstSecond.lastIndex, combined.lastIndex] [])
        (encoding := rfl)
        ((disjunctionInduction.appendRebased leftInduction).appendRebased
          rightInduction)
  | falsumElimination premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.falsumElimination premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.falsumElimination _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | universalIntroduction premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.universalIntroduction premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.universalIntroduction _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | universalElimination term premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.universalElimination term premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.universalElimination _ _ _
          [(encodeHistoryDerivation premise).lastIndex]
          [term.raw.code])
        (encoding := rfl)
        inductionHypothesis
  | existentialIntroduction term premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.existentialIntroduction term premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.existentialIntroduction _ _ _
          [(encodeHistoryDerivation premise).lastIndex]
          [term.raw.code])
        (encoding := rfl)
        inductionHypothesis
  | existentialElimination existential branch
      existentialInduction branchInduction =>
      let combined :=
        (encodeHistoryDerivation existential).appendRebased
          (encodeHistoryDerivation branch)
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.existentialElimination existential branch)
        (archive := combined)
        (line := proofLine ProofRuleTag.existentialElimination _ _ _
          [(encodeHistoryDerivation existential).lastIndex,
            combined.lastIndex] [])
        (encoding := rfl)
        (existentialInduction.appendRebased branchInduction)
  | equalityReflexivity term =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.equalityReflexivity term)
        (archive := ProofArchive.empty)
        (line := proofLine ProofRuleTag.equalityReflexivity _ _ _ []
          [term.raw.code])
        (encoding := rfl)
        (ArchiveSegmentAccepted.empty history)
  | equalitySymmetry premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.equalitySymmetry premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.equalitySymmetry _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | equalityTransitivity firstProof secondProof
      firstInduction secondInduction =>
      let combined :=
        (encodeHistoryDerivation firstProof).appendRebased
          (encodeHistoryDerivation secondProof)
      apply ArchiveSegmentAccepted.finishEncoded
        (proof :=
          Derivation.equalityTransitivity firstProof secondProof)
        (archive := combined)
        (line := proofLine ProofRuleTag.equalityTransitivity _ _ _
          [(encodeHistoryDerivation firstProof).lastIndex,
            combined.lastIndex] [])
        (encoding := rfl)
        (firstInduction.appendRebased secondInduction)
  | equalitySubstitution body equality premise
      equalityInduction premiseInduction =>
      let combined :=
        (encodeHistoryDerivation equality).appendRebased
          (encodeHistoryDerivation premise)
      apply ArchiveSegmentAccepted.finishEncoded
        (proof :=
          Derivation.equalitySubstitution body equality premise)
        (archive := combined)
        (line := proofLine ProofRuleTag.equalitySubstitution _ _ _
          [(encodeHistoryDerivation equality).lastIndex,
            combined.lastIndex] [body.raw.code])
        (encoding := rfl)
        (equalityInduction.appendRebased premiseInduction)
  | liftVariables premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.liftVariables premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.liftVariables _ _ _
          [(encodeHistoryDerivation premise).lastIndex] [])
        (encoding := rfl)
        inductionHypothesis
  | freeInstantiation replacement premise inductionHypothesis =>
      apply ArchiveSegmentAccepted.finishEncoded
        (proof := Derivation.freeInstantiation replacement premise)
        (archive := encodeHistoryDerivation premise)
        (line := proofLine ProofRuleTag.freeInstantiation _ _ _
          [(encodeHistoryDerivation premise).lastIndex]
          [replacement.raw.code])
        (encoding := rfl)
        inductionHypothesis
  | doubleNegationElimination permission _premise _inductionHypothesis =>
      exact nomatch permission

theorem proofLine_rebase_zero_constructive
    (line : ProofLine) :
    line.rebase 0 = line := by
  cases line with
  | mk rule bound contextCode conclusionCode premises parameters =>
      apply congrArg
        (fun unchangedPremises : List Nat =>
          ({ rule := rule
             bound := bound
             contextCode := contextCode
             conclusionCode := conclusionCode
             premises := unchangedPremises
             parameters := parameters } : ProofLine))
      induction premises with
      | nil => rfl
      | cons reference remaining inductionHypothesis =>
          calc
            (0 + reference) ::
                  List.map (fun index => 0 + index) remaining =
                reference ::
                  List.map (fun index => 0 + index) remaining :=
              congrArg
                (fun head =>
                  head :: List.map (fun index => 0 + index) remaining)
                (natZeroAddConstructive reference)
            _ = reference :: remaining :=
              congrArg (List.cons reference) inductionHypothesis

theorem ProofArchive.rebase_zero_constructive
    (archive : ProofArchive) :
    archive.rebase 0 = archive := by
  cases archive with
  | mk lines =>
      apply congrArg
        (fun unchangedLines : List ProofLine =>
          ({ lines := unchangedLines } : ProofArchive))
      induction lines with
      | nil => rfl
      | cons line remaining inductionHypothesis =>
          calc
            line.rebase 0 ::
                  List.map (ProofLine.rebase 0) remaining =
                line :: List.map (ProofLine.rebase 0) remaining :=
              congrArg
                (fun head =>
                  head :: List.map (ProofLine.rebase 0) remaining)
                (proofLine_rebase_zero_constructive line)
            _ = line :: remaining :=
              congrArg (List.cons line) inductionHypothesis

theorem listAppendNilConstructive
    {alpha : Type}
    (values : List alpha) :
    values ++ [] = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

theorem embeddedArchive_nil
    (archive : ProofArchive) :
    embeddedArchive [] archive [] = archive := by
  unfold embeddedArchive
  apply congrArg
    (fun unchangedLines : List ProofLine =>
      ({ lines := unchangedLines } : ProofArchive))
  change (archive.rebase 0).lines ++ [] = archive.lines
  exact (listAppendNilConstructive (archive.rebase 0).lines).trans
    (congrArg ProofArchive.lines
      (ProofArchive.rebase_zero_constructive archive))


theorem proofCheckFold_encodeHistoryDerivation
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    proofCheckFold (encodeHistoryDerivation proof).lineCount 1 history.quote
      (encodeHistoryDerivation proof).quote = 1 := by
  have accepted :=
    encodeHistoryDerivation_segmentAccepted proof [] [] (by rfl)
  rw [embeddedArchive_nil,
    show ([] : List ProofLine).length = 0 by rfl,
    natZeroAddConstructive] at accepted
  exact accepted

theorem encodeHistoryDerivation_lineCount_positive
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    0 < (encodeHistoryDerivation proof).lineCount :=
  encodeHistoryDerivation_lineCount_positive_early proof

theorem encodeHistoryDerivation_terminalFrame
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    numericLineBound
        (numericArchiveLine (encodeHistoryDerivation proof).quote
          (encodeHistoryDerivation proof).lastIndex) = bound ∧
    numericLineContext
        (numericArchiveLine (encodeHistoryDerivation proof).quote
          (encodeHistoryDerivation proof).lastIndex) = context.quote ∧
    numericLineConclusion
        (numericArchiveLine (encodeHistoryDerivation proof).quote
          (encodeHistoryDerivation proof).lastIndex) =
      conclusion.raw.code := by
  have frame :=
    encodeHistoryDerivation_embeddedTerminalFrame proof [] []
  dsimp only at frame
  rw [embeddedArchive_nil,
    show ([] : List ProofLine).length = 0 by rfl,
    natZeroAddConstructive] at frame
  exact frame

theorem proofCheckBit_encodeHistoryDerivation
    (history : TheoryHistory)
    (sentence : Sentence)
    (proof : Derivation LogicMode.intuitionistic history.theory
      FormulaContext.nil sentence.scopedFormula) :
    proofCheckBit history.quote (encodeHistoryDerivation proof).quote
      sentence.quote = 1 := by
  have fold := proofCheckFold_encodeHistoryDerivation proof
  have positive := encodeHistoryDerivation_lineCount_positive proof
  have terminal := encodeHistoryDerivation_terminalFrame proof
  have terminalBound :
      natUnpairLeft
          (natUnpairRight
            (betaComponent
              (encodeHistoryDerivation proof).betaDividend
              (encodeHistoryDerivation proof).betaCoefficient
              (encodeHistoryDerivation proof).lineCount.pred)) = 0 := by
    simpa only [numericLineBound_eq_unpair,
      numericArchiveLine_eq_beta, ProofArchive.quote,
      ProofArchive.lastIndex, natUnpairLeft_pair,
      natUnpairRight_pair] using terminal.1
  have terminalContext :
      natUnpairLeft
          (natUnpairRight
            (natUnpairRight
              (betaComponent
                (encodeHistoryDerivation proof).betaDividend
                (encodeHistoryDerivation proof).betaCoefficient
                (encodeHistoryDerivation proof).lineCount.pred))) = 0 := by
    simpa only [numericLineContext_eq_unpair,
      numericArchiveLine_eq_beta, ProofArchive.quote,
      ProofArchive.lastIndex, natUnpairLeft_pair,
      natUnpairRight_pair, FormulaContext.quote] using terminal.2.1
  have terminalConclusion :
      natUnpairLeft
          (natUnpairRight
            (natUnpairRight
              (natUnpairRight
                (betaComponent
                  (encodeHistoryDerivation proof).betaDividend
                  (encodeHistoryDerivation proof).betaCoefficient
                  (encodeHistoryDerivation proof).lineCount.pred)))) =
        sentence.quote := by
    simpa only [numericLineConclusion_eq_unpair,
      numericArchiveLine_eq_beta, ProofArchive.quote,
      ProofArchive.lastIndex, natUnpairLeft_pair,
      natUnpairRight_pair, Sentence.quote, Sentence.scopedFormula] using
        terminal.2.2
  unfold proofCheckBit
  rw [show natUnpairLeft (encodeHistoryDerivation proof).quote =
      (encodeHistoryDerivation proof).lineCount by
    unfold ProofArchive.quote
    rw [natUnpairLeft_pair]]
  rw [show natUnpairRight (encodeHistoryDerivation proof).quote =
      natPair (encodeHistoryDerivation proof).betaDividend
        (encodeHistoryDerivation proof).betaCoefficient by
    unfold ProofArchive.quote
    rw [natUnpairRight_pair]]
  rw [natUnpairLeft_pair, natUnpairRight_pair]
  dsimp only
  rw [fold, terminalBound, terminalContext, terminalConclusion]
  have positiveBit :
      natPositiveBit (encodeHistoryDerivation proof).lineCount = 1 :=
    (natPositiveBit_eq_one_iff _).mpr positive
  have scopedBit :
      PRFunction.isScopedFormulaCode.run
        (NatVector.cons 0
          (NatVector.cons sentence.quote NatVector.nil)) = 1 :=
    PRFunction.isScopedFormulaCode_accepts sentence.scopedFormula
  rw [positiveBit, scopedBit]
  simp only [natEqualBit_refl]
  rfl

theorem historyProvable_iff_numericProof
    (history : TheoryHistory)
    (sentence : Sentence) :
    HistoryProvable history sentence ↔
      Exists fun proofCode =>
        proofCheckBit history.quote proofCode sentence.quote = 1 := by
  constructor
  · intro provable
    exact Nonempty.elim provable (fun proof =>
      Exists.intro (encodeHistoryDerivation proof).quote
        (proofCheckBit_encodeHistoryDerivation history sentence proof))
  · intro encoded
    cases encoded with
    | intro proofCode accepted =>
        exact proofCheckBit_sound history proofCode sentence accepted

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.encodedTerminalRuleBodyAccepted
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_segmentAccepted
#print axioms RelationalPerimeter.HeytingArithmetic.proofCheckBit_encodeHistoryDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.historyProvable_iff_numericProof
/- AXIOM_AUDIT_END -/
