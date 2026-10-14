import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveProofCheck
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveAxiomCorrectness
import RelationalPerimeter.Constitution.HeytingArithmetic.HistoryProofArchiveChecking

/-!
# Typed correctness of the primitive-recursive proof verifier

This module reconstructs positive `Derivation` values from accepted numeric
lines and, conversely, verifies the canonical numeric encoding of every typed
derivation.  No semantic truth predicate is used in either direction.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open Lean.Parser.Tactic

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

@[irreducible] def numericArchiveLine (archiveCode lineIndex : Nat) : Nat :=
  PRFunction.archiveLineCode.run
    (NatVector.cons archiveCode (NatVector.cons lineIndex NatVector.nil))

@[irreducible] def numericArchiveLineCount (archiveCode : Nat) : Nat :=
  PRFunction.archiveLineCount.run (NatVector.cons archiveCode NatVector.nil)

@[irreducible] def numericCheckProofLine
    (historyCode archiveCode lineIndex : Nat) : Nat :=
  PRFunction.checkProofLine.run
    (NatVector.cons historyCode
      (NatVector.cons archiveCode
        (NatVector.cons lineIndex NatVector.nil)))

@[irreducible] def numericLineRule (lineCode : Nat) : Nat :=
  PRFunction.proofLineRule.run (NatVector.cons lineCode NatVector.nil)

@[irreducible] def numericLineBound (lineCode : Nat) : Nat :=
  PRFunction.proofLineBound.run (NatVector.cons lineCode NatVector.nil)

@[irreducible] def numericLineContext (lineCode : Nat) : Nat :=
  PRFunction.proofLineContext.run (NatVector.cons lineCode NatVector.nil)

@[irreducible] def numericLineConclusion (lineCode : Nat) : Nat :=
  PRFunction.proofLineConclusion.run (NatVector.cons lineCode NatVector.nil)

@[irreducible] def numericLinePremises (lineCode : Nat) : Nat :=
  PRFunction.proofLinePremises.run (NatVector.cons lineCode NatVector.nil)

@[irreducible] def numericLineParameters (lineCode : Nat) : Nat :=
  PRFunction.proofLineParameters.run (NatVector.cons lineCode NatVector.nil)

@[simp] theorem numericCheckProofLine_run_inputs
    (historyCode archiveCode lineIndex : Nat) :
    numericCheckProofLine historyCode archiveCode lineIndex =
      PRFunction.checkProofLine.run
        (proofCheckInputs historyCode archiveCode lineIndex) := by
  unfold numericCheckProofLine proofCheckInputs
  rfl

@[simp] theorem PRFunction.run_archiveLineCode_numeric
    (archiveCode lineIndex : Nat) :
    PRFunction.archiveLineCode.run
        (NatVector.cons archiveCode
          (NatVector.cons lineIndex NatVector.nil)) =
      numericArchiveLine archiveCode lineIndex := by
  unfold numericArchiveLine
  rfl

@[simp] theorem PRFunction.run_archiveLineCount_numeric
    (archiveCode : Nat) :
    PRFunction.archiveLineCount.run
        (NatVector.cons archiveCode NatVector.nil) =
      numericArchiveLineCount archiveCode := by
  unfold numericArchiveLineCount
  rfl

@[simp] theorem PRFunction.run_proofLineRule_numeric
    (lineCode : Nat) :
    PRFunction.proofLineRule.run
        (NatVector.cons lineCode NatVector.nil) =
      numericLineRule lineCode := by
  unfold numericLineRule
  rfl

@[simp] theorem PRFunction.run_proofLineBound_numeric
    (lineCode : Nat) :
    PRFunction.proofLineBound.run
        (NatVector.cons lineCode NatVector.nil) =
      numericLineBound lineCode := by
  unfold numericLineBound
  rfl

@[simp] theorem PRFunction.run_proofLineContext_numeric
    (lineCode : Nat) :
    PRFunction.proofLineContext.run
        (NatVector.cons lineCode NatVector.nil) =
      numericLineContext lineCode := by
  unfold numericLineContext
  rfl

@[simp] theorem PRFunction.run_proofLineConclusion_numeric
    (lineCode : Nat) :
    PRFunction.proofLineConclusion.run
        (NatVector.cons lineCode NatVector.nil) =
      numericLineConclusion lineCode := by
  unfold numericLineConclusion
  rfl

@[simp] theorem PRFunction.run_proofLinePremises_numeric
    (lineCode : Nat) :
    PRFunction.proofLinePremises.run
        (NatVector.cons lineCode NatVector.nil) =
      numericLinePremises lineCode := by
  unfold numericLinePremises
  rfl

@[simp] theorem PRFunction.run_proofLineParameters_numeric
    (lineCode : Nat) :
    PRFunction.proofLineParameters.run
        (NatVector.cons lineCode NatVector.nil) =
      numericLineParameters lineCode := by
  unfold numericLineParameters
  rfl

@[simp] theorem numericArchiveLine_eq_beta
    (archiveCode lineIndex : Nat) :
    numericArchiveLine archiveCode lineIndex =
      betaComponent
        (natUnpairLeft (natUnpairRight archiveCode))
        (natUnpairRight (natUnpairRight archiveCode))
        lineIndex := by
  unfold numericArchiveLine
  rw [PRFunction.run_archiveLineCode]

@[simp] theorem numericLineBound_eq_unpair
    (lineCode : Nat) :
    numericLineBound lineCode =
      natUnpairLeft (natUnpairRight lineCode) := by
  unfold numericLineBound
  rw [PRFunction.run_proofLineBound]

@[simp] theorem numericLineContext_eq_unpair
    (lineCode : Nat) :
    numericLineContext lineCode =
      natUnpairLeft (natUnpairRight (natUnpairRight lineCode)) := by
  unfold numericLineContext
  rw [PRFunction.run_proofLineContext]

@[simp] theorem numericLineConclusion_eq_unpair
    (lineCode : Nat) :
    numericLineConclusion lineCode =
      natUnpairLeft
        (natUnpairRight (natUnpairRight (natUnpairRight lineCode))) := by
  unfold numericLineConclusion
  rw [PRFunction.run_proofLineConclusion]

@[simp] theorem numericLineRule_quote (line : ProofLine) :
    numericLineRule line.quote = line.rule.code := by
  unfold numericLineRule ProofLine.quote
  rw [PRFunction.run_proofLineRule, natUnpairLeft_pair]

@[simp] theorem numericLineBound_quote (line : ProofLine) :
    numericLineBound line.quote = line.bound := by
  unfold numericLineBound ProofLine.quote
  rw [PRFunction.run_proofLineBound, natUnpairRight_pair,
    natUnpairLeft_pair]

@[simp] theorem numericLineContext_quote (line : ProofLine) :
    numericLineContext line.quote = line.contextCode := by
  unfold numericLineContext ProofLine.quote
  rw [PRFunction.run_proofLineContext, natUnpairRight_pair,
    natUnpairRight_pair, natUnpairLeft_pair]

@[simp] theorem numericLineConclusion_quote (line : ProofLine) :
    numericLineConclusion line.quote = line.conclusionCode := by
  unfold numericLineConclusion ProofLine.quote
  rw [PRFunction.run_proofLineConclusion, natUnpairRight_pair,
    natUnpairRight_pair, natUnpairRight_pair, natUnpairLeft_pair]

@[simp] theorem numericLinePremises_quote (line : ProofLine) :
    numericLinePremises line.quote = quoteNatList line.premises := by
  unfold numericLinePremises ProofLine.quote
  rw [PRFunction.run_proofLinePremises, natUnpairRight_pair,
    natUnpairRight_pair, natUnpairRight_pair, natUnpairRight_pair,
    natUnpairLeft_pair]

@[simp] theorem numericLineParameters_quote (line : ProofLine) :
    numericLineParameters line.quote = quoteNatList line.parameters := by
  unfold numericLineParameters ProofLine.quote
  rw [PRFunction.run_proofLineParameters, natUnpairRight_pair,
    natUnpairRight_pair, natUnpairRight_pair, natUnpairRight_pair,
    natUnpairRight_pair]

@[simp] theorem natEqualBit_refl (value : Nat) :
    natEqualBit value value = 1 :=
  (natEqualBit_eq_one_iff value value).mpr rfl

@[simp] theorem quoteNatList_nil :
    quoteNatList [] = 0 := by
  rfl

@[simp] theorem codedListEntry_quoteNatList_zero
    (head : Nat)
    (tail : List Nat) :
    codedListEntry (quoteNatList (head :: tail)) 0 = head := by
  rw [quoteNatList, codedListEntry, codedListHead, natUnpair_pair]

@[simp] theorem codedListEntry_quoteNatList_succ
    (head : Nat)
    (tail : List Nat)
    (index : Nat) :
    codedListEntry (quoteNatList (head :: tail)) (Nat.succ index) =
      codedListEntry (quoteNatList tail) index := by
  rw [codedListEntry, quoteNatList, codedListTail, natUnpair_pair]

@[simp] theorem numericArchiveLineCount_archiveQuote
    (archive : ProofArchive) :
    numericArchiveLineCount archive.quote = archive.lineCount := by
  unfold numericArchiveLineCount ProofArchive.quote
  rw [PRFunction.run_archiveLineCount, natUnpairLeft_pair]

theorem numericArchiveLine_archiveQuote
    (archive : ProofArchive)
    (index : Nat)
    (bounded : index < archive.lineCount) :
    numericArchiveLine archive.quote index =
      archive.lineCode index bounded := by
  unfold numericArchiveLine ProofArchive.quote
  rw [PRFunction.run_archiveLineCode, natUnpairRight_pair,
    natUnpairLeft_pair, natUnpairRight_pair]
  exact ProofArchive.betaLookup_lineCode archive index bounded

theorem lineCodeVector_get_append
    (prefixLines : List ProofLine)
    (line : ProofLine)
    (suffix : List ProofLine)
    (bounded :
      prefixLines.length < (prefixLines ++ line :: suffix).length) :
    (ProofArchive.lineCodeVector (prefixLines ++ line :: suffix)).get
        prefixLines.length bounded = line.quote := by
  induction prefixLines with
  | nil => rfl
  | cons head prefixLines inductionHypothesis =>
      exact inductionHypothesis (Nat.lt_of_succ_lt_succ bounded)

@[simp] theorem betaComponent_lineCodeVector_append
    (prefixLines : List ProofLine)
    (line : ProofLine)
    (suffix : List ProofLine) :
    betaComponent
        (ProofArchive.lineCodeVector
          (prefixLines ++ line :: suffix)).betaDividend
        (ProofArchive.lineCodeVector
          (prefixLines ++ line :: suffix)).betaCoefficient
        prefixLines.length =
      line.quote := by
  have bounded :
      prefixLines.length < (prefixLines ++ line :: suffix).length := by
    rw [listLengthAppendConstructive]
    exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ suffix.length)
  unfold betaComponent
  exact
    (constructiveRemainder_betaDividend
      (ProofArchive.lineCodeVector (prefixLines ++ line :: suffix))
      bounded).trans
      (lineCodeVector_get_append prefixLines line suffix bounded)

@[simp] theorem betaComponent_lineCodeVector_appendSingleton
    (prefixLines : List ProofLine)
    (line : ProofLine)
    (suffixLines : List ProofLine) :
    betaComponent
        (ProofArchive.lineCodeVector
          (prefixLines ++ [line] ++ suffixLines)).betaDividend
        (ProofArchive.lineCodeVector
          (prefixLines ++ [line] ++ suffixLines)).betaCoefficient
        prefixLines.length =
      line.quote := by
  have listShape :
      prefixLines ++ [line] ++ suffixLines =
        prefixLines ++ line :: suffixLines := by
    induction prefixLines with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        exact congrArg (List.cons head) inductionHypothesis
  rw [listShape]
  exact betaComponent_lineCodeVector_append prefixLines line suffixLines

/-- Place a rebased archive between an already existing prefix and an arbitrary
future suffix.  This is the invariant needed by encoder completeness: every
recursive proof block is checked in the one final archive, never in an
isolated archive whose beta witness would later change. -/
def embeddedArchive
    (prefixLines : List ProofLine)
    (archive : ProofArchive)
    (suffixLines : List ProofLine) : ProofArchive :=
  { lines :=
      prefixLines ++
        (archive.rebase prefixLines.length).lines ++
        suffixLines }

@[simp] theorem embeddedArchive_lineCount
    (prefixLines suffixLines : List ProofLine)
    (archive : ProofArchive) :
    (embeddedArchive prefixLines archive suffixLines).lineCount =
      prefixLines.length + archive.lineCount + suffixLines.length := by
  unfold embeddedArchive ProofArchive.lineCount
  rw [listLengthAppendConstructive, listLengthAppendConstructive]
  change prefixLines.length +
      (archive.rebase prefixLines.length).lineCount +
      suffixLines.length =
    prefixLines.length + archive.lineCount + suffixLines.length
  rw [ProofArchive.lineCount_rebase]

theorem natAddAssocConstructive
    (first second third : Nat) :
    (first + second) + third = first + (second + third) := by
  induction third with
  | zero => rfl
  | succ third inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

theorem proofLine_rebase_add
    (first second : Nat)
    (line : ProofLine) :
    (line.rebase second).rebase first =
      line.rebase (first + second) := by
  cases line with
  | mk rule bound contextCode conclusionCode premises parameters =>
      apply congrArg
        (fun rebasedPremises : List Nat =>
          ({ rule := rule
             bound := bound
             contextCode := contextCode
             conclusionCode := conclusionCode
             premises := rebasedPremises
             parameters := parameters } : ProofLine))
      induction premises with
      | nil => rfl
      | cons reference remaining inductionHypothesis =>
          calc
            (first + (second + reference)) ::
                  List.map (fun index => first + index)
                    (List.map (fun index => second + index) remaining) =
                ((first + second) + reference) ::
                  List.map (fun index => first + index)
                    (List.map (fun index => second + index) remaining) :=
              congrArg
                (fun head =>
                  head ::
                    List.map (fun index => first + index)
                      (List.map (fun index => second + index)
                        remaining))
                (natAddAssocConstructive first second reference).symm
            _ = ((first + second) + reference) ::
                  List.map (fun index => first + second + index)
                    remaining :=
              congrArg (List.cons ((first + second) + reference))
                inductionHypothesis

theorem listMapRebaseAddConstructive
    (first second : Nat)
    (lines : List ProofLine) :
    List.map (ProofLine.rebase first)
        (List.map (ProofLine.rebase second) lines) =
      List.map (ProofLine.rebase (first + second)) lines := by
  induction lines with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      calc
        (head.rebase second).rebase first ::
              List.map (ProofLine.rebase first)
                (List.map (ProofLine.rebase second) tail) =
            head.rebase (first + second) ::
              List.map (ProofLine.rebase first)
                (List.map (ProofLine.rebase second) tail) :=
          congrArg
            (fun rebasedHead =>
              rebasedHead ::
                List.map (ProofLine.rebase first)
                  (List.map (ProofLine.rebase second) tail))
            (proofLine_rebase_add first second head)
        _ = head.rebase (first + second) ::
              List.map (ProofLine.rebase (first + second)) tail :=
          congrArg (List.cons (head.rebase (first + second)))
            inductionHypothesis

theorem listMapAppendConstructive
    {alpha beta : Type}
    (transform : alpha -> beta)
    (left right : List alpha) :
    List.map transform (left ++ right) =
      List.map transform left ++ List.map transform right := by
  induction left with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons (transform head)) inductionHypothesis

theorem listAppendAssocConstructive
    {alpha : Type}
    (first second third : List alpha) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

theorem embeddedArchive_finish
    (prefixLines suffixLines : List ProofLine)
    (archive : ProofArchive)
    (line : ProofLine) :
    embeddedArchive prefixLines (archive.finish line) suffixLines =
      embeddedArchive prefixLines archive
        (line.rebase prefixLines.length :: suffixLines) := by
  cases archive with
  | mk lines =>
      apply congrArg (fun result : List ProofLine =>
        ({ lines := result } : ProofArchive))
      unfold ProofArchive.finish ProofArchive.rebase
      rw [listMapAppendConstructive]
      dsimp only
      let rebasedLines :=
        List.map (ProofLine.rebase prefixLines.length) lines
      let rebasedLine := line.rebase prefixLines.length
      change
        (prefixLines ++ (rebasedLines ++ [rebasedLine])) ++ suffixLines =
          (prefixLines ++ rebasedLines) ++
            (rebasedLine :: suffixLines)
      calc
        (prefixLines ++ (rebasedLines ++ [rebasedLine])) ++ suffixLines =
            prefixLines ++
              ((rebasedLines ++ [rebasedLine]) ++ suffixLines) :=
          listAppendAssocConstructive prefixLines
            (rebasedLines ++ [rebasedLine]) suffixLines
        _ = prefixLines ++
              (rebasedLines ++ ([rebasedLine] ++ suffixLines)) :=
          congrArg (fun remaining => prefixLines ++ remaining)
            (listAppendAssocConstructive
              rebasedLines [rebasedLine] suffixLines)
        _ = (prefixLines ++ rebasedLines) ++
              ([rebasedLine] ++ suffixLines) :=
          (listAppendAssocConstructive prefixLines rebasedLines
            ([rebasedLine] ++ suffixLines)).symm
        _ = (prefixLines ++ rebasedLines) ++
              (rebasedLine :: suffixLines) := rfl

@[simp] theorem numericArchiveLine_embeddedFinish
    (prefixLines suffixLines : List ProofLine)
    (archive : ProofArchive)
    (line : ProofLine) :
    numericArchiveLine
        (embeddedArchive prefixLines (archive.finish line)
          suffixLines).quote
        (prefixLines.length + archive.lineCount) =
      (line.rebase prefixLines.length).quote := by
  let earlierLines :=
    prefixLines ++ (archive.rebase prefixLines.length).lines
  have lineShape :
      (embeddedArchive prefixLines (archive.finish line)
        suffixLines).lines =
      earlierLines ++ line.rebase prefixLines.length :: suffixLines := by
    unfold earlierLines
    rw [embeddedArchive_finish]
    rfl
  have earlierLength :
      earlierLines.length = prefixLines.length + archive.lineCount := by
    unfold earlierLines
    rw [listLengthAppendConstructive]
    change prefixLines.length +
        (archive.rebase prefixLines.length).lineCount =
      prefixLines.length + archive.lineCount
    rw [ProofArchive.lineCount_rebase]
  unfold numericArchiveLine ProofArchive.quote
  rw [PRFunction.run_archiveLineCode, natUnpairRight_pair,
    natUnpairLeft_pair, natUnpairRight_pair]
  unfold ProofArchive.betaDividend ProofArchive.betaCoefficient
  rw [lineShape, ← earlierLength]
  exact betaComponent_lineCodeVector_append earlierLines
    (line.rebase prefixLines.length) suffixLines

@[simp] theorem numericArchiveLine_embeddedSingleton
    (prefixLines suffixLines : List ProofLine)
    (line : ProofLine) :
    numericArchiveLine
        (embeddedArchive prefixLines (ProofArchive.singleton line)
          suffixLines).quote
        prefixLines.length =
      (line.rebase prefixLines.length).quote := by
  have singletonAsFinish :
      ProofArchive.singleton line = ProofArchive.empty.finish line := by
    rfl
  rw [singletonAsFinish]
  simpa [ProofArchive.empty, ProofArchive.lineCount] using
    numericArchiveLine_embeddedFinish prefixLines suffixLines
      ProofArchive.empty line

@[simp] theorem ProofArchive.lineCount_singleton
    (line : ProofLine) :
    (ProofArchive.singleton line).lineCount = 1 := by
  rfl

@[simp] theorem ProofArchive.lastIndex_singleton
    (line : ProofLine) :
    (ProofArchive.singleton line).lastIndex = 0 := by
  rfl

@[simp] theorem ProofArchive.lastIndex_finish
    (archive : ProofArchive)
    (line : ProofLine) :
    (archive.finish line).lastIndex = archive.lineCount := by
  unfold ProofArchive.lastIndex
  rw [ProofArchive.lineCount_finish]
  rfl

theorem embeddedArchive_appendRebased_left
    (prefixLines suffixLines : List ProofLine)
    (earlier later : ProofArchive) :
    embeddedArchive prefixLines (earlier.appendRebased later)
        suffixLines =
      embeddedArchive prefixLines earlier
        ((later.rebase
          (prefixLines.length + earlier.lineCount)).lines ++ suffixLines) := by
  cases earlier with
  | mk earlierLines =>
      cases later with
      | mk laterLines =>
          apply congrArg (fun result : List ProofLine =>
            ({ lines := result } : ProofArchive))
          unfold ProofArchive.appendRebased ProofArchive.rebase
            ProofArchive.lineCount
          rw [listMapAppendConstructive,
            listMapRebaseAddConstructive]
          let rebasedEarlier :=
            List.map (ProofLine.rebase prefixLines.length)
              earlierLines
          let rebasedLater :=
            List.map
              (ProofLine.rebase
                (prefixLines.length + earlierLines.length))
              laterLines
          change
            (prefixLines ++ (rebasedEarlier ++ rebasedLater)) ++
                suffixLines =
              (prefixLines ++ rebasedEarlier) ++
                (rebasedLater ++ suffixLines)
          calc
            (prefixLines ++ (rebasedEarlier ++ rebasedLater)) ++
                  suffixLines =
                prefixLines ++
                  ((rebasedEarlier ++ rebasedLater) ++ suffixLines) :=
              listAppendAssocConstructive prefixLines
                (rebasedEarlier ++ rebasedLater) suffixLines
            _ = prefixLines ++
                  (rebasedEarlier ++ (rebasedLater ++ suffixLines)) :=
              congrArg (fun remaining => prefixLines ++ remaining)
                (listAppendAssocConstructive rebasedEarlier
                  rebasedLater suffixLines)
            _ = (prefixLines ++ rebasedEarlier) ++
                  (rebasedLater ++ suffixLines) :=
              (listAppendAssocConstructive prefixLines
                rebasedEarlier (rebasedLater ++ suffixLines)).symm

theorem embeddedArchive_appendRebased_right
    (prefixLines suffixLines : List ProofLine)
    (earlier later : ProofArchive) :
    embeddedArchive prefixLines (earlier.appendRebased later)
        suffixLines =
      embeddedArchive
        (prefixLines ++ (earlier.rebase prefixLines.length).lines)
        later suffixLines := by
  cases earlier with
  | mk earlierLines =>
      cases later with
      | mk laterLines =>
          apply congrArg (fun result : List ProofLine =>
            ({ lines := result } : ProofArchive))
          unfold ProofArchive.appendRebased ProofArchive.rebase
            ProofArchive.lineCount
          rw [listMapAppendConstructive,
            listMapRebaseAddConstructive,
            listLengthAppendConstructive,
            listLengthMapConstructive]
          let rebasedEarlier :=
            List.map (ProofLine.rebase prefixLines.length)
              earlierLines
          let rebasedLater :=
            List.map
              (ProofLine.rebase
                (prefixLines.length + earlierLines.length))
              laterLines
          change
            (prefixLines ++ (rebasedEarlier ++ rebasedLater)) ++
                suffixLines =
              ((prefixLines ++ rebasedEarlier) ++ rebasedLater) ++
                suffixLines
          exact congrArg (fun accumulated => accumulated ++ suffixLines)
            ((listAppendAssocConstructive prefixLines
              rebasedEarlier rebasedLater).symm)

/-- Acceptance of a transparent archive block in every surrounding archive.
The incoming prefix is assumed accepted; the result advances the verified
fold exactly across the embedded block. -/
def ArchiveSegmentAccepted
    (history : TheoryHistory)
    (archive : ProofArchive) : Prop :=
  forall (prefixLines suffixLines : List ProofLine),
    proofCheckFold prefixLines.length 1 history.quote
        (embeddedArchive prefixLines archive suffixLines).quote = 1 ->
      proofCheckFold (prefixLines.length + archive.lineCount) 1
        history.quote
        (embeddedArchive prefixLines archive suffixLines).quote = 1

theorem ArchiveSegmentAccepted.empty
    (history : TheoryHistory) :
    ArchiveSegmentAccepted history ProofArchive.empty := by
  intro prefixLines suffixLines prefixAccepted
  simpa [ProofArchive.empty, ProofArchive.lineCount] using prefixAccepted

theorem ArchiveSegmentAccepted.finish
    {history : TheoryHistory}
    {archive : ProofArchive}
    (acceptedArchive : ArchiveSegmentAccepted history archive)
    (line : ProofLine)
    (lineAccepted :
      forall (prefixLines suffixLines : List ProofLine),
        numericCheckProofLine history.quote
          (embeddedArchive prefixLines (archive.finish line)
            suffixLines).quote
          (prefixLines.length + archive.lineCount) = 1) :
    ArchiveSegmentAccepted history (archive.finish line) := by
  intro prefixLines suffixLines prefixAccepted
  have prefixAcceptedBeforeLine := prefixAccepted
  rw [embeddedArchive_finish] at prefixAcceptedBeforeLine
  have acceptedBeforeLine :=
    acceptedArchive prefixLines
      (line.rebase prefixLines.length :: suffixLines)
      prefixAcceptedBeforeLine
  rw [← embeddedArchive_finish] at acceptedBeforeLine
  have acceptedLine := lineAccepted prefixLines suffixLines
  rw [ProofArchive.lineCount_finish, Nat.add_succ]
  change natAndBit
    (proofCheckFold (prefixLines.length + archive.lineCount) 1
      history.quote
      (embeddedArchive prefixLines (archive.finish line)
        suffixLines).quote)
    (PRFunction.checkProofLine.run
      (NatVector.cons history.quote
        (NatVector.cons
          (embeddedArchive prefixLines (archive.finish line)
            suffixLines).quote
          (NatVector.cons
            (prefixLines.length + archive.lineCount)
            NatVector.nil)))) = 1
  unfold numericCheckProofLine at acceptedLine
  rw [acceptedBeforeLine, acceptedLine]
  rfl

theorem ArchiveSegmentAccepted.singleton
    {history : TheoryHistory}
    (line : ProofLine)
    (lineAccepted :
      forall (prefixLines suffixLines : List ProofLine),
        numericCheckProofLine history.quote
          (embeddedArchive prefixLines (ProofArchive.singleton line)
            suffixLines).quote
          prefixLines.length = 1) :
    ArchiveSegmentAccepted history (ProofArchive.singleton line) := by
  have finished :
      ProofArchive.singleton line = ProofArchive.empty.finish line := by
    rfl
  rw [finished]
  apply (ArchiveSegmentAccepted.empty history).finish line
  intro prefixLines suffixLines
  change numericCheckProofLine history.quote
    (embeddedArchive prefixLines (ProofArchive.singleton line)
      suffixLines).quote
    prefixLines.length = 1
  exact lineAccepted prefixLines suffixLines

theorem ArchiveSegmentAccepted.appendRebased
    {history : TheoryHistory}
    {earlier later : ProofArchive}
    (earlierAccepted : ArchiveSegmentAccepted history earlier)
    (laterAccepted : ArchiveSegmentAccepted history later) :
    ArchiveSegmentAccepted history (earlier.appendRebased later) := by
  intro prefixLines suffixLines prefixAccepted
  have acceptedForEarlier := prefixAccepted
  rw [embeddedArchive_appendRebased_left] at acceptedForEarlier
  have throughEarlier :=
    earlierAccepted prefixLines
      ((later.rebase
        (prefixLines.length + earlier.lineCount)).lines ++ suffixLines)
      acceptedForEarlier
  let laterPrefix :=
    prefixLines ++ (earlier.rebase prefixLines.length).lines
  have laterPrefixLength :
      laterPrefix.length = prefixLines.length + earlier.lineCount := by
    unfold laterPrefix
    rw [listLengthAppendConstructive]
    exact congrArg (prefixLines.length + ·)
      (ProofArchive.lineCount_rebase earlier prefixLines.length)
  have embeddingEquality :
      embeddedArchive prefixLines earlier
          ((later.rebase
            (prefixLines.length + earlier.lineCount)).lines ++ suffixLines) =
        embeddedArchive laterPrefix later suffixLines := by
    unfold laterPrefix
    exact
      (embeddedArchive_appendRebased_left prefixLines suffixLines
        earlier later).symm.trans
      (embeddedArchive_appendRebased_right prefixLines suffixLines
        earlier later)
  rw [embeddingEquality] at throughEarlier
  rw [← laterPrefixLength] at throughEarlier
  have throughLater :=
    laterAccepted laterPrefix suffixLines throughEarlier
  rw [laterPrefixLength] at throughLater
  have laterToGlobal :
      embeddedArchive laterPrefix later suffixLines =
        embeddedArchive prefixLines (earlier.appendRebased later)
          suffixLines := by
    exact embeddingEquality.symm.trans
      (embeddedArchive_appendRebased_left prefixLines suffixLines
        earlier later).symm
  rw [laterToGlobal] at throughLater
  rw [ProofArchive.lineCount_appendRebased]
  simpa [Nat.add_assoc] using throughLater

/-- Canonical typed decoding of a formula code whose scoped inhabitance has
already been established propositionally.  The code decoder chooses the raw
syntax; the witness is used only to certify its scope and exact code. -/
structure DecodedScopedFormula (bound code : Nat) : Type where
  formula : ScopedFormula bound
  codeExact : formula.raw.code = code

def decodeScopedFormulaOfExistence
    (bound code : Nat)
    (witness : Exists fun formula : ScopedFormula bound =>
      formula.raw.code = code) :
    DecodedScopedFormula bound code := by
  cases decoded : decodeFormula code with
  | none =>
      have impossible : False := by
        cases witness with
        | intro formula formulaCode =>
            have canonical :
                decodeFormula code = some formula.raw := by
              rw [← formulaCode, decodeFormula_code]
            have collision :
                (none : Option RawFormula) = some formula.raw :=
              decoded.symm.trans canonical
            cases collision
      exact impossible.elim
  | some raw =>
      have rawScoped : raw.WellScoped bound := by
        cases witness with
        | intro formula formulaCode =>
            have canonical :
                decodeFormula code = some formula.raw := by
              rw [← formulaCode, decodeFormula_code]
            have sameRaw : raw = formula.raw :=
              Option.some.inj (decoded.symm.trans canonical)
            rw [sameRaw]
            exact formula.isScoped
      have rawCode : raw.code = code := by
        cases witness with
        | intro formula formulaCode =>
            have canonical :
                decodeFormula code = some formula.raw := by
              rw [← formulaCode, decodeFormula_code]
            have sameRaw : raw = formula.raw :=
              Option.some.inj (decoded.symm.trans canonical)
            rw [sameRaw]
            exact formulaCode
      exact
        { formula := { raw := raw, isScoped := rawScoped }
          codeExact := rawCode }

/-- Canonical reconstruction of a formula context from its list of raw codes.
No inhabitant is selected from `Exists`: each head is computed by
`decodeFormula`, and the existential evidence only proves the computed data
well scoped. -/
def decodeFormulaContextList
    (bound : Nat) :
    (codes : List Nat) ->
    (Exists fun context : FormulaContext bound =>
      context.rawCodes = codes) ->
    Subtype fun context : FormulaContext bound =>
      context.rawCodes = codes
  | [], _witness => ⟨FormulaContext.nil, rfl⟩
  | headCode :: tailCodes, witness =>
      let headWitness :
          Exists fun formula : ScopedFormula bound =>
            formula.raw.code = headCode := by
        cases witness with
        | intro context contextCodes =>
            cases context with
            | nil =>
                change ([] : List Nat) = headCode :: tailCodes at contextCodes
                cases contextCodes
            | cons head tail =>
                exact Exists.intro head (List.cons.inj contextCodes).1
      let tailWitness :
          Exists fun context : FormulaContext bound =>
            context.rawCodes = tailCodes := by
        cases witness with
        | intro context contextCodes =>
            cases context with
            | nil =>
                change ([] : List Nat) = headCode :: tailCodes at contextCodes
                cases contextCodes
            | cons head tail =>
                exact Exists.intro tail (List.cons.inj contextCodes).2
      let head := decodeScopedFormulaOfExistence
        bound headCode headWitness
      let tail := decodeFormulaContextList bound tailCodes tailWitness
      ⟨FormulaContext.cons head.formula tail.val, by
        change head.formula.raw.code :: tail.val.rawCodes =
          headCode :: tailCodes
        rw [head.codeExact, tail.property]⟩

/-- Canonical typed decoding of a context code from propositional recognition. -/
structure DecodedFormulaContext (bound code : Nat) : Type where
  context : FormulaContext bound
  quoteExact : context.quote = code

def decodeFormulaContextOfExistence
    (bound code : Nat)
    (witness : Exists fun context : FormulaContext bound =>
      context.quote = code) :
    DecodedFormulaContext bound code := by
  cases decoded : decodeNatList code with
  | none =>
      have impossible : False := by
        cases witness with
        | intro context contextCode =>
            have canonical :
                decodeNatList code = some context.rawCodes := by
              rw [← contextCode,
                FormulaContext.quote_eq_quoteNatList_rawCodes,
                decodeNatList_quote]
            have collision :
                (none : Option (List Nat)) = some context.rawCodes :=
              decoded.symm.trans canonical
            cases collision
      exact impossible.elim
  | some codes =>
      have contextualCodes :
          Exists fun context : FormulaContext bound =>
            context.rawCodes = codes ∧ context.quote = code := by
        cases witness with
        | intro context contextCode =>
            have canonical :
                decodeNatList code = some context.rawCodes := by
              rw [← contextCode,
                FormulaContext.quote_eq_quoteNatList_rawCodes,
                decodeNatList_quote]
            have sameCodes : context.rawCodes = codes :=
              Option.some.inj (canonical.symm.trans decoded)
            exact Exists.intro context (And.intro sameCodes contextCode)
      have codeWitness :
          Exists fun context : FormulaContext bound =>
            context.rawCodes = codes := by
        cases contextualCodes with
        | intro context exactness =>
            exact Exists.intro context exactness.1
      let result := decodeFormulaContextList bound codes codeWitness
      have quoteExact : result.val.quote = code := by
        rw [FormulaContext.quote_eq_quoteNatList_rawCodes,
          result.property]
        cases contextualCodes with
        | intro context exactness =>
            rw [← exactness.1,
              ← FormulaContext.quote_eq_quoteNatList_rawCodes]
            exact exactness.2
      exact
        { context := result.val
          quoteExact := quoteExact }

structure DecodedNumericLineFrame
    (archiveCode lineIndex : Nat) : Type where
  lineInArchive :
    lineIndex < numericArchiveLineCount archiveCode
  context : FormulaContext
    (numericLineBound (numericArchiveLine archiveCode lineIndex))
  conclusion : ScopedFormula
    (numericLineBound (numericArchiveLine archiveCode lineIndex))
  contextExact : context.quote =
    numericLineContext (numericArchiveLine archiveCode lineIndex)
  conclusionExact : conclusion.raw.code =
    numericLineConclusion (numericArchiveLine archiveCode lineIndex)

/-! ## Lightweight semantic coordinates for the named checker components -/

@[simp] theorem PRFunction.run_proofCheckHistory
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckHistory.run
      (proofCheckInputs historyCode archiveCode lineIndex) = historyCode := by
  rfl

@[simp] theorem PRFunction.run_proofCheckArchive
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckArchive.run
      (proofCheckInputs historyCode archiveCode lineIndex) = archiveCode := by
  rfl

@[simp] theorem PRFunction.run_proofCheckIndex
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckIndex.run
      (proofCheckInputs historyCode archiveCode lineIndex) = lineIndex := by
  rfl

@[simp] theorem PRFunction.run_proofCheckLine
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckLine.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericArchiveLine archiveCode lineIndex := by
  unfold PRFunction.proofCheckLine PRFunction.lineAtIn
    proofCheckInputs numericArchiveLine PRFunction.proofCheckArchive
    PRFunction.proofCheckIndex
  repeat first
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]

@[simp] theorem PRFunction.run_proofCheckBound
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckBound.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineBound (numericArchiveLine archiveCode lineIndex) := by
  unfold PRFunction.proofCheckBound PRFunction.lineBoundIn
    numericLineBound
  rw [PRFunction.run_unaryIn]
  repeat rw [PRFunction.run_proofLineBound]
  rw [PRFunction.run_proofCheckLine]

@[simp] theorem PRFunction.run_proofCheckContext
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckContext.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineContext (numericArchiveLine archiveCode lineIndex) := by
  unfold PRFunction.proofCheckContext PRFunction.lineContextIn
    numericLineContext
  rw [PRFunction.run_unaryIn]
  repeat rw [PRFunction.run_proofLineContext]
  rw [PRFunction.run_proofCheckLine]

@[simp] theorem PRFunction.run_proofCheckConclusion
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckConclusion.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineConclusion (numericArchiveLine archiveCode lineIndex) := by
  unfold PRFunction.proofCheckConclusion PRFunction.lineConclusionIn
    numericLineConclusion
  rw [PRFunction.run_unaryIn]
  repeat rw [PRFunction.run_proofLineConclusion]
  rw [PRFunction.run_proofCheckLine]

@[simp] theorem PRFunction.run_proofCheckPremises
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckPremises.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLinePremises (numericArchiveLine archiveCode lineIndex) := by
  unfold PRFunction.proofCheckPremises PRFunction.linePremisesIn
    numericLinePremises
  rw [PRFunction.run_unaryIn]
  repeat rw [PRFunction.run_proofLinePremises]
  rw [PRFunction.run_proofCheckLine]

@[simp] theorem PRFunction.run_proofCheckParameters
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckParameters.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineParameters (numericArchiveLine archiveCode lineIndex) := by
  unfold PRFunction.proofCheckParameters PRFunction.lineParametersIn
    numericLineParameters
  rw [PRFunction.run_unaryIn]
  repeat rw [PRFunction.run_proofLineParameters]
  rw [PRFunction.run_proofCheckLine]

@[simp] theorem PRFunction.run_proofCheckReference
    (position historyCode archiveCode lineIndex : Nat) :
    (PRFunction.proofCheckReference position).run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
        (numericLinePremises (numericArchiveLine archiveCode lineIndex))
        position := by
  unfold PRFunction.proofCheckReference PRFunction.listEntryIn
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_codedListEntry,
    PRFunction.run_proofCheckPremises, PRFunction.run_constant]

@[simp] theorem PRFunction.run_proofCheckParameter
    (position historyCode archiveCode lineIndex : Nat) :
    (PRFunction.proofCheckParameter position).run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
        (numericLineParameters (numericArchiveLine archiveCode lineIndex))
        position := by
  unfold PRFunction.proofCheckParameter PRFunction.listEntryIn
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_codedListEntry,
    PRFunction.run_proofCheckParameters, PRFunction.run_constant]

theorem numericArchiveLine_eq_run
    (archiveCode lineIndex : Nat) :
    numericArchiveLine archiveCode lineIndex =
      PRFunction.archiveLineCode.run
        (NatVector.cons archiveCode
          (NatVector.cons lineIndex NatVector.nil)) := by
  unfold numericArchiveLine
  rfl

@[simp] theorem PRFunction.run_proofCheckFirstLine
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstLine.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericArchiveLine archiveCode
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
          (numericLinePremises (numericArchiveLine archiveCode lineIndex))
          0) := by
  unfold PRFunction.proofCheckFirstLine PRFunction.proofCheckFirstRef
    PRFunction.lineAtIn
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_proofCheckArchive, PRFunction.run_proofCheckReference]
  exact (numericArchiveLine_eq_run archiveCode _).symm

@[simp] theorem PRFunction.run_proofCheckSecondLine
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondLine.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericArchiveLine archiveCode
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
          (numericLinePremises (numericArchiveLine archiveCode lineIndex))
          1) := by
  unfold PRFunction.proofCheckSecondLine PRFunction.proofCheckSecondRef
    PRFunction.lineAtIn
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_proofCheckArchive, PRFunction.run_proofCheckReference]
  exact (numericArchiveLine_eq_run archiveCode _).symm

@[simp] theorem PRFunction.run_proofCheckThirdLine
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdLine.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericArchiveLine archiveCode
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
          (numericLinePremises (numericArchiveLine archiveCode lineIndex))
          2) := by
  unfold PRFunction.proofCheckThirdLine PRFunction.proofCheckThirdRef
    PRFunction.lineAtIn
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_proofCheckArchive, PRFunction.run_proofCheckReference]
  exact (numericArchiveLine_eq_run archiveCode _).symm

@[simp] theorem PRFunction.run_proofCheckFirstBound
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstBound.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineBound (PRFunction.proofCheckFirstLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckFirstBound PRFunction.lineBoundIn
    numericLineBound
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineBound]

@[simp] theorem PRFunction.run_proofCheckSecondBound
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondBound.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineBound (PRFunction.proofCheckSecondLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckSecondBound PRFunction.lineBoundIn
    numericLineBound
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineBound]

@[simp] theorem PRFunction.run_proofCheckThirdBound
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdBound.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineBound (PRFunction.proofCheckThirdLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckThirdBound PRFunction.lineBoundIn
    numericLineBound
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineBound]

@[simp] theorem PRFunction.run_proofCheckFirstContext
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstContext.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineContext (PRFunction.proofCheckFirstLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckFirstContext PRFunction.lineContextIn
    numericLineContext
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineContext]

@[simp] theorem PRFunction.run_proofCheckSecondContext
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondContext.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineContext (PRFunction.proofCheckSecondLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckSecondContext PRFunction.lineContextIn
    numericLineContext
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineContext]

@[simp] theorem PRFunction.run_proofCheckThirdContext
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdContext.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineContext (PRFunction.proofCheckThirdLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckThirdContext PRFunction.lineContextIn
    numericLineContext
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineContext]

@[simp] theorem PRFunction.run_proofCheckFirstConclusion
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstConclusion.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineConclusion (PRFunction.proofCheckFirstLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckFirstConclusion
    PRFunction.lineConclusionIn numericLineConclusion
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineConclusion]

@[simp] theorem PRFunction.run_proofCheckSecondConclusion
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondConclusion.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineConclusion (PRFunction.proofCheckSecondLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckSecondConclusion
    PRFunction.lineConclusionIn numericLineConclusion
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineConclusion]

@[simp] theorem PRFunction.run_proofCheckThirdConclusion
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdConclusion.run
      (proofCheckInputs historyCode archiveCode lineIndex) =
      numericLineConclusion (PRFunction.proofCheckThirdLine.run
        (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold PRFunction.proofCheckThirdConclusion
    PRFunction.lineConclusionIn numericLineConclusion
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineConclusion]

@[simp] theorem PRFunction.run_proofCheckHistory_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckHistory.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      historyCode := by
  exact
    PRFunction.run_proofCheckHistory historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckIndex_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckIndex.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      lineIndex := by
  exact
    PRFunction.run_proofCheckIndex historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckLine_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckLine.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericArchiveLine archiveCode lineIndex := by
  exact
    PRFunction.run_proofCheckLine historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckBound_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckBound.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineBound (numericArchiveLine archiveCode lineIndex) := by
  exact
    PRFunction.run_proofCheckBound historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckContext_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckContext.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineContext (numericArchiveLine archiveCode lineIndex) := by
  exact
    PRFunction.run_proofCheckContext historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckConclusion_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckConclusion.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineConclusion
        (numericArchiveLine archiveCode lineIndex) := by
  exact
    PRFunction.run_proofCheckConclusion historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckPremises_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckPremises.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLinePremises
        (numericArchiveLine archiveCode lineIndex) := by
  exact
    PRFunction.run_proofCheckPremises historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckParameters_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckParameters.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineParameters
        (numericArchiveLine archiveCode lineIndex) := by
  exact
    PRFunction.run_proofCheckParameters historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckReference_raw
    (position historyCode archiveCode lineIndex : Nat) :
    (PRFunction.proofCheckReference position).run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
        (numericLinePremises
          (numericArchiveLine archiveCode lineIndex))
        position := by
  exact
    PRFunction.run_proofCheckReference
      position historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckParameter_raw
    (position historyCode archiveCode lineIndex : Nat) :
    (PRFunction.proofCheckParameter position).run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
        (numericLineParameters
          (numericArchiveLine archiveCode lineIndex))
        position := by
  exact
    PRFunction.run_proofCheckParameter
      position historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckFirstLine_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstLine.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericArchiveLine archiveCode
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
          (numericLinePremises
            (numericArchiveLine archiveCode lineIndex))
          0) := by
  exact
    PRFunction.run_proofCheckFirstLine
      historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckFirstBound_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstBound.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineBound
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            0)) := by
  exact
    (PRFunction.run_proofCheckFirstBound
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineBound
        (PRFunction.run_proofCheckFirstLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckFirstContext_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstContext.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineContext
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            0)) := by
  exact
    (PRFunction.run_proofCheckFirstContext
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineContext
        (PRFunction.run_proofCheckFirstLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckFirstConclusion_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckFirstConclusion.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineConclusion
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            0)) := by
  exact
    (PRFunction.run_proofCheckFirstConclusion
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineConclusion
        (PRFunction.run_proofCheckFirstLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckSecondLine_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondLine.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericArchiveLine archiveCode
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
          (numericLinePremises
            (numericArchiveLine archiveCode lineIndex))
          1) := by
  exact
    PRFunction.run_proofCheckSecondLine
      historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckSecondBound_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondBound.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineBound
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            1)) := by
  exact
    (PRFunction.run_proofCheckSecondBound
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineBound
        (PRFunction.run_proofCheckSecondLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckSecondContext_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondContext.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineContext
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            1)) := by
  exact
    (PRFunction.run_proofCheckSecondContext
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineContext
        (PRFunction.run_proofCheckSecondLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckSecondConclusion_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckSecondConclusion.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineConclusion
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            1)) := by
  exact
    (PRFunction.run_proofCheckSecondConclusion
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineConclusion
        (PRFunction.run_proofCheckSecondLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckThirdLine_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdLine.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericArchiveLine archiveCode
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
          (numericLinePremises
            (numericArchiveLine archiveCode lineIndex))
          2) := by
  exact
    PRFunction.run_proofCheckThirdLine
      historyCode archiveCode lineIndex

@[simp] theorem PRFunction.run_proofCheckThirdBound_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdBound.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineBound
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            2)) := by
  exact
    (PRFunction.run_proofCheckThirdBound
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineBound
        (PRFunction.run_proofCheckThirdLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckThirdContext_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdContext.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineContext
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            2)) := by
  exact
    (PRFunction.run_proofCheckThirdContext
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineContext
        (PRFunction.run_proofCheckThirdLine
          historyCode archiveCode lineIndex))

@[simp] theorem PRFunction.run_proofCheckThirdConclusion_raw
    (historyCode archiveCode lineIndex : Nat) :
    PRFunction.proofCheckThirdConclusion.run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      numericLineConclusion
        (numericArchiveLine archiveCode
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListEntry
            (numericLinePremises
              (numericArchiveLine archiveCode lineIndex))
            2)) := by
  exact
    (PRFunction.run_proofCheckThirdConclusion
      historyCode archiveCode lineIndex).trans
      (congrArg numericLineConclusion
        (PRFunction.run_proofCheckThirdLine
          historyCode archiveCode lineIndex))

def checkProofLine_positive_decodes_frame
    (historyCode archiveCode lineIndex : Nat)
    (accepted : 0 < numericCheckProofLine historyCode archiveCode lineIndex) :
    DecodedNumericLineFrame archiveCode lineIndex := by
  unfold numericCheckProofLine PRFunction.checkProofLine at accepted
  rw [PRFunction.run_conjoin] at accepted
  have outer := (natAndBit_pos_iff _ _).mp accepted
  clear accepted
  unfold PRFunction.checkProofLineFrame
    PRFunction.lessIn PRFunction.lineAtIn PRFunction.lineBoundIn
    PRFunction.lineContextIn PRFunction.lineConclusionIn at outer
  repeat unfold PRFunction.allBits at outer
  repeat first
    | rw [PRFunction.run_conjoin] at outer
    | rw [PRFunction.run_binaryIn] at outer
    | rw [PRFunction.run_unaryIn] at outer
    | rw [PRFunction.run_composition] at outer
    | rw [PRFunctionVector.run_cons] at outer
    | rw [PRFunctionVector.run_singleton] at outer
    | rw [PRFunction.run_projection] at outer
    | rw [NatVector.get_cons_zero] at outer
    | rw [NatVector.get_cons_succ] at outer
    | rw [PRFunction.run_archiveLineCode] at outer
    | rw [PRFunction.run_archiveLineCount] at outer
    | rw [PRFunction.run_proofLineBound] at outer
    | rw [PRFunction.run_proofLineContext] at outer
    | rw [PRFunction.run_proofLineConclusion] at outer
    | rw [PRFunction.run_lessBit] at outer
  have first := (natAndBit_pos_iff _ _).mp outer.1
  have second := (natAndBit_pos_iff _ _).mp first.2
  have third := (natAndBit_pos_iff _ _).mp second.2
  have indexStrictRaw := (natLessBit_pos_iff _ _).mp first.1
  have indexStrict :
      lineIndex < numericArchiveLineCount archiveCode := by
    unfold numericArchiveLineCount
    rw [PRFunction.run_archiveLineCount]
    exact indexStrictRaw
  have contextPositive :
      0 < PRFunction.isContextCode.run
        (NatVector.cons
          (numericLineBound (numericArchiveLine archiveCode lineIndex))
          (NatVector.cons
            (numericLineContext (numericArchiveLine archiveCode lineIndex))
            NatVector.nil)) := by
    unfold numericLineBound numericLineContext numericArchiveLine
    repeat first
      | rw [PRFunction.run_archiveLineCode]
      | rw [PRFunction.run_proofLineBound]
      | rw [PRFunction.run_proofLineContext]
    exact second.1
  have conclusionPositive :
      0 < PRFunction.isScopedFormulaCode.run
        (NatVector.cons
          (numericLineBound (numericArchiveLine archiveCode lineIndex))
          (NatVector.cons
            (numericLineConclusion (numericArchiveLine archiveCode lineIndex))
            NatVector.nil)) := by
    unfold numericLineBound numericLineConclusion numericArchiveLine
    repeat first
      | rw [PRFunction.run_archiveLineCode]
      | rw [PRFunction.run_proofLineBound]
      | rw [PRFunction.run_proofLineConclusion]
    exact third.1
  let decodedContext := decodeFormulaContextOfExistence
    (numericLineBound (numericArchiveLine archiveCode lineIndex))
    (numericLineContext (numericArchiveLine archiveCode lineIndex))
    (PRFunction.isContextCode_positive_sound
      (numericLineBound (numericArchiveLine archiveCode lineIndex))
      (numericLineContext (numericArchiveLine archiveCode lineIndex))
      contextPositive)
  let decodedConclusion := decodeScopedFormulaOfExistence
    (numericLineBound (numericArchiveLine archiveCode lineIndex))
    (numericLineConclusion (numericArchiveLine archiveCode lineIndex))
    (PRFunction.isScopedFormulaCode_positive_sound
      (numericLineBound (numericArchiveLine archiveCode lineIndex))
      (numericLineConclusion (numericArchiveLine archiveCode lineIndex))
      conclusionPositive)
  exact
    { lineInArchive := indexStrict
      context := decodedContext.context
      conclusion := decodedConclusion.formula
      contextExact := decodedContext.quoteExact
      conclusionExact := decodedConclusion.codeExact }

structure AcceptedNumericPrefix
    (history : TheoryHistory)
    (archiveCode lineCount : Nat) : Type where
  proofAt : forall index, index < lineCount ->
    PackedHistoryDerivation history
  boundAligned : forall index (bounded : index < lineCount),
    (proofAt index bounded).bound =
      numericLineBound (numericArchiveLine archiveCode index)
  contextAligned : forall index (bounded : index < lineCount),
    (proofAt index bounded).context.quote =
      numericLineContext (numericArchiveLine archiveCode index)
  conclusionAligned : forall index (bounded : index < lineCount),
    (proofAt index bounded).conclusion.raw.code =
      numericLineConclusion (numericArchiveLine archiveCode index)

def AcceptedNumericPrefix.at
    {history : TheoryHistory}
    {archiveCode lineCount : Nat}
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineCount)
    (index : Nat)
    (bounded : index < lineCount) : PackedHistoryDerivation history :=
  acceptedPrefix.proofAt index bounded

@[simp] theorem AcceptedNumericPrefix.at_bound
    {history : TheoryHistory}
    {archiveCode lineCount : Nat}
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineCount)
    (index : Nat)
    (bounded : index < lineCount) :
    (acceptedPrefix.at index bounded).bound =
      numericLineBound (numericArchiveLine archiveCode index) :=
  acceptedPrefix.boundAligned index bounded

@[simp] theorem AcceptedNumericPrefix.at_contextCode
    {history : TheoryHistory}
    {archiveCode lineCount : Nat}
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineCount)
    (index : Nat)
    (bounded : index < lineCount) :
    (acceptedPrefix.at index bounded).context.quote =
      numericLineContext (numericArchiveLine archiveCode index) :=
  acceptedPrefix.contextAligned index bounded

@[simp] theorem AcceptedNumericPrefix.at_conclusionCode
    {history : TheoryHistory}
    {archiveCode lineCount : Nat}
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineCount)
    (index : Nat)
    (bounded : index < lineCount) :
    (acceptedPrefix.at index bounded).conclusion.raw.code =
      numericLineConclusion (numericArchiveLine archiveCode index) :=
  acceptedPrefix.conclusionAligned index bounded

def PackedHistoryDerivation.recoverFromCodes
    {history : TheoryHistory}
    (packed : PackedHistoryDerivation history)
    {bound : Nat}
    (context : FormulaContext bound)
    (conclusion : ScopedFormula bound)
    (sameBound : packed.bound = bound)
    (sameContext : packed.context.quote = context.quote)
    (sameConclusion : packed.conclusion.raw.code = conclusion.raw.code) :
    Derivation LogicMode.intuitionistic history.theory context conclusion := by
  subst bound
  have contextEquality : packed.context = context :=
    FormulaContext.eq_of_quote_eq sameContext
  subst context
  have conclusionEquality : packed.conclusion = conclusion :=
    ScopedFormula.eq_of_code_eq sameConclusion
  subst conclusion
  exact packed.proof

/-- A packed derivation transported to an explicitly selected bound. -/
structure HistoryDerivationAtBound
    (history : TheoryHistory) (bound : Nat) : Type where
  context : FormulaContext bound
  conclusion : ScopedFormula bound
  proof : Derivation LogicMode.intuitionistic history.theory context conclusion

def PackedHistoryDerivation.atBound
    {history : TheoryHistory}
    (packed : PackedHistoryDerivation history)
    (bound : Nat)
    (sameBound : packed.bound = bound) :
    HistoryDerivationAtBound history bound := by
  cases sameBound
  exact
    { context := packed.context
      conclusion := packed.conclusion
      proof := packed.proof }

@[simp] theorem PackedHistoryDerivation.atBound_context_quote
    {history : TheoryHistory}
    (packed : PackedHistoryDerivation history)
    (bound : Nat)
    (sameBound : packed.bound = bound) :
    (packed.atBound bound sameBound).context.quote =
      packed.context.quote := by
  cases sameBound
  rfl

@[simp] theorem PackedHistoryDerivation.atBound_conclusion_code
    {history : TheoryHistory}
    (packed : PackedHistoryDerivation history)
    (bound : Nat)
    (sameBound : packed.bound = bound) :
    (packed.atBound bound sameBound).conclusion.raw.code =
      packed.conclusion.raw.code := by
  cases sameBound
  rfl

structure ReconstructedNumericLine
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat) : Type where
  packed : PackedHistoryDerivation history
  boundExact : packed.bound =
    numericLineBound (numericArchiveLine archiveCode lineIndex)
  contextExact : packed.context.quote =
    numericLineContext (numericArchiveLine archiveCode lineIndex)
  conclusionExact : packed.conclusion.raw.code =
    numericLineConclusion (numericArchiveLine archiveCode lineIndex)

structure ScopedConjunctionView {bound : Nat}
    (formula : ScopedFormula bound) : Type where
  left : ScopedFormula bound
  right : ScopedFormula bound
  exact : formula = ScopedFormula.conj left right

structure ScopedDisjunctionView {bound : Nat}
    (formula : ScopedFormula bound) : Type where
  left : ScopedFormula bound
  right : ScopedFormula bound
  exact : formula = ScopedFormula.disj left right

structure ScopedImplicationView {bound : Nat}
    (formula : ScopedFormula bound) : Type where
  left : ScopedFormula bound
  right : ScopedFormula bound
  exact : formula = ScopedFormula.impl left right

structure ScopedEqualityView {bound : Nat}
    (formula : ScopedFormula bound) : Type where
  left : ScopedTerm bound
  right : ScopedTerm bound
  exact : formula = ScopedFormula.equal left right

structure ScopedUniversalView {bound : Nat}
    (formula : ScopedFormula bound) : Type where
  body : ScopedFormula (Nat.succ bound)
  exact : formula = ScopedFormula.all body

structure ScopedExistentialView {bound : Nat}
    (formula : ScopedFormula bound) : Type where
  body : ScopedFormula (Nat.succ bound)
  exact : formula = ScopedFormula.ex body

def eliminateImpossibleNatEquality
    {result : Sort _}
    {left right : Nat}
    (same : left = right)
    (different : Not (left = right)) :
    result :=
  (different same).elim

def ScopedFormula.conjunctionViewOfTag
    {bound : Nat}
    (formula : ScopedFormula bound)
    (tag : natUnpairLeft formula.raw.code.pred = 2) :
    ScopedConjunctionView formula := by
  cases formula with
  | mk raw scoping =>
      cases raw with
      | falsum => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | equal left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | conj left right =>
          exact
            { left := { raw := left, isScoped := scoping.1 }
              right := { raw := right, isScoped := scoping.2 }
              exact := rfl }
      | disj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | impl left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | all body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | ex body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)

def ScopedFormula.disjunctionViewOfTag
    {bound : Nat}
    (formula : ScopedFormula bound)
    (tag : natUnpairLeft formula.raw.code.pred = 3) :
    ScopedDisjunctionView formula := by
  cases formula with
  | mk raw scoping =>
      cases raw with
      | falsum => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | equal left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | conj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | disj left right =>
          exact
            { left := { raw := left, isScoped := scoping.1 }
              right := { raw := right, isScoped := scoping.2 }
              exact := rfl }
      | impl left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | all body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | ex body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)

def ScopedFormula.implicationViewOfTag
    {bound : Nat}
    (formula : ScopedFormula bound)
    (tag : natUnpairLeft formula.raw.code.pred = 4) :
    ScopedImplicationView formula := by
  cases formula with
  | mk raw scoping =>
      cases raw with
      | falsum => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | equal left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | conj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | disj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | impl left right =>
          exact
            { left := { raw := left, isScoped := scoping.1 }
              right := { raw := right, isScoped := scoping.2 }
              exact := rfl }
      | all body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | ex body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)

def ScopedFormula.equalityViewOfTag
    {bound : Nat}
    (formula : ScopedFormula bound)
    (tag : natUnpairLeft formula.raw.code.pred = 1) :
    ScopedEqualityView formula := by
  cases formula with
  | mk raw scoping =>
      cases raw with
      | falsum => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | equal left right =>
          exact
            { left := { raw := left, isScoped := scoping.1 }
              right := { raw := right, isScoped := scoping.2 }
              exact := rfl }
      | conj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | disj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | impl left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | all body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | ex body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)

def ScopedFormula.universalViewOfTag
    {bound : Nat}
    (formula : ScopedFormula bound)
    (tag : natUnpairLeft formula.raw.code.pred = 5) :
    ScopedUniversalView formula := by
  cases formula with
  | mk raw scoping =>
      cases raw with
      | falsum => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | equal left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | conj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | disj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | impl left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | all body =>
          exact
            { body := { raw := body, isScoped := scoping }
              exact := rfl }
      | ex body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)

def ScopedFormula.existentialViewOfTag
    {bound : Nat}
    (formula : ScopedFormula bound)
    (tag : natUnpairLeft formula.raw.code.pred = 6) :
    ScopedExistentialView formula := by
  cases formula with
  | mk raw scoping =>
      cases raw with
      | falsum => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | equal left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | conj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | disj left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | impl left right => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | all body => dsimp [RawFormula.code] at tag; rw [natUnpairLeft_pair] at tag; exact eliminateImpossibleNatEquality tag (by decide)
      | ex body =>
          exact
            { body := { raw := body, isScoped := scoping }
              exact := rfl }

theorem ScopedConjunctionView.leftCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedConjunctionView formula) :
    natUnpairLeft (natUnpairRight formula.raw.code.pred) =
      view.left.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairLeft
            (natUnpairRight
              (Nat.succ
                (natPair 2
                  (natPair left.raw.code right.raw.code))).pred) =
          left.raw.code
      rw [Nat.pred_succ, natUnpairRight_pair, natUnpairLeft_pair]

theorem ScopedConjunctionView.rightCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedConjunctionView formula) :
    natUnpairRight (natUnpairRight formula.raw.code.pred) =
      view.right.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairRight
            (natUnpairRight
              (Nat.succ
                (natPair 2
                  (natPair left.raw.code right.raw.code))).pred) =
          right.raw.code
      rw [Nat.pred_succ]
      repeat rw [natUnpairRight_pair]

theorem ScopedDisjunctionView.leftCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedDisjunctionView formula) :
    natUnpairLeft (natUnpairRight formula.raw.code.pred) =
      view.left.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairLeft
            (natUnpairRight
              (Nat.succ
                (natPair 3
                  (natPair left.raw.code right.raw.code))).pred) =
          left.raw.code
      rw [Nat.pred_succ, natUnpairRight_pair, natUnpairLeft_pair]

theorem ScopedDisjunctionView.rightCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedDisjunctionView formula) :
    natUnpairRight (natUnpairRight formula.raw.code.pred) =
      view.right.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairRight
            (natUnpairRight
              (Nat.succ
                (natPair 3
                  (natPair left.raw.code right.raw.code))).pred) =
          right.raw.code
      rw [Nat.pred_succ]
      repeat rw [natUnpairRight_pair]

theorem ScopedImplicationView.leftCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedImplicationView formula) :
    natUnpairLeft (natUnpairRight formula.raw.code.pred) =
      view.left.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairLeft
            (natUnpairRight
              (Nat.succ
                (natPair 4
                  (natPair left.raw.code right.raw.code))).pred) =
          left.raw.code
      rw [Nat.pred_succ, natUnpairRight_pair, natUnpairLeft_pair]

theorem ScopedImplicationView.rightCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedImplicationView formula) :
    natUnpairRight (natUnpairRight formula.raw.code.pred) =
      view.right.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairRight
            (natUnpairRight
              (Nat.succ
                (natPair 4
                  (natPair left.raw.code right.raw.code))).pred) =
          right.raw.code
      rw [Nat.pred_succ]
      repeat rw [natUnpairRight_pair]

theorem ScopedEqualityView.leftCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedEqualityView formula) :
    natUnpairLeft (natUnpairRight formula.raw.code.pred) =
      view.left.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairLeft
            (natUnpairRight
              (Nat.succ
                (natPair 1
                  (natPair left.raw.code right.raw.code))).pred) =
          left.raw.code
      rw [Nat.pred_succ, natUnpairRight_pair, natUnpairLeft_pair]

theorem ScopedEqualityView.rightCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedEqualityView formula) :
    natUnpairRight (natUnpairRight formula.raw.code.pred) =
      view.right.raw.code := by
  cases view with
  | mk left right exact =>
      cases exact
      change
        natUnpairRight
            (natUnpairRight
              (Nat.succ
                (natPair 1
                  (natPair left.raw.code right.raw.code))).pred) =
          right.raw.code
      rw [Nat.pred_succ]
      repeat rw [natUnpairRight_pair]

theorem ScopedUniversalView.bodyCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedUniversalView formula) :
    natUnpairRight formula.raw.code.pred = view.body.raw.code := by
  cases view with
  | mk body exact =>
      cases exact
      change
        natUnpairRight
            (Nat.succ (natPair 5 body.raw.code)).pred =
          body.raw.code
      rw [Nat.pred_succ, natUnpairRight_pair]

theorem ScopedExistentialView.bodyCode
    {bound : Nat}
    {formula : ScopedFormula bound}
    (view : ScopedExistentialView formula) :
    natUnpairRight formula.raw.code.pred = view.body.raw.code := by
  cases view with
  | mk body exact =>
      cases exact
      change
        natUnpairRight
            (Nat.succ (natPair 6 body.raw.code)).pred =
          body.raw.code
      rw [Nat.pred_succ, natUnpairRight_pair]

theorem checkProofLine_selected_body_positive
    (expected : Nat)
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = expected)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    0 < (PRFunction.checkProofLineRuleBody expected).run
      (proofCheckInputs history.quote archiveCode lineIndex) := by
  have fullPositive := accepted
  unfold numericCheckProofLine PRFunction.checkProofLine at fullPositive
  rw [PRFunction.run_conjoin] at fullPositive
  have rulePart := (natAndBit_pos_iff _ _).mp fullPositive |>.2
  change 0 < PRFunction.checkProofLineRules.run
    (proofCheckInputs history.quote archiveCode lineIndex) at rulePart
  have alternatives :=
    (PRFunction.checkProofLineRules_positive_iff
      history.quote archiveCode lineIndex).mp rulePart
  have tagExact :
      proofCheckRuleValue archiveCode lineIndex = expected := by
    unfold proofCheckRuleValue
    unfold numericLineRule numericArchiveLine at ruleExact
    exact ruleExact
  exact proofCheckRuleAlternatives_body_of_tag expected history.quote
    archiveCode lineIndex
    intuitionisticProofRuleTags
    tagExact alternatives

theorem checkProofLine_rule0_body_positive
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 0)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    0 < (PRFunction.checkProofLineRuleBody 0).run
      (NatVector.cons history.quote
        (NatVector.cons archiveCode
          (NatVector.cons lineIndex NatVector.nil))) := by
  change 0 < (PRFunction.checkProofLineRuleBody 0).run
    (proofCheckInputs history.quote archiveCode lineIndex)
  exact checkProofLine_selected_body_positive 0 history archiveCode
    lineIndex ruleExact accepted

theorem PRFunction.run_proofCheckTheoryAxiomBody_numeric
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat) :
    PRFunction.proofCheckTheoryAxiomBody.run
        (proofCheckInputs history.quote archiveCode lineIndex) =
      natAndBit
        (natEqualBit
          (numericLinePremises
            (numericArchiveLine archiveCode lineIndex))
          0)
        (natAndBit
          (PRFunction.isHistoryAxiomCode.run
            (NatVector.cons history.quote
              (NatVector.cons
                (numericLineBound
                  (numericArchiveLine archiveCode lineIndex))
                (NatVector.cons
                  (numericLineConclusion
                    (numericArchiveLine archiveCode lineIndex))
                  (NatVector.cons
                    (numericLineParameters
                      (numericArchiveLine archiveCode lineIndex))
                    NatVector.nil)))))
          1) := by
  unfold PRFunction.proofCheckTheoryAxiomBody PRFunction.allBits
    PRFunction.sameIn PRFunction.proofCheckEmpty
  repeat unfold PRFunction.allBits
  repeat first
    | rw [PRFunction.run_conjoin]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_equalBit]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_proofCheckPremises]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_proofCheckHistory]
    | rw [PRFunction.run_proofCheckBound]
    | rw [PRFunction.run_proofCheckConclusion]
    | rw [PRFunction.run_proofCheckParameters]

theorem checkProofLine_rule0_axiom_positive
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 0)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    0 < PRFunction.isHistoryAxiomCode.run
      (NatVector.cons history.quote
        (NatVector.cons
          (numericLineBound (numericArchiveLine archiveCode lineIndex))
          (NatVector.cons
            (numericLineConclusion
              (numericArchiveLine archiveCode lineIndex))
            (NatVector.cons
              (numericLineParameters
                (numericArchiveLine archiveCode lineIndex))
              NatVector.nil)))) := by
  have rulePart :
      0 < PRFunction.proofCheckTheoryAxiomBody.run
        (proofCheckInputs history.quote archiveCode lineIndex) :=
    checkProofLine_rule0_body_positive
      history archiveCode lineIndex ruleExact accepted
  have normalized :
      0 < natAndBit
        (natEqualBit
          (numericLinePremises
            (numericArchiveLine archiveCode lineIndex))
          0)
        (natAndBit
          (PRFunction.isHistoryAxiomCode.run
            (NatVector.cons history.quote
              (NatVector.cons
                (numericLineBound
                  (numericArchiveLine archiveCode lineIndex))
                (NatVector.cons
                  (numericLineConclusion
                    (numericArchiveLine archiveCode lineIndex))
                  (NatVector.cons
                    (numericLineParameters
                      (numericArchiveLine archiveCode lineIndex))
                    NatVector.nil)))))
          1) :=
    Eq.mp
      (congrArg (fun value : Nat => 0 < value)
        (PRFunction.run_proofCheckTheoryAxiomBody_numeric
          history archiveCode lineIndex))
      rulePart
  exact ((natAndBit_pos_iff _ _).mp
    ((natAndBit_pos_iff _ _).mp normalized).2).1

def checkProofLine_rule0_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 0)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have axiomPositive := checkProofLine_rule0_axiom_positive
    history archiveCode lineIndex ruleExact accepted
  let lineCode := numericArchiveLine archiveCode lineIndex
  let bound := numericLineBound lineCode
  let context := frame.context
  let conclusion := frame.conclusion
  cases PRFunction.isHistoryAxiomCode_positive_sound history bound
      (numericLineConclusion lineCode) (numericLineParameters lineCode)
      axiomPositive with
  | mk axiomFormula witness conclusionCode parametersCode =>
      have sameConclusion : axiomFormula = conclusion := by
        apply ScopedFormula.eq_of_code_eq
        exact conclusionCode.trans frame.conclusionExact.symm
      subst conclusion
      let packed : PackedHistoryDerivation history :=
        { bound := bound
          context := context
          conclusion := axiomFormula
          proof := Derivation.theoryAxiom witness }
      exact
        { packed := packed
          boundExact := rfl
          contextExact := frame.contextExact
          conclusionExact := conclusionCode }

macro "normalize_line_program" loc:(location)? : tactic =>
  `(tactic|
    (try dsimp only [PRFunction.checkProofLineRuleBody] $[$loc]?) <;>
    (try unfold PRFunction.checkProofLineRuleBodies $[$loc]?) <;>
    (try dsimp only [
      PRFunction.proofCheckTheoryAxiomBody,
      PRFunction.proofCheckHypothesisBody,
      PRFunction.proofCheckWeakenBody,
      PRFunction.proofCheckImplicationIntroductionBody,
      PRFunction.proofCheckImplicationEliminationBody,
      PRFunction.proofCheckConjunctionIntroductionBody,
      PRFunction.proofCheckConjunctionEliminationLeftBody,
      PRFunction.proofCheckConjunctionEliminationRightBody,
      PRFunction.proofCheckDisjunctionIntroductionLeftBody,
      PRFunction.proofCheckDisjunctionIntroductionRightBody,
      PRFunction.proofCheckDisjunctionEliminationBody,
      PRFunction.proofCheckFalsumEliminationBody,
      PRFunction.proofCheckUniversalIntroductionBody,
      PRFunction.proofCheckUniversalEliminationBody,
      PRFunction.proofCheckExistentialIntroductionBody,
      PRFunction.proofCheckExistentialEliminationBody,
      PRFunction.proofCheckEqualityReflexivityBody,
      PRFunction.proofCheckEqualitySymmetryBody,
      PRFunction.proofCheckEqualityTransitivityBody,
      PRFunction.proofCheckEqualitySubstitutionBody,
      PRFunction.proofCheckLiftVariablesBody,
      PRFunction.proofCheckFreeInstantiationBody,
      PRFunction.proofCheckDoubleNegationEliminationBody,
      PRFunction.checkProofLineRuleTag,
      PRFunction.sameIn,
      PRFunction.lessIn,
      PRFunction.lineAtIn,
      PRFunction.lineRuleIn,
      PRFunction.lineBoundIn,
      PRFunction.lineContextIn,
      PRFunction.lineConclusionIn,
      PRFunction.linePremisesIn,
      PRFunction.lineParametersIn,
      PRFunction.listEntryIn,
      PRFunction.syntaxEncodedIn,
      PRFunction.syntaxTagIn,
      PRFunction.syntaxPayloadIn,
      PRFunction.syntaxLeftIn,
      PRFunction.syntaxRightIn,
      PRFunction.contextConsIn,
      PRFunction.formulaEqualIn,
      PRFunction.formulaConjIn,
      PRFunction.formulaDisjIn,
      PRFunction.formulaImplIn,
      PRFunction.formulaAllIn,
      PRFunction.formulaExIn,
      PRFunction.instantiateFormulaIn,
      PRFunction.raiseFormulaOneIn,
      PRFunction.raiseContextOneIn,
      PRFunction.instantiateContextIn,
      PRFunction.proofCheckUnaryChronological,
      PRFunction.proofCheckBinaryChronological,
      PRFunction.proofCheckTernaryChronological,
      PRFunction.proofCheckUnaryPremises,
      PRFunction.proofCheckBinaryPremises,
      PRFunction.proofCheckTernaryPremises,
      PRFunction.proofCheckSameFirstFrame,
      PRFunction.proofCheckSameSecondFrame,
      PRFunction.proofCheckEmptyParameters,
      PRFunction.proofCheckSingletonParameter,
      PRFunction.proofCheckSyntaxTagIs,
      PRFunction.proofCheckFirstRef,
      PRFunction.proofCheckSecondRef,
      PRFunction.proofCheckThirdRef,
      PRFunction.proofCheckSuccessorBound,
      PRFunction.proofCheckFalsum,
      PRFunction.proofCheckEmpty,
      proofCheckInputs] $[$loc]?) <;>
    (try simp only [
      PRFunction.run_proofCheckHistory,
      PRFunction.run_proofCheckArchive,
      PRFunction.run_proofCheckIndex,
      PRFunction.run_proofCheckLine,
      PRFunction.run_proofCheckBound,
      PRFunction.run_proofCheckContext,
      PRFunction.run_proofCheckConclusion,
      PRFunction.run_proofCheckPremises,
      PRFunction.run_proofCheckParameters,
      PRFunction.run_proofCheckReference,
      PRFunction.run_proofCheckParameter,
      PRFunction.run_proofCheckFirstLine,
      PRFunction.run_proofCheckSecondLine,
      PRFunction.run_proofCheckThirdLine,
      PRFunction.run_proofCheckFirstBound,
      PRFunction.run_proofCheckSecondBound,
      PRFunction.run_proofCheckThirdBound,
      PRFunction.run_proofCheckFirstContext,
      PRFunction.run_proofCheckSecondContext,
      PRFunction.run_proofCheckThirdContext,
      PRFunction.run_proofCheckFirstConclusion,
      PRFunction.run_proofCheckSecondConclusion,
      PRFunction.run_proofCheckThirdConclusion,
      PRFunction.run_proofCheckHistory_raw,
      PRFunction.run_proofCheckIndex_raw,
      PRFunction.run_proofCheckLine_raw,
      PRFunction.run_proofCheckBound_raw,
      PRFunction.run_proofCheckContext_raw,
      PRFunction.run_proofCheckConclusion_raw,
      PRFunction.run_proofCheckPremises_raw,
      PRFunction.run_proofCheckParameters_raw,
      PRFunction.run_proofCheckReference_raw,
      PRFunction.run_proofCheckParameter_raw,
      PRFunction.run_proofCheckFirstLine_raw,
      PRFunction.run_proofCheckFirstBound_raw,
      PRFunction.run_proofCheckFirstContext_raw,
      PRFunction.run_proofCheckFirstConclusion_raw,
      PRFunction.run_proofCheckSecondLine_raw,
      PRFunction.run_proofCheckSecondBound_raw,
      PRFunction.run_proofCheckSecondContext_raw,
      PRFunction.run_proofCheckSecondConclusion_raw,
      PRFunction.run_proofCheckThirdLine_raw,
      PRFunction.run_proofCheckThirdBound_raw,
      PRFunction.run_proofCheckThirdContext_raw,
      PRFunction.run_proofCheckThirdConclusion_raw] $[$loc]?) <;>
    (repeat first
      | unfold PRFunction.allBits $[$loc]?
      | unfold PRFunction.anyBits $[$loc]?
      | rw [PRFunction.run_checkProofLineRuleCheck] $[$loc]?
      | rw [PRFunction.run_conjoin] $[$loc]?
      | rw [PRFunction.run_binaryIn] $[$loc]?
      | rw [PRFunction.run_unaryIn] $[$loc]?
      | rw [PRFunction.run_composition] $[$loc]?
      | rw [PRFunctionVector.run_cons] $[$loc]?
      | rw [PRFunctionVector.run_singleton] $[$loc]?
      | rw [PRFunction.run_projection] $[$loc]?
      | rw [NatVector.get_cons_zero] $[$loc]?
      | rw [NatVector.get_cons_succ] $[$loc]?
      | rw [PRFunction.run_constant] $[$loc]?
      | rw [PRFunction.run_successor] $[$loc]?
      | rw [PRFunction.run_predecessor] $[$loc]?
      | rw [PRFunction.run_unpairLeft] $[$loc]?
      | rw [PRFunction.run_unpairRight] $[$loc]?
      | rw [PRFunction.run_archiveLineCode_numeric] $[$loc]?
      | rw [PRFunction.run_archiveLineCount_numeric] $[$loc]?
      | rw [PRFunction.run_proofLineRule_numeric] $[$loc]?
      | rw [PRFunction.run_proofLineBound_numeric] $[$loc]?
      | rw [PRFunction.run_proofLineContext_numeric] $[$loc]?
      | rw [PRFunction.run_proofLineConclusion_numeric] $[$loc]?
      | rw [PRFunction.run_proofLinePremises_numeric] $[$loc]?
      | rw [PRFunction.run_proofLineParameters_numeric] $[$loc]?
      | rw [PRFunction.run_archiveLineCode] $[$loc]?
      | rw [PRFunction.run_archiveLineCount] $[$loc]?
      | rw [PRFunction.run_proofLineRule] $[$loc]?
      | rw [PRFunction.run_proofLineBound] $[$loc]?
      | rw [PRFunction.run_proofLineContext] $[$loc]?
      | rw [PRFunction.run_proofLineConclusion] $[$loc]?
      | rw [PRFunction.run_proofLinePremises] $[$loc]?
      | rw [PRFunction.run_proofLineParameters] $[$loc]?
      | rw [PRFunction.run_codedListEntry] $[$loc]?
      | rw [PRFunction.run_codedListSingleton] $[$loc]?
      | rw [PRFunction.run_codedListPair] $[$loc]?
      | rw [PRFunction.run_codedListTriple] $[$loc]?
      | rw [PRFunction.run_lessBit] $[$loc]?
      | rw [PRFunction.run_equalBit] $[$loc]?
      | rw [PRFunction.run_andBit] $[$loc]?
      | rw [PRFunction.run_orBit] $[$loc]?
      | rw [PRFunction.run_isContextCode] $[$loc]?
      | rw [PRFunction.run_isScopedFormulaCode] $[$loc]?
      | rw [PRFunction.run_isScopedTermCode] $[$loc]?
      | rw [PRFunction.run_theoryHistoryContains] $[$loc]?
      | rw [PRFunction.run_raiseContextCode] $[$loc]?
      | rw [PRFunction.run_raiseFormulaCode] $[$loc]?
      | rw [PRFunction.run_instantiateContextTermCode] $[$loc]?
      | rw [PRFunction.run_machineInstantiateTerm] $[$loc]?
      | rw [PRFunction.run_formulaEqualCode] $[$loc]?
      | rw [PRFunction.run_formulaConjunctionCode] $[$loc]?
      | rw [PRFunction.run_formulaDisjunctionCode] $[$loc]?
      | rw [PRFunction.run_formulaImplicationCode] $[$loc]?
      | rw [PRFunction.run_formulaUniversalCode] $[$loc]?
      | rw [PRFunction.run_formulaExistentialCode] $[$loc]?
      | rw [PRFunction.run_falsumCode] $[$loc]?) <;>
    (try simp only [
      PRFunction.run_proofCheckHistory,
      PRFunction.run_proofCheckArchive,
      PRFunction.run_proofCheckIndex,
      PRFunction.run_proofCheckLine,
      PRFunction.run_proofCheckBound,
      PRFunction.run_proofCheckContext,
      PRFunction.run_proofCheckConclusion,
      PRFunction.run_proofCheckPremises,
      PRFunction.run_proofCheckParameters,
      PRFunction.run_proofCheckReference,
      PRFunction.run_proofCheckParameter,
      PRFunction.run_proofCheckFirstLine,
      PRFunction.run_proofCheckSecondLine,
      PRFunction.run_proofCheckThirdLine,
      PRFunction.run_proofCheckFirstBound,
      PRFunction.run_proofCheckSecondBound,
      PRFunction.run_proofCheckThirdBound,
      PRFunction.run_proofCheckFirstContext,
      PRFunction.run_proofCheckSecondContext,
      PRFunction.run_proofCheckThirdContext,
      PRFunction.run_proofCheckFirstConclusion,
      PRFunction.run_proofCheckSecondConclusion,
      PRFunction.run_proofCheckThirdConclusion,
      PRFunction.run_proofCheckHistory_raw,
      PRFunction.run_proofCheckIndex_raw,
      PRFunction.run_proofCheckLine_raw,
      PRFunction.run_proofCheckBound_raw,
      PRFunction.run_proofCheckContext_raw,
      PRFunction.run_proofCheckConclusion_raw,
      PRFunction.run_proofCheckPremises_raw,
      PRFunction.run_proofCheckParameters_raw,
      PRFunction.run_proofCheckReference_raw,
      PRFunction.run_proofCheckParameter_raw,
      PRFunction.run_proofCheckFirstLine_raw,
      PRFunction.run_proofCheckFirstBound_raw,
      PRFunction.run_proofCheckFirstContext_raw,
      PRFunction.run_proofCheckFirstConclusion_raw,
      PRFunction.run_proofCheckSecondLine_raw,
      PRFunction.run_proofCheckSecondBound_raw,
      PRFunction.run_proofCheckSecondContext_raw,
      PRFunction.run_proofCheckSecondConclusion_raw,
      PRFunction.run_proofCheckThirdLine_raw,
      PRFunction.run_proofCheckThirdBound_raw,
      PRFunction.run_proofCheckThirdContext_raw,
      PRFunction.run_proofCheckThirdConclusion_raw] $[$loc]?))

def checkProofLine_rule1_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 1)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have fields := (natAndBit_pos_iff _ _).mp rulePart
  have second := (natAndBit_pos_iff _ _).mp fields.2
  have third := (natAndBit_pos_iff _ _).mp second.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  have member : ContextMember frame.conclusion frame.context := by
    apply FormulaContext.numeric_positive_implies_member
    rw [frame.contextExact, frame.conclusionExact]
    rw [PRFunction.run_theoryHistoryContains]
    exact third.1
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := Derivation.hypothesis member }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule16_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 16)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have fields := (natAndBit_pos_iff _ _).mp rulePart
  have second := (natAndBit_pos_iff _ _).mp fields.2
  have third := (natAndBit_pos_iff _ _).mp second.2
  have fourth := (natAndBit_pos_iff _ _).mp third.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let termCode := codedListEntry (numericLineParameters lineCode) 0
  have termPositive :
      0 < PRFunction.isScopedTermCode.run
        (NatVector.cons (numericLineBound lineCode)
          (NatVector.cons termCode NatVector.nil)) := by
    rw [PRFunction.run_isScopedTermCode,
      PRFunction.run_isScopedFormulaCode]
    exact third.1
  let decodedTerm := PRFunction.decodeScopedTermCodePositive
    (numericLineBound lineCode) termCode termPositive
  let term := decodedTerm.term
  have termExact : term.raw.code = termCode := decodedTerm.codeExact
  have conclusionCode := (natEqualBit_pos_iff _ _).mp fourth.1
  have sameConclusion :
      ScopedFormula.equal term term = frame.conclusion := by
    apply ScopedFormula.eq_of_code_eq
    simp only [ScopedFormula.equal, RawFormula.code]
    rw [termExact]
    exact conclusionCode.symm.trans frame.conclusionExact.symm
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := by
        rw [← sameConclusion]
        exact Derivation.equalityReflexivity term }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule2_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 2)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let parameters := numericLineParameters lineCode
  let reference := codedListEntry premises 0
  let extraCode := codedListEntry parameters 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have extraPositive :
      0 < PRFunction.isScopedFormulaCode.run
        (NatVector.cons (numericLineBound lineCode)
          (NatVector.cons extraCode NatVector.nil)) := by
    rw [PRFunction.run_isScopedFormulaCode]
    exact f6.1
  let decodedExtra := PRFunction.decodeScopedFormulaCodePositive
    (numericLineBound lineCode) extraCode extraPositive
  let extra := decodedExtra.formula
  have extraExact : extra.raw.code = extraCode := decodedExtra.codeExact
  have sameBound := (natEqualBit_pos_iff _ _).mp f3.1
  have sameContext := (natEqualBit_pos_iff _ _).mp f4.1
  have sameConclusion := (natEqualBit_pos_iff _ _).mp f5.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact sameBound
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have builtContextCode :
      (FormulaContext.cons extra premiseAt.context).quote =
        numericLineContext lineCode := by
    simp only [FormulaContext.quote]
    rw [extraExact, PackedHistoryDerivation.atBound_context_quote,
      AcceptedNumericPrefix.at_contextCode]
    rw [PRFunction.run_codedListCons] at sameContext
    exact sameContext.symm
  have builtConclusionCode :
      premiseAt.conclusion.raw.code = numericLineConclusion lineCode := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode, sameConclusion]
  have contextEquality :
      FormulaContext.cons extra premiseAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq
      (builtContextCode.trans frame.contextExact.symm)
  have conclusionEquality : premiseAt.conclusion = frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (builtConclusionCode.trans frame.conclusionExact.symm)
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := by
        rw [← contextEquality, ← conclusionEquality]
        exact Derivation.weaken extra premiseAt.proof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule20_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 20)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp f3.1
  have contextCode := (natEqualBit_pos_iff _ _).mp f4.1
  have conclusionCode := (natEqualBit_pos_iff _ _).mp f5.1
  have currentBound :
      numericLineBound lineCode = Nat.succ premise.bound := by
    rw [AcceptedNumericPrefix.at_bound]
    exact boundCode
  let liftedContext := premise.context.lift
  let liftedConclusion := premise.conclusion.lift
  have liftedContextCode : liftedContext.quote =
      numericLineContext lineCode := by
    unfold liftedContext
    rw [← PRFunction.raiseContextCode_lift,
      PRFunction.run_raiseContextCode,
      AcceptedNumericPrefix.at_contextCode]
    exact contextCode.symm
  have liftedConclusionCode : liftedConclusion.raw.code =
      numericLineConclusion lineCode := by
    unfold liftedConclusion
    rw [ScopedFormula.lift_code,
      PRFunction.run_raiseFormulaCode,
      AcceptedNumericPrefix.at_conclusionCode]
    exact conclusionCode.symm
  let packed : PackedHistoryDerivation history :=
    { bound := Nat.succ premise.bound
      context := liftedContext
      conclusion := liftedConclusion
      proof := Derivation.liftVariables premise.proof }
  exact
    { packed := packed
      boundExact := currentBound.symm
      contextExact := liftedContextCode
      conclusionExact := liftedConclusionCode }

def checkProofLine_rule11_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 11)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have falsumCode := (natEqualBit_pos_iff _ _).mp f4.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact boundCode
  have premiseProof :
      Derivation LogicMode.intuitionistic history.theory frame.context
        (ScopedFormula.falsum (numericLineBound lineCode)) := by
    apply premise.recoverFromCodes
    · exact premiseBound
    · rw [AcceptedNumericPrefix.at_contextCode,
        contextCode, frame.contextExact]
    · rw [AcceptedNumericPrefix.at_conclusionCode,
        falsumCode]
      rfl
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := Derivation.falsumElimination premiseProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule4_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact :
      numericLineRule (numericArchiveLine archiveCode lineIndex) = 4)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology1 := (natAndBit_pos_iff _ _).mp f1.1
  have chronology2 := (natAndBit_pos_iff _ _).mp chronology1.2
  have chronology3 := (natAndBit_pos_iff _ _).mp chronology2.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have firstFrame := (natAndBit_pos_iff _ _).mp f3.1
  have firstFrameTail := (natAndBit_pos_iff _ _).mp firstFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have secondFrame := (natAndBit_pos_iff _ _).mp f4.1
  have secondFrameTail := (natAndBit_pos_iff _ _).mp secondFrame.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  have f7 := (natAndBit_pos_iff _ _).mp f6.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let firstRef := codedListEntry premises 0
  let secondRef := codedListEntry premises 1
  have firstEarlier : firstRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronology2.1
  have secondEarlier : secondRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronology3.1
  let first := acceptedPrefix.at firstRef firstEarlier
  let second := acceptedPrefix.at secondRef secondEarlier
  have firstBoundCode := (natEqualBit_pos_iff _ _).mp firstFrame.1
  have firstContextCode := (natEqualBit_pos_iff _ _).mp firstFrameTail.1
  have secondBoundCode := (natEqualBit_pos_iff _ _).mp secondFrame.1
  have secondContextCode := (natEqualBit_pos_iff _ _).mp secondFrameTail.1
  have leftCode := (natEqualBit_pos_iff _ _).mp f6.1
  have rightCode := (natEqualBit_pos_iff _ _).mp f7.1
  have firstBound : first.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact firstBoundCode
  have secondBound : second.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact secondBoundCode
  let firstAt := first.atBound (numericLineBound lineCode) firstBound
  let secondAt := second.atBound (numericLineBound lineCode) secondBound
  have firstContextEquality : firstAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        firstContextCode, frame.contextExact])
  have secondContextEquality : secondAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        secondContextCode, frame.contextExact])
  have secondProof :
      Derivation LogicMode.intuitionistic history.theory frame.context
        secondAt.conclusion := by
    rw [← secondContextEquality]
    exact secondAt.proof
  have firstAtCode :
      firstAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode firstRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have secondAtCode :
      secondAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode secondRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have firstTagNumeric := (natEqualBit_pos_iff _ _).mp f5.1
  have firstTag :
      natUnpairLeft firstAt.conclusion.raw.code.pred = 4 := by
    rw [firstAtCode]
    exact firstTagNumeric
  let view := firstAt.conclusion.implicationViewOfTag firstTag
  have projectedLeft :
      natUnpairLeft (natUnpairRight firstAt.conclusion.raw.code.pred) =
        view.left.raw.code := by
    exact view.leftCode
  have projectedRight :
      natUnpairRight (natUnpairRight firstAt.conclusion.raw.code.pred) =
        view.right.raw.code := by
    exact view.rightCode
  have leftEquality : view.left = secondAt.conclusion :=
    ScopedFormula.eq_of_code_eq (by
      calc
        view.left.raw.code =
            natUnpairLeft
              (natUnpairRight firstAt.conclusion.raw.code.pred) :=
          projectedLeft.symm
        _ = natUnpairLeft
              (natUnpairRight
                (numericLineConclusion
                  (numericArchiveLine archiveCode firstRef)).pred) := by
            rw [firstAtCode]
        _ = numericLineConclusion
              (numericArchiveLine archiveCode secondRef) := leftCode
        _ = secondAt.conclusion.raw.code := secondAtCode.symm)
  have rightEquality : view.right = frame.conclusion :=
    ScopedFormula.eq_of_code_eq (by
      calc
        view.right.raw.code =
            natUnpairRight
              (natUnpairRight firstAt.conclusion.raw.code.pred) :=
          projectedRight.symm
        _ = natUnpairRight
              (natUnpairRight
                (numericLineConclusion
                  (numericArchiveLine archiveCode firstRef)).pred) := by
            rw [firstAtCode]
        _ = numericLineConclusion
              (numericArchiveLine archiveCode lineIndex) := rightCode
        _ = frame.conclusion.raw.code := frame.conclusionExact.symm)
  have implicationEquality :
      firstAt.conclusion =
        ScopedFormula.impl secondAt.conclusion frame.conclusion := by
    rw [view.exact, leftEquality, rightEquality]
  have firstProof :
      Derivation LogicMode.intuitionistic history.theory frame.context
        (ScopedFormula.impl secondAt.conclusion frame.conclusion) := by
    rw [← firstContextEquality]
    rw [← implicationEquality]
    exact firstAt.proof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := Derivation.implicationElimination firstProof secondProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule5_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 5)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have c1 := (natAndBit_pos_iff _ _).mp f1.1
  have c2 := (natAndBit_pos_iff _ _).mp c1.2
  have c3 := (natAndBit_pos_iff _ _).mp c2.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have firstFrame := (natAndBit_pos_iff _ _).mp f3.1
  have firstFrameTail := (natAndBit_pos_iff _ _).mp firstFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have secondFrame := (natAndBit_pos_iff _ _).mp f4.1
  have secondFrameTail := (natAndBit_pos_iff _ _).mp secondFrame.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let firstRef := codedListEntry premises 0
  let secondRef := codedListEntry premises 1
  have firstEarlier : firstRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c2.1
  have secondEarlier : secondRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c3.1
  let first := acceptedPrefix.at firstRef firstEarlier
  let second := acceptedPrefix.at secondRef secondEarlier
  have firstBoundCode := (natEqualBit_pos_iff _ _).mp firstFrame.1
  have firstContextCode := (natEqualBit_pos_iff _ _).mp firstFrameTail.1
  have secondBoundCode := (natEqualBit_pos_iff _ _).mp secondFrame.1
  have secondContextCode := (natEqualBit_pos_iff _ _).mp secondFrameTail.1
  have conclusionCode := (natEqualBit_pos_iff _ _).mp f5.1
  have firstBound : first.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact firstBoundCode
  have secondBound : second.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact secondBoundCode
  let firstAt := first.atBound (numericLineBound lineCode) firstBound
  let secondAt := second.atBound (numericLineBound lineCode) secondBound
  have firstContextEquality : firstAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        firstContextCode, frame.contextExact])
  have secondContextEquality : secondAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        secondContextCode, frame.contextExact])
  have firstProof : Derivation LogicMode.intuitionistic history.theory
      frame.context firstAt.conclusion := by
    rw [← firstContextEquality]
    exact firstAt.proof
  have secondProof : Derivation LogicMode.intuitionistic history.theory
      frame.context secondAt.conclusion := by
    rw [← secondContextEquality]
    exact secondAt.proof
  have builtCode :
      (ScopedFormula.conj firstAt.conclusion secondAt.conclusion).raw.code =
        numericLineConclusion lineCode := by
    simp only [ScopedFormula.conj, RawFormula.code]
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode,
      AcceptedNumericPrefix.at_conclusionCode, conclusionCode]
  have sameConclusion :
      ScopedFormula.conj firstAt.conclusion secondAt.conclusion =
        frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (builtCode.trans frame.conclusionExact.symm)
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [← sameConclusion]
    exact Derivation.conjunctionIntroduction firstProof secondProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule6_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 6)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have tagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have selectedCode := (natEqualBit_pos_iff _ _).mp f5.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have premiseTag : natUnpairLeft premiseAt.conclusion.raw.code.pred = 2 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact tagCode
  let view := premiseAt.conclusion.conjunctionViewOfTag premiseTag
  have premiseAtCode :
      premiseAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode reference) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have selectedIsLeft :
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
        view.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
          natUnpairLeft
            (natUnpairRight premiseAt.conclusion.raw.code.pred) := by
              rw [premiseAtCode]
      _ = view.left.raw.code := by
        exact view.leftCode
  have leftCode : view.left.raw.code = numericLineConclusion lineCode := by
    exact selectedIsLeft.symm.trans selectedCode.symm
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.conj view.left view.right) := by
    have contextEquality : premiseAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          contextCode, frame.contextExact])
    rw [← contextEquality, ← view.exact]
    exact premiseAt.proof
  have sameConclusion : view.left = frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (leftCode.trans frame.conclusionExact.symm)
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [← sameConclusion]
    exact Derivation.conjunctionEliminationLeft premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule7_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 7)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have tagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have selectedCode := (natEqualBit_pos_iff _ _).mp f5.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have premiseTag : natUnpairLeft premiseAt.conclusion.raw.code.pred = 2 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact tagCode
  let view := premiseAt.conclusion.conjunctionViewOfTag premiseTag
  have premiseAtCode :
      premiseAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode reference) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have selectedIsRight :
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
        view.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
          natUnpairRight
            (natUnpairRight premiseAt.conclusion.raw.code.pred) := by
              rw [premiseAtCode]
      _ = view.right.raw.code := by
        exact view.rightCode
  have rightCode : view.right.raw.code = numericLineConclusion lineCode := by
    exact selectedIsRight.symm.trans selectedCode.symm
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.conj view.left view.right) := by
    have contextEquality : premiseAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          contextCode, frame.contextExact])
    rw [← contextEquality, ← view.exact]
    exact premiseAt.proof
  have sameConclusion : view.right = frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (rightCode.trans frame.conclusionExact.symm)
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [← sameConclusion]
    exact Derivation.conjunctionEliminationRight premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule8_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 8)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have tagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have selectedCode := (natEqualBit_pos_iff _ _).mp f5.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    rw [AcceptedNumericPrefix.at_bound]
    exact boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 3 := by
    rw [frame.conclusionExact]
    exact tagCode
  let view := frame.conclusion.disjunctionViewOfTag currentTag
  have selectedIsLeft :
      natUnpairLeft
          (natUnpairRight (numericLineConclusion lineCode).pred) =
        view.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairLeft
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = view.left.raw.code := by
        exact view.leftCode
  have premiseCode : premiseAt.conclusion.raw.code = view.left.raw.code := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact selectedCode.trans selectedIsLeft
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context view.left := by
    have contextEquality : premiseAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          contextCode, frame.contextExact])
    have conclusionEquality : premiseAt.conclusion = view.left :=
      ScopedFormula.eq_of_code_eq premiseCode
    rw [← contextEquality, ← conclusionEquality]
    exact premiseAt.proof
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [view.exact]
    exact Derivation.disjunctionIntroductionLeft premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule9_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 9)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have tagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have selectedCode := (natEqualBit_pos_iff _ _).mp f5.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 3 := by
    rw [frame.conclusionExact]
    exact tagCode
  let view := frame.conclusion.disjunctionViewOfTag currentTag
  have selectedIsRight :
      natUnpairRight
          (natUnpairRight (numericLineConclusion lineCode).pred) =
        view.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairRight
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = view.right.raw.code := by
        exact view.rightCode
  have premiseCode : premiseAt.conclusion.raw.code = view.right.raw.code := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact selectedCode.trans selectedIsRight
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context view.right := by
    have contextEquality : premiseAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          contextCode, frame.contextExact])
    have conclusionEquality : premiseAt.conclusion = view.right :=
      ScopedFormula.eq_of_code_eq premiseCode
    rw [← contextEquality, ← conclusionEquality]
    exact premiseAt.proof
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [view.exact]
    exact Derivation.disjunctionIntroductionRight premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule3_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 3)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have tagCode := (natEqualBit_pos_iff _ _).mp f3.1
  have boundCode := (natEqualBit_pos_iff _ _).mp f4.1
  have contextCode := (natEqualBit_pos_iff _ _).mp f5.1
  have conclusionCode := (natEqualBit_pos_iff _ _).mp f6.1
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 4 := by
    rw [frame.conclusionExact]
    exact tagCode
  let view := frame.conclusion.implicationViewOfTag currentTag
  have premiseBound : premise.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have leftNumeric :
      natUnpairLeft (natUnpairRight (numericLineConclusion lineCode).pred) =
        view.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairLeft
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = view.left.raw.code := by
        exact view.leftCode
  have rightNumeric :
      natUnpairRight (natUnpairRight (numericLineConclusion lineCode).pred) =
        view.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairRight
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = view.right.raw.code := by
        exact view.rightCode
  have premiseContextCode : premiseAt.context.quote =
      (FormulaContext.cons view.left frame.context).quote := by
    rw [PackedHistoryDerivation.atBound_context_quote,
      AcceptedNumericPrefix.at_contextCode, contextCode]
    simp only [FormulaContext.quote]
    rw [leftNumeric, frame.contextExact, PRFunction.run_codedListCons]
  have premiseConclusionCode : premiseAt.conclusion.raw.code =
      view.right.raw.code := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode, conclusionCode, rightNumeric]
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      (FormulaContext.cons view.left frame.context) view.right := by
    have contextEquality :
        premiseAt.context = FormulaContext.cons view.left frame.context :=
      FormulaContext.eq_of_quote_eq premiseContextCode
    have conclusionEquality : premiseAt.conclusion = view.right :=
      ScopedFormula.eq_of_code_eq premiseConclusionCode
    rw [← contextEquality, ← conclusionEquality]
    exact premiseAt.proof
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [view.exact]
    exact Derivation.implicationIntroduction premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule12_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 12)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have tagCode := (natEqualBit_pos_iff _ _).mp f3.1
  have boundCode := (natEqualBit_pos_iff _ _).mp f4.1
  have contextCode := (natEqualBit_pos_iff _ _).mp f5.1
  have conclusionCode := (natEqualBit_pos_iff _ _).mp f6.1
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 5 := by
    rw [frame.conclusionExact]
    exact tagCode
  let view := frame.conclusion.universalViewOfTag currentTag
  have premiseBound : premise.bound = Nat.succ (numericLineBound lineCode) := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  have bodyNumeric :
      natUnpairRight (numericLineConclusion lineCode).pred =
        view.body.raw.code := by
    calc
      natUnpairRight (numericLineConclusion lineCode).pred =
          natUnpairRight frame.conclusion.raw.code.pred := by
            rw [frame.conclusionExact]
      _ = view.body.raw.code := by
        exact view.bodyCode
  have liftedContextCode : frame.context.lift.quote =
      premise.context.quote := by
    calc
      frame.context.lift.quote =
          PRFunction.raiseContextCode.run
            (NatVector.cons frame.context.quote
              (NatVector.cons 1 NatVector.nil)) :=
        (PRFunction.raiseContextCode_lift frame.context).symm
      _ = PRFunction.raiseContextCode.run
            (NatVector.cons (numericLineContext lineCode)
              (NatVector.cons 1 NatVector.nil)) := by
        rw [frame.contextExact]
      _ = numericLineContext
            (numericArchiveLine archiveCode reference) := by
        rw [PRFunction.run_raiseContextCode]
        exact contextCode.symm
      _ = premise.context.quote :=
        (AcceptedNumericPrefix.at_contextCode acceptedPrefix reference
          referenceEarlier).symm
  have premiseConclusionCode : premise.conclusion.raw.code =
      view.body.raw.code := by
    rw [AcceptedNumericPrefix.at_conclusionCode, conclusionCode,
      bodyNumeric]
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context.lift view.body := by
    apply premise.recoverFromCodes
    · exact premiseBound
    · exact liftedContextCode.symm
    · exact premiseConclusionCode
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [view.exact]
    exact Derivation.universalIntroduction premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule13_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 13)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  let termCode := codedListEntry (numericLineParameters lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have tagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have conclusionCode := (natEqualBit_pos_iff _ _).mp f6.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have premiseTag : natUnpairLeft premiseAt.conclusion.raw.code.pred = 5 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact tagCode
  let view := premiseAt.conclusion.universalViewOfTag premiseTag
  have termScoped : 0 < PRFunction.isScopedTermCode.run
      (NatVector.cons (numericLineBound lineCode)
        (NatVector.cons termCode NatVector.nil)) := by
    unfold termCode lineCode
    rw [PRFunction.run_isScopedTermCode,
      PRFunction.run_isScopedFormulaCode]
    exact f5.1
  let decodedTerm := PRFunction.decodeScopedTermCodePositive
    (numericLineBound lineCode) termCode termScoped
  let term := decodedTerm.term
  have termExact : term.raw.code = termCode := decodedTerm.codeExact
  have contextEquality : premiseAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        contextCode, frame.contextExact])
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.all view.body) := by
    rw [← contextEquality, ← view.exact]
    exact premiseAt.proof
  have premiseAtCode :
      premiseAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode reference) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have bodyPayload :
      natUnpairRight
          (numericLineConclusion
            (numericArchiveLine archiveCode reference)).pred =
        view.body.raw.code := by
    calc
      natUnpairRight
          (numericLineConclusion
            (numericArchiveLine archiveCode reference)).pred =
          natUnpairRight premiseAt.conclusion.raw.code.pred := by
            rw [premiseAtCode]
      _ = view.body.raw.code := by
        exact view.bodyCode
  have builtCode : (view.body.instantiate term).raw.code =
      numericLineConclusion lineCode := by
    unfold ScopedFormula.instantiate
    rw [← machineInstantiateTermCode_code, termExact,
      conclusionCode, bodyPayload]
  have sameConclusion : view.body.instantiate term = frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (builtCode.trans frame.conclusionExact.symm)
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [← sameConclusion]
    exact Derivation.universalElimination term premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule14_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 14)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  let termCode := codedListEntry (numericLineParameters lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have tagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have premiseConclusionCode := (natEqualBit_pos_iff _ _).mp f6.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 6 := by
    rw [frame.conclusionExact]
    exact tagCode
  let view := frame.conclusion.existentialViewOfTag currentTag
  have termScoped : 0 < PRFunction.isScopedTermCode.run
      (NatVector.cons (numericLineBound lineCode)
        (NatVector.cons termCode NatVector.nil)) := by
    unfold termCode lineCode
    rw [PRFunction.run_isScopedTermCode,
      PRFunction.run_isScopedFormulaCode]
    exact f5.1
  let decodedTerm := PRFunction.decodeScopedTermCodePositive
    (numericLineBound lineCode) termCode termScoped
  let term := decodedTerm.term
  have termExact : term.raw.code = termCode := decodedTerm.codeExact
  have bodyPayload :
      natUnpairRight (numericLineConclusion lineCode).pred =
        view.body.raw.code := by
    calc
      natUnpairRight (numericLineConclusion lineCode).pred =
          natUnpairRight frame.conclusion.raw.code.pred := by
            rw [frame.conclusionExact]
      _ = view.body.raw.code := by
        exact view.bodyCode
  have instantiatedCode : (view.body.instantiate term).raw.code =
      premiseAt.conclusion.raw.code := by
    unfold ScopedFormula.instantiate
    rw [← machineInstantiateTermCode_code, termExact,
      PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode,
      premiseConclusionCode, bodyPayload]
  have contextEquality : premiseAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        contextCode, frame.contextExact])
  have conclusionEquality :
      premiseAt.conclusion = view.body.instantiate term :=
    ScopedFormula.eq_of_code_eq instantiatedCode.symm
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (view.body.instantiate term) := by
    rw [← contextEquality, ← conclusionEquality]
    exact premiseAt.proof
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [view.exact]
    exact Derivation.existentialIntroduction term premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule17_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 17)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have sameFrame := (natAndBit_pos_iff _ _).mp f3.1
  have sameFrameTail := (natAndBit_pos_iff _ _).mp sameFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  have f7 := (natAndBit_pos_iff _ _).mp f6.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp sameFrame.1
  have contextCode := (natEqualBit_pos_iff _ _).mp sameFrameTail.1
  have premiseTagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have currentTagCode := (natEqualBit_pos_iff _ _).mp f5.1
  have leftRightCode := (natEqualBit_pos_iff _ _).mp f6.1
  have rightLeftCode := (natEqualBit_pos_iff _ _).mp f7.1
  have premiseBound : premise.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound (numericLineBound lineCode) premiseBound
  have premiseTag : natUnpairLeft premiseAt.conclusion.raw.code.pred = 1 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact premiseTagCode
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 1 := by
    rw [frame.conclusionExact]
    exact currentTagCode
  let premiseView := premiseAt.conclusion.equalityViewOfTag premiseTag
  let currentView := frame.conclusion.equalityViewOfTag currentTag
  have currentLeftCode :
      natUnpairLeft (natUnpairRight (numericLineConclusion lineCode).pred) =
        currentView.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairLeft
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = currentView.left.raw.code := by
        exact currentView.leftCode
  have currentRightCode :
      natUnpairRight (natUnpairRight (numericLineConclusion lineCode).pred) =
        currentView.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairRight
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = currentView.right.raw.code := by
        exact currentView.rightCode
  have premiseAtCode :
      premiseAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode reference) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have premiseLeftCode :
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
        premiseView.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
          natUnpairLeft
            (natUnpairRight premiseAt.conclusion.raw.code.pred) := by
              rw [premiseAtCode]
      _ = premiseView.left.raw.code := by
        exact premiseView.leftCode
  have premiseRightCode :
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
        premiseView.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode reference)).pred) =
          natUnpairRight
            (natUnpairRight premiseAt.conclusion.raw.code.pred) := by
              rw [premiseAtCode]
      _ = premiseView.right.raw.code := by
        exact premiseView.rightCode
  have leftRaw : currentView.left.raw = premiseView.right.raw :=
    RawTerm.code_injective
      (currentLeftCode.symm.trans
        (leftRightCode.trans premiseRightCode))
  have rightRaw : currentView.right.raw = premiseView.left.raw :=
    RawTerm.code_injective
      (currentRightCode.symm.trans
        (rightLeftCode.trans premiseLeftCode))
  have leftExact : currentView.left = premiseView.right :=
    ScopedTerm.eq_of_raw_eq leftRaw
  have rightExact : currentView.right = premiseView.left :=
    ScopedTerm.eq_of_raw_eq rightRaw
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.equal premiseView.left premiseView.right) := by
    have contextEquality : premiseAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          contextCode, frame.contextExact])
    rw [← contextEquality, ← premiseView.exact]
    exact premiseAt.proof
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [currentView.exact, leftExact, rightExact]
    exact Derivation.equalitySymmetry premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule21_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 21)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have chronology := (natAndBit_pos_iff _ _).mp f1.1
  have chronologyTail := (natAndBit_pos_iff _ _).mp chronology.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let reference := codedListEntry (numericLinePremises lineCode) 0
  let termCode := codedListEntry (numericLineParameters lineCode) 0
  have referenceEarlier : reference < lineIndex :=
    (natLessBit_pos_iff _ _).mp chronologyTail.1
  let premise := acceptedPrefix.at reference referenceEarlier
  have boundCode := (natEqualBit_pos_iff _ _).mp f3.1
  have contextCode := (natEqualBit_pos_iff _ _).mp f5.1
  have conclusionCode := (natEqualBit_pos_iff _ _).mp f6.1
  have premiseBound : premise.bound = Nat.succ (numericLineBound lineCode) := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix reference
      referenceEarlier).trans boundCode
  let premiseAt := premise.atBound
    (Nat.succ (numericLineBound lineCode)) premiseBound
  have termScoped : 0 < PRFunction.isScopedTermCode.run
      (NatVector.cons (numericLineBound lineCode)
        (NatVector.cons termCode NatVector.nil)) := by
    unfold termCode lineCode
    rw [PRFunction.run_isScopedTermCode,
      PRFunction.run_isScopedFormulaCode]
    exact f4.1
  let decodedTerm := PRFunction.decodeScopedTermCodePositive
    (numericLineBound lineCode) termCode termScoped
  let term := decodedTerm.term
  have termExact : term.raw.code = termCode := decodedTerm.codeExact
  let instantiatedContext := premiseAt.context.instantiate term
  let instantiatedConclusion := premiseAt.conclusion.instantiate term
  have instantiatedContextCode : instantiatedContext.quote =
      numericLineContext lineCode := by
    unfold instantiatedContext
    rw [← PRFunction.instantiateContextTermCode_code,
      PackedHistoryDerivation.atBound_context_quote,
      AcceptedNumericPrefix.at_contextCode, termExact,
      PRFunction.run_instantiateContextTermCode, contextCode]
  have instantiatedConclusionCode : instantiatedConclusion.raw.code =
      numericLineConclusion lineCode := by
    unfold instantiatedConclusion ScopedFormula.instantiate
    rw [← machineInstantiateTermCode_code,
      PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode, termExact,
      conclusionCode]
  have contextEquality : instantiatedContext = frame.context :=
    FormulaContext.eq_of_quote_eq
      (instantiatedContextCode.trans frame.contextExact.symm)
  have conclusionEquality :
      instantiatedConclusion = frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (instantiatedConclusionCode.trans frame.conclusionExact.symm)
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [← contextEquality, ← conclusionEquality]
    exact Derivation.freeInstantiation term premiseAt.proof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule15_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 15)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have c1 := (natAndBit_pos_iff _ _).mp f1.1
  have c2 := (natAndBit_pos_iff _ _).mp c1.2
  have c3 := (natAndBit_pos_iff _ _).mp c2.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have firstFrame := (natAndBit_pos_iff _ _).mp f3.1
  have firstFrameTail := (natAndBit_pos_iff _ _).mp firstFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  have f7 := (natAndBit_pos_iff _ _).mp f6.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let firstRef := codedListEntry premises 0
  let secondRef := codedListEntry premises 1
  have firstEarlier : firstRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c2.1
  have secondEarlier : secondRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c3.1
  let first := acceptedPrefix.at firstRef firstEarlier
  let second := acceptedPrefix.at secondRef secondEarlier
  have firstBoundCode := (natEqualBit_pos_iff _ _).mp firstFrame.1
  have firstContextCode := (natEqualBit_pos_iff _ _).mp firstFrameTail.1
  have firstTagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have secondBoundCode := (natEqualBit_pos_iff _ _).mp f5.1
  have secondContextCode := (natEqualBit_pos_iff _ _).mp f6.1
  have secondConclusionCode := (natEqualBit_pos_iff _ _).mp f7.1
  have firstBound : first.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix firstRef
      firstEarlier).trans firstBoundCode
  let firstAt := first.atBound (numericLineBound lineCode) firstBound
  have firstTag : natUnpairLeft firstAt.conclusion.raw.code.pred = 6 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact firstTagCode
  let view := firstAt.conclusion.existentialViewOfTag firstTag
  have firstProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.ex view.body) := by
    have contextEquality : firstAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          firstContextCode, frame.contextExact])
    rw [← contextEquality, ← view.exact]
    exact firstAt.proof
  have secondBound :
      second.bound = Nat.succ (numericLineBound lineCode) := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix secondRef
      secondEarlier).trans secondBoundCode
  have firstAtCode :
      firstAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode firstRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have bodyNumeric :
      natUnpairRight
          (numericLineConclusion
            (numericArchiveLine archiveCode firstRef)).pred =
        view.body.raw.code := by
    calc
      natUnpairRight
          (numericLineConclusion
            (numericArchiveLine archiveCode firstRef)).pred =
          natUnpairRight firstAt.conclusion.raw.code.pred := by
            rw [firstAtCode]
      _ = view.body.raw.code := by
        exact view.bodyCode
  have branchContextCode :
      (FormulaContext.cons view.body frame.context.lift).quote =
        second.context.quote := by
    rw [AcceptedNumericPrefix.at_contextCode, secondContextCode]
    simp only [FormulaContext.quote]
    rw [bodyNumeric, PRFunction.run_codedListCons,
      ← PRFunction.raiseContextCode_lift frame.context,
      PRFunction.run_raiseContextCode, frame.contextExact]
  have branchConclusionCode : frame.conclusion.lift.raw.code =
      second.conclusion.raw.code := by
    calc
      frame.conclusion.lift.raw.code =
          PRFunction.raiseFormulaCode.run
            (NatVector.cons frame.conclusion.raw.code
              (NatVector.cons 1 NatVector.nil)) :=
        ScopedFormula.lift_code frame.conclusion
      _ = machineRaiseFormulaCode
            (numericLineConclusion lineCode) 1 := by
        rw [PRFunction.run_raiseFormulaCode, frame.conclusionExact]
      _ = numericLineConclusion
            (numericArchiveLine archiveCode secondRef) :=
        secondConclusionCode.symm
      _ = second.conclusion.raw.code :=
        (AcceptedNumericPrefix.at_conclusionCode acceptedPrefix secondRef
          secondEarlier).symm
  have secondProof : Derivation LogicMode.intuitionistic history.theory
      (FormulaContext.cons view.body frame.context.lift)
      frame.conclusion.lift := by
    apply second.recoverFromCodes
    · exact secondBound
    · exact branchContextCode.symm
    · exact branchConclusionCode.symm
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := Derivation.existentialElimination firstProof secondProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule18_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 18)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have c1 := (natAndBit_pos_iff _ _).mp f1.1
  have c2 := (natAndBit_pos_iff _ _).mp c1.2
  have c3 := (natAndBit_pos_iff _ _).mp c2.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have firstFrame := (natAndBit_pos_iff _ _).mp f3.1
  have firstFrameTail := (natAndBit_pos_iff _ _).mp firstFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have secondFrame := (natAndBit_pos_iff _ _).mp f4.1
  have secondFrameTail := (natAndBit_pos_iff _ _).mp secondFrame.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  have f7 := (natAndBit_pos_iff _ _).mp f6.2
  have f8 := (natAndBit_pos_iff _ _).mp f7.2
  have f9 := (natAndBit_pos_iff _ _).mp f8.2
  have f10 := (natAndBit_pos_iff _ _).mp f9.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let firstRef := codedListEntry premises 0
  let secondRef := codedListEntry premises 1
  have firstEarlier : firstRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c2.1
  have secondEarlier : secondRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c3.1
  let first := acceptedPrefix.at firstRef firstEarlier
  let second := acceptedPrefix.at secondRef secondEarlier
  have firstBoundCode := (natEqualBit_pos_iff _ _).mp firstFrame.1
  have firstContextCode := (natEqualBit_pos_iff _ _).mp firstFrameTail.1
  have secondBoundCode := (natEqualBit_pos_iff _ _).mp secondFrame.1
  have secondContextCode := (natEqualBit_pos_iff _ _).mp secondFrameTail.1
  have firstTagCode := (natEqualBit_pos_iff _ _).mp f5.1
  have secondTagCode := (natEqualBit_pos_iff _ _).mp f6.1
  have currentTagCode := (natEqualBit_pos_iff _ _).mp f7.1
  have middleCode := (natEqualBit_pos_iff _ _).mp f8.1
  have currentLeftCode := (natEqualBit_pos_iff _ _).mp f9.1
  have currentRightCode := (natEqualBit_pos_iff _ _).mp f10.1
  have firstBound : first.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix firstRef
      firstEarlier).trans firstBoundCode
  have secondBound : second.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix secondRef
      secondEarlier).trans secondBoundCode
  let firstAt := first.atBound (numericLineBound lineCode) firstBound
  let secondAt := second.atBound (numericLineBound lineCode) secondBound
  have firstTag : natUnpairLeft firstAt.conclusion.raw.code.pred = 1 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact firstTagCode
  have secondTag : natUnpairLeft secondAt.conclusion.raw.code.pred = 1 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact secondTagCode
  have currentTag : natUnpairLeft frame.conclusion.raw.code.pred = 1 := by
    rw [frame.conclusionExact]
    exact currentTagCode
  let firstView := firstAt.conclusion.equalityViewOfTag firstTag
  let secondView := secondAt.conclusion.equalityViewOfTag secondTag
  let currentView := frame.conclusion.equalityViewOfTag currentTag
  have firstContextEquality : firstAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        firstContextCode, frame.contextExact])
  have secondContextEquality : secondAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        secondContextCode, frame.contextExact])
  have firstProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.equal firstView.left firstView.right) := by
    rw [← firstContextEquality, ← firstView.exact]
    exact firstAt.proof
  have firstAtCode :
      firstAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode firstRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have secondAtCode :
      secondAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode secondRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have firstRightNumeric :
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
        firstView.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
          natUnpairRight
            (natUnpairRight firstAt.conclusion.raw.code.pred) := by
              rw [firstAtCode]
      _ = firstView.right.raw.code := by
        exact firstView.rightCode
  have secondLeftNumeric :
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode secondRef)).pred) =
        secondView.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode secondRef)).pred) =
          natUnpairLeft
            (natUnpairRight secondAt.conclusion.raw.code.pred) := by
              rw [secondAtCode]
      _ = secondView.left.raw.code := by
        exact secondView.leftCode
  have middleRaw : firstView.right.raw = secondView.left.raw :=
    RawTerm.code_injective
      (firstRightNumeric.symm.trans
        (middleCode.trans secondLeftNumeric))
  have middleExact : firstView.right = secondView.left :=
    ScopedTerm.eq_of_raw_eq middleRaw
  have secondProofRaw : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.equal secondView.left secondView.right) := by
    rw [← secondContextEquality, ← secondView.exact]
    exact secondAt.proof
  have secondProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.equal firstView.right secondView.right) := by
    rw [middleExact]
    exact secondProofRaw
  have currentLeftNumeric :
      natUnpairLeft (natUnpairRight (numericLineConclusion lineCode).pred) =
        currentView.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairLeft
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = currentView.left.raw.code := by
        exact currentView.leftCode
  have currentRightNumeric :
      natUnpairRight (natUnpairRight (numericLineConclusion lineCode).pred) =
        currentView.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight (numericLineConclusion lineCode).pred) =
          natUnpairRight
            (natUnpairRight frame.conclusion.raw.code.pred) := by
              rw [frame.conclusionExact]
      _ = currentView.right.raw.code := by
        exact currentView.rightCode
  have firstLeftNumeric :
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
        firstView.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
          natUnpairLeft
            (natUnpairRight firstAt.conclusion.raw.code.pred) := by
              rw [firstAtCode]
      _ = firstView.left.raw.code := by
        exact firstView.leftCode
  have secondRightNumeric :
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode secondRef)).pred) =
        secondView.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode secondRef)).pred) =
          natUnpairRight
            (natUnpairRight secondAt.conclusion.raw.code.pred) := by
              rw [secondAtCode]
      _ = secondView.right.raw.code := by
        exact secondView.rightCode
  have currentLeftRaw : currentView.left.raw = firstView.left.raw :=
    RawTerm.code_injective
      (currentLeftNumeric.symm.trans
        (currentLeftCode.trans firstLeftNumeric))
  have currentRightRaw : currentView.right.raw = secondView.right.raw :=
    RawTerm.code_injective
      (currentRightNumeric.symm.trans
        (currentRightCode.trans secondRightNumeric))
  have currentLeftExact : currentView.left = firstView.left :=
    ScopedTerm.eq_of_raw_eq currentLeftRaw
  have currentRightExact : currentView.right = secondView.right :=
    ScopedTerm.eq_of_raw_eq currentRightRaw
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [currentView.exact, currentLeftExact, currentRightExact]
    exact Derivation.equalityTransitivity firstProof secondProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule19_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 19)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have c1 := (natAndBit_pos_iff _ _).mp f1.1
  have c2 := (natAndBit_pos_iff _ _).mp c1.2
  have c3 := (natAndBit_pos_iff _ _).mp c2.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have firstFrame := (natAndBit_pos_iff _ _).mp f3.1
  have firstFrameTail := (natAndBit_pos_iff _ _).mp firstFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have secondFrame := (natAndBit_pos_iff _ _).mp f4.1
  have secondFrameTail := (natAndBit_pos_iff _ _).mp secondFrame.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  have f7 := (natAndBit_pos_iff _ _).mp f6.2
  have f8 := (natAndBit_pos_iff _ _).mp f7.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let firstRef := codedListEntry premises 0
  let secondRef := codedListEntry premises 1
  let bodyCode := codedListEntry (numericLineParameters lineCode) 0
  have firstEarlier : firstRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c2.1
  have secondEarlier : secondRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c3.1
  let first := acceptedPrefix.at firstRef firstEarlier
  let second := acceptedPrefix.at secondRef secondEarlier
  have firstBoundCode := (natEqualBit_pos_iff _ _).mp firstFrame.1
  have firstContextCode := (natEqualBit_pos_iff _ _).mp firstFrameTail.1
  have secondBoundCode := (natEqualBit_pos_iff _ _).mp secondFrame.1
  have secondContextCode := (natEqualBit_pos_iff _ _).mp secondFrameTail.1
  have firstTagCode := (natEqualBit_pos_iff _ _).mp f5.1
  have secondConclusionCode := (natEqualBit_pos_iff _ _).mp f7.1
  have currentConclusionCode := (natEqualBit_pos_iff _ _).mp f8.1
  have firstBound : first.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix firstRef
      firstEarlier).trans firstBoundCode
  have secondBound : second.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix secondRef
      secondEarlier).trans secondBoundCode
  let firstAt := first.atBound (numericLineBound lineCode) firstBound
  let secondAt := second.atBound (numericLineBound lineCode) secondBound
  have firstTag : natUnpairLeft firstAt.conclusion.raw.code.pred = 1 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact firstTagCode
  let equality := firstAt.conclusion.equalityViewOfTag firstTag
  have bodyScoped : 0 < PRFunction.isScopedFormulaCode.run
      (NatVector.cons (Nat.succ (numericLineBound lineCode))
        (NatVector.cons bodyCode NatVector.nil)) := by
    unfold bodyCode lineCode
    rw [PRFunction.run_isScopedFormulaCode]
    exact f6.1
  let decodedBody := PRFunction.decodeScopedFormulaCodePositive
    (Nat.succ (numericLineBound lineCode)) bodyCode bodyScoped
  let body := decodedBody.formula
  have bodyExact : body.raw.code = bodyCode := decodedBody.codeExact
  have firstContextEquality : firstAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        firstContextCode, frame.contextExact])
  have secondContextEquality : secondAt.context = frame.context :=
    FormulaContext.eq_of_quote_eq (by
      rw [PackedHistoryDerivation.atBound_context_quote,
        AcceptedNumericPrefix.at_contextCode,
        secondContextCode, frame.contextExact])
  have equalityProof : Derivation LogicMode.intuitionistic history.theory
      frame.context
      (ScopedFormula.equal equality.left equality.right) := by
    rw [← firstContextEquality, ← equality.exact]
    exact firstAt.proof
  have firstAtCode :
      firstAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode firstRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have equalityLeftNumeric :
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
        equality.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
          natUnpairLeft
            (natUnpairRight firstAt.conclusion.raw.code.pred) := by
              rw [firstAtCode]
      _ = equality.left.raw.code := by
        exact equality.leftCode
  have equalityRightNumeric :
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
        equality.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
          natUnpairRight
            (natUnpairRight firstAt.conclusion.raw.code.pred) := by
              rw [firstAtCode]
      _ = equality.right.raw.code := by
        exact equality.rightCode
  have leftInstanceCode : (body.instantiate equality.left).raw.code =
      secondAt.conclusion.raw.code := by
    unfold ScopedFormula.instantiate
    rw [← machineInstantiateTermCode_code,
      bodyExact, PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode,
      secondConclusionCode, equalityLeftNumeric]
  have leftInstanceEquality :
      secondAt.conclusion = body.instantiate equality.left :=
    ScopedFormula.eq_of_code_eq leftInstanceCode.symm
  have premiseProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (body.instantiate equality.left) := by
    rw [← secondContextEquality, ← leftInstanceEquality]
    exact secondAt.proof
  have rightInstanceCode :
      (body.instantiate equality.right).raw.code =
        numericLineConclusion lineCode := by
    unfold ScopedFormula.instantiate
    rw [← machineInstantiateTermCode_code, bodyExact,
      currentConclusionCode, equalityRightNumeric]
  have sameConclusion :
      body.instantiate equality.right = frame.conclusion :=
    ScopedFormula.eq_of_code_eq
      (rightInstanceCode.trans frame.conclusionExact.symm)
  have builtProof : Derivation LogicMode.intuitionistic history.theory
      frame.context frame.conclusion := by
    rw [← sameConclusion]
    exact Derivation.equalitySubstitution body
      equalityProof premiseProof
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := builtProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def checkProofLine_rule10_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (ruleExact : numericLineRule
      (numericArchiveLine archiveCode lineIndex) = 10)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let frame := checkProofLine_positive_decodes_frame
    history.quote archiveCode lineIndex accepted
  have rulePart := checkProofLine_selected_body_positive _
    history archiveCode lineIndex ruleExact accepted
  normalize_line_program at rulePart
  have f1 := (natAndBit_pos_iff _ _).mp rulePart
  have f2 := (natAndBit_pos_iff _ _).mp f1.2
  have c1 := (natAndBit_pos_iff _ _).mp f1.1
  have c2 := (natAndBit_pos_iff _ _).mp c1.2
  have c3 := (natAndBit_pos_iff _ _).mp c2.2
  have c4 := (natAndBit_pos_iff _ _).mp c3.2
  have f3 := (natAndBit_pos_iff _ _).mp f2.2
  have firstFrame := (natAndBit_pos_iff _ _).mp f3.1
  have firstFrameTail := (natAndBit_pos_iff _ _).mp firstFrame.2
  have f4 := (natAndBit_pos_iff _ _).mp f3.2
  have f5 := (natAndBit_pos_iff _ _).mp f4.2
  have f6 := (natAndBit_pos_iff _ _).mp f5.2
  have f7 := (natAndBit_pos_iff _ _).mp f6.2
  have f8 := (natAndBit_pos_iff _ _).mp f7.2
  have f9 := (natAndBit_pos_iff _ _).mp f8.2
  have f10 := (natAndBit_pos_iff _ _).mp f9.2
  let lineCode := numericArchiveLine archiveCode lineIndex
  let premises := numericLinePremises lineCode
  let firstRef := codedListEntry premises 0
  let secondRef := codedListEntry premises 1
  let thirdRef := codedListEntry premises 2
  have firstEarlier : firstRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c2.1
  have secondEarlier : secondRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c3.1
  have thirdEarlier : thirdRef < lineIndex :=
    (natLessBit_pos_iff _ _).mp c4.1
  let first := acceptedPrefix.at firstRef firstEarlier
  let second := acceptedPrefix.at secondRef secondEarlier
  let third := acceptedPrefix.at thirdRef thirdEarlier
  have firstBoundCode := (natEqualBit_pos_iff _ _).mp firstFrame.1
  have firstContextCode := (natEqualBit_pos_iff _ _).mp firstFrameTail.1
  have firstTagCode := (natEqualBit_pos_iff _ _).mp f4.1
  have secondBoundCode := (natEqualBit_pos_iff _ _).mp f5.1
  have thirdBoundCode := (natEqualBit_pos_iff _ _).mp f6.1
  have secondContextCode := (natEqualBit_pos_iff _ _).mp f7.1
  have thirdContextCode := (natEqualBit_pos_iff _ _).mp f8.1
  have secondConclusionCode := (natEqualBit_pos_iff _ _).mp f9.1
  have thirdConclusionCode := (natEqualBit_pos_iff _ _).mp f10.1
  have firstBound : first.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix firstRef
      firstEarlier).trans firstBoundCode
  have secondBound : second.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix secondRef
      secondEarlier).trans secondBoundCode
  have thirdBound : third.bound = numericLineBound lineCode := by
    exact (AcceptedNumericPrefix.at_bound acceptedPrefix thirdRef
      thirdEarlier).trans thirdBoundCode
  let firstAt := first.atBound (numericLineBound lineCode) firstBound
  have firstTag : natUnpairLeft firstAt.conclusion.raw.code.pred = 3 := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
    exact firstTagCode
  let view := firstAt.conclusion.disjunctionViewOfTag firstTag
  have firstProof : Derivation LogicMode.intuitionistic history.theory
      frame.context (ScopedFormula.disj view.left view.right) := by
    have contextEquality : firstAt.context = frame.context :=
      FormulaContext.eq_of_quote_eq (by
        rw [PackedHistoryDerivation.atBound_context_quote,
          AcceptedNumericPrefix.at_contextCode,
          firstContextCode, frame.contextExact])
    rw [← contextEquality, ← view.exact]
    exact firstAt.proof
  have firstAtCode :
      firstAt.conclusion.raw.code =
        numericLineConclusion (numericArchiveLine archiveCode firstRef) := by
    rw [PackedHistoryDerivation.atBound_conclusion_code,
      AcceptedNumericPrefix.at_conclusionCode]
  have leftNumeric :
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
        view.left.raw.code := by
    calc
      natUnpairLeft
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
          natUnpairLeft
            (natUnpairRight firstAt.conclusion.raw.code.pred) := by
              rw [firstAtCode]
      _ = view.left.raw.code := by
        exact view.leftCode
  have rightNumeric :
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
        view.right.raw.code := by
    calc
      natUnpairRight
          (natUnpairRight
            (numericLineConclusion
              (numericArchiveLine archiveCode firstRef)).pred) =
          natUnpairRight
            (natUnpairRight firstAt.conclusion.raw.code.pred) := by
              rw [firstAtCode]
      _ = view.right.raw.code := by
        exact view.rightCode
  have secondContextExact :
      second.context.quote =
        (FormulaContext.cons view.left frame.context).quote := by
    rw [AcceptedNumericPrefix.at_contextCode, secondContextCode]
    simp only [FormulaContext.quote]
    rw [leftNumeric, frame.contextExact, PRFunction.run_codedListCons]
  have thirdContextExact :
      third.context.quote =
        (FormulaContext.cons view.right frame.context).quote := by
    rw [AcceptedNumericPrefix.at_contextCode, thirdContextCode]
    simp only [FormulaContext.quote]
    rw [rightNumeric, frame.contextExact, PRFunction.run_codedListCons]
  have secondProof : Derivation LogicMode.intuitionistic history.theory
      (FormulaContext.cons view.left frame.context) frame.conclusion := by
    apply second.recoverFromCodes
    · exact secondBound
    · exact secondContextExact
    · rw [AcceptedNumericPrefix.at_conclusionCode,
        secondConclusionCode, frame.conclusionExact]
  have thirdProof : Derivation LogicMode.intuitionistic history.theory
      (FormulaContext.cons view.right frame.context) frame.conclusion := by
    apply third.recoverFromCodes
    · exact thirdBound
    · exact thirdContextExact
    · rw [AcceptedNumericPrefix.at_conclusionCode,
        thirdConclusionCode, frame.conclusionExact]
  let packed : PackedHistoryDerivation history :=
    { bound := numericLineBound lineCode
      context := frame.context
      conclusion := frame.conclusion
      proof := Derivation.disjunctionElimination
        firstProof secondProof thirdProof }
  exact
    { packed := packed
      boundExact := rfl
      contextExact := frame.contextExact
      conclusionExact := frame.conclusionExact }

def ExcludesNat (value : Nat) : List Nat -> Prop
  | [] => True
  | head :: tail => Not (value = head) ∧ ExcludesNat value tail

theorem ExcludesNat.notMem
    {value : Nat}
    {values : List Nat}
    (excluded : ExcludesNat value values) :
    Not (value ∈ values) := by
  intro member
  induction values with
  | nil =>
      cases member
  | cons head tail inductionHypothesis =>
      cases excluded with
      | intro headExcluded tailExcluded =>
          cases member with
          | head => exact headExcluded rfl
          | tail _ tailMember =>
              exact inductionHypothesis tailExcluded tailMember

def checkProofLine_positive_reconstruct
    (history : TheoryHistory)
    (archiveCode lineIndex : Nat)
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineIndex)
    (accepted : 0 < numericCheckProofLine history.quote archiveCode lineIndex) :
    ReconstructedNumericLine history archiveCode lineIndex := by
  let rule := numericLineRule (numericArchiveLine archiveCode lineIndex)
  by_cases rule0 : rule = 0
  · exact checkProofLine_rule0_reconstruct history archiveCode lineIndex
      rule0 accepted
  by_cases rule1 : rule = 1
  · exact checkProofLine_rule1_reconstruct history archiveCode lineIndex
      rule1 accepted
  by_cases rule2 : rule = 2
  · exact checkProofLine_rule2_reconstruct history archiveCode lineIndex
      acceptedPrefix rule2 accepted
  by_cases rule3 : rule = 3
  · exact checkProofLine_rule3_reconstruct history archiveCode lineIndex
      acceptedPrefix rule3 accepted
  by_cases rule4 : rule = 4
  · exact checkProofLine_rule4_reconstruct history archiveCode lineIndex
      acceptedPrefix rule4 accepted
  by_cases rule5 : rule = 5
  · exact checkProofLine_rule5_reconstruct history archiveCode lineIndex
      acceptedPrefix rule5 accepted
  by_cases rule6 : rule = 6
  · exact checkProofLine_rule6_reconstruct history archiveCode lineIndex
      acceptedPrefix rule6 accepted
  by_cases rule7 : rule = 7
  · exact checkProofLine_rule7_reconstruct history archiveCode lineIndex
      acceptedPrefix rule7 accepted
  by_cases rule8 : rule = 8
  · exact checkProofLine_rule8_reconstruct history archiveCode lineIndex
      acceptedPrefix rule8 accepted
  by_cases rule9 : rule = 9
  · exact checkProofLine_rule9_reconstruct history archiveCode lineIndex
      acceptedPrefix rule9 accepted
  by_cases rule10 : rule = 10
  · exact checkProofLine_rule10_reconstruct history archiveCode lineIndex
      acceptedPrefix rule10 accepted
  by_cases rule11 : rule = 11
  · exact checkProofLine_rule11_reconstruct history archiveCode lineIndex
      acceptedPrefix rule11 accepted
  by_cases rule12 : rule = 12
  · exact checkProofLine_rule12_reconstruct history archiveCode lineIndex
      acceptedPrefix rule12 accepted
  by_cases rule13 : rule = 13
  · exact checkProofLine_rule13_reconstruct history archiveCode lineIndex
      acceptedPrefix rule13 accepted
  by_cases rule14 : rule = 14
  · exact checkProofLine_rule14_reconstruct history archiveCode lineIndex
      acceptedPrefix rule14 accepted
  by_cases rule15 : rule = 15
  · exact checkProofLine_rule15_reconstruct history archiveCode lineIndex
      acceptedPrefix rule15 accepted
  by_cases rule16 : rule = 16
  · exact checkProofLine_rule16_reconstruct history archiveCode lineIndex
      rule16 accepted
  by_cases rule17 : rule = 17
  · exact checkProofLine_rule17_reconstruct history archiveCode lineIndex
      acceptedPrefix rule17 accepted
  by_cases rule18 : rule = 18
  · exact checkProofLine_rule18_reconstruct history archiveCode lineIndex
      acceptedPrefix rule18 accepted
  by_cases rule19 : rule = 19
  · exact checkProofLine_rule19_reconstruct history archiveCode lineIndex
      acceptedPrefix rule19 accepted
  by_cases rule20 : rule = 20
  · exact checkProofLine_rule20_reconstruct history archiveCode lineIndex
      acceptedPrefix rule20 accepted
  by_cases rule21 : rule = 21
  · exact checkProofLine_rule21_reconstruct history archiveCode lineIndex
      acceptedPrefix rule21 accepted
  have fullPositive := accepted
  unfold numericCheckProofLine PRFunction.checkProofLine at fullPositive
  rw [PRFunction.run_conjoin] at fullPositive
  have rulePart := (natAndBit_pos_iff _ _).mp fullPositive |>.2
  change 0 < PRFunction.checkProofLineRules.run
    (proofCheckInputs history.quote archiveCode lineIndex) at rulePart
  have alternatives :=
    (PRFunction.checkProofLineRules_positive_iff
      history.quote archiveCode lineIndex).mp rulePart
  have tagMem := proofCheckRuleAlternatives_tag_mem
    history.quote archiveCode lineIndex
    intuitionisticProofRuleTags
    alternatives
  have tagExact : proofCheckRuleValue archiveCode lineIndex = rule := by
    unfold proofCheckRuleValue rule numericLineRule numericArchiveLine
    rfl
  rw [tagExact] at tagMem
  have excluded : ExcludesNat rule intuitionisticProofRuleTags := by
    unfold intuitionisticProofRuleTags intuitionisticRuleTags
    exact
      ⟨rule21, rule20, rule19, rule18, rule17, rule16, rule15, rule14,
        rule13, rule12, rule11, rule10, rule9, rule8, rule7, rule6,
        rule5, rule4, rule3, rule2, rule1, rule0, True.intro⟩
  exact (excluded.notMem tagMem).elim

/-! ## From accepted numeric folds to typed chronological prefixes -/

theorem proofCheckFold_positive_initial
    (lineCount accepted historyCode archiveCode : Nat)
    (positive : 0 <
      proofCheckFold lineCount accepted historyCode archiveCode) :
    0 < accepted := by
  induction lineCount generalizing accepted with
  | zero => exact positive
  | succ lineCount inductionHypothesis =>
      exact inductionHypothesis _
        ((natAndBit_pos_iff _ _).mp positive).1

theorem proofCheckFold_positive_line
    (lineCount accepted historyCode archiveCode lineIndex : Nat)
    (positive : 0 <
      proofCheckFold lineCount accepted historyCode archiveCode)
    (bounded : lineIndex < lineCount) :
    0 < numericCheckProofLine historyCode archiveCode lineIndex := by
  induction lineCount generalizing accepted with
  | zero => exact (Nat.not_lt_zero lineIndex bounded).elim
  | succ lineCount inductionHypothesis =>
      have parts := (natAndBit_pos_iff _ _).mp positive
      have recursivePositive : 0 <
          proofCheckFold lineCount accepted historyCode archiveCode :=
        parts.1
      have currentPositive :
          0 < numericCheckProofLine historyCode archiveCode lineCount :=
        by
          unfold numericCheckProofLine
          exact parts.2
      by_cases earlier : lineIndex < lineCount
      · exact inductionHypothesis _ recursivePositive earlier
      · have same : lineIndex = lineCount :=
          Nat.eq_of_lt_succ_of_not_lt bounded earlier
        subst lineIndex
        exact currentPositive

def AcceptedNumericPrefix.empty
    (history : TheoryHistory)
    (archiveCode : Nat) :
    AcceptedNumericPrefix history archiveCode 0 :=
  { proofAt := fun index bounded =>
      (Nat.not_lt_zero index bounded).elim
    boundAligned := fun index bounded =>
      (Nat.not_lt_zero index bounded).elim
    contextAligned := fun index bounded =>
      (Nat.not_lt_zero index bounded).elim
    conclusionAligned := fun index bounded =>
      (Nat.not_lt_zero index bounded).elim }

def AcceptedNumericPrefix.extend
    {history : TheoryHistory}
    {archiveCode lineCount : Nat}
    (acceptedPrefix : AcceptedNumericPrefix history archiveCode lineCount)
    (current : ReconstructedNumericLine history archiveCode lineCount) :
    AcceptedNumericPrefix history archiveCode (Nat.succ lineCount) := by
  let proofAt : forall index, index < Nat.succ lineCount ->
      PackedHistoryDerivation history := fun index bounded =>
    if earlier : index < lineCount then
      acceptedPrefix.at index earlier
    else
      current.packed
  have proofAt_earlier :
      forall index (bounded : index < Nat.succ lineCount)
        (earlier : index < lineCount),
        proofAt index bounded = acceptedPrefix.at index earlier := by
    intro index bounded earlier
    unfold proofAt
    rw [dif_pos earlier]
  have proofAt_current :
      forall index (bounded : index < Nat.succ lineCount)
        (notEarlier : Not (index < lineCount)),
        proofAt index bounded = current.packed := by
    intro index bounded notEarlier
    unfold proofAt
    rw [dif_neg notEarlier]
  refine
    { proofAt := proofAt
      boundAligned := ?_
      contextAligned := ?_
      conclusionAligned := ?_ }
  · intro index bounded
    by_cases earlier : index < lineCount
    · rw [proofAt_earlier index bounded earlier]
      exact acceptedPrefix.at_bound index earlier
    · rw [proofAt_current index bounded earlier]
      have same : index = lineCount :=
        Nat.eq_of_lt_succ_of_not_lt bounded earlier
      subst index
      exact current.boundExact
  · intro index bounded
    by_cases earlier : index < lineCount
    · rw [proofAt_earlier index bounded earlier]
      exact acceptedPrefix.at_contextCode index earlier
    · rw [proofAt_current index bounded earlier]
      have same : index = lineCount :=
        Nat.eq_of_lt_succ_of_not_lt bounded earlier
      subst index
      exact current.contextExact
  · intro index bounded
    by_cases earlier : index < lineCount
    · rw [proofAt_earlier index bounded earlier]
      exact acceptedPrefix.at_conclusionCode index earlier
    · rw [proofAt_current index bounded earlier]
      have same : index = lineCount :=
        Nat.eq_of_lt_succ_of_not_lt bounded earlier
      subst index
      exact current.conclusionExact

def acceptedNumericPrefix_of_fold_positive
    (history : TheoryHistory)
    (archiveCode lineCount accepted : Nat)
    (positive : 0 <
      proofCheckFold lineCount accepted history.quote archiveCode) :
    AcceptedNumericPrefix history archiveCode lineCount := by
  induction lineCount generalizing accepted with
  | zero => exact AcceptedNumericPrefix.empty history archiveCode
  | succ lineCount inductionHypothesis =>
      have parts := (natAndBit_pos_iff _ _).mp positive
      have recursivePositive : 0 <
          proofCheckFold lineCount accepted history.quote archiveCode :=
        parts.1
      have acceptedPrefix := inductionHypothesis _ recursivePositive
      have linePositive :
          0 < numericCheckProofLine history.quote archiveCode lineCount :=
        by
          unfold numericCheckProofLine
          exact parts.2
      exact acceptedPrefix.extend
        (checkProofLine_positive_reconstruct history archiveCode lineCount
          acceptedPrefix linePositive)

/-! ## Soundness of the complete numeric verifier -/

theorem proofCheckBit_sound
    (history : TheoryHistory)
    (proofCode : Nat)
    (sentence : Sentence)
    (accepted : proofCheckBit history.quote proofCode sentence.quote = 1) :
    HistoryProvable history sentence := by
  unfold proofCheckBit at accepted
  dsimp only at accepted
  have first := (natAndBit_eq_one_iff _ _).mp accepted
  have lineCountPositive : 0 < natUnpairLeft proofCode :=
    (natPositiveBit_pos_iff _).mp first.1
  have second := (natAndBit_pos_iff _ _).mp first.2
  have foldPositive : 0 <
      proofCheckFold (natUnpairLeft proofCode) 1 history.quote proofCode :=
    second.1
  have third := (natAndBit_pos_iff _ _).mp second.2
  have fourth := (natAndBit_pos_iff _ _).mp third.2
  have fifth := (natAndBit_pos_iff _ _).mp fourth.2
  have terminalBound :
      numericLineBound
          (numericArchiveLine proofCode (natUnpairLeft proofCode).pred) = 0 := by
    rw [numericLineBound_eq_unpair, numericArchiveLine_eq_beta]
    exact (natEqualBit_pos_iff _ _).mp third.1
  have terminalContext :
      numericLineContext
          (numericArchiveLine proofCode (natUnpairLeft proofCode).pred) = 0 := by
    rw [numericLineContext_eq_unpair, numericArchiveLine_eq_beta]
    exact (natEqualBit_pos_iff _ _).mp fourth.1
  have terminalConclusion :
      numericLineConclusion
          (numericArchiveLine proofCode (natUnpairLeft proofCode).pred) =
        sentence.quote := by
    rw [numericLineConclusion_eq_unpair, numericArchiveLine_eq_beta]
    exact (natEqualBit_pos_iff _ _).mp fifth.1
  let acceptedPrefix := acceptedNumericPrefix_of_fold_positive history proofCode
    (natUnpairLeft proofCode) 1 foldPositive
  have lastBounded : (natUnpairLeft proofCode).pred <
      natUnpairLeft proofCode :=
    Nat.pred_lt (Nat.ne_of_gt lineCountPositive)
  let last := acceptedPrefix.at (natUnpairLeft proofCode).pred lastBounded
  have lastBound : last.bound = 0 := by
    unfold last
    rw [AcceptedNumericPrefix.at_bound, terminalBound]
  have lastContext :
      last.context.quote = (FormulaContext.nil : FormulaContext 0).quote := by
    unfold last
    rw [AcceptedNumericPrefix.at_contextCode, terminalContext]
    rfl
  have lastConclusion :
      last.conclusion.raw.code = sentence.scopedFormula.raw.code := by
    unfold last
    rw [AcceptedNumericPrefix.at_conclusionCode, terminalConclusion]
    rfl
  exact Nonempty.intro
    (last.recoverFromCodes FormulaContext.nil sentence.scopedFormula
      lastBound lastContext lastConclusion)

/-! ## Completeness on the canonical encoding of typed derivations -/

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.natAddAssocConstructive
#print axioms RelationalPerimeter.HeytingArithmetic.proofLine_rebase_add
#print axioms RelationalPerimeter.HeytingArithmetic.listMapRebaseAddConstructive
#print axioms RelationalPerimeter.HeytingArithmetic.embeddedArchive_appendRebased_left
#print axioms RelationalPerimeter.HeytingArithmetic.embeddedArchive_appendRebased_right
#print axioms RelationalPerimeter.HeytingArithmetic.embeddedArchive_finish
#print axioms RelationalPerimeter.HeytingArithmetic.numericArchiveLine_embeddedFinish
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule0_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule1_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule2_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule3_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule4_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule5_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule6_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule7_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule8_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule9_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule10_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule11_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule12_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule13_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule14_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule15_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule16_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule17_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule18_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule19_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule20_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_rule21_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.checkProofLine_positive_reconstruct
#print axioms RelationalPerimeter.HeytingArithmetic.proofCheckBit_sound
/- AXIOM_AUDIT_END -/
