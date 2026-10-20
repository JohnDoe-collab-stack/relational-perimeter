import RelationalPerimeter.Instances.HeytingArithmetic.Godel
import RelationalPerimeter.Instances.HeytingArithmetic.TheoryHistorySoundness

/-!
# Effective Gödel production for a positively sound theory history

The numeric proof checker already receives the intrinsic history code.  This
module exposes that parameter through checked certificates, transports the
existing HA fixed-point derivation into the history, and closes the generic
Gödel interface from a positive soundness certificate for the same history.
-/

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

/-! ## History-indexed checked proofs -/

/-- Boolean facade over the proof checker at one exact theory history. -/
def historyProofCheck
    (history : TheoryHistory)
    (proofCode sentenceCode : Nat) : Bool :=
  if proofCheckBit history.quote proofCode sentenceCode = 1 then true else false

theorem historyProofCheck_eq_true_iff
    (history : TheoryHistory)
    (proofCode sentenceCode : Nat) :
    historyProofCheck history proofCode sentenceCode = true ↔
      proofCheckBit history.quote proofCode sentenceCode = 1 := by
  apply Iff.intro
  · intro verified
    unfold historyProofCheck at verified
    by_cases accepted : proofCheckBit history.quote proofCode sentenceCode = 1
    · exact accepted
    · rw [if_neg accepted] at verified
      exact Bool.noConfusion verified
  · intro accepted
    unfold historyProofCheck
    rw [if_pos accepted]

/-- Decode a checked certificate at its exact history. -/
def historyDerivationOfCheckedProof
    (history : TheoryHistory)
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) sentence) :
    Derivation LogicMode.intuitionistic history.theory FormulaContext.nil
      sentence.scopedFormula := by
  rcases proof with ⟨proofCode, ⟨verification⟩⟩
  exact decodeAcceptedHistoryProof history proofCode sentence
    ((historyProofCheck_eq_true_iff history proofCode sentence.quote).mp
      verification)

/-- Encode a typed historical derivation for the checker of the same history. -/
def historyCheckedProofOfDerivation
    (history : TheoryHistory)
    {sentence : Sentence}
    (proof : Derivation LogicMode.intuitionistic history.theory
      FormulaContext.nil sentence.scopedFormula) :
    CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence := by
  let archive := encodeHistoryDerivation proof
  refine ⟨archive.quote, ⟨?_⟩⟩
  apply (historyProofCheck_eq_true_iff history archive.quote
    sentence.quote).mpr
  exact proofCheckBit_encodeHistoryDerivation history sentence proof

/-- Preserve a checked proof through the exact positive extension step. -/
def historyCheckedProofPreserved
    {history : TheoryHistory}
    {newest sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) sentence) :
    CheckedSentenceProof Sentence.quote
      (historyProofCheck (.extend history newest)) sentence :=
  historyCheckedProofOfDerivation (.extend history newest)
    (historyDerivationPreserve
      (historyDerivationOfCheckedProof history proof))

/-- The newest stored sentence has a checked proof in the extended history. -/
def newestHistoryCheckedProof
    (history : TheoryHistory)
    (sentence : Sentence) :
    CheckedSentenceProof Sentence.quote
      (historyProofCheck (.extend history sentence)) sentence :=
  historyCheckedProofOfDerivation (.extend history sentence)
    (Derivation.theoryAxiom
      (HistoryAxiom.added TheoryHistory.Contains.newest))

/-! ## History-indexed equivalence and diagonal production -/

def historyEquivalenceCheck
    (history : TheoryHistory)
    (certificateCode leftCode rightCode : Nat) : Bool :=
  historyProofCheck history certificateCode
    (haBiconditionalCode leftCode rightCode)

def historyBiconditionalProofOfCheckedEquivalence
    (history : TheoryHistory)
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history) left right) :
    CheckedSentenceProof Sentence.quote (historyProofCheck history)
      (haBiconditional left right) := by
  rcases equivalence with ⟨certificateCode, ⟨verification⟩⟩
  exact ⟨certificateCode, ⟨by
    rw [haBiconditional_quote]
    exact verification⟩⟩

def historyProofForward
    (history : TheoryHistory)
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history) left right)
    (leftProof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) left) :
    CheckedSentenceProof Sentence.quote (historyProofCheck history) right :=
  let biconditionalProof := historyDerivationOfCheckedProof history
    (historyBiconditionalProofOfCheckedEquivalence history equivalence)
  let implicationProof :=
    Derivation.conjunctionEliminationLeft biconditionalProof
  let argumentProof := historyDerivationOfCheckedProof history leftProof
  historyCheckedProofOfDerivation history
    (Derivation.implicationElimination implicationProof argumentProof)

def historyProofBackward
    (history : TheoryHistory)
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history) left right)
    (rightProof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) right) :
    CheckedSentenceProof Sentence.quote (historyProofCheck history) left :=
  let biconditionalProof := historyDerivationOfCheckedProof history
    (historyBiconditionalProofOfCheckedEquivalence history equivalence)
  let implicationProof :=
    Derivation.conjunctionEliminationRight biconditionalProof
  let argumentProof := historyDerivationOfCheckedProof history rightProof
  historyCheckedProofOfDerivation history
    (Derivation.implicationElimination implicationProof argumentProof)

def historyDiagonalDerivation
    (history : TheoryHistory)
    (target source : Predicate) :
    Derivation LogicMode.intuitionistic history.theory FormulaContext.nil
      (haBiconditional (haDiagonalLeft target source)
        (haDiagonalRight target source)).scopedFormula :=
  haDerivationToHistory history (haDiagonalDerivation target source)

def historyDiagonalProofArchive
    (history : TheoryHistory)
    (target source : Predicate) : ProofArchive :=
  encodeHistoryDerivation (historyDiagonalDerivation history target source)

theorem historyDiagonalProofArchive_accepted
    (history : TheoryHistory)
    (target source : Predicate) :
    historyProofCheck history
        (historyDiagonalProofArchive history target source).quote
        (haBiconditional (haDiagonalLeft target source)
          (haDiagonalRight target source)).quote = true := by
  apply (historyProofCheck_eq_true_iff history _ _).mpr
  exact proofCheckBit_encodeHistoryDerivation history
    (haBiconditional (haDiagonalLeft target source)
      (haDiagonalRight target source))
    (historyDiagonalDerivation history target source)

theorem historyDiagonalEquivalence_accepted
    (history : TheoryHistory)
    (target source : Predicate) :
    historyEquivalenceCheck history
        (historyDiagonalProofArchive history target source).quote
        (haDiagonalLeft target source).quote
        (haDiagonalRight target source).quote = true := by
  unfold historyEquivalenceCheck
  rw [← haBiconditional_quote]
  exact historyDiagonalProofArchive_accepted history target source

def historyDiagonalizeExact
    (history : TheoryHistory)
    (target source : Predicate) :
    CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history)
      ((haDiagonalize target).applyNumeral source.raw.code)
      (target.applyNumeral
        (source.applyNumeral source.raw.code).quote) :=
  ⟨(historyDiagonalProofArchive history target source).quote,
    ⟨historyDiagonalEquivalence_accepted history target source⟩⟩

/-! ## Sound interpretation of the history proof predicate -/

def historyTruth (sentence : Sentence) : Type := PLift sentence.models

def historyProofSound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) sentence) :
    historyTruth sentence :=
  ⟨historyDerivation_sound sound
    (historyDerivationOfCheckedProof history proof)
    emptyEnvironment trivial⟩

def historyEquivalenceTruthForward
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history) left right) :
    historyTruth left → historyTruth right := by
  intro leftTruth
  let biconditionalTruth := historyProofSound sound
    (historyBiconditionalProofOfCheckedEquivalence history equivalence)
  exact ⟨biconditionalTruth.down.1 leftTruth.down⟩

def historyEquivalenceTruthBackward
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history) left right) :
    historyTruth right → historyTruth left := by
  intro rightTruth
  let biconditionalTruth := historyProofSound sound
    (historyBiconditionalProofOfCheckedEquivalence history equivalence)
  exact ⟨biconditionalTruth.down.2 rightTruth.down⟩

def historyUnprovabilityPredicate (history : TheoryHistory) : Predicate :=
  { raw := RawFormula.neg (provabilityPredicate history).raw
    isScoped := And.intro (provabilityPredicate history).isScoped trivial }

theorem historyUnprovabilityPredicate_spec
    (history : TheoryHistory)
    (sentence : Sentence) :
    (historyUnprovabilityPredicate history |>.applyNumeral sentence.quote |>.models) ↔
      ((provabilityPredicate history |>.applyNumeral sentence.quote |>.models) →
        False) := by
  rfl

def historyRepresentsUnprovabilityForward
    {history : TheoryHistory}
    (sentence : Sentence) :
    historyTruth
        ((historyUnprovabilityPredicate history).applyNumeral sentence.quote) →
      CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence →
        Empty := by
  intro unprovabilityTruth checkedProof
  have noProvability :
      (provabilityPredicate history).applyNumeral sentence.quote |>.models →
        False :=
    (historyUnprovabilityPredicate_spec history sentence).mp
      unprovabilityTruth.down
  apply False.elim
  apply noProvability
  apply (provabilityPredicate_spec history sentence).mpr
  exact Nonempty.intro (historyDerivationOfCheckedProof history checkedProof)

def historyRepresentsUnprovabilityBackward
    {history : TheoryHistory}
    (sentence : Sentence) :
    (CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence →
      Empty) →
    historyTruth
      ((historyUnprovabilityPredicate history).applyNumeral sentence.quote) := by
  intro noCheckedProof
  refine ⟨(historyUnprovabilityPredicate_spec history sentence).mpr ?_⟩
  intro provabilityTruth
  have provable : HistoryProvable history sentence :=
    (provabilityPredicate_spec history sentence).mp provabilityTruth
  exact Nonempty.elim provable (fun derivation =>
    Empty.elim
      (noCheckedProof (historyCheckedProofOfDerivation history derivation)))

/-! ## Closed effective system and executed production -/

def soundHistoryEffectiveGodelSystem
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history) :
    EffectivelyPresentedSoundGodelSystem :=
  { UnaryFormula := Predicate
    Sentence := Sentence
    encodeUnary := fun predicate => predicate.raw.code
    decodeUnary := decodePredicate
    decodeUnary_encode := decodePredicate_code
    encodeSentence := Sentence.quote
    decodeSentence := decodeSentence
    decodeSentence_encode := decodeSentence_quote
    substitute := Predicate.applyNumeral
    diagonalize := haDiagonalize
    proofCheck := historyProofCheck history
    equivalenceCheck := historyEquivalenceCheck history
    diagonalizeExact := historyDiagonalizeExact history
    proofForward := historyProofForward history
    proofBackward := historyProofBackward history
    Truth := historyTruth
    proofSound := historyProofSound sound
    equivalenceTruthForward := historyEquivalenceTruthForward sound
    equivalenceTruthBackward := historyEquivalenceTruthBackward sound
    unprovabilityFormula := historyUnprovabilityPredicate history
    representsUnprovabilityForward :=
      historyRepresentsUnprovabilityForward
    representsUnprovabilityBackward :=
      historyRepresentsUnprovabilityBackward }

def soundHistoryGodelExecution
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history) :
    ExecutedGodelProduction
      (soundHistoryEffectiveGodelSystem sound).toGodelSyntax
      (soundHistoryEffectiveGodelSystem sound).unprovabilityFormula
      (soundHistoryEffectiveGodelSystem sound).toGodelInterpretation :=
  effectiveGodelExecution (soundHistoryEffectiveGodelSystem sound)

def rootSoundTheoryHistory : SoundTheoryHistory .root := .root

theorem historyProofCheck_root_eq_haProofCheck
    (proofCode sentenceCode : Nat) :
    historyProofCheck .root proofCode sentenceCode =
      haProofCheck proofCode sentenceCode :=
  rfl

theorem historyEquivalenceCheck_root_eq_haEquivalenceCheck
    (certificateCode leftCode rightCode : Nat) :
    historyEquivalenceCheck .root certificateCode leftCode rightCode =
      haEquivalenceCheck certificateCode leftCode rightCode :=
  rfl

theorem historyTruth_eq_haTruth (sentence : Sentence) :
    historyTruth sentence = haTruth sentence :=
  rfl

theorem historyUnprovabilityPredicate_root_eq_haUnprovabilityPredicate :
    historyUnprovabilityPredicate .root = haUnprovabilityPredicate :=
  rfl

theorem rootHistoryGodelRawSentence_eq_haGodelRawSentence :
    (haDiagonalize (historyUnprovabilityPredicate .root)).applyNumeral
        (haDiagonalize (historyUnprovabilityPredicate .root)).raw.code =
      (haDiagonalize haUnprovabilityPredicate).applyNumeral
        (haDiagonalize haUnprovabilityPredicate).raw.code := by
  rw [historyUnprovabilityPredicate_root_eq_haUnprovabilityPredicate]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofCheck
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofCheck_eq_true_iff
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivationOfCheckedProof
#print axioms RelationalPerimeter.HeytingArithmetic.historyCheckedProofOfDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.historyCheckedProofPreserved
#print axioms RelationalPerimeter.HeytingArithmetic.newestHistoryCheckedProof
#print axioms RelationalPerimeter.HeytingArithmetic.historyEquivalenceCheck
#print axioms RelationalPerimeter.HeytingArithmetic.historyBiconditionalProofOfCheckedEquivalence
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofForward
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofBackward
#print axioms RelationalPerimeter.HeytingArithmetic.historyDiagonalDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.historyDiagonalProofArchive
#print axioms RelationalPerimeter.HeytingArithmetic.historyDiagonalProofArchive_accepted
#print axioms RelationalPerimeter.HeytingArithmetic.historyDiagonalEquivalence_accepted
#print axioms RelationalPerimeter.HeytingArithmetic.historyDiagonalizeExact
#print axioms RelationalPerimeter.HeytingArithmetic.historyTruth
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofSound
#print axioms RelationalPerimeter.HeytingArithmetic.historyEquivalenceTruthForward
#print axioms RelationalPerimeter.HeytingArithmetic.historyEquivalenceTruthBackward
#print axioms RelationalPerimeter.HeytingArithmetic.historyUnprovabilityPredicate
#print axioms RelationalPerimeter.HeytingArithmetic.historyUnprovabilityPredicate_spec
#print axioms RelationalPerimeter.HeytingArithmetic.historyRepresentsUnprovabilityForward
#print axioms RelationalPerimeter.HeytingArithmetic.historyRepresentsUnprovabilityBackward
#print axioms RelationalPerimeter.HeytingArithmetic.soundHistoryEffectiveGodelSystem
#print axioms RelationalPerimeter.HeytingArithmetic.soundHistoryGodelExecution
#print axioms RelationalPerimeter.HeytingArithmetic.rootSoundTheoryHistory
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofCheck_root_eq_haProofCheck
#print axioms RelationalPerimeter.HeytingArithmetic.historyEquivalenceCheck_root_eq_haEquivalenceCheck
#print axioms RelationalPerimeter.HeytingArithmetic.historyTruth_eq_haTruth
#print axioms RelationalPerimeter.HeytingArithmetic.historyUnprovabilityPredicate_root_eq_haUnprovabilityPredicate
#print axioms RelationalPerimeter.HeytingArithmetic.rootHistoryGodelRawSentence_eq_haGodelRawSentence
/- AXIOM_AUDIT_END -/
