import RelationalPerimeter.Constitution.HeytingArithmeticGodelInstance

/-!
# Effective Gödel systems for sound finite HA histories

The root HA realization is lifted uniformly to every finite intrinsic theory
history whose added sentences are supplied with standard-model truth.  The
numeric checker, its decoder, the represented provability predicate and the
fixed-point certificate are all indexed by the same history value.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

/-! ## Positive soundness data for finite histories -/

/-- Standard-model truth for every sentence positively stored in a history. -/
structure SoundTheoryHistory (history : TheoryHistory) : Type where
  addedSentenceTrue :
    {sentence : Sentence} -> history.Contains sentence -> PLift sentence.models

/-- The root history has no added sentence and is therefore sound. -/
def rootSoundTheoryHistory : SoundTheoryHistory TheoryHistory.root :=
  { addedSentenceTrue := fun evidence =>
      False.elim (TheoryHistory.rootContainsElim evidence) }

/-- Extend a sound history by the truth witness of exactly its newest
sentence.  Earlier truth witnesses are transported without reconstruction. -/
def SoundTheoryHistory.extend
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {sentence : Sentence}
    (sentenceTruth : PLift sentence.models) :
    SoundTheoryHistory (.extend history sentence) :=
  { addedSentenceTrue := fun evidence => by
      cases evidence with
      | newest => exact sentenceTruth
      | earlier earlierEvidence =>
          exact sound.addedSentenceTrue earlierEvidence }

/-- A history whose newest stored sentence is falsity cannot carry the
soundness data required by the progression. -/
def soundTheoryHistoryRejectsNewestFalse
    (history : TheoryHistory) :
    SoundTheoryHistory (.extend history falseSentence) -> Empty := by
  intro sound
  have falseTruth : PLift falseSentence.models :=
    sound.addedSentenceTrue TheoryHistory.Contains.newest
  exact False.elim falseTruth.down

/-- A closed true sentence remains true after it is lifted to any ambient
scope used by a postulate occurrence. -/
theorem Sentence.atBound_sound
    (sentence : Sentence)
    (truth : sentence.models)
    (bound : Nat)
    (environment : Environment) :
    (sentence.atBound bound).raw.Holds environment := by
  induction bound generalizing environment with
  | zero =>
      exact
        (sentence.holds_environment_independent
          emptyEnvironment environment).mp truth
  | succ bound inductionHypothesis =>
      let tailEnvironment : Environment := fun index =>
        environment (Nat.succ index)
      have rebuilt : (index : Nat) ->
          pushEnvironment tailEnvironment (environment 0) index =
            environment index := by
        intro index
        cases index <;> rfl
      have liftedTruth : (sentence.atBound bound).lift.raw.Holds
          (pushEnvironment tailEnvironment (environment 0)) :=
        ((sentence.atBound bound).holds_lift
          tailEnvironment (environment 0)).mpr
            (inductionHypothesis tailEnvironment)
      exact ((sentence.atBound bound).lift.raw.holds_congr
          (pushEnvironment tailEnvironment (environment 0))
          environment rebuilt).mp liftedTruth

theorem historyAxiom_sound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {bound : Nat}
    {formula : ScopedFormula bound}
    (witness : HistoryAxiom history formula)
    (environment : Environment) :
    formula.raw.Holds environment := by
  cases witness with
  | arithmetic arithmeticWitness =>
      exact standardArithmeticAxiom_sound arithmeticWitness environment
  | added evidence =>
      rename_i sentence
      exact sentence.atBound_sound
        (sound.addedSentenceTrue evidence).down bound environment

/-- Constructive standard-model soundness for a finite sound history. -/
theorem historyDerivation_sound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {bound : Nat}
    {sourceContext : FormulaContext bound}
    {sourceConclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic history.theory
      sourceContext sourceConclusion)
    (environment : Environment)
    (contextHolds : sourceContext.StandardHolds environment) :
    sourceConclusion.raw.Holds environment := by
  induction proof generalizing environment with
  | theoryAxiom witness =>
      exact historyAxiom_sound sound witness environment
  | hypothesis member =>
      exact member.standardHolds environment contextHolds
  | weaken extra premise inductionHypothesis =>
      exact inductionHypothesis environment contextHolds.2
  | implicationIntroduction premise inductionHypothesis =>
      exact fun leftHolds =>
        inductionHypothesis environment (And.intro leftHolds contextHolds)
  | implicationElimination implication argument
      implicationHypothesis argumentHypothesis =>
      exact (implicationHypothesis environment contextHolds)
        (argumentHypothesis environment contextHolds)
  | conjunctionIntroduction left right leftHypothesis rightHypothesis =>
      exact And.intro (leftHypothesis environment contextHolds)
        (rightHypothesis environment contextHolds)
  | conjunctionEliminationLeft premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).1
  | conjunctionEliminationRight premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).2
  | disjunctionIntroductionLeft premise inductionHypothesis =>
      exact Or.inl (inductionHypothesis environment contextHolds)
  | disjunctionIntroductionRight premise inductionHypothesis =>
      exact Or.inr (inductionHypothesis environment contextHolds)
  | disjunctionElimination disjunction leftBranch rightBranch
      disjunctionHypothesis leftHypothesis rightHypothesis =>
      rename_i context leftFormula rightFormula conclusion
      cases disjunctionHypothesis environment contextHolds with
      | inl leftHolds =>
          exact leftHypothesis environment (And.intro leftHolds contextHolds)
      | inr rightHolds =>
          exact rightHypothesis environment (And.intro rightHolds contextHolds)
  | falsumElimination premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).elim
  | universalIntroduction premise inductionHypothesis =>
      rename_i context body
      intro value
      exact inductionHypothesis (pushEnvironment environment value)
        (context.standardHolds_lift environment value contextHolds)
  | universalElimination term premise inductionHypothesis =>
      rename_i context body
      exact (body.holds_instantiate term environment).mpr
        (inductionHypothesis environment contextHolds
          (term.raw.evaluate environment))
  | existentialIntroduction term premise inductionHypothesis =>
      rename_i context body
      exact Exists.intro (term.raw.evaluate environment)
        ((body.holds_instantiate term environment).mp
          (inductionHypothesis environment contextHolds))
  | existentialElimination existential branch
      existentialHypothesis branchHypothesis =>
      rename_i context body conclusion
      cases existentialHypothesis environment contextHolds with
      | intro value bodyHolds =>
          have branchConclusion := branchHypothesis
            (pushEnvironment environment value)
            (And.intro bodyHolds
              (context.standardHolds_lift environment value contextHolds))
          exact (conclusion.holds_lift environment value).mp branchConclusion
  | equalityReflexivity term => rfl
  | equalitySymmetry premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).symm
  | equalityTransitivity first second firstHypothesis secondHypothesis =>
      exact (firstHypothesis environment contextHolds).trans
        (secondHypothesis environment contextHolds)
  | equalitySubstitution body equality premise
      equalityHypothesis premiseHypothesis =>
      rename_i context left right
      have termEquality := equalityHypothesis environment contextHolds
      have atLeft := (body.holds_instantiate left environment).mp
        (premiseHypothesis environment contextHolds)
      have atRight : body.raw.Holds
          (pushEnvironment environment (right.raw.evaluate environment)) := by
        rw [<- termEquality]
        exact atLeft
      exact (body.holds_instantiate right environment).mpr atRight
  | liftVariables premise inductionHypothesis =>
      rename_i context conclusion
      let tailEnvironment : Environment := fun index =>
        environment (Nat.succ index)
      have rebuilt : (index : Nat) ->
          pushEnvironment tailEnvironment (environment 0) index =
            environment index := by
        intro index
        cases index <;> rfl
      have canonicalLiftedContext : context.lift.StandardHolds
          (pushEnvironment tailEnvironment (environment 0)) :=
        (context.lift.standardHolds_congr environment
          (pushEnvironment tailEnvironment (environment 0))
          (fun index _bounded => (rebuilt index).symm)).mp contextHolds
      have earlierContext : context.StandardHolds tailEnvironment :=
        (context.standardHolds_lift_iff tailEnvironment
          (environment 0)).mp canonicalLiftedContext
      have earlierConclusion := inductionHypothesis tailEnvironment earlierContext
      exact conclusion.lift.raw.holds_congr
        (pushEnvironment tailEnvironment (environment 0)) environment rebuilt
        |>.mp ((conclusion.holds_lift tailEnvironment (environment 0)).mpr
          earlierConclusion)
  | freeInstantiation replacement premise inductionHypothesis =>
      rename_i context conclusion
      have earlierContext : context.StandardHolds
          (pushEnvironment environment
            (replacement.raw.evaluate environment)) :=
        (context.standardHolds_instantiate replacement environment).mp
          contextHolds
      exact (conclusion.holds_instantiate replacement environment).mpr
        (inductionHypothesis
          (pushEnvironment environment (replacement.raw.evaluate environment))
          earlierContext)
  | doubleNegationElimination permission premise inductionHypothesis =>
      cases permission

/-! ## History-indexed checked proofs -/

def historyProofCheck
    (history : TheoryHistory)
    (proofCode sentenceCode : Nat) : Bool :=
  if proofCheckBit history.quote proofCode sentenceCode = 1 then true else false

theorem historyProofCheck_eq_true_iff
    (history : TheoryHistory)
    (proofCode sentenceCode : Nat) :
    historyProofCheck history proofCode sentenceCode = true <->
      proofCheckBit history.quote proofCode sentenceCode = 1 := by
  unfold historyProofCheck
  by_cases accepted : proofCheckBit history.quote proofCode sentenceCode = 1
  · rw [if_pos accepted]
    exact ⟨fun _ => accepted, fun _ => rfl⟩
  · rw [if_neg accepted]
    constructor
    · intro impossible
      cases impossible
    · intro equality
      exact (accepted equality).elim

theorem historyProofCheck_root_eq_haProofCheck
    (proofCode sentenceCode : Nat) :
    historyProofCheck TheoryHistory.root proofCode sentenceCode =
      haProofCheck proofCode sentenceCode :=
  rfl

def historyDerivationOfCheckedProof
    (history : TheoryHistory)
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) sentence) :
    Derivation LogicMode.intuitionistic history.theory
      FormulaContext.nil sentence.scopedFormula := by
  rcases proof with ⟨proofCode, ⟨verification⟩⟩
  exact decodeAcceptedHistoryProof history proofCode sentence
    ((historyProofCheck_eq_true_iff history proofCode sentence.quote).mp
      verification)

def historyCheckedProofOfDerivation
    {history : TheoryHistory}
    {sentence : Sentence}
    (proof : Derivation LogicMode.intuitionistic history.theory
      FormulaContext.nil sentence.scopedFormula) :
    CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence := by
  let archive := encodeHistoryDerivation proof
  refine ⟨archive.quote, ⟨?_⟩⟩
  apply (historyProofCheck_eq_true_iff
    history archive.quote sentence.quote).mpr
  exact proofCheckBit_encodeHistoryDerivation history sentence proof

/-! ## History-indexed equivalence and fixed point -/

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
  historyCheckedProofOfDerivation
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
  historyCheckedProofOfDerivation
    (Derivation.implicationElimination implicationProof argumentProof)

def historyDiagonalProofArchive
    (history : TheoryHistory)
    (target source : Predicate) : ProofArchive :=
  encodeHistoryDerivation
    (haDerivationToHistory history (haDiagonalDerivation target source))

theorem historyDiagonalProofArchive_accepted
    (history : TheoryHistory)
    (target source : Predicate) :
    historyProofCheck history (historyDiagonalProofArchive history target source).quote
        (haBiconditional (haDiagonalLeft target source)
          (haDiagonalRight target source)).quote = true := by
  apply (historyProofCheck_eq_true_iff history _ _).mpr
  exact proofCheckBit_encodeHistoryDerivation history
    (haBiconditional (haDiagonalLeft target source)
      (haDiagonalRight target source))
    (haDerivationToHistory history (haDiagonalDerivation target source))

def historyDiagonalizeExact
    (history : TheoryHistory)
    (target source : Predicate) :
    CheckedSentenceEquivalence Sentence.quote (historyEquivalenceCheck history)
      ((haDiagonalize target).applyNumeral source.raw.code)
      (target.applyNumeral (source.applyNumeral source.raw.code).quote) :=
  ⟨(historyDiagonalProofArchive history target source).quote,
    ⟨by
      unfold historyEquivalenceCheck
      rw [<- haBiconditional_quote]
      exact historyDiagonalProofArchive_accepted history target source⟩⟩

/-! ## History semantics and represented unprovability -/

def historyProofSound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck history) sentence) :
    haTruth sentence :=
  ⟨historyDerivation_sound sound
    (historyDerivationOfCheckedProof history proof) emptyEnvironment trivial⟩

def historyEquivalenceTruthForward
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      (historyEquivalenceCheck history) left right) :
    haTruth left -> haTruth right := by
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
    haTruth right -> haTruth left := by
  intro rightTruth
  let biconditionalTruth := historyProofSound sound
    (historyBiconditionalProofOfCheckedEquivalence history equivalence)
  exact ⟨biconditionalTruth.down.2 rightTruth.down⟩

def historyUnprovabilityPredicate (history : TheoryHistory) : Predicate :=
  { raw := RawFormula.neg (provabilityPredicate history).raw
    isScoped := And.intro (provabilityPredicate history).isScoped trivial }

theorem historyUnprovabilityPredicate_root_eq_haUnprovabilityPredicate :
    historyUnprovabilityPredicate TheoryHistory.root =
      haUnprovabilityPredicate :=
  rfl

theorem historyUnprovabilityPredicate_spec
    (history : TheoryHistory)
    (sentence : Sentence) :
    ((historyUnprovabilityPredicate history).applyNumeral sentence.quote).models <->
      (((provabilityPredicate history).applyNumeral sentence.quote).models ->
        False) := by
  rfl

def historyRepresentsUnprovabilityForward
    (history : TheoryHistory)
    (sentence : Sentence) :
    haTruth
        ((historyUnprovabilityPredicate history).applyNumeral sentence.quote) ->
      CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence ->
        Empty := by
  intro unprovabilityTruth checkedProof
  have noProvability :
      ((provabilityPredicate history).applyNumeral sentence.quote).models ->
        False :=
    (historyUnprovabilityPredicate_spec history sentence).mp
      unprovabilityTruth.down
  apply False.elim
  apply noProvability
  apply (provabilityPredicate_spec history sentence).mpr
  exact Nonempty.intro
    (historyDerivationOfCheckedProof history checkedProof)

def historyRepresentsUnprovabilityBackward
    (history : TheoryHistory)
    (sentence : Sentence) :
    (CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence ->
      Empty) ->
    haTruth
      ((historyUnprovabilityPredicate history).applyNumeral sentence.quote) := by
  intro noCheckedProof
  refine ⟨(historyUnprovabilityPredicate_spec history sentence).mpr ?_⟩
  intro provabilityTruth
  have provable : HistoryProvable history sentence :=
    (provabilityPredicate_spec history sentence).mp provabilityTruth
  exact Nonempty.elim provable (fun derivation =>
    Empty.elim
      (noCheckedProof (historyCheckedProofOfDerivation derivation)))

/-! ## Uniform effective system for one sound history -/

def soundHistoryEffectiveGodelSystem
    (history : TheoryHistory)
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
    Truth := haTruth
    proofSound := historyProofSound sound
    equivalenceTruthForward := historyEquivalenceTruthForward sound
    equivalenceTruthBackward := historyEquivalenceTruthBackward sound
    unprovabilityFormula := historyUnprovabilityPredicate history
    representsUnprovabilityForward :=
      historyRepresentsUnprovabilityForward history
    representsUnprovabilityBackward :=
      historyRepresentsUnprovabilityBackward history }

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory
#print axioms RelationalPerimeter.HeytingArithmetic.rootSoundTheoryHistory
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory.extend
#print axioms RelationalPerimeter.HeytingArithmetic.soundTheoryHistoryRejectsNewestFalse
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence.atBound_sound
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivation_sound
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofCheck_eq_true_iff
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofCheck_root_eq_haProofCheck
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivationOfCheckedProof
#print axioms RelationalPerimeter.HeytingArithmetic.historyCheckedProofOfDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.historyDiagonalizeExact
#print axioms RelationalPerimeter.HeytingArithmetic.historyProofSound
#print axioms RelationalPerimeter.HeytingArithmetic.historyUnprovabilityPredicate_root_eq_haUnprovabilityPredicate
#print axioms RelationalPerimeter.HeytingArithmetic.historyUnprovabilityPredicate_spec
#print axioms RelationalPerimeter.HeytingArithmetic.historyRepresentsUnprovabilityForward
#print axioms RelationalPerimeter.HeytingArithmetic.historyRepresentsUnprovabilityBackward
#print axioms RelationalPerimeter.HeytingArithmetic.soundHistoryEffectiveGodelSystem
/- AXIOM_AUDIT_END -/
