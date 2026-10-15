import StrongPerimetralTurning

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Executed Gödel diagonal production

This module contains only the effective syntax, semantic contracts, executed
diagonal production, and certification of the produced sentence.  It does not
define a perimetral presentation or a closure rejection.
-/

namespace StrongPerimetralTurning

universe uA uB uC uP uV

structure GodelDiagonalSyntax where
  Code : Type uC
  UnaryFormula : Type uA
  Sentence : Type uB
  Proof : Sentence → Type uP
  ProvableIff : Sentence → Sentence → Type uV
  quoteUnary : UnaryFormula → Code
  quoteSentence : Sentence → Code
  substitute : UnaryFormula → Code → Sentence
  diagonalize : UnaryFormula → UnaryFormula
  diagonalizeExact :
    (target source : UnaryFormula) →
      ProvableIff
        (substitute (diagonalize target) (quoteUnary source))
        (substitute target
          (quoteSentence (substitute source (quoteUnary source))))
  proofForward :
    {left right : Sentence} → ProvableIff left right → Proof left → Proof right
  proofBackward :
    {left right : Sentence} → ProvableIff left right → Proof right → Proof left

def godelSentence
    (coding : GodelDiagonalSyntax)
    (target : coding.UnaryFormula) : coding.Sentence :=
  coding.substitute (coding.diagonalize target)
    (coding.quoteUnary (coding.diagonalize target))

def godelSentence_fixedPoint
    (coding : GodelDiagonalSyntax)
    (target : coding.UnaryFormula) :
    coding.ProvableIff
      (godelSentence coding target)
      (coding.substitute target
        (coding.quoteSentence (godelSentence coding target))) :=
  coding.diagonalizeExact target (coding.diagonalize target)

structure GodelProvabilityInterpretation
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula) where
  Truth : coding.Sentence → Type uP
  proofSound :
    {sentence : coding.Sentence} → coding.Proof sentence → Truth sentence
  provableIffTruthForward :
    {left right : coding.Sentence} →
      coding.ProvableIff left right → Truth left → Truth right
  provableIffTruthBackward :
    {left right : coding.Sentence} →
      coding.ProvableIff left right → Truth right → Truth left
  representsUnprovabilityForward :
    (sentence : coding.Sentence) →
      Truth
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence sentence)) →
        coding.Proof sentence → Empty
  representsUnprovabilityBackward :
    (sentence : coding.Sentence) →
      (coding.Proof sentence → Empty) →
        Truth
          (coding.substitute unprovabilityFormula
            (coding.quoteSentence sentence))

namespace GodelProvabilityInterpretation

def fixedPointTruth_implies_unprovability
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (sentence : coding.Sentence)
    (fixedPoint :
      coding.ProvableIff sentence
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence sentence))) :
    interpretation.Truth sentence → coding.Proof sentence → Empty :=
  fun truthWitness =>
    interpretation.representsUnprovabilityForward sentence
      (interpretation.provableIffTruthForward fixedPoint truthWitness)

def fixedPointUnprovability_implies_truth
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (sentence : coding.Sentence)
    (fixedPoint :
      coding.ProvableIff sentence
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence sentence))) :
    (coding.Proof sentence → Empty) → interpretation.Truth sentence :=
  fun noProof =>
    interpretation.provableIffTruthBackward fixedPoint
      (interpretation.representsUnprovabilityBackward sentence noProof)

def fixedPoint_unprovable
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (sentence : coding.Sentence)
    (fixedPoint :
      coding.ProvableIff sentence
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence sentence))) :
    coding.Proof sentence → Empty := by
  intro proof
  exact interpretation.fixedPointTruth_implies_unprovability sentence
    fixedPoint (interpretation.proofSound proof) proof

def fixedPoint_true
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (sentence : coding.Sentence)
    (fixedPoint :
      coding.ProvableIff sentence
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence sentence))) :
    interpretation.Truth sentence :=
  interpretation.fixedPointUnprovability_implies_truth sentence fixedPoint
    (interpretation.fixedPoint_unprovable sentence fixedPoint)

def fixedPoint_rejectsProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (sentence : coding.Sentence)
    (fixedPoint :
      coding.ProvableIff sentence
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence sentence))) :
    (interpretation.Truth sentence → coding.Proof sentence) → Empty := by
  intro completeness
  exact interpretation.fixedPoint_unprovable sentence fixedPoint
    (completeness (interpretation.fixedPoint_true sentence fixedPoint))

end GodelProvabilityInterpretation

structure ExecutedGodelDiagonalProduction
    (coding : GodelDiagonalSyntax)
    (sourceFormula : coding.UnaryFormula) where
  diagonalFormula : coding.UnaryFormula
  diagonalExact : diagonalFormula = coding.diagonalize sourceFormula

def executeGodelDiagonalProduction
    (coding : GodelDiagonalSyntax)
    (sourceFormula : coding.UnaryFormula) :
    ExecutedGodelDiagonalProduction coding sourceFormula :=
  { diagonalFormula := coding.diagonalize sourceFormula
    diagonalExact := rfl }

structure ExecutedGodelSentenceProduction
    (coding : GodelDiagonalSyntax)
    (sourceFormula : coding.UnaryFormula) where
  diagonal : ExecutedGodelDiagonalProduction coding sourceFormula
  sentence : coding.Sentence
  sentenceExact :
    sentence = coding.substitute diagonal.diagonalFormula
      (coding.quoteUnary diagonal.diagonalFormula)

def executeGodelSentenceProduction
    {coding : GodelDiagonalSyntax}
    {sourceFormula : coding.UnaryFormula}
    (diagonal : ExecutedGodelDiagonalProduction coding sourceFormula) :
    ExecutedGodelSentenceProduction coding sourceFormula :=
  { diagonal := diagonal
    sentence := coding.substitute diagonal.diagonalFormula
      (coding.quoteUnary diagonal.diagonalFormula)
    sentenceExact := rfl }

theorem ExecutedGodelSentenceProduction.sentence_is_godelSentence
    {coding : GodelDiagonalSyntax}
    {sourceFormula : coding.UnaryFormula}
    (production : ExecutedGodelSentenceProduction coding sourceFormula) :
    production.sentence = godelSentence coding sourceFormula := by
  calc
    production.sentence =
        coding.substitute production.diagonal.diagonalFormula
          (coding.quoteUnary production.diagonal.diagonalFormula) :=
      production.sentenceExact
    _ = coding.substitute (coding.diagonalize sourceFormula)
          (coding.quoteUnary (coding.diagonalize sourceFormula)) := by
      rw [production.diagonal.diagonalExact]
    _ = godelSentence coding sourceFormula := rfl

structure ExecutedGodelWitness
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) where
  production : ExecutedGodelSentenceProduction coding unprovabilityFormula
  fixedPoint :
    coding.ProvableIff production.sentence
      (coding.substitute unprovabilityFormula
        (coding.quoteSentence production.sentence))
  trueWitness : interpretation.Truth production.sentence
  unprovable : coding.Proof production.sentence → Empty

def certifyExecutedGodelWitness
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (production :
      ExecutedGodelSentenceProduction coding unprovabilityFormula) :
    ExecutedGodelWitness coding unprovabilityFormula interpretation := by
  have fixedPoint :
      coding.ProvableIff production.sentence
        (coding.substitute unprovabilityFormula
          (coding.quoteSentence production.sentence)) := by
    rw [production.sentenceExact, production.diagonal.diagonalExact]
    exact godelSentence_fixedPoint coding unprovabilityFormula
  have unprovable : coding.Proof production.sentence → Empty :=
    interpretation.fixedPoint_unprovable production.sentence fixedPoint
  have trueWitness : interpretation.Truth production.sentence :=
    interpretation.fixedPointUnprovability_implies_truth
      production.sentence fixedPoint unprovable
  exact
    { production := production
      fixedPoint := fixedPoint
      trueWitness := trueWitness
      unprovable := unprovable }

abbrev ExecutedGodelProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    Type _ :=
  interpretation.Truth witness.production.sentence →
    coding.Proof witness.production.sentence

def ExecutedGodelWitness.rejectProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ExecutedGodelProducedCompleteness witness → Empty :=
  fun completeness => witness.unprovable (completeness witness.trueWitness)

inductive ExecutedGodelProductionState
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) : Type _
  | received :
      ExecutedGodelProductionState coding unprovabilityFormula interpretation
  | diagonalized :
      ExecutedGodelDiagonalProduction coding unprovabilityFormula →
        ExecutedGodelProductionState coding unprovabilityFormula interpretation
  | sentenceProduced :
      ExecutedGodelSentenceProduction coding unprovabilityFormula →
        ExecutedGodelProductionState coding unprovabilityFormula interpretation
  | witnessProduced :
      ExecutedGodelWitness coding unprovabilityFormula interpretation →
        ExecutedGodelProductionState coding unprovabilityFormula interpretation

inductive ExecutedGodelProductionStep
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula} :
    ExecutedGodelProductionState coding unprovabilityFormula interpretation →
      ExecutedGodelProductionState coding unprovabilityFormula interpretation →
        Type _
  | diagonalize :
      ExecutedGodelProductionStep .received
        (.diagonalized
          (executeGodelDiagonalProduction coding unprovabilityFormula))
  | selfApply
      (diagonal :
        ExecutedGodelDiagonalProduction coding unprovabilityFormula) :
      ExecutedGodelProductionStep (.diagonalized diagonal)
        (.sentenceProduced (executeGodelSentenceProduction diagonal))
  | certify
      (production :
        ExecutedGodelSentenceProduction coding unprovabilityFormula) :
      ExecutedGodelProductionStep (.sentenceProduced production)
        (.witnessProduced
          (certifyExecutedGodelWitness coding unprovabilityFormula
            interpretation production))

structure ExecutedGodelProduction
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) where
  witness : ExecutedGodelWitness coding unprovabilityFormula interpretation
  history :
    History (@ExecutedGodelProductionStep coding unprovabilityFormula
      interpretation)
      (.received)
      (.witnessProduced witness)

def executeGodelProduction
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    ExecutedGodelProduction coding unprovabilityFormula interpretation := by
  let diagonal :=
    executeGodelDiagonalProduction coding unprovabilityFormula
  let production := executeGodelSentenceProduction diagonal
  let witness :=
    certifyExecutedGodelWitness coding unprovabilityFormula
      interpretation production
  exact
    { witness := witness
      history :=
        .extend
          (.extend
            (.extend .root .diagonalize)
            (.selfApply diagonal))
          (.certify production) }

structure ExecutedGodelProductionOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  diagonal : ExecutedGodelDiagonalProduction coding unprovabilityFormula
  production : ExecutedGodelSentenceProduction coding unprovabilityFormula
  diagonalIsCanonical :
    diagonal = executeGodelDiagonalProduction coding unprovabilityFormula
  productionIsSelfApplication :
    production = executeGodelSentenceProduction diagonal
  witnessIsCertification :
    execution.witness =
      certifyExecutedGodelWitness coding unprovabilityFormula
        interpretation production
  diagonalizeOccurrence : History.Occurrence execution.history
  selfApplyOccurrence : History.Occurrence execution.history
  certifyOccurrence : History.Occurrence execution.history
  diagonalizeNextSelfApply :
    History.OccurrenceNext diagonalizeOccurrence selfApplyOccurrence
  selfApplyNextCertify :
    History.OccurrenceNext selfApplyOccurrence certifyOccurrence

def ExecutedGodelProduction.occurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ExecutedGodelProductionOccurrences execution := by
  cases execution with
  | mk witness history =>
      cases history with
      | extend beforeCertify certifyStep =>
          cases certifyStep with
          | certify production =>
              cases beforeCertify with
              | extend beforeSelfApply selfApplyStep =>
                  cases selfApplyStep with
                  | selfApply diagonal =>
                      cases beforeSelfApply with
                      | extend beforeDiagonalize diagonalizeStep =>
                          cases diagonalizeStep with
                          | diagonalize =>
                              cases beforeDiagonalize with
                              | root =>
                                  exact
                                    { diagonal :=
                                        executeGodelDiagonalProduction coding
                                          unprovabilityFormula
                                      production :=
                                        executeGodelSentenceProduction
                                          (executeGodelDiagonalProduction coding
                                            unprovabilityFormula)
                                      diagonalIsCanonical := rfl
                                      productionIsSelfApplication := rfl
                                      witnessIsCertification := rfl
                                      diagonalizeOccurrence :=
                                        .earlier (.earlier .last)
                                      selfApplyOccurrence := .earlier .last
                                      certifyOccurrence := .last
                                      diagonalizeNextSelfApply :=
                                        .earlier_earlier .previous_last
                                      selfApplyNextCertify := .previous_last }
                              | extend _ impossible => exact nomatch impossible

abbrev CheckedSentenceProof
    {Sentence : Type}
    (encodeSentence : Sentence → Nat)
    (proofCheck : Nat → Nat → Bool)
    (sentence : Sentence) : Type :=
  Σ proofCode : Nat,
    PLift (proofCheck proofCode (encodeSentence sentence) = true)

abbrev CheckedSentenceEquivalence
    {Sentence : Type}
    (encodeSentence : Sentence → Nat)
    (equivalenceCheck : Nat → Nat → Nat → Bool)
    (left right : Sentence) : Type :=
  Σ certificateCode : Nat,
    PLift
      (equivalenceCheck certificateCode
        (encodeSentence left) (encodeSentence right) = true)

structure EffectivelyPresentedSoundGodelSystem where
  UnaryFormula : Type
  Sentence : Type
  encodeUnary : UnaryFormula → Nat
  decodeUnary : Nat → Option UnaryFormula
  decodeUnary_encode :
    (formula : UnaryFormula) →
      decodeUnary (encodeUnary formula) = some formula
  encodeSentence : Sentence → Nat
  decodeSentence : Nat → Option Sentence
  decodeSentence_encode :
    (sentence : Sentence) →
      decodeSentence (encodeSentence sentence) = some sentence
  substitute : UnaryFormula → Nat → Sentence
  diagonalize : UnaryFormula → UnaryFormula
  proofCheck : Nat → Nat → Bool
  equivalenceCheck : Nat → Nat → Nat → Bool
  diagonalizeExact :
    (target source : UnaryFormula) →
      CheckedSentenceEquivalence encodeSentence equivalenceCheck
        (substitute (diagonalize target) (encodeUnary source))
        (substitute target
          (encodeSentence (substitute source (encodeUnary source))))
  proofForward :
    {left right : Sentence} →
      CheckedSentenceEquivalence encodeSentence equivalenceCheck left right →
      CheckedSentenceProof encodeSentence proofCheck left →
      CheckedSentenceProof encodeSentence proofCheck right
  proofBackward :
    {left right : Sentence} →
      CheckedSentenceEquivalence encodeSentence equivalenceCheck left right →
      CheckedSentenceProof encodeSentence proofCheck right →
      CheckedSentenceProof encodeSentence proofCheck left
  Truth : Sentence → Type
  proofSound :
    {sentence : Sentence} →
      CheckedSentenceProof encodeSentence proofCheck sentence → Truth sentence
  equivalenceTruthForward :
    {left right : Sentence} →
      CheckedSentenceEquivalence encodeSentence equivalenceCheck left right →
        Truth left → Truth right
  equivalenceTruthBackward :
    {left right : Sentence} →
      CheckedSentenceEquivalence encodeSentence equivalenceCheck left right →
        Truth right → Truth left
  unprovabilityFormula : UnaryFormula
  representsUnprovabilityForward :
    (sentence : Sentence) →
      Truth (substitute unprovabilityFormula (encodeSentence sentence)) →
        CheckedSentenceProof encodeSentence proofCheck sentence → Empty
  representsUnprovabilityBackward :
    (sentence : Sentence) →
      (CheckedSentenceProof encodeSentence proofCheck sentence → Empty) →
        Truth (substitute unprovabilityFormula (encodeSentence sentence))

def EffectivelyPresentedSoundGodelSystem.encodeUnary_injective
    (system : EffectivelyPresentedSoundGodelSystem)
    {left right : system.UnaryFormula}
    (equality : system.encodeUnary left = system.encodeUnary right) :
    left = right := by
  have decodedEquality : some left = some right :=
    (system.decodeUnary_encode left).symm.trans
      ((congrArg system.decodeUnary equality).trans
        (system.decodeUnary_encode right))
  exact Option.some.inj decodedEquality

def EffectivelyPresentedSoundGodelSystem.encodeSentence_injective
    (system : EffectivelyPresentedSoundGodelSystem)
    {left right : system.Sentence}
    (equality : system.encodeSentence left = system.encodeSentence right) :
    left = right := by
  have decodedEquality : some left = some right :=
    (system.decodeSentence_encode left).symm.trans
      ((congrArg system.decodeSentence equality).trans
        (system.decodeSentence_encode right))
  exact Option.some.inj decodedEquality

def EffectivelyPresentedSoundGodelSystem.toGodelSyntax
    (system : EffectivelyPresentedSoundGodelSystem) :
    GodelDiagonalSyntax :=
  { Code := Nat
    UnaryFormula := system.UnaryFormula
    Sentence := system.Sentence
    Proof := CheckedSentenceProof system.encodeSentence system.proofCheck
    ProvableIff :=
      CheckedSentenceEquivalence system.encodeSentence
        system.equivalenceCheck
    quoteUnary := system.encodeUnary
    quoteSentence := system.encodeSentence
    substitute := system.substitute
    diagonalize := system.diagonalize
    diagonalizeExact := system.diagonalizeExact
    proofForward := system.proofForward
    proofBackward := system.proofBackward }

def EffectivelyPresentedSoundGodelSystem.toGodelInterpretation
    (system : EffectivelyPresentedSoundGodelSystem) :
    GodelProvabilityInterpretation system.toGodelSyntax
      system.unprovabilityFormula :=
  { Truth := system.Truth
    proofSound := system.proofSound
    provableIffTruthForward := system.equivalenceTruthForward
    provableIffTruthBackward := system.equivalenceTruthBackward
    representsUnprovabilityForward :=
      system.representsUnprovabilityForward
    representsUnprovabilityBackward :=
      system.representsUnprovabilityBackward }

abbrev effectiveGodelExecution
    (system : EffectivelyPresentedSoundGodelSystem) :
    ExecutedGodelProduction system.toGodelSyntax system.unprovabilityFormula
      system.toGodelInterpretation :=
  executeGodelProduction system.toGodelSyntax system.unprovabilityFormula
    system.toGodelInterpretation

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelDiagonalSyntax
#print axioms StrongPerimetralTurning.godelSentence
#print axioms StrongPerimetralTurning.godelSentence_fixedPoint
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.fixedPointTruth_implies_unprovability
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.fixedPointUnprovability_implies_truth
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.fixedPoint_unprovable
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.fixedPoint_true
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.fixedPoint_rejectsProducedCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalProduction
#print axioms StrongPerimetralTurning.executeGodelDiagonalProduction
#print axioms StrongPerimetralTurning.ExecutedGodelSentenceProduction
#print axioms StrongPerimetralTurning.executeGodelSentenceProduction
#print axioms StrongPerimetralTurning.ExecutedGodelSentenceProduction.sentence_is_godelSentence
#print axioms StrongPerimetralTurning.ExecutedGodelWitness
#print axioms StrongPerimetralTurning.certifyExecutedGodelWitness
#print axioms StrongPerimetralTurning.ExecutedGodelProducedCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelWitness.rejectProducedCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelProductionState
#print axioms StrongPerimetralTurning.ExecutedGodelProductionStep
#print axioms StrongPerimetralTurning.ExecutedGodelProduction
#print axioms StrongPerimetralTurning.executeGodelProduction
#print axioms StrongPerimetralTurning.ExecutedGodelProductionOccurrences
#print axioms StrongPerimetralTurning.ExecutedGodelProduction.occurrences
#print axioms StrongPerimetralTurning.CheckedSentenceProof
#print axioms StrongPerimetralTurning.CheckedSentenceEquivalence
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.encodeUnary_injective
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.encodeSentence_injective
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.toGodelSyntax
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.toGodelInterpretation
#print axioms StrongPerimetralTurning.effectiveGodelExecution
/- AXIOM_AUDIT_END -/
