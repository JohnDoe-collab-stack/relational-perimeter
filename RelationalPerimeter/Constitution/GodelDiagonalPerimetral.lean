import StrongPerimetralTurning

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gödel diagonal perimeter layer

This module contains the Gödel-specific constructions formerly embedded in
`StrongPerimetralTurning.lean`.  The public namespace and declaration names
are preserved; only their module ownership is separated from the foundational
strong-perimeter development.
-/

namespace StrongPerimetralTurning

universe uA uB uC uP uV

/-! ## Godel diagonal production and failure of total closure

This section separates the three ingredients that a Godel argument actually
uses.  First, quotation and substitution produce a syntactic fixed point.
Second, soundness and representation of unprovability turn that fixed point
into a true sentence with no proof.  Third, a total closure would identify the
type of truth witnesses with the type of proofs and is therefore rejected.

The generic fixed-point argument is followed first by an extensional
compatibility layer and then by the authoritative executed construction.  The
extensional layer is not used as evidence of internal production: only the
later `ExecutedGodelConstitutiveStep` history starts without a diagonal or a
sentence, produces both in order, and passes the same certified witness to the
perimetral continuation. -/

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

/- These lemmas expose the full diagonal dependency for an arbitrary produced
   sentence.  The fixed point is received explicitly and is then shared by the
   unprovability and truth derivations; no canonical sentence is regenerated. -/
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

def godelTruth_implies_unprovability
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    interpretation.Truth (godelSentence coding unprovabilityFormula) →
      coding.Proof (godelSentence coding unprovabilityFormula) → Empty :=
  interpretation.fixedPointTruth_implies_unprovability _
    (godelSentence_fixedPoint coding unprovabilityFormula)

def godelUnprovability_implies_truth
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    (coding.Proof (godelSentence coding unprovabilityFormula) → Empty) →
      interpretation.Truth (godelSentence coding unprovabilityFormula) :=
  interpretation.fixedPointUnprovability_implies_truth _
    (godelSentence_fixedPoint coding unprovabilityFormula)

def godelSentence_unprovable
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    coding.Proof (godelSentence coding unprovabilityFormula) → Empty :=
  interpretation.fixedPoint_unprovable _
    (godelSentence_fixedPoint coding unprovabilityFormula)

def godelSentence_true
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    interpretation.Truth (godelSentence coding unprovabilityFormula) :=
  interpretation.fixedPoint_true _
    (godelSentence_fixedPoint coding unprovabilityFormula)

end GodelProvabilityInterpretation

structure GodelFirstIncompletenessConclusion
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) where
  sentence : coding.Sentence
  fixedPoint :
    coding.ProvableIff sentence
      (coding.substitute unprovabilityFormula
        (coding.quoteSentence sentence))
  trueWitness : interpretation.Truth sentence
  unprovable : coding.Proof sentence → Empty

def godelFirstIncompleteness
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    GodelFirstIncompletenessConclusion
      coding unprovabilityFormula interpretation :=
  { sentence := godelSentence coding unprovabilityFormula
    fixedPoint := godelSentence_fixedPoint coding unprovabilityFormula
    trueWitness := interpretation.godelSentence_true
    unprovable := interpretation.godelSentence_unprovable }

/-! ### Extensional compatibility layer

This layer records the endpoint equations used by the generic presentation.
Because its initial difference already contains the diagonal and sentence, it
does not establish internal production and is not the final concrete theorem.
That obligation is discharged by the executed history in the next section. -/

structure GodelConstitutiveDifference
    (coding : GodelDiagonalSyntax) where
  sourceFormula : coding.UnaryFormula
  diagonalFormula : coding.UnaryFormula
  sentence : coding.Sentence
  diagonalExact : diagonalFormula = coding.diagonalize sourceFormula
  sentenceExact :
    sentence = coding.substitute diagonalFormula
      (coding.quoteUnary diagonalFormula)

def godelMasterDifference
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula) :
    GodelConstitutiveDifference coding :=
  { sourceFormula := unprovabilityFormula
    diagonalFormula := coding.diagonalize unprovabilityFormula
    sentence := godelSentence coding unprovabilityFormula
    diagonalExact := rfl
    sentenceExact := rfl }

def godelInitialNode
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula) :
    LocalNode Unit Unit (fun _ _ => Unit)
      (GodelConstitutiveDifference coding) (fun _ => Unit) :=
  { explicit := ()
    implicit := ()
    difference := godelMasterDifference coding unprovabilityFormula
    provenance := ()
    internallyCompatible := () }

def godelFinalNode
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula) :
    LocalNode Unit Unit (fun _ _ => Unit)
      (GodelConstitutiveDifference coding) (fun _ => Unit) :=
  godelInitialNode coding unprovabilityFormula

def godelPerimeter
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula) :
    PerimeterSpine (fun _ _ => Unit)
      (godelInitialNode coding unprovabilityFormula) :=
  .advance () (.boundary (godelFinalNode coding unprovabilityFormula))

structure GodelTotalLoop
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) : Type where
  identifiesTruthAndProof :
    interpretation.Truth
      (godelSentence coding unprovabilityFormula) =
    coding.Proof
      (godelSentence coding unprovabilityFormula)

def godelCircularPresentation
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    CircularPresentation :=
  { Explicit := Unit
    Implicit := Unit
    Compatible := fun _ _ => Unit
    Difference := GodelConstitutiveDifference coding
    Provenance := fun _ => Unit
    initialNode := godelInitialNode coding unprovabilityFormula
    perimeter := godelPerimeter coding unprovabilityFormula
    perimeterPositive := .here
    finalJunction := ()
    Endpoint := Type uP
    leftEndpoint := interpretation.Truth
      (godelSentence coding unprovabilityFormula)
    rightEndpoint := coding.Proof
      (godelSentence coding unprovabilityFormula)
    leftPole := fun difference => interpretation.Truth difference.sentence
    rightPole := fun difference => coding.Proof difference.sentence
    initialLeftPole := rfl
    initialRightPole := rfl
    TotalLoop := GodelTotalLoop interpretation
    closeFromIdentification := fun equality =>
      { identifiesTruthAndProof := equality }
    loopContractsInitialDifference := fun loop =>
      loop.identifiesTruthAndProof
    rejectInitialContraction := fun _ equality =>
      Empty.elim
        (interpretation.godelSentence_unprovable
          (Eq.mp equality
            interpretation.godelSentence_true)) }

def godelDiagonalProductionHistory
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    RootedGeneratedHistory
      (godelCircularPresentation coding unprovabilityFormula interpretation) :=
  perimeterDeployment
    (godelCircularPresentation coding unprovabilityFormula interpretation)

def godelConstitutiveHistory
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    RootedGeneratedHistory
      (godelCircularPresentation coding unprovabilityFormula interpretation) :=
  oneStepAfterPerimeter
    (godelCircularPresentation coding unprovabilityFormula interpretation)

def godelProductionPrefixOfConstitutiveHistory
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    PerimeterExtension
      (godelCircularPresentation coding unprovabilityFormula interpretation)
      (godelConstitutiveHistory coding unprovabilityFormula interpretation) :=
  oneStepAfterPerimeter_is_extension
    (godelCircularPresentation coding unprovabilityFormula interpretation)

def godelDiagonalProductionIsStrict
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    StrictConstitutivePrefix
      (rootedHistoryRoot
        (godelCircularPresentation coding unprovabilityFormula interpretation))
      (godelDiagonalProductionHistory
        coding unprovabilityFormula interpretation) := by
  let positiveData := perimeterDeployment_positive
    (godelCircularPresentation coding unprovabilityFormula interpretation)
  exact
    { continuation := positiveData.1
      historyExact :=
        (History.root_append positiveData.1.toHistory).trans
          positiveData.2.down }

def producedGodelFormulaAtBoundaryCode
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    {cursor : PerimeterCursor
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)} →
      BoundaryDifferenceCode
        (godelCircularPresentation
          coding unprovabilityFormula interpretation) cursor →
        coding.UnaryFormula
  | _, .initial _ =>
      (godelCircularPresentation
        coding unprovabilityFormula interpretation).initialNode.difference.sourceFormula
  | _, .afterFormation previous _formation formationIsSuccessor =>
      match formationIsSuccessor with
      | rfl => coding.diagonalize
          (producedGodelFormulaAtBoundaryCode
            coding unprovabilityFormula interpretation previous)

def internallyProducedGodelFormula
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    coding.UnaryFormula :=
  producedGodelFormulaAtBoundaryCode coding unprovabilityFormula
    interpretation
    (godelDiagonalProductionHistory
      coding unprovabilityFormula interpretation).endpoint.2.1.1

theorem internallyProducedGodelFormula_is_diagonal
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    internallyProducedGodelFormula
        coding unprovabilityFormula interpretation =
      coding.diagonalize unprovabilityFormula :=
  rfl

def internallyProducedGodelSentence
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    coding.Sentence :=
  coding.substitute
    (internallyProducedGodelFormula
      coding unprovabilityFormula interpretation)
    (coding.quoteUnary
      (internallyProducedGodelFormula
        coding unprovabilityFormula interpretation))

theorem internallyProducedGodelSentence_is_godelSentence
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    internallyProducedGodelSentence
        coding unprovabilityFormula interpretation =
      godelSentence coding unprovabilityFormula := by
  unfold internallyProducedGodelSentence godelSentence
  rw [internallyProducedGodelFormula_is_diagonal]

def internallyProducedGodelSentence_fixedPoint
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    coding.ProvableIff
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation)
      (coding.substitute unprovabilityFormula
        (coding.quoteSentence
          (internallyProducedGodelSentence
            coding unprovabilityFormula interpretation))) := by
  rw [internallyProducedGodelSentence_is_godelSentence]
  exact godelSentence_fixedPoint coding unprovabilityFormula

def internallyProducedGodelSentence_unprovable
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    coding.Proof
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation) → Empty := by
  rw [internallyProducedGodelSentence_is_godelSentence]
  exact interpretation.godelSentence_unprovable

def internallyProducedGodelSentence_true
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    interpretation.Truth
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation) := by
  rw [internallyProducedGodelSentence_is_godelSentence]
  exact interpretation.godelSentence_true

def internallyProducedGodelSentence_rejectsTruthProofIdentification
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    interpretation.Truth
        (internallyProducedGodelSentence
          coding unprovabilityFormula interpretation) =
      coding.Proof
        (internallyProducedGodelSentence
          coding unprovabilityFormula interpretation) → Empty :=
  fun identification =>
    internallyProducedGodelSentence_unprovable
      coding unprovabilityFormula interpretation
      (Eq.mp identification
        (internallyProducedGodelSentence_true
          coding unprovabilityFormula interpretation))

theorem godelPresentation_initialDifference_is_produced
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    (godelCircularPresentation coding unprovabilityFormula
      interpretation).initialNode.difference.sentence =
      internallyProducedGodelSentence
        coding unprovabilityFormula interpretation :=
  (internallyProducedGodelSentence_is_godelSentence
    coding unprovabilityFormula interpretation).symm

abbrev GodelSemanticCompleteness
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) : Type _ :=
  (sentence : coding.Sentence) →
    interpretation.Truth sentence → coding.Proof sentence

def internallyProducedGodelSentence_refutesCompleteness
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    GodelSemanticCompleteness
      coding unprovabilityFormula interpretation → Empty := by
  intro completeness
  exact internallyProducedGodelSentence_unprovable
    coding unprovabilityFormula interpretation
    (completeness _
      (internallyProducedGodelSentence_true
        coding unprovabilityFormula interpretation))

def internallyGeneratedGodelWitness
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    RootedGeneratedHistory
      (godelCircularPresentation
        coding unprovabilityFormula interpretation) :=
  godelConstitutiveHistory coding unprovabilityFormula interpretation

def internallyGeneratedGodelWitness_locallyExact
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    ExactNonClosingRealization
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation) :=
  oneStepAfterPerimeter_nonClosingRealization
    (godelCircularPresentation coding unprovabilityFormula interpretation)

def internallyGeneratedGodelWitness_is_strict
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    StrictConstitutivePrefix
      (perimeterDeployment
        (godelCircularPresentation
          coding unprovabilityFormula interpretation))
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation) :=
  oneStepAfterPerimeterStrict
    (godelCircularPresentation coding unprovabilityFormula interpretation)

def godelClosureForcesTruthProofIdentification
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (closure :
      CircularClosureMeaning
        (godelCircularPresentation
          coding unprovabilityFormula interpretation)
        (internallyGeneratedGodelWitness
          coding unprovabilityFormula interpretation)) :
    interpretation.Truth
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation) =
    coding.Proof
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation) := by
  rw [internallyProducedGodelSentence_is_godelSentence]
  exact
    (closure
      (internallyGeneratedGodelWitness_is_strict
        coding unprovabilityFormula interpretation)).identifiesTruthAndProof

theorem internallyGeneratedGodelWitness_rejectsGlobalClosure
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    CircularClosureMeaning
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation) → False := by
  intro closure
  exact Empty.elim
    (internallyProducedGodelSentence_rejectsTruthProofIdentification
      coding unprovabilityFormula interpretation
      (godelClosureForcesTruthProofIdentification closure))

theorem internallyGeneratedGodelWitness_rejectsTotalizingRegime
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    CircularRefinement
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation) → False := by
  intro refinement
  exact internallyGeneratedGodelWitness_rejectsGlobalClosure
    coding unprovabilityFormula interpretation
    (circularRefinement_soundSpecification refinement).trajectory

structure GodelDiagonalPerimetralLink
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) where
  firstIncompleteness :
    GodelFirstIncompletenessConclusion
      coding unprovabilityFormula interpretation
  firstIncompletenessSentenceIsProduced :
    firstIncompleteness.sentence =
      internallyProducedGodelSentence
        coding unprovabilityFormula interpretation
  productionIsStrict :
    StrictConstitutivePrefix
      (rootedHistoryRoot
        (godelCircularPresentation
          coding unprovabilityFormula interpretation))
      (godelDiagonalProductionHistory
        coding unprovabilityFormula interpretation)
  productionPrefixIsSameHistory :
    PerimeterExtension
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation)
  closureDifferenceIsProducedSentence :
    (godelCircularPresentation coding unprovabilityFormula
      interpretation).initialNode.difference.sentence =
      internallyProducedGodelSentence
        coding unprovabilityFormula interpretation
  producedFormulaIsDiagonal :
    internallyProducedGodelFormula
        coding unprovabilityFormula interpretation =
      coding.diagonalize unprovabilityFormula
  fixedPoint :
    coding.ProvableIff
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation)
      (coding.substitute unprovabilityFormula
        (coding.quoteSentence
          (internallyProducedGodelSentence
            coding unprovabilityFormula interpretation)))
  sentenceIsTrue :
    interpretation.Truth
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation)
  sentenceHasNoProof :
    coding.Proof
      (internallyProducedGodelSentence
        coding unprovabilityFormula interpretation) → Empty
  producedSentenceRejectsTruthProofIdentification :
    interpretation.Truth
        (internallyProducedGodelSentence
          coding unprovabilityFormula interpretation) =
      coding.Proof
        (internallyProducedGodelSentence
          coding unprovabilityFormula interpretation) → Empty
  rejectsSemanticCompleteness :
    GodelSemanticCompleteness
      coding unprovabilityFormula interpretation → Empty
  closureContinuationLocallyExact :
    ExactNonClosingRealization
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation)
  rejectsGlobalClosure :
    CircularClosureMeaning
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation) → False
  rejectsTotalizingRegime :
    CircularRefinement
      (godelCircularPresentation
        coding unprovabilityFormula interpretation)
      (internallyGeneratedGodelWitness
        coding unprovabilityFormula interpretation) → False

def godelDiagonalPerimetralLink
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    GodelDiagonalPerimetralLink
      coding unprovabilityFormula interpretation :=
  { productionIsStrict :=
      godelDiagonalProductionIsStrict
        coding unprovabilityFormula interpretation
    firstIncompleteness :=
      godelFirstIncompleteness
        coding unprovabilityFormula interpretation
    firstIncompletenessSentenceIsProduced :=
      (internallyProducedGodelSentence_is_godelSentence
        coding unprovabilityFormula interpretation).symm
    productionPrefixIsSameHistory :=
      godelProductionPrefixOfConstitutiveHistory
        coding unprovabilityFormula interpretation
    closureDifferenceIsProducedSentence :=
      godelPresentation_initialDifference_is_produced
        coding unprovabilityFormula interpretation
    producedFormulaIsDiagonal :=
      internallyProducedGodelFormula_is_diagonal
        coding unprovabilityFormula interpretation
    fixedPoint :=
      internallyProducedGodelSentence_fixedPoint
        coding unprovabilityFormula interpretation
    sentenceIsTrue :=
      internallyProducedGodelSentence_true
        coding unprovabilityFormula interpretation
    sentenceHasNoProof :=
      internallyProducedGodelSentence_unprovable
        coding unprovabilityFormula interpretation
    producedSentenceRejectsTruthProofIdentification :=
      internallyProducedGodelSentence_rejectsTruthProofIdentification
        coding unprovabilityFormula interpretation
    rejectsSemanticCompleteness :=
      internallyProducedGodelSentence_refutesCompleteness
        coding unprovabilityFormula interpretation
    closureContinuationLocallyExact :=
      internallyGeneratedGodelWitness_locallyExact
        coding unprovabilityFormula interpretation
    rejectsGlobalClosure :=
      internallyGeneratedGodelWitness_rejectsGlobalClosure
        coding unprovabilityFormula interpretation
    rejectsTotalizingRegime :=
      internallyGeneratedGodelWitness_rejectsTotalizingRegime
        coding unprovabilityFormula interpretation }

/-! ### Executed end-to-end diagonal production

The structures above expose the extensional equations needed to relate the
generic circular presentation to a Godel sentence.  The construction below is
the authoritative constitutive chain: no diagonal formula or sentence occurs
in its received state.  Every later resource contains the exact earlier
resource that produced it, and the perimetral continuation is constructed only
from the resulting certified witness. -/

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
    (production :
      ExecutedGodelSentenceProduction coding sourceFormula) :
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
  production :
    ExecutedGodelSentenceProduction coding unprovabilityFormula
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

structure ExecutedGodelTotalLoop
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    Type where
  identifiesProducedTruthAndProof :
    interpretation.Truth witness.production.sentence =
      coding.Proof witness.production.sentence

/- The standard semantic obstruction needed from the produced sentence is
   only the directed completeness map below.  A total loop is stronger: its
   type identification induces this map, but the two notions are not
   identified.  This factorization makes explicit which part of the circular
   closure is rejected by the Godel witness. -/
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

def ExecutedGodelTotalLoop.toProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (loop : ExecutedGodelTotalLoop witness) :
    ExecutedGodelProducedCompleteness witness :=
  fun truthWitness =>
    Eq.mp loop.identifiesProducedTruthAndProof truthWitness

def ExecutedGodelWitness.rejectProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ExecutedGodelProducedCompleteness witness → Empty :=
  fun completeness => witness.unprovable (completeness witness.trueWitness)

def ExecutedGodelWitness.rejectTotalLoopThroughCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ExecutedGodelTotalLoop witness → Empty :=
  fun loop =>
    witness.rejectProducedCompleteness loop.toProducedCompleteness

def ExecutedGodelWitness.rejectTotalLoop
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ExecutedGodelTotalLoop witness → Empty :=
  witness.rejectTotalLoopThroughCompleteness

def executedGodelNode
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    LocalNode Unit Unit (fun _ _ => Unit)
      (ExecutedGodelWitness coding unprovabilityFormula interpretation)
      (fun candidate => PLift (candidate = witness)) :=
  { explicit := ()
    implicit := ()
    difference := witness
    provenance := ⟨rfl⟩
    internallyCompatible := () }

def executedGodelPerimeter
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    PerimeterSpine (fun _ _ => Unit) (executedGodelNode witness) :=
  .advance () (.boundary (executedGodelNode witness))

def executedGodelCircularPresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    CircularPresentation :=
  { Explicit := Unit
    Implicit := Unit
    Compatible := fun _ _ => Unit
    Difference :=
      ExecutedGodelWitness coding unprovabilityFormula interpretation
    Provenance := fun candidate => PLift (candidate = witness)
    initialNode := executedGodelNode witness
    perimeter := executedGodelPerimeter witness
    perimeterPositive := .here
    finalJunction := ()
    Endpoint := Type uP
    leftEndpoint := interpretation.Truth witness.production.sentence
    rightEndpoint := coding.Proof witness.production.sentence
    leftPole := fun candidate =>
      interpretation.Truth candidate.production.sentence
    rightPole := fun candidate => coding.Proof candidate.production.sentence
    initialLeftPole := rfl
    initialRightPole := rfl
    TotalLoop := ExecutedGodelTotalLoop witness
    closeFromIdentification := fun equality =>
      { identifiesProducedTruthAndProof := equality }
    loopContractsInitialDifference := fun loop =>
      loop.identifiesProducedTruthAndProof
    rejectInitialContraction := fun _ equality =>
      Empty.elim
        (witness.unprovable (Eq.mp equality witness.trueWitness)) }

structure ExecutedGodelRegimeExit
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) where
  witness :
    ExecutedGodelWitness coding unprovabilityFormula interpretation
  continuation :
    RootedGeneratedHistory (executedGodelCircularPresentation witness)
  continuationIsCanonical :
    continuation =
      oneStepAfterPerimeter (executedGodelCircularPresentation witness)
  locallyExact :
    ExactNonClosingRealization
      (executedGodelCircularPresentation witness) continuation
  rejectsGlobalClosure :
    CircularClosureMeaning
      (executedGodelCircularPresentation witness) continuation → False
  rejectsTotalizingRegime :
    CircularRefinement
      (executedGodelCircularPresentation witness) continuation → False

def executeGodelRegimeExit
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ExecutedGodelRegimeExit coding unprovabilityFormula interpretation :=
  { witness := witness
    continuation :=
      oneStepAfterPerimeter (executedGodelCircularPresentation witness)
    continuationIsCanonical := rfl
    locallyExact :=
      oneStepAfterPerimeter_nonClosingRealization
        (executedGodelCircularPresentation witness)
    rejectsGlobalClosure :=
      oneStepAfterPerimeter_notClosureMeaning
        (executedGodelCircularPresentation witness)
    rejectsTotalizingRegime := fun refinement =>
      oneStepAfterPerimeter_notClosureMeaning
        (executedGodelCircularPresentation witness)
        (circularRefinement_soundSpecification refinement).trajectory }

inductive ExecutedGodelConstitutiveState
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) : Type _
  | received : ExecutedGodelConstitutiveState coding
      unprovabilityFormula interpretation
  | diagonalized :
      ExecutedGodelDiagonalProduction coding unprovabilityFormula →
        ExecutedGodelConstitutiveState coding
          unprovabilityFormula interpretation
  | sentenceProduced :
      ExecutedGodelSentenceProduction coding unprovabilityFormula →
        ExecutedGodelConstitutiveState coding
          unprovabilityFormula interpretation
  | witnessProduced :
      ExecutedGodelWitness coding unprovabilityFormula interpretation →
        ExecutedGodelConstitutiveState coding
          unprovabilityFormula interpretation
  | regimeExited :
      ExecutedGodelRegimeExit coding unprovabilityFormula interpretation →
        ExecutedGodelConstitutiveState coding
          unprovabilityFormula interpretation

inductive ExecutedGodelConstitutiveStep
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula} :
    ExecutedGodelConstitutiveState coding unprovabilityFormula interpretation →
      ExecutedGodelConstitutiveState coding unprovabilityFormula interpretation →
        Type _
  | diagonalize :
      ExecutedGodelConstitutiveStep .received
        (.diagonalized
          (executeGodelDiagonalProduction coding unprovabilityFormula))
  | selfApply
      (diagonal :
        ExecutedGodelDiagonalProduction coding unprovabilityFormula) :
      ExecutedGodelConstitutiveStep (.diagonalized diagonal)
        (.sentenceProduced (executeGodelSentenceProduction diagonal))
  | certify
      (production :
        ExecutedGodelSentenceProduction coding unprovabilityFormula) :
      ExecutedGodelConstitutiveStep (.sentenceProduced production)
        (.witnessProduced
          (certifyExecutedGodelWitness coding unprovabilityFormula
            interpretation production))
  | continue
      (witness :
        ExecutedGodelWitness coding unprovabilityFormula interpretation) :
      ExecutedGodelConstitutiveStep (.witnessProduced witness)
        (.regimeExited
          (executeGodelRegimeExit coding unprovabilityFormula
            interpretation witness))

structure ExecutedGodelDiagonalPerimetralLink
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) where
  exit : ExecutedGodelRegimeExit coding unprovabilityFormula interpretation
  history :
    History (@ExecutedGodelConstitutiveStep coding unprovabilityFormula
      interpretation)
      (.received)
      (.regimeExited exit)

def executedGodelDiagonalPerimetralLink
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    ExecutedGodelDiagonalPerimetralLink
      coding unprovabilityFormula interpretation := by
  let diagonal :=
    executeGodelDiagonalProduction coding unprovabilityFormula
  let sentence := executeGodelSentenceProduction diagonal
  let witness :=
    certifyExecutedGodelWitness coding unprovabilityFormula
      interpretation sentence
  let exit :=
    executeGodelRegimeExit coding unprovabilityFormula interpretation witness
  exact
    { exit := exit
      history :=
        .extend
          (.extend
            (.extend
              (.extend .root .diagonalize)
              (.selfApply diagonal))
            (.certify sentence))
          (.continue witness) }

/-! ### Closed arithmetized realization

The concrete realization below does not postulate a `diagonal` formula and
does not define unprovability as the absence of the abstract `Proof` type.
Unary formulas contain ordinary code terms.  Diagonalization is the executable
operation which precomposes every code term with self-substitution.  Proofs are
separately coded derivation trees checked by `NumberedVerifies`; abstract
provability is only the sigma type of a code together with its verification.
Every syntactic category used by quotation has an injective natural-number
Godel numbering. -/

inductive NumberedCodeTerm : Type
  | codeVariable : NumberedCodeTerm
  | selfSubstitution : NumberedCodeTerm → NumberedCodeTerm

namespace NumberedCodeTerm

def godelNumber : NumberedCodeTerm → Nat
  | .codeVariable => 0
  | .selfSubstitution term => Nat.succ term.godelNumber

def decode : Nat → NumberedCodeTerm
  | 0 => .codeVariable
  | Nat.succ number => .selfSubstitution (decode number)

theorem decode_godelNumber (term : NumberedCodeTerm) :
    decode term.godelNumber = term := by
  induction term with
  | codeVariable => rfl
  | selfSubstitution term inductionHypothesis =>
      change NumberedCodeTerm.selfSubstitution (decode term.godelNumber) =
        NumberedCodeTerm.selfSubstitution term
      rw [inductionHypothesis]

theorem godelNumber_injective
    {left right : NumberedCodeTerm}
    (equality : left.godelNumber = right.godelNumber) : left = right := by
  calc
    left = decode left.godelNumber := (decode_godelNumber left).symm
    _ = decode right.godelNumber := congrArg decode equality
    _ = right := decode_godelNumber right

def precomposeSelfSubstitution : NumberedCodeTerm → NumberedCodeTerm
  | .codeVariable => .selfSubstitution .codeVariable
  | .selfSubstitution term =>
      .selfSubstitution term.precomposeSelfSubstitution

end NumberedCodeTerm

inductive NumberedProofAtom : Type
  | verifies : NumberedCodeTerm → NumberedProofAtom

def NumberedProofAtom.godelNumber : NumberedProofAtom → Nat
  | .verifies term => term.godelNumber

def NumberedProofAtom.decode (number : Nat) : NumberedProofAtom :=
  .verifies (NumberedCodeTerm.decode number)

theorem NumberedProofAtom.decode_godelNumber
    (atom : NumberedProofAtom) :
    decode atom.godelNumber = atom := by
  cases atom with
  | verifies term =>
      change NumberedProofAtom.verifies
        (NumberedCodeTerm.decode term.godelNumber) =
          NumberedProofAtom.verifies term
      rw [NumberedCodeTerm.decode_godelNumber]

inductive NumberedProofMatrix : Type
  | falsity : NumberedProofMatrix
  | tautology : NumberedProofMatrix
  | impliesAtomFalse : NumberedProofAtom → NumberedProofMatrix

def NumberedProofMatrix.godelNumber : NumberedProofMatrix → Nat
  | .falsity => 0
  | .tautology => 1
  | .impliesAtomFalse atom => Nat.succ (Nat.succ atom.godelNumber)

def NumberedProofMatrix.decode : Nat → NumberedProofMatrix
  | 0 => .falsity
  | 1 => .tautology
  | Nat.succ (Nat.succ number) =>
      .impliesAtomFalse (NumberedProofAtom.decode number)

theorem NumberedProofMatrix.decode_godelNumber
    (matrix : NumberedProofMatrix) :
    decode matrix.godelNumber = matrix := by
  cases matrix with
  | falsity => rfl
  | tautology => rfl
  | impliesAtomFalse atom =>
      change NumberedProofMatrix.impliesAtomFalse
        (NumberedProofAtom.decode atom.godelNumber) =
          NumberedProofMatrix.impliesAtomFalse atom
      rw [NumberedProofAtom.decode_godelNumber]

inductive NumberedUnaryFormula : Type
  | theoremFormula : NumberedUnaryFormula
  | forallProof : NumberedProofMatrix → NumberedUnaryFormula

def NumberedUnaryFormula.godelNumber : NumberedUnaryFormula → Nat
  | .theoremFormula => 0
  | .forallProof matrix => Nat.succ matrix.godelNumber

def NumberedUnaryFormula.decode : Nat → NumberedUnaryFormula
  | 0 => .theoremFormula
  | Nat.succ number => .forallProof (NumberedProofMatrix.decode number)

theorem NumberedUnaryFormula.decode_godelNumber
    (formula : NumberedUnaryFormula) :
    decode formula.godelNumber = formula := by
  cases formula with
  | theoremFormula => rfl
  | forallProof matrix =>
      change NumberedUnaryFormula.forallProof
        (NumberedProofMatrix.decode matrix.godelNumber) =
          NumberedUnaryFormula.forallProof matrix
      rw [NumberedProofMatrix.decode_godelNumber]

theorem NumberedUnaryFormula.godelNumber_injective
    {left right : NumberedUnaryFormula}
    (equality : left.godelNumber = right.godelNumber) : left = right := by
  calc
    left = decode left.godelNumber := (decode_godelNumber left).symm
    _ = decode right.godelNumber := congrArg decode equality
    _ = right := decode_godelNumber right

def NumberedProofAtom.diagonalize : NumberedProofAtom → NumberedProofAtom
  | .verifies term => .verifies term.precomposeSelfSubstitution

def NumberedProofMatrix.diagonalize :
    NumberedProofMatrix → NumberedProofMatrix
  | .falsity => .falsity
  | .tautology => .tautology
  | .impliesAtomFalse atom => .impliesAtomFalse atom.diagonalize

def NumberedUnaryFormula.diagonalize :
    NumberedUnaryFormula → NumberedUnaryFormula
  | .theoremFormula => .theoremFormula
  | .forallProof matrix => .forallProof matrix.diagonalize

def numberedUnprovabilityFormula : NumberedUnaryFormula :=
  .forallProof
    (.impliesAtomFalse (.verifies .codeVariable))

inductive NumberedSentence : Type
  | apply : NumberedUnaryFormula → Nat → NumberedSentence

def godelDouble : Nat → Nat
  | 0 => 0
  | Nat.succ number => Nat.succ (Nat.succ (godelDouble number))

def godelParity : Nat → Bool
  | 0 => false
  | 1 => true
  | Nat.succ (Nat.succ number) => godelParity number

theorem godelDouble_injective
    {left right : Nat}
    (equality : godelDouble left = godelDouble right) : left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ right => cases equality
  | succ left inductionHypothesis =>
      cases right with
      | zero => cases equality
      | succ right =>
          apply congrArg Nat.succ
          apply inductionHypothesis
          exact Nat.succ.inj (Nat.succ.inj equality)

theorem godelParity_double (number : Nat) :
    godelParity (godelDouble number) = false := by
  induction number with
  | zero => rfl
  | succ number inductionHypothesis => exact inductionHypothesis

theorem godelParity_succ_double (number : Nat) :
    godelParity (Nat.succ (godelDouble number)) = true := by
  induction number with
  | zero => rfl
  | succ number inductionHypothesis => exact inductionHypothesis

def godelPair : Nat → Nat → Nat
  | 0, right => godelDouble right
  | left + 1, right =>
      Nat.succ (godelDouble (godelPair left right))

theorem godelPair_injective
    {leftFirst leftSecond rightFirst rightSecond : Nat}
    (equality :
      godelPair leftFirst leftSecond =
        godelPair rightFirst rightSecond) :
    leftFirst = rightFirst ∧ leftSecond = rightSecond := by
  induction leftFirst generalizing rightFirst with
  | zero =>
      cases rightFirst with
      | zero =>
          constructor
          · rfl
          · exact godelDouble_injective equality
      | succ rightFirst =>
          change godelDouble leftSecond =
            Nat.succ (godelDouble (godelPair rightFirst rightSecond)) at equality
          have parityEquality := congrArg godelParity equality
          rw [godelParity_double, godelParity_succ_double] at parityEquality
          cases parityEquality
  | succ leftFirst inductionHypothesis =>
      cases rightFirst with
      | zero =>
          change Nat.succ (godelDouble (godelPair leftFirst leftSecond)) =
            godelDouble rightSecond at equality
          have parityEquality := congrArg godelParity equality
          rw [godelParity_succ_double, godelParity_double] at parityEquality
          cases parityEquality
      | succ rightFirst =>
          have doubledEquality :
              godelDouble (godelPair leftFirst leftSecond) =
                godelDouble (godelPair rightFirst rightSecond) :=
            Nat.succ.inj equality
          have inner :
              godelPair leftFirst leftSecond =
                godelPair rightFirst rightSecond :=
            godelDouble_injective doubledEquality
          rcases inductionHypothesis inner with
            ⟨firstEquality, secondEquality⟩
          exact ⟨congrArg Nat.succ firstEquality, secondEquality⟩

def NumberedSentence.godelNumber : NumberedSentence → Nat
  | .apply formula argument =>
      godelPair formula.godelNumber argument

theorem NumberedSentence.godelNumber_injective
    {left right : NumberedSentence}
    (equality : left.godelNumber = right.godelNumber) : left = right := by
  cases left with
  | apply leftFormula leftArgument =>
      cases right with
      | apply rightFormula rightArgument =>
          rcases godelPair_injective equality with
            ⟨formulaNumberEquality, argumentEquality⟩
          have formulaEquality : leftFormula = rightFormula :=
            NumberedUnaryFormula.godelNumber_injective
              formulaNumberEquality
          cases formulaEquality
          cases argumentEquality
          rfl

def NumberedCodeTerm.evaluate
    (argument : Nat) : NumberedCodeTerm → Nat
  | .codeVariable => argument
  | .selfSubstitution term =>
      let source :=
        NumberedUnaryFormula.decode (NumberedCodeTerm.evaluate argument term)
      NumberedSentence.godelNumber
        (.apply source source.godelNumber)

theorem NumberedCodeTerm.evaluate_precomposeSelfSubstitution
    (term : NumberedCodeTerm)
    (source : NumberedUnaryFormula) :
    evaluate source.godelNumber term.precomposeSelfSubstitution =
      evaluate
        (NumberedSentence.godelNumber
          (.apply source source.godelNumber)) term := by
  induction term with
  | codeVariable =>
      change
        (NumberedSentence.apply
          (NumberedUnaryFormula.decode source.godelNumber)
          (NumberedUnaryFormula.decode source.godelNumber).godelNumber).godelNumber =
        (NumberedSentence.apply source source.godelNumber).godelNumber
      rw [NumberedUnaryFormula.decode_godelNumber]
  | selfSubstitution term inductionHypothesis =>
      simp only [precomposeSelfSubstitution, evaluate]
      rw [inductionHypothesis]

def numberedSubstitute
    (formula : NumberedUnaryFormula) (code : Nat) : NumberedSentence :=
  .apply formula code

inductive NumberedProvableIff :
    NumberedSentence → NumberedSentence → Type
  | theoremArguments (leftArgument rightArgument : Nat) :
      NumberedProvableIff
        (.apply .theoremFormula leftArgument)
        (.apply .theoremFormula rightArgument)
  | universalFalsityArguments (leftArgument rightArgument : Nat) :
      NumberedProvableIff
        (.apply (.forallProof .falsity) leftArgument)
        (.apply (.forallProof .falsity) rightArgument)
  | universalTautologyArguments (leftArgument rightArgument : Nat) :
      NumberedProvableIff
        (.apply (.forallProof .tautology) leftArgument)
        (.apply (.forallProof .tautology) rightArgument)
  | proofRejectionEvaluation
      (leftTerm rightTerm : NumberedCodeTerm)
      (leftArgument rightArgument : Nat)
      (evaluationExact :
        leftTerm.evaluate leftArgument = rightTerm.evaluate rightArgument) :
      NumberedProvableIff
        (.apply
          (.forallProof
            (.impliesAtomFalse (.verifies leftTerm))) leftArgument)
        (.apply
          (.forallProof
            (.impliesAtomFalse (.verifies rightTerm))) rightArgument)

def numberedDiagonalizeExact
    (target source : NumberedUnaryFormula) :
    NumberedProvableIff
      (numberedSubstitute target.diagonalize source.godelNumber)
      (numberedSubstitute target
        (NumberedSentence.apply source source.godelNumber).godelNumber) := by
  cases target with
  | theoremFormula => exact .theoremArguments _ _
  | forallProof matrix =>
      cases matrix with
      | falsity => exact .universalFalsityArguments _ _
      | tautology => exact .universalTautologyArguments _ _
      | impliesAtomFalse atom =>
          cases atom with
          | verifies term =>
              exact .proofRejectionEvaluation _ _ _ _
                (NumberedCodeTerm.evaluate_precomposeSelfSubstitution
                  term source)

/- The false universal below is used only as a concrete target whose absence
of proofs can be checked from the derivation rules.  Applying the very same
diagonalized unprovability formula used by the Godel sentence to the code of
this formula produces a non-self-referential, provable rejection sentence.
It prevents the proof calculus from excluding either all universal formulas
or the whole diagonalized proof-rejection family by syntax alone. -/

def numberedImpossibleUnaryFormula : NumberedUnaryFormula :=
  .forallProof .falsity

def numberedImpossibleSelfApplication : NumberedSentence :=
  .apply numberedImpossibleUnaryFormula
    numberedImpossibleUnaryFormula.godelNumber

def numberedNonDiagonalRejectionSentence : NumberedSentence :=
  .apply numberedUnprovabilityFormula.diagonalize
    numberedImpossibleUnaryFormula.godelNumber

abbrev NumberedProofCode : Type := Nat

def NumberedProvableIff.godelNumber :
    {left right : NumberedSentence} →
      NumberedProvableIff left right → Nat
  | left, right, _ => godelPair left.godelNumber right.godelNumber

def NumberedProofCode.godelNumber (proofCode : NumberedProofCode) : Nat :=
  proofCode

def NumberedProofCode.theoremIntroduction
    (argument : Nat) : NumberedProofCode :=
  godelPair 0 argument

def NumberedProofCode.universalTautologyIntroduction
    (argument : Nat) : NumberedProofCode :=
  godelPair 3 argument

def NumberedProofCode.impossibleSelfApplicationRejection :
    NumberedProofCode :=
  godelPair 4 numberedImpossibleSelfApplication.godelNumber

def NumberedProofCode.equivalenceForward
    (left right : NumberedSentence)
    (previous : NumberedProofCode) : NumberedProofCode :=
  godelPair 1
    (godelPair
      (godelPair left.godelNumber right.godelNumber)
      previous.godelNumber)

def NumberedProofCode.equivalenceBackward
    (left right : NumberedSentence)
    (previous : NumberedProofCode) : NumberedProofCode :=
  godelPair 2
    (godelPair
      (godelPair left.godelNumber right.godelNumber)
      previous.godelNumber)

inductive NumberedVerifies : NumberedProofCode → NumberedSentence → Type
  | theoremIntroduction (argument : Nat) :
      NumberedVerifies (.theoremIntroduction argument)
        (.apply .theoremFormula argument)
  | universalTautologyIntroduction (argument : Nat) :
      NumberedVerifies (.universalTautologyIntroduction argument)
        (.apply (.forallProof .tautology) argument)
  | impossibleSelfApplicationRejection :
      NumberedVerifies .impossibleSelfApplicationRejection
        numberedNonDiagonalRejectionSentence
  | equivalenceForward
      (left right : NumberedSentence)
      {previous : NumberedProofCode} :
      NumberedProvableIff left right →
      NumberedVerifies previous left →
      NumberedVerifies
        (.equivalenceForward left right previous) right
  | equivalenceBackward
      (left right : NumberedSentence)
      {previous : NumberedProofCode} :
      NumberedProvableIff left right →
      NumberedVerifies previous right →
      NumberedVerifies
        (.equivalenceBackward left right previous) left

theorem NumberedVerifies.notUniversalFalsity
    {proofCode : NumberedProofCode}
    {sentence : NumberedSentence}
    (verification : NumberedVerifies proofCode sentence) :
    (argument : Nat) →
      sentence = .apply (.forallProof .falsity) argument → False := by
  induction verification with
  | theoremIntroduction _ =>
      intro _ equality
      cases equality
  | universalTautologyIntroduction _ =>
      intro _ equality
      cases equality
  | impossibleSelfApplicationRejection =>
      intro _ equality
      cases equality
  | equivalenceForward _ _ derivation _ inductionHypothesis =>
      intro argument equality
      cases derivation with
      | theoremArguments _ _ => cases equality
      | universalFalsityArguments leftArgument _ =>
          exact inductionHypothesis leftArgument rfl
      | universalTautologyArguments _ _ => cases equality
      | proofRejectionEvaluation _ _ _ _ _ => cases equality
  | equivalenceBackward _ _ derivation _ inductionHypothesis =>
      intro argument equality
      cases derivation with
      | theoremArguments _ _ => cases equality
      | universalFalsityArguments _ rightArgument =>
          exact inductionHypothesis rightArgument rfl
      | universalTautologyArguments _ _ => cases equality
      | proofRejectionEvaluation _ _ _ _ _ => cases equality

def NumberedVerifies.impossibleSelfApplication
    {proofCode : NumberedProofCode} :
    NumberedVerifies proofCode numberedImpossibleSelfApplication → Empty :=
  fun verification =>
    False.elim
      (verification.notUniversalFalsity
        numberedImpossibleUnaryFormula.godelNumber rfl)

abbrev NumberedProof (sentence : NumberedSentence) : Type :=
  Σ proofCode : NumberedProofCode, NumberedVerifies proofCode sentence

def numberedProofAtomTruth
    (proofCode : NumberedProofCode)
    (argument : Nat) : NumberedProofAtom → Type
  | .verifies term =>
      Σ sentence : NumberedSentence,
        PLift (sentence.godelNumber = term.evaluate argument) ×
          NumberedVerifies proofCode sentence

def numberedProofMatrixTruth
    (proofCode : NumberedProofCode)
    (argument : Nat) : NumberedProofMatrix → Type
  | .falsity => Empty
  | .tautology => Unit
  | .impliesAtomFalse atom =>
      numberedProofAtomTruth proofCode argument atom → Empty

def numberedFormulaTruth : NumberedUnaryFormula → Nat → Type
  | .theoremFormula, _ => Unit
  | .forallProof matrix, argument =>
      (proofCode : NumberedProofCode) →
        numberedProofMatrixTruth proofCode argument matrix

def numberedTruth : NumberedSentence → Type
  | .apply formula argument => numberedFormulaTruth formula argument

def NumberedProvableIff.truthForward
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    numberedTruth left → numberedTruth right := by
  cases derivation with
  | theoremArguments _ _ => exact fun _ => ()
  | universalFalsityArguments _ _ => exact fun truthWitness => truthWitness
  | universalTautologyArguments _ _ => exact fun _ _ => ()
  | proofRejectionEvaluation leftTerm rightTerm
      leftArgument rightArgument evaluationExact =>
      intro truthWitness proofCode atomWitness
      rcases atomWitness with
        ⟨sentence, ⟨numberEquality⟩, verification⟩
      exact truthWitness proofCode
        ⟨sentence,
          ⟨numberEquality.trans evaluationExact.symm⟩,
          verification⟩

def NumberedProvableIff.truthBackward
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    numberedTruth right → numberedTruth left := by
  cases derivation with
  | theoremArguments _ _ => exact fun _ => ()
  | universalFalsityArguments _ _ => exact fun truthWitness => truthWitness
  | universalTautologyArguments _ _ => exact fun _ _ => ()
  | proofRejectionEvaluation leftTerm rightTerm
      leftArgument rightArgument evaluationExact =>
      intro truthWitness proofCode atomWitness
      rcases atomWitness with
        ⟨sentence, ⟨numberEquality⟩, verification⟩
      exact truthWitness proofCode
        ⟨sentence,
          ⟨numberEquality.trans evaluationExact⟩,
          verification⟩

def NumberedVerifies.sound
    {proofCode : NumberedProofCode}
    {sentence : NumberedSentence} :
    NumberedVerifies proofCode sentence → numberedTruth sentence
  | .theoremIntroduction _ => ()
  | .universalTautologyIntroduction _ => fun _ => ()
  | .impossibleSelfApplicationRejection => by
      intro proofCode atomWitness
      rcases atomWitness with
        ⟨candidate, ⟨codeEquality⟩, verification⟩
      have evaluatedCode :
          (NumberedCodeTerm.selfSubstitution
            .codeVariable).evaluate
              numberedImpossibleUnaryFormula.godelNumber =
            numberedImpossibleSelfApplication.godelNumber := by
        change
          (NumberedSentence.apply
            (NumberedUnaryFormula.decode
              numberedImpossibleUnaryFormula.godelNumber)
            (NumberedUnaryFormula.decode
              numberedImpossibleUnaryFormula.godelNumber).godelNumber).godelNumber =
          numberedImpossibleSelfApplication.godelNumber
        rw [NumberedUnaryFormula.decode_godelNumber]
        rfl
      have candidateCode :
          candidate.godelNumber =
            numberedImpossibleSelfApplication.godelNumber :=
        codeEquality.trans evaluatedCode
      have candidateEquality :
          candidate = numberedImpossibleSelfApplication :=
        NumberedSentence.godelNumber_injective candidateCode
      cases candidateEquality
      exact verification.impossibleSelfApplication
  | .equivalenceForward left right derivation verification =>
      derivation.truthForward verification.sound
  | .equivalenceBackward left right derivation verification =>
      derivation.truthBackward verification.sound

def NumberedProof.sound
    {sentence : NumberedSentence}
    (proof : NumberedProof sentence) : numberedTruth sentence :=
  proof.2.sound

def numberedUniversalTautologyProof
    (argument : Nat) :
    NumberedProof (.apply (.forallProof .tautology) argument) :=
  ⟨.universalTautologyIntroduction argument,
    .universalTautologyIntroduction argument⟩

def numberedNonDiagonalRejectionProof :
    NumberedProof numberedNonDiagonalRejectionSentence :=
  ⟨.impossibleSelfApplicationRejection,
    .impossibleSelfApplicationRejection⟩

def numberedUniversalFormulaExclusionRejected :
    ((matrix : NumberedProofMatrix) →
      (argument : Nat) →
        NumberedProof (.apply (.forallProof matrix) argument) → Empty) →
      Empty :=
  fun exclusion =>
    exclusion .tautology 0 (numberedUniversalTautologyProof 0)

def numberedDiagonalizedFormulaExclusionRejected :
    ((argument : Nat) →
      NumberedProof
        (.apply numberedUnprovabilityFormula.diagonalize argument) → Empty) →
      Empty :=
  fun exclusion =>
    exclusion numberedImpossibleUnaryFormula.godelNumber
      numberedNonDiagonalRejectionProof

def numberedProofForward
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    NumberedProof left → NumberedProof right :=
  fun proof =>
    ⟨.equivalenceForward left right proof.1,
      .equivalenceForward left right derivation proof.2⟩

def numberedProofBackward
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    NumberedProof right → NumberedProof left :=
  fun proof =>
    ⟨.equivalenceBackward left right proof.1,
      .equivalenceBackward left right derivation proof.2⟩

def numberedGodelSyntax : GodelDiagonalSyntax :=
  { Code := Nat
    UnaryFormula := NumberedUnaryFormula
    Sentence := NumberedSentence
    Proof := NumberedProof
    ProvableIff := NumberedProvableIff
    quoteUnary := NumberedUnaryFormula.godelNumber
    quoteSentence := NumberedSentence.godelNumber
    substitute := numberedSubstitute
    diagonalize := NumberedUnaryFormula.diagonalize
    diagonalizeExact := numberedDiagonalizeExact
    proofForward := numberedProofForward
    proofBackward := numberedProofBackward }

def numberedGodelInterpretation :
    GodelProvabilityInterpretation
      numberedGodelSyntax numberedUnprovabilityFormula :=
  { Truth := numberedTruth
    proofSound := NumberedProof.sound
    provableIffTruthForward := NumberedProvableIff.truthForward
    provableIffTruthBackward := NumberedProvableIff.truthBackward
    representsUnprovabilityForward := by
      intro sentence truthWitness proof
      exact truthWitness proof.1
        ⟨sentence, ⟨rfl⟩, proof.2⟩
    representsUnprovabilityBackward := by
      intro sentence noProof proofCode atomWitness
      rcases atomWitness with
        ⟨candidate, ⟨codeEquality⟩, verification⟩
      have candidateEquality : candidate = sentence :=
        NumberedSentence.godelNumber_injective codeEquality
      cases candidateEquality
      exact noProof ⟨proofCode, verification⟩ }

abbrev numberedExecutedDiagonalProduction :
    ExecutedGodelDiagonalProduction
      numberedGodelSyntax numberedUnprovabilityFormula :=
  executeGodelDiagonalProduction
    numberedGodelSyntax numberedUnprovabilityFormula

abbrev numberedExecutedSentenceProduction :
    ExecutedGodelSentenceProduction
      numberedGodelSyntax numberedUnprovabilityFormula :=
  executeGodelSentenceProduction numberedExecutedDiagonalProduction

abbrev numberedInternallyProducedGodelSentence : NumberedSentence :=
  numberedExecutedSentenceProduction.sentence

abbrev numberedExecutedGodelWitness :
    ExecutedGodelWitness
      numberedGodelSyntax numberedUnprovabilityFormula
        numberedGodelInterpretation :=
  certifyExecutedGodelWitness
    numberedGodelSyntax numberedUnprovabilityFormula
      numberedGodelInterpretation numberedExecutedSentenceProduction

structure NumberedDiagonalCollision
    (proof : NumberedProof numberedInternallyProducedGodelSentence) where
  truthFromSoundness :
    numberedTruth numberedInternallyProducedGodelSentence
  noProofFromProducedFixedPoint :
    NumberedProof numberedInternallyProducedGodelSentence → Empty

def numberedDiagonalCollision
    (proof : NumberedProof numberedInternallyProducedGodelSentence) :
    NumberedDiagonalCollision proof :=
  let truthFromSoundness := proof.sound
  let representedUnprovability :=
    numberedGodelInterpretation.provableIffTruthForward
      numberedExecutedGodelWitness.fixedPoint truthFromSoundness
  { truthFromSoundness := truthFromSoundness
    noProofFromProducedFixedPoint :=
      numberedGodelInterpretation.representsUnprovabilityForward
        numberedInternallyProducedGodelSentence representedUnprovability }

def numberedInternallyProducedGodelSentence_unprovableByDiagonal :
    NumberedProof numberedInternallyProducedGodelSentence → Empty :=
  fun proof =>
    (numberedDiagonalCollision proof).noProofFromProducedFixedPoint proof

def numberedInternallyProducedGodelSentence_true :
    numberedTruth numberedInternallyProducedGodelSentence :=
  numberedExecutedGodelWitness.trueWitness

def numberedInternallyProducedGodelSentence_unprovable :
    NumberedProof numberedInternallyProducedGodelSentence → Empty :=
  numberedInternallyProducedGodelSentence_unprovableByDiagonal

def concreteGodelFirstIncompleteness :
    GodelFirstIncompletenessConclusion
      numberedGodelSyntax numberedUnprovabilityFormula
        numberedGodelInterpretation :=
  { sentence := numberedExecutedGodelWitness.production.sentence
    fixedPoint := numberedExecutedGodelWitness.fixedPoint
    trueWitness := numberedExecutedGodelWitness.trueWitness
    unprovable := numberedExecutedGodelWitness.unprovable }

structure ConcreteGodelDiagonalPerimetralConclusion where
  execution :
    ExecutedGodelDiagonalPerimetralLink
      numberedGodelSyntax numberedUnprovabilityFormula
        numberedGodelInterpretation
  unprovabilityFormulaIsComposed :
    numberedUnprovabilityFormula =
      .forallProof
        (.impliesAtomFalse (.verifies .codeVariable))
  proofCalculusAdmitsUniversalFormula :
    NumberedProof (.apply (.forallProof .tautology) 0)
  proofCalculusAdmitsSameDiagonalizedFormula :
    NumberedProof numberedNonDiagonalRejectionSentence
  rejectsUniversalFormulaExclusion :
    ((matrix : NumberedProofMatrix) →
      (argument : Nat) →
        NumberedProof (.apply (.forallProof matrix) argument) → Empty) →
      Empty
  rejectsDiagonalizedFormulaExclusion :
    ((argument : Nat) →
      NumberedProof
        (.apply numberedUnprovabilityFormula.diagonalize argument) → Empty) →
      Empty
  producedFixedPoint :
    NumberedProvableIff execution.exit.witness.production.sentence
      (numberedSubstitute numberedUnprovabilityFormula
        execution.exit.witness.production.sentence.godelNumber)
  producedSentenceIsTrue :
    numberedTruth execution.exit.witness.production.sentence
  producedSentenceHasNoProof :
    NumberedProof execution.exit.witness.production.sentence → Empty
  producedCollisionUsesSoundnessAndFixedPoint :
    (proof : NumberedProof numberedInternallyProducedGodelSentence) →
      NumberedDiagonalCollision proof
  producedWitnessRejectsTotalLoop :
    ExecutedGodelTotalLoop execution.exit.witness → Empty
  continuationConsumesProducedWitness :
    execution.exit.continuation =
      oneStepAfterPerimeter
        (executedGodelCircularPresentation execution.exit.witness)
  continuationRejectsGlobalClosure :
    CircularClosureMeaning
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation → False
  continuationRejectsTotalizingRegime :
    CircularRefinement
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation → False

def concreteGodelDiagonalPerimetralTheorem :
    ConcreteGodelDiagonalPerimetralConclusion := by
  let execution :=
    executedGodelDiagonalPerimetralLink
      numberedGodelSyntax numberedUnprovabilityFormula
        numberedGodelInterpretation
  exact
    { execution := execution
      unprovabilityFormulaIsComposed := rfl
      proofCalculusAdmitsUniversalFormula :=
        numberedUniversalTautologyProof 0
      proofCalculusAdmitsSameDiagonalizedFormula :=
        numberedNonDiagonalRejectionProof
      rejectsUniversalFormulaExclusion :=
        numberedUniversalFormulaExclusionRejected
      rejectsDiagonalizedFormulaExclusion :=
        numberedDiagonalizedFormulaExclusionRejected
      producedFixedPoint := execution.exit.witness.fixedPoint
      producedSentenceIsTrue := execution.exit.witness.trueWitness
      producedSentenceHasNoProof :=
        numberedInternallyProducedGodelSentence_unprovableByDiagonal
      producedCollisionUsesSoundnessAndFixedPoint :=
        numberedDiagonalCollision
      producedWitnessRejectsTotalLoop :=
        execution.exit.witness.rejectTotalLoop
      continuationConsumesProducedWitness :=
        execution.exit.continuationIsCanonical
      continuationRejectsGlobalClosure :=
        execution.exit.rejectsGlobalClosure
      continuationRejectsTotalizingRegime :=
        execution.exit.rejectsTotalizingRegime }

/-! ### Uniform proof admission: the diagonal obstruction is semantic

The closed verifier above remains useful as a small executable instance, but
its constructors can also be inspected to obtain a separate syntactic
non-derivability argument.  The authoritative construction below removes that
possible shortcut.  A seed relation may accept *any* numbered sentence.  The
uniform verifier merely closes those admissions under the same executable
equivalence rules.  In particular, a total seed admits the produced Godel
sentence, so neither its syntax nor the verifier shape excludes it.

Correction is a separate datum.  The diagonal argument proves that every
correct seed rejects the produced sentence and, conversely, that the total
seed cannot be correct.  A concrete kernel seed closes the correction
obligation without naming the Godel sentence.  It does explicitly accept the
distinct `numberedNonDiagonalRejectionSentence` through
`impossibleSelfApplicationRejection`; this positive inhabitant is what rules
out a blanket syntactic exclusion of the proof-rejection family.  The same
witness obtained from that corrected uniform verifier is then passed to the
perimetral continuation.

TODO(arithmetic-generality): extend this concrete syntax-and-semantics result
to the usual general scope of Godel incompleteness for effectively presented
arithmetical theories, including an internal arithmetization of derivations
and the required representability hypotheses.  The uniform sound-seed result
below does not by itself discharge that obligation. -/

abbrev UniformNumberedSeed : Type 1 :=
  NumberedProofCode → NumberedSentence → Type

inductive UniformNumberedVerifies
    (Seed : UniformNumberedSeed) :
    NumberedProofCode → NumberedSentence → Type
  | admitted
      {seedCode : NumberedProofCode}
      {sentence : NumberedSentence} :
      Seed seedCode sentence →
        UniformNumberedVerifies Seed
          (godelPair 5 seedCode) sentence
  | equivalenceForward
      (left right : NumberedSentence)
      {previous : NumberedProofCode} :
      NumberedProvableIff left right →
      UniformNumberedVerifies Seed previous left →
      UniformNumberedVerifies Seed
        (.equivalenceForward left right previous) right
  | equivalenceBackward
      (left right : NumberedSentence)
      {previous : NumberedProofCode} :
      NumberedProvableIff left right →
      UniformNumberedVerifies Seed previous right →
      UniformNumberedVerifies Seed
        (.equivalenceBackward left right previous) left

abbrev UniformNumberedProof
    (Seed : UniformNumberedSeed)
    (sentence : NumberedSentence) : Type :=
  Σ proofCode : NumberedProofCode,
    UniformNumberedVerifies Seed proofCode sentence

def uniformNumberedProofAtomTruth
    (Seed : UniformNumberedSeed)
    (proofCode : NumberedProofCode)
    (argument : Nat) : NumberedProofAtom → Type
  | .verifies term =>
      Σ sentence : NumberedSentence,
        PLift (sentence.godelNumber = term.evaluate argument) ×
          UniformNumberedVerifies Seed proofCode sentence

def uniformNumberedProofMatrixTruth
    (Seed : UniformNumberedSeed)
    (proofCode : NumberedProofCode)
    (argument : Nat) : NumberedProofMatrix → Type
  | .falsity => Empty
  | .tautology => Unit
  | .impliesAtomFalse atom =>
      uniformNumberedProofAtomTruth Seed proofCode argument atom → Empty

def uniformNumberedTruth
    (Seed : UniformNumberedSeed) : NumberedUnaryFormula → Nat → Type
  | .theoremFormula, _ => Unit
  | .forallProof matrix, argument =>
      (proofCode : NumberedProofCode) →
        uniformNumberedProofMatrixTruth Seed proofCode argument matrix

def uniformNumberedSentenceTruth
    (Seed : UniformNumberedSeed) : NumberedSentence → Type
  | .apply formula argument => uniformNumberedTruth Seed formula argument

abbrev UniformNumberedSeedSound
    (Seed : UniformNumberedSeed) : Type :=
  {proofCode : NumberedProofCode} →
    {sentence : NumberedSentence} →
      Seed proofCode sentence → uniformNumberedSentenceTruth Seed sentence

def uniformNumberedTruthForward
    {Seed : UniformNumberedSeed}
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    uniformNumberedSentenceTruth Seed left →
      uniformNumberedSentenceTruth Seed right := by
  cases derivation with
  | theoremArguments _ _ => exact fun _ => ()
  | universalFalsityArguments _ _ => exact fun truthWitness => truthWitness
  | universalTautologyArguments _ _ => exact fun _ _ => ()
  | proofRejectionEvaluation leftTerm rightTerm
      leftArgument rightArgument evaluationExact =>
      intro truthWitness proofCode atomWitness
      rcases atomWitness with
        ⟨sentence, ⟨numberEquality⟩, verification⟩
      exact truthWitness proofCode
        ⟨sentence,
          ⟨numberEquality.trans evaluationExact.symm⟩,
          verification⟩

def uniformNumberedTruthBackward
    {Seed : UniformNumberedSeed}
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    uniformNumberedSentenceTruth Seed right →
      uniformNumberedSentenceTruth Seed left := by
  cases derivation with
  | theoremArguments _ _ => exact fun _ => ()
  | universalFalsityArguments _ _ => exact fun truthWitness => truthWitness
  | universalTautologyArguments _ _ => exact fun _ _ => ()
  | proofRejectionEvaluation leftTerm rightTerm
      leftArgument rightArgument evaluationExact =>
      intro truthWitness proofCode atomWitness
      rcases atomWitness with
        ⟨sentence, ⟨numberEquality⟩, verification⟩
      exact truthWitness proofCode
        ⟨sentence,
          ⟨numberEquality.trans evaluationExact⟩,
          verification⟩

def UniformNumberedVerifies.sound
    {Seed : UniformNumberedSeed}
    (seedSound : UniformNumberedSeedSound Seed)
    {proofCode : NumberedProofCode}
    {sentence : NumberedSentence} :
    UniformNumberedVerifies Seed proofCode sentence →
      uniformNumberedSentenceTruth Seed sentence
  | .admitted admission => seedSound admission
  | .equivalenceForward _ _ derivation verification =>
      uniformNumberedTruthForward derivation (verification.sound seedSound)
  | .equivalenceBackward _ _ derivation verification =>
      uniformNumberedTruthBackward derivation (verification.sound seedSound)

def UniformNumberedProof.sound
    {Seed : UniformNumberedSeed}
    (seedSound : UniformNumberedSeedSound Seed)
    {sentence : NumberedSentence}
    (proof : UniformNumberedProof Seed sentence) :
    uniformNumberedSentenceTruth Seed sentence :=
  proof.2.sound seedSound

def uniformNumberedProofForward
    {Seed : UniformNumberedSeed}
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    UniformNumberedProof Seed left → UniformNumberedProof Seed right :=
  fun proof =>
    ⟨.equivalenceForward left right proof.1,
      .equivalenceForward left right derivation proof.2⟩

def uniformNumberedProofBackward
    {Seed : UniformNumberedSeed}
    {left right : NumberedSentence}
    (derivation : NumberedProvableIff left right) :
    UniformNumberedProof Seed right → UniformNumberedProof Seed left :=
  fun proof =>
    ⟨.equivalenceBackward left right proof.1,
      .equivalenceBackward left right derivation proof.2⟩

def uniformNumberedGodelSyntax
    (Seed : UniformNumberedSeed) : GodelDiagonalSyntax :=
  { Code := Nat
    UnaryFormula := NumberedUnaryFormula
    Sentence := NumberedSentence
    Proof := UniformNumberedProof Seed
    ProvableIff := NumberedProvableIff
    quoteUnary := NumberedUnaryFormula.godelNumber
    quoteSentence := NumberedSentence.godelNumber
    substitute := numberedSubstitute
    diagonalize := NumberedUnaryFormula.diagonalize
    diagonalizeExact := numberedDiagonalizeExact
    proofForward := uniformNumberedProofForward
    proofBackward := uniformNumberedProofBackward }

def uniformNumberedGodelInterpretation
    (Seed : UniformNumberedSeed)
    (seedSound : UniformNumberedSeedSound Seed) :
    GodelProvabilityInterpretation
      (uniformNumberedGodelSyntax Seed) numberedUnprovabilityFormula :=
  { Truth := uniformNumberedSentenceTruth Seed
    proofSound := UniformNumberedProof.sound seedSound
    provableIffTruthForward := uniformNumberedTruthForward
    provableIffTruthBackward := uniformNumberedTruthBackward
    representsUnprovabilityForward := by
      intro sentence truthWitness proof
      exact truthWitness proof.1
        ⟨sentence, ⟨rfl⟩, proof.2⟩
    representsUnprovabilityBackward := by
      intro sentence noProof proofCode atomWitness
      rcases atomWitness with
        ⟨candidate, ⟨codeEquality⟩, verification⟩
      have candidateEquality : candidate = sentence :=
        NumberedSentence.godelNumber_injective codeEquality
      cases candidateEquality
      exact noProof ⟨proofCode, verification⟩ }

def everySoundUniformSeedRejectsItsGodelSentence
    (Seed : UniformNumberedSeed)
    (seedSound : UniformNumberedSeedSound Seed) :
    UniformNumberedProof Seed
      (godelSentence
        (uniformNumberedGodelSyntax Seed)
        numberedUnprovabilityFormula) → Empty :=
  (uniformNumberedGodelInterpretation Seed seedSound).godelSentence_unprovable

def UniformTotalSeed
    (_ : NumberedProofCode) (_ : NumberedSentence) : Type :=
  Unit

def uniformTotalSeedAdmitsGodelSentence :
    UniformNumberedProof UniformTotalSeed
      (godelSentence
        (uniformNumberedGodelSyntax UniformTotalSeed)
        numberedUnprovabilityFormula) :=
  ⟨godelPair 5 0, .admitted ()⟩

/- The total seed is already unsound independently of diagonalization: it
   admits an instance whose semantics is the empty type for every proof code.
   This witness is kept separate from the diagonal argument so that it cannot
   be used to explain the Godel obstruction. -/
def uniformTotalSeedAdmitsUniversalFalsity :
    UniformNumberedProof UniformTotalSeed
      (.apply (.forallProof .falsity) 0) :=
  ⟨godelPair 5 0, .admitted ()⟩

def uniformTotalSeedCannotBeSoundWithoutDiagonal :
    UniformNumberedSeedSound UniformTotalSeed → Empty :=
  fun seedSound =>
    (uniformTotalSeedAdmitsUniversalFalsity.sound seedSound) 0

def uniformTotalSeedCannotBeSound :
    UniformNumberedSeedSound UniformTotalSeed → Empty :=
  fun seedSound =>
    everySoundUniformSeedRejectsItsGodelSentence
      UniformTotalSeed seedSound uniformTotalSeedAdmitsGodelSentence

def uniformVerifierExclusionWithoutSoundnessRejected :
    ((Seed : UniformNumberedSeed) →
      UniformNumberedProof Seed
        (godelSentence
          (uniformNumberedGodelSyntax Seed)
          numberedUnprovabilityFormula) → Empty) → Empty :=
  fun allegedStructuralExclusion =>
    allegedStructuralExclusion UniformTotalSeed
      uniformTotalSeedAdmitsGodelSentence

theorem uniformNumberedGodelSentence_seedIndependent
    (leftSeed rightSeed : UniformNumberedSeed) :
    godelSentence
        (uniformNumberedGodelSyntax leftSeed)
        numberedUnprovabilityFormula =
      godelSentence
        (uniformNumberedGodelSyntax rightSeed)
        numberedUnprovabilityFormula :=
  rfl

abbrev uniformCanonicalGodelSentence : NumberedSentence :=
  godelSentence
    (uniformNumberedGodelSyntax UniformTotalSeed)
    numberedUnprovabilityFormula

/- This seed has exactly one admissible sentence: the common diagonal
   sentence.  It has no unrelated false admission from which unsoundness could
   be obtained. -/
def UniformGodelOnlySeed
    (_ : NumberedProofCode) (sentence : NumberedSentence) : Type :=
  PLift (sentence = uniformCanonicalGodelSentence)

def UniformGodelOnlySeed.admittedSentenceExact
    {proofCode : NumberedProofCode}
    {sentence : NumberedSentence}
    (admission : UniformGodelOnlySeed proofCode sentence) :
    sentence = uniformCanonicalGodelSentence :=
  admission.down

def uniformGodelOnlySeedAdmitsItsGodelSentence :
    UniformNumberedProof UniformGodelOnlySeed
      (godelSentence
        (uniformNumberedGodelSyntax UniformGodelOnlySeed)
        numberedUnprovabilityFormula) :=
  ⟨godelPair 5 0,
    .admitted
      ⟨uniformNumberedGodelSentence_seedIndependent
        UniformGodelOnlySeed UniformTotalSeed⟩⟩

def uniformGodelOnlySeedCannotBeSound :
    UniformNumberedSeedSound UniformGodelOnlySeed → Empty :=
  fun seedSound =>
    everySoundUniformSeedRejectsItsGodelSentence
      UniformGodelOnlySeed seedSound
        uniformGodelOnlySeedAdmitsItsGodelSentence

inductive UniformKernelSeed :
    NumberedProofCode → NumberedSentence → Type
  | theoremIntroduction (argument : Nat) :
      UniformKernelSeed (.theoremIntroduction argument)
        (.apply .theoremFormula argument)
  | universalTautologyIntroduction (argument : Nat) :
      UniformKernelSeed (.universalTautologyIntroduction argument)
        (.apply (.forallProof .tautology) argument)
  | impossibleSelfApplicationRejection :
      UniformKernelSeed .impossibleSelfApplicationRejection
        numberedNonDiagonalRejectionSentence

theorem UniformNumberedVerifies.kernelNotUniversalFalsity
    {proofCode : NumberedProofCode}
    {sentence : NumberedSentence}
    (verification :
      UniformNumberedVerifies UniformKernelSeed proofCode sentence) :
    (argument : Nat) →
      sentence = .apply (.forallProof .falsity) argument → False := by
  induction verification with
  | admitted admission =>
      cases admission with
      | theoremIntroduction _ =>
          intro _ equality
          cases equality
      | universalTautologyIntroduction _ =>
          intro _ equality
          cases equality
      | impossibleSelfApplicationRejection =>
          intro _ equality
          cases equality
  | equivalenceForward _ _ derivation _ inductionHypothesis =>
      intro argument equality
      cases derivation with
      | theoremArguments _ _ => cases equality
      | universalFalsityArguments leftArgument _ =>
          exact inductionHypothesis leftArgument rfl
      | universalTautologyArguments _ _ => cases equality
      | proofRejectionEvaluation _ _ _ _ _ => cases equality
  | equivalenceBackward _ _ derivation _ inductionHypothesis =>
      intro argument equality
      cases derivation with
      | theoremArguments _ _ => cases equality
      | universalFalsityArguments _ rightArgument =>
          exact inductionHypothesis rightArgument rfl
      | universalTautologyArguments _ _ => cases equality
      | proofRejectionEvaluation _ _ _ _ _ => cases equality

def UniformNumberedVerifies.kernelImpossibleSelfApplication
    {proofCode : NumberedProofCode} :
    UniformNumberedVerifies UniformKernelSeed proofCode
      numberedImpossibleSelfApplication → Empty :=
  fun verification =>
    False.elim
      (verification.kernelNotUniversalFalsity
        numberedImpossibleUnaryFormula.godelNumber rfl)

def uniformKernelSeedSound :
    UniformNumberedSeedSound UniformKernelSeed := by
  intro proofCode sentence admission
  cases admission with
  | theoremIntroduction _ => exact ()
  | universalTautologyIntroduction _ => exact fun _ => ()
  | impossibleSelfApplicationRejection =>
      intro candidateProofCode atomWitness
      rcases atomWitness with
        ⟨candidate, ⟨codeEquality⟩, verification⟩
      have evaluatedCode :
          (NumberedCodeTerm.selfSubstitution
            .codeVariable).evaluate
              numberedImpossibleUnaryFormula.godelNumber =
            numberedImpossibleSelfApplication.godelNumber := by
        change
          (NumberedSentence.apply
            (NumberedUnaryFormula.decode
              numberedImpossibleUnaryFormula.godelNumber)
            (NumberedUnaryFormula.decode
              numberedImpossibleUnaryFormula.godelNumber).godelNumber).godelNumber =
          numberedImpossibleSelfApplication.godelNumber
        rw [NumberedUnaryFormula.decode_godelNumber]
        rfl
      have candidateCode :
          candidate.godelNumber =
            numberedImpossibleSelfApplication.godelNumber :=
        codeEquality.trans evaluatedCode
      have candidateEquality :
          candidate = numberedImpossibleSelfApplication :=
        NumberedSentence.godelNumber_injective candidateCode
      cases candidateEquality
      exact verification.kernelImpossibleSelfApplication

def uniformKernelNonDiagonalRejectionProof :
    UniformNumberedProof UniformKernelSeed
      numberedNonDiagonalRejectionSentence :=
  ⟨godelPair 5 NumberedProofCode.impossibleSelfApplicationRejection,
    .admitted .impossibleSelfApplicationRejection⟩

def uniformKernelProofRejectionFamilyIsInhabited :
    Σ argument : Nat,
      UniformNumberedProof UniformKernelSeed
        (.apply numberedUnprovabilityFormula.diagonalize argument) :=
  ⟨numberedImpossibleUnaryFormula.godelNumber,
    uniformKernelNonDiagonalRejectionProof⟩

def uniformKernelProofRejectionFamilyExclusionRejected :
    ((argument : Nat) →
      UniformNumberedProof UniformKernelSeed
        (.apply numberedUnprovabilityFormula.diagonalize argument) →
          Empty) → Empty :=
  fun allegedFamilyExclusion =>
    allegedFamilyExclusion
      numberedImpossibleUnaryFormula.godelNumber
      uniformKernelNonDiagonalRejectionProof

abbrev uniformKernelGodelSyntax : GodelDiagonalSyntax :=
  uniformNumberedGodelSyntax UniformKernelSeed

abbrev uniformKernelGodelInterpretation :
    GodelProvabilityInterpretation
      uniformKernelGodelSyntax numberedUnprovabilityFormula :=
  uniformNumberedGodelInterpretation
    UniformKernelSeed uniformKernelSeedSound

abbrev uniformKernelExecutedGodelLink :
    ExecutedGodelDiagonalPerimetralLink
      uniformKernelGodelSyntax numberedUnprovabilityFormula
        uniformKernelGodelInterpretation :=
  executedGodelDiagonalPerimetralLink
    uniformKernelGodelSyntax numberedUnprovabilityFormula
      uniformKernelGodelInterpretation

theorem uniformKernelProducedSentence_is_proofRejectionFamily :
    uniformKernelExecutedGodelLink.exit.witness.production.sentence =
      .apply numberedUnprovabilityFormula.diagonalize
        numberedUnprovabilityFormula.diagonalize.godelNumber := by
  rw [uniformKernelExecutedGodelLink.exit.witness.production
    |>.sentence_is_godelSentence]
  rfl

theorem uniformKernelProducedSentence_is_totalSeedGodelSentence :
    uniformKernelExecutedGodelLink.exit.witness.production.sentence =
      godelSentence
        (uniformNumberedGodelSyntax UniformTotalSeed)
        numberedUnprovabilityFormula :=
  uniformKernelExecutedGodelLink.exit.witness.production
    |>.sentence_is_godelSentence
    |>.trans
      (uniformNumberedGodelSentence_seedIndependent
        UniformKernelSeed UniformTotalSeed)

def uniformTotalSeedAdmitsKernelProducedSentence :
    UniformNumberedProof UniformTotalSeed
      uniformKernelExecutedGodelLink.exit.witness.production.sentence :=
  Eq.mp
    (congrArg (UniformNumberedProof UniformTotalSeed)
      uniformKernelProducedSentence_is_totalSeedGodelSentence.symm)
    uniformTotalSeedAdmitsGodelSentence

theorem uniformKernelProducedSentence_is_godelOnlySeedGodelSentence :
    uniformKernelExecutedGodelLink.exit.witness.production.sentence =
      godelSentence
        (uniformNumberedGodelSyntax UniformGodelOnlySeed)
        numberedUnprovabilityFormula :=
  uniformKernelExecutedGodelLink.exit.witness.production
    |>.sentence_is_godelSentence
    |>.trans
      (uniformNumberedGodelSentence_seedIndependent
        UniformKernelSeed UniformGodelOnlySeed)

def uniformGodelOnlySeedAdmitsKernelProducedSentence :
    UniformNumberedProof UniformGodelOnlySeed
      uniformKernelExecutedGodelLink.exit.witness.production.sentence :=
  Eq.mp
    (congrArg (UniformNumberedProof UniformGodelOnlySeed)
      uniformKernelProducedSentence_is_godelOnlySeedGodelSentence.symm)
    uniformGodelOnlySeedAdmitsItsGodelSentence

structure UniformExecutedDiagonalCollision
    {Seed : UniformNumberedSeed}
    (seedSound : UniformNumberedSeedSound Seed)
    (witness :
      ExecutedGodelWitness
        (uniformNumberedGodelSyntax Seed)
        numberedUnprovabilityFormula
        (uniformNumberedGodelInterpretation Seed seedSound))
    (proof : UniformNumberedProof Seed witness.production.sentence) where
  truthFromSoundness :
    uniformNumberedSentenceTruth Seed witness.production.sentence
  noProofFromProducedFixedPoint :
    UniformNumberedProof Seed witness.production.sentence → Empty

def uniformExecutedDiagonalCollision
    {Seed : UniformNumberedSeed}
    (seedSound : UniformNumberedSeedSound Seed)
    (witness :
      ExecutedGodelWitness
        (uniformNumberedGodelSyntax Seed)
        numberedUnprovabilityFormula
        (uniformNumberedGodelInterpretation Seed seedSound))
    (proof : UniformNumberedProof Seed witness.production.sentence) :
    UniformExecutedDiagonalCollision seedSound witness proof :=
  let interpretation :=
    uniformNumberedGodelInterpretation Seed seedSound
  let truthFromSoundness := proof.sound seedSound
  let representedUnprovability :=
    interpretation.provableIffTruthForward
      witness.fixedPoint truthFromSoundness
  { truthFromSoundness := truthFromSoundness
    noProofFromProducedFixedPoint :=
      interpretation.representsUnprovabilityForward
        witness.production.sentence representedUnprovability }

def uniformKernelGlobalClosureForcesProducedIdentification
    (closure :
      CircularClosureMeaning
        (executedGodelCircularPresentation
          uniformKernelExecutedGodelLink.exit.witness)
        uniformKernelExecutedGodelLink.exit.continuation) :
    uniformNumberedSentenceTruth UniformKernelSeed
        uniformKernelExecutedGodelLink.exit.witness.production.sentence =
      UniformNumberedProof UniformKernelSeed
        uniformKernelExecutedGodelLink.exit.witness.production.sentence := by
  have strictContinuation :
      StrictConstitutivePrefix
        (perimeterDeployment
          (executedGodelCircularPresentation
            uniformKernelExecutedGodelLink.exit.witness))
        uniformKernelExecutedGodelLink.exit.continuation := by
    rw [uniformKernelExecutedGodelLink.exit.continuationIsCanonical]
    exact oneStepAfterPerimeterStrict
      (executedGodelCircularPresentation
        uniformKernelExecutedGodelLink.exit.witness)
  exact (closure strictContinuation).identifiesProducedTruthAndProof

def uniformKernelTotalizingRegimeForcesProducedIdentification
    (refinement :
      CircularRefinement
        (executedGodelCircularPresentation
          uniformKernelExecutedGodelLink.exit.witness)
        uniformKernelExecutedGodelLink.exit.continuation) :
    uniformNumberedSentenceTruth UniformKernelSeed
        uniformKernelExecutedGodelLink.exit.witness.production.sentence =
      UniformNumberedProof UniformKernelSeed
        uniformKernelExecutedGodelLink.exit.witness.production.sentence :=
  uniformKernelGlobalClosureForcesProducedIdentification
    (circularRefinement_soundSpecification refinement).trajectory

def uniformKernelProducedWitnessRejectsGlobalClosure :
    CircularClosureMeaning
      (executedGodelCircularPresentation
        uniformKernelExecutedGodelLink.exit.witness)
      uniformKernelExecutedGodelLink.exit.continuation → False :=
  fun closure =>
    Empty.elim
      (uniformKernelExecutedGodelLink.exit.witness.unprovable
        (Eq.mp
          (uniformKernelGlobalClosureForcesProducedIdentification closure)
          uniformKernelExecutedGodelLink.exit.witness.trueWitness))

def uniformKernelProducedWitnessRejectsTotalizingRegime :
    CircularRefinement
      (executedGodelCircularPresentation
        uniformKernelExecutedGodelLink.exit.witness)
      uniformKernelExecutedGodelLink.exit.continuation → False :=
  fun refinement =>
    Empty.elim
      (uniformKernelExecutedGodelLink.exit.witness.unprovable
        (Eq.mp
          (uniformKernelTotalizingRegimeForcesProducedIdentification
            refinement)
          uniformKernelExecutedGodelLink.exit.witness.trueWitness))

structure UniformGodelDiagonalPerimetralConclusion where
  execution :
    ExecutedGodelDiagonalPerimetralLink
      uniformKernelGodelSyntax numberedUnprovabilityFormula
        uniformKernelGodelInterpretation
  concreteSeedIsSound : UniformNumberedSeedSound UniformKernelSeed
  producedSentenceIsInProofRejectionFamily :
    execution.exit.witness.production.sentence =
      .apply numberedUnprovabilityFormula.diagonalize
        numberedUnprovabilityFormula.diagonalize.godelNumber
  concreteProofRejectionFamilyHasAProof :
    Σ argument : Nat,
      UniformNumberedProof UniformKernelSeed
        (.apply numberedUnprovabilityFormula.diagonalize argument)
  concreteProofRejectionFamilyExclusionIsImpossible :
    ((argument : Nat) →
      UniformNumberedProof UniformKernelSeed
        (.apply numberedUnprovabilityFormula.diagonalize argument) →
          Empty) → Empty
  syntaxAndVerifierAdmitTheProducedSentence :
    UniformNumberedProof UniformTotalSeed
      execution.exit.witness.production.sentence
  totalSeedAdmitsNonDiagonalUniversalFalsity :
    UniformNumberedProof UniformTotalSeed
      (.apply (.forallProof .falsity) 0)
  totalSeedHasIndependentUnsoundness :
    UniformNumberedSeedSound UniformTotalSeed → Empty
  godelOnlySeedAdmissionsAreExact :
    {proofCode : NumberedProofCode} →
      {sentence : NumberedSentence} →
        UniformGodelOnlySeed proofCode sentence →
          sentence = uniformCanonicalGodelSentence
  godelOnlySeedAdmitsTheProducedSentence :
    UniformNumberedProof UniformGodelOnlySeed
      execution.exit.witness.production.sentence
  godelOnlyAdmissionIsIncompatibleWithSoundness :
    UniformNumberedSeedSound UniformGodelOnlySeed → Empty
  structuralExclusionWithoutSoundnessIsImpossible :
    ((Seed : UniformNumberedSeed) →
      UniformNumberedProof Seed
        (godelSentence
          (uniformNumberedGodelSyntax Seed)
          numberedUnprovabilityFormula) → Empty) → Empty
  totalAdmissionIsIncompatibleWithSoundness :
    UniformNumberedSeedSound UniformTotalSeed → Empty
  everySoundAdmissionIsObstructedDiagonally :
    (Seed : UniformNumberedSeed) →
      (seedSound : UniformNumberedSeedSound Seed) →
        UniformNumberedProof Seed
          (godelSentence
            (uniformNumberedGodelSyntax Seed)
            numberedUnprovabilityFormula) → Empty
  producedCollisionConsumesTheSameWitness :
    (proof :
      UniformNumberedProof UniformKernelSeed
        execution.exit.witness.production.sentence) →
      UniformExecutedDiagonalCollision
        uniformKernelSeedSound execution.exit.witness proof
  producedWitnessRejectsTotalLoop :
    ExecutedGodelTotalLoop execution.exit.witness → Empty
  producedWitnessRejectsSemanticCompleteness :
    ExecutedGodelProducedCompleteness execution.exit.witness → Empty
  totalLoopFactorsThroughSemanticCompleteness :
    ExecutedGodelTotalLoop execution.exit.witness →
      ExecutedGodelProducedCompleteness execution.exit.witness
  continuationConsumesProducedWitness :
    execution.exit.continuation =
      oneStepAfterPerimeter
        (executedGodelCircularPresentation execution.exit.witness)
  globalClosureForcesProducedIdentification :
    CircularClosureMeaning
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation →
        uniformNumberedSentenceTruth UniformKernelSeed
            execution.exit.witness.production.sentence =
          UniformNumberedProof UniformKernelSeed
            execution.exit.witness.production.sentence
  totalizingRegimeForcesProducedIdentification :
    CircularRefinement
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation →
        uniformNumberedSentenceTruth UniformKernelSeed
            execution.exit.witness.production.sentence =
          UniformNumberedProof UniformKernelSeed
            execution.exit.witness.production.sentence
  continuationRejectsGlobalClosure :
    CircularClosureMeaning
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation → False
  continuationRejectsTotalizingRegime :
    CircularRefinement
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation → False

def uniformGodelDiagonalPerimetralTheorem :
    UniformGodelDiagonalPerimetralConclusion :=
  { execution := uniformKernelExecutedGodelLink
    concreteSeedIsSound := uniformKernelSeedSound
    producedSentenceIsInProofRejectionFamily :=
      uniformKernelProducedSentence_is_proofRejectionFamily
    concreteProofRejectionFamilyHasAProof :=
      uniformKernelProofRejectionFamilyIsInhabited
    concreteProofRejectionFamilyExclusionIsImpossible :=
      uniformKernelProofRejectionFamilyExclusionRejected
    syntaxAndVerifierAdmitTheProducedSentence :=
      uniformTotalSeedAdmitsKernelProducedSentence
    totalSeedAdmitsNonDiagonalUniversalFalsity :=
      uniformTotalSeedAdmitsUniversalFalsity
    totalSeedHasIndependentUnsoundness :=
      uniformTotalSeedCannotBeSoundWithoutDiagonal
    godelOnlySeedAdmissionsAreExact :=
      UniformGodelOnlySeed.admittedSentenceExact
    godelOnlySeedAdmitsTheProducedSentence :=
      uniformGodelOnlySeedAdmitsKernelProducedSentence
    godelOnlyAdmissionIsIncompatibleWithSoundness :=
      uniformGodelOnlySeedCannotBeSound
    structuralExclusionWithoutSoundnessIsImpossible :=
      uniformVerifierExclusionWithoutSoundnessRejected
    totalAdmissionIsIncompatibleWithSoundness :=
      uniformTotalSeedCannotBeSound
    everySoundAdmissionIsObstructedDiagonally :=
      everySoundUniformSeedRejectsItsGodelSentence
    producedCollisionConsumesTheSameWitness :=
      fun proof =>
        uniformExecutedDiagonalCollision uniformKernelSeedSound
          uniformKernelExecutedGodelLink.exit.witness proof
    producedWitnessRejectsTotalLoop :=
      uniformKernelExecutedGodelLink.exit.witness.rejectTotalLoop
    producedWitnessRejectsSemanticCompleteness :=
      uniformKernelExecutedGodelLink.exit.witness.rejectProducedCompleteness
    totalLoopFactorsThroughSemanticCompleteness :=
      ExecutedGodelTotalLoop.toProducedCompleteness
    continuationConsumesProducedWitness :=
      uniformKernelExecutedGodelLink.exit.continuationIsCanonical
    globalClosureForcesProducedIdentification :=
      uniformKernelGlobalClosureForcesProducedIdentification
    totalizingRegimeForcesProducedIdentification :=
      uniformKernelTotalizingRegimeForcesProducedIdentification
    continuationRejectsGlobalClosure :=
      uniformKernelProducedWitnessRejectsGlobalClosure
    continuationRejectsTotalizingRegime :=
      uniformKernelProducedWitnessRejectsTotalizingRegime }

/-! ### Effective presentation bridge to the soundness form of incompleteness

The concrete uniform verifier above is an executable separating model.  The
following independent adapter states the standard hypotheses used by the
soundness-based Godel argument in effective form.  Sentences and unary
formulas have natural-number encodings with executable decoders; proofs and
provable equivalences are natural-number certificates accepted by Boolean
verifiers.  Diagonal exactness, soundness, truth transport, and internal
representation of unprovability are the explicit mathematical premises.

No incompleteness conclusion, truth witness for the diagonal sentence, or
rejection of its proof occurs among the fields.  Those are derived below and
then consumed by the same perimetral presentation and continuation.  This is
a correspondence theorem for every system satisfying the displayed standard
hypotheses; constructing such data for a particular arithmetic theory remains
the separate arithmetic-realization obligation recorded in the TODO above. -/

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
      CheckedSentenceProof encodeSentence proofCheck sentence →
        Truth sentence
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

abbrev effectiveGodelExecutedLink
    (system : EffectivelyPresentedSoundGodelSystem) :
    ExecutedGodelDiagonalPerimetralLink
      system.toGodelSyntax system.unprovabilityFormula
        system.toGodelInterpretation :=
  executedGodelDiagonalPerimetralLink
    system.toGodelSyntax system.unprovabilityFormula
      system.toGodelInterpretation

structure EffectiveGodelPerimetralCorrespondence
    (system : EffectivelyPresentedSoundGodelSystem) where
  execution :
    ExecutedGodelDiagonalPerimetralLink
      system.toGodelSyntax system.unprovabilityFormula
        system.toGodelInterpretation
  producedSentenceIsConstructedDiagonal :
    execution.exit.witness.production.sentence =
      godelSentence system.toGodelSyntax system.unprovabilityFormula
  producedFixedPoint :
    system.toGodelSyntax.ProvableIff
      execution.exit.witness.production.sentence
      (system.toGodelSyntax.substitute system.unprovabilityFormula
        (system.toGodelSyntax.quoteSentence
          execution.exit.witness.production.sentence))
  producedSentenceIsTrue :
    system.toGodelInterpretation.Truth
      execution.exit.witness.production.sentence
  producedSentenceIsUnprovable :
    system.toGodelSyntax.Proof
      execution.exit.witness.production.sentence → Empty
  semanticCompletenessAtProducedSentenceIsImpossible :
    ExecutedGodelProducedCompleteness execution.exit.witness → Empty
  totalLoopFactorsThroughSemanticCompleteness :
    ExecutedGodelTotalLoop execution.exit.witness →
      ExecutedGodelProducedCompleteness execution.exit.witness
  continuationIsTheConstructedPositiveExtension :
    execution.exit.continuation =
      oneStepAfterPerimeter
        (executedGodelCircularPresentation execution.exit.witness)
  continuationIsStrict :
    StrictConstitutivePrefix
      (perimeterDeployment
        (executedGodelCircularPresentation execution.exit.witness))
      execution.exit.continuation
  continuationIsLocallyExact :
    ExactNonClosingRealization
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation
  specifiedGlobalClosureIsImpossible :
    CircularClosureMeaning
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation → False
  specifiedTotalizingRegimeIsImpossible :
    CircularRefinement
      (executedGodelCircularPresentation execution.exit.witness)
      execution.exit.continuation → False

def effectiveGodelPerimetralCorrespondence
    (system : EffectivelyPresentedSoundGodelSystem) :
    EffectiveGodelPerimetralCorrespondence system := by
  let execution := effectiveGodelExecutedLink system
  exact
    { execution := execution
      producedSentenceIsConstructedDiagonal :=
        execution.exit.witness.production.sentence_is_godelSentence
      producedFixedPoint := execution.exit.witness.fixedPoint
      producedSentenceIsTrue := execution.exit.witness.trueWitness
      producedSentenceIsUnprovable := execution.exit.witness.unprovable
      semanticCompletenessAtProducedSentenceIsImpossible :=
        execution.exit.witness.rejectProducedCompleteness
      totalLoopFactorsThroughSemanticCompleteness :=
        ExecutedGodelTotalLoop.toProducedCompleteness
      continuationIsTheConstructedPositiveExtension :=
        execution.exit.continuationIsCanonical
      continuationIsStrict := by
        rw [execution.exit.continuationIsCanonical]
        exact
          oneStepAfterPerimeterStrict
            (executedGodelCircularPresentation execution.exit.witness)
      continuationIsLocallyExact := execution.exit.locallyExact
      specifiedGlobalClosureIsImpossible :=
        execution.exit.rejectsGlobalClosure
      specifiedTotalizingRegimeIsImpossible :=
        execution.exit.rejectsTotalizingRegime }

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
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.godelTruth_implies_unprovability
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.godelUnprovability_implies_truth
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.godelSentence_unprovable
#print axioms StrongPerimetralTurning.GodelProvabilityInterpretation.godelSentence_true
#print axioms StrongPerimetralTurning.GodelFirstIncompletenessConclusion
#print axioms StrongPerimetralTurning.godelFirstIncompleteness
#print axioms StrongPerimetralTurning.GodelConstitutiveDifference
#print axioms StrongPerimetralTurning.godelMasterDifference
#print axioms StrongPerimetralTurning.godelConstitutiveHistory
#print axioms StrongPerimetralTurning.godelProductionPrefixOfConstitutiveHistory
#print axioms StrongPerimetralTurning.godelDiagonalProductionHistory
#print axioms StrongPerimetralTurning.godelDiagonalProductionIsStrict
#print axioms StrongPerimetralTurning.producedGodelFormulaAtBoundaryCode
#print axioms StrongPerimetralTurning.internallyProducedGodelFormula
#print axioms StrongPerimetralTurning.internallyProducedGodelFormula_is_diagonal
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence_is_godelSentence
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence_fixedPoint
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence_unprovable
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence_true
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence_rejectsTruthProofIdentification
#print axioms StrongPerimetralTurning.godelPresentation_initialDifference_is_produced
#print axioms StrongPerimetralTurning.GodelSemanticCompleteness
#print axioms StrongPerimetralTurning.internallyProducedGodelSentence_refutesCompleteness
#print axioms StrongPerimetralTurning.godelInitialNode
#print axioms StrongPerimetralTurning.godelFinalNode
#print axioms StrongPerimetralTurning.godelPerimeter
#print axioms StrongPerimetralTurning.GodelTotalLoop
#print axioms StrongPerimetralTurning.godelCircularPresentation
#print axioms StrongPerimetralTurning.internallyGeneratedGodelWitness
#print axioms StrongPerimetralTurning.internallyGeneratedGodelWitness_locallyExact
#print axioms StrongPerimetralTurning.internallyGeneratedGodelWitness_is_strict
#print axioms StrongPerimetralTurning.godelClosureForcesTruthProofIdentification
#print axioms StrongPerimetralTurning.internallyGeneratedGodelWitness_rejectsGlobalClosure
#print axioms StrongPerimetralTurning.internallyGeneratedGodelWitness_rejectsTotalizingRegime
#print axioms StrongPerimetralTurning.GodelDiagonalPerimetralLink
#print axioms StrongPerimetralTurning.godelDiagonalPerimetralLink
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalProduction
#print axioms StrongPerimetralTurning.executeGodelDiagonalProduction
#print axioms StrongPerimetralTurning.ExecutedGodelSentenceProduction
#print axioms StrongPerimetralTurning.executeGodelSentenceProduction
#print axioms StrongPerimetralTurning.ExecutedGodelSentenceProduction.sentence_is_godelSentence
#print axioms StrongPerimetralTurning.ExecutedGodelWitness
#print axioms StrongPerimetralTurning.certifyExecutedGodelWitness
#print axioms StrongPerimetralTurning.ExecutedGodelTotalLoop
#print axioms StrongPerimetralTurning.ExecutedGodelProducedCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelTotalLoop.toProducedCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelWitness.rejectProducedCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelWitness.rejectTotalLoopThroughCompleteness
#print axioms StrongPerimetralTurning.ExecutedGodelWitness.rejectTotalLoop
#print axioms StrongPerimetralTurning.executedGodelNode
#print axioms StrongPerimetralTurning.executedGodelPerimeter
#print axioms StrongPerimetralTurning.executedGodelCircularPresentation
#print axioms StrongPerimetralTurning.ExecutedGodelRegimeExit
#print axioms StrongPerimetralTurning.executeGodelRegimeExit
#print axioms StrongPerimetralTurning.ExecutedGodelConstitutiveState
#print axioms StrongPerimetralTurning.ExecutedGodelConstitutiveStep
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink
#print axioms StrongPerimetralTurning.executedGodelDiagonalPerimetralLink
#print axioms StrongPerimetralTurning.NumberedCodeTerm
#print axioms StrongPerimetralTurning.NumberedCodeTerm.godelNumber
#print axioms StrongPerimetralTurning.NumberedCodeTerm.decode
#print axioms StrongPerimetralTurning.NumberedCodeTerm.decode_godelNumber
#print axioms StrongPerimetralTurning.NumberedCodeTerm.godelNumber_injective
#print axioms StrongPerimetralTurning.NumberedCodeTerm.precomposeSelfSubstitution
#print axioms StrongPerimetralTurning.NumberedProofAtom
#print axioms StrongPerimetralTurning.NumberedProofAtom.godelNumber
#print axioms StrongPerimetralTurning.NumberedProofAtom.decode
#print axioms StrongPerimetralTurning.NumberedProofAtom.decode_godelNumber
#print axioms StrongPerimetralTurning.NumberedProofMatrix
#print axioms StrongPerimetralTurning.NumberedProofMatrix.godelNumber
#print axioms StrongPerimetralTurning.NumberedProofMatrix.decode
#print axioms StrongPerimetralTurning.NumberedProofMatrix.decode_godelNumber
#print axioms StrongPerimetralTurning.NumberedUnaryFormula
#print axioms StrongPerimetralTurning.NumberedSentence
#print axioms StrongPerimetralTurning.NumberedUnaryFormula.godelNumber
#print axioms StrongPerimetralTurning.NumberedUnaryFormula.decode
#print axioms StrongPerimetralTurning.NumberedUnaryFormula.decode_godelNumber
#print axioms StrongPerimetralTurning.NumberedUnaryFormula.godelNumber_injective
#print axioms StrongPerimetralTurning.NumberedProofAtom.diagonalize
#print axioms StrongPerimetralTurning.NumberedProofMatrix.diagonalize
#print axioms StrongPerimetralTurning.NumberedUnaryFormula.diagonalize
#print axioms StrongPerimetralTurning.numberedUnprovabilityFormula
#print axioms StrongPerimetralTurning.godelDouble
#print axioms StrongPerimetralTurning.godelParity
#print axioms StrongPerimetralTurning.godelDouble_injective
#print axioms StrongPerimetralTurning.godelParity_double
#print axioms StrongPerimetralTurning.godelParity_succ_double
#print axioms StrongPerimetralTurning.godelPair
#print axioms StrongPerimetralTurning.godelPair_injective
#print axioms StrongPerimetralTurning.NumberedSentence.godelNumber
#print axioms StrongPerimetralTurning.NumberedSentence.godelNumber_injective
#print axioms StrongPerimetralTurning.NumberedCodeTerm.evaluate
#print axioms StrongPerimetralTurning.NumberedCodeTerm.evaluate_precomposeSelfSubstitution
#print axioms StrongPerimetralTurning.numberedSubstitute
#print axioms StrongPerimetralTurning.NumberedProvableIff
#print axioms StrongPerimetralTurning.numberedDiagonalizeExact
#print axioms StrongPerimetralTurning.numberedImpossibleUnaryFormula
#print axioms StrongPerimetralTurning.numberedImpossibleSelfApplication
#print axioms StrongPerimetralTurning.numberedNonDiagonalRejectionSentence
#print axioms StrongPerimetralTurning.NumberedProvableIff.godelNumber
#print axioms StrongPerimetralTurning.NumberedProofCode
#print axioms StrongPerimetralTurning.NumberedProofCode.godelNumber
#print axioms StrongPerimetralTurning.NumberedProofCode.theoremIntroduction
#print axioms StrongPerimetralTurning.NumberedProofCode.universalTautologyIntroduction
#print axioms StrongPerimetralTurning.NumberedProofCode.impossibleSelfApplicationRejection
#print axioms StrongPerimetralTurning.NumberedProofCode.equivalenceForward
#print axioms StrongPerimetralTurning.NumberedProofCode.equivalenceBackward
#print axioms StrongPerimetralTurning.NumberedVerifies
#print axioms StrongPerimetralTurning.NumberedVerifies.notUniversalFalsity
#print axioms StrongPerimetralTurning.NumberedVerifies.impossibleSelfApplication
#print axioms StrongPerimetralTurning.NumberedProof
#print axioms StrongPerimetralTurning.numberedProofAtomTruth
#print axioms StrongPerimetralTurning.numberedProofMatrixTruth
#print axioms StrongPerimetralTurning.numberedFormulaTruth
#print axioms StrongPerimetralTurning.numberedTruth
#print axioms StrongPerimetralTurning.NumberedProvableIff.truthForward
#print axioms StrongPerimetralTurning.NumberedProvableIff.truthBackward
#print axioms StrongPerimetralTurning.NumberedVerifies.sound
#print axioms StrongPerimetralTurning.NumberedProof.sound
#print axioms StrongPerimetralTurning.numberedUniversalTautologyProof
#print axioms StrongPerimetralTurning.numberedNonDiagonalRejectionProof
#print axioms StrongPerimetralTurning.numberedUniversalFormulaExclusionRejected
#print axioms StrongPerimetralTurning.numberedDiagonalizedFormulaExclusionRejected
#print axioms StrongPerimetralTurning.numberedProofForward
#print axioms StrongPerimetralTurning.numberedProofBackward
#print axioms StrongPerimetralTurning.numberedGodelSyntax
#print axioms StrongPerimetralTurning.numberedGodelInterpretation
#print axioms StrongPerimetralTurning.numberedExecutedDiagonalProduction
#print axioms StrongPerimetralTurning.numberedExecutedSentenceProduction
#print axioms StrongPerimetralTurning.numberedExecutedGodelWitness
#print axioms StrongPerimetralTurning.numberedInternallyProducedGodelSentence
#print axioms StrongPerimetralTurning.NumberedDiagonalCollision
#print axioms StrongPerimetralTurning.numberedDiagonalCollision
#print axioms StrongPerimetralTurning.numberedInternallyProducedGodelSentence_unprovableByDiagonal
#print axioms StrongPerimetralTurning.numberedInternallyProducedGodelSentence_true
#print axioms StrongPerimetralTurning.numberedInternallyProducedGodelSentence_unprovable
#print axioms StrongPerimetralTurning.concreteGodelFirstIncompleteness
#print axioms StrongPerimetralTurning.ConcreteGodelDiagonalPerimetralConclusion
#print axioms StrongPerimetralTurning.concreteGodelDiagonalPerimetralTheorem
#print axioms StrongPerimetralTurning.UniformNumberedSeed
#print axioms StrongPerimetralTurning.UniformNumberedVerifies
#print axioms StrongPerimetralTurning.UniformNumberedProof
#print axioms StrongPerimetralTurning.uniformNumberedProofAtomTruth
#print axioms StrongPerimetralTurning.uniformNumberedProofMatrixTruth
#print axioms StrongPerimetralTurning.uniformNumberedTruth
#print axioms StrongPerimetralTurning.uniformNumberedSentenceTruth
#print axioms StrongPerimetralTurning.UniformNumberedSeedSound
#print axioms StrongPerimetralTurning.uniformNumberedTruthForward
#print axioms StrongPerimetralTurning.uniformNumberedTruthBackward
#print axioms StrongPerimetralTurning.UniformNumberedVerifies.sound
#print axioms StrongPerimetralTurning.UniformNumberedProof.sound
#print axioms StrongPerimetralTurning.uniformNumberedProofForward
#print axioms StrongPerimetralTurning.uniformNumberedProofBackward
#print axioms StrongPerimetralTurning.uniformNumberedGodelSyntax
#print axioms StrongPerimetralTurning.uniformNumberedGodelInterpretation
#print axioms StrongPerimetralTurning.everySoundUniformSeedRejectsItsGodelSentence
#print axioms StrongPerimetralTurning.UniformTotalSeed
#print axioms StrongPerimetralTurning.uniformTotalSeedAdmitsGodelSentence
#print axioms StrongPerimetralTurning.uniformTotalSeedAdmitsUniversalFalsity
#print axioms StrongPerimetralTurning.uniformTotalSeedCannotBeSoundWithoutDiagonal
#print axioms StrongPerimetralTurning.uniformTotalSeedCannotBeSound
#print axioms StrongPerimetralTurning.uniformVerifierExclusionWithoutSoundnessRejected
#print axioms StrongPerimetralTurning.uniformNumberedGodelSentence_seedIndependent
#print axioms StrongPerimetralTurning.uniformCanonicalGodelSentence
#print axioms StrongPerimetralTurning.UniformGodelOnlySeed
#print axioms StrongPerimetralTurning.UniformGodelOnlySeed.admittedSentenceExact
#print axioms StrongPerimetralTurning.uniformGodelOnlySeedAdmitsItsGodelSentence
#print axioms StrongPerimetralTurning.uniformGodelOnlySeedCannotBeSound
#print axioms StrongPerimetralTurning.UniformKernelSeed
#print axioms StrongPerimetralTurning.UniformNumberedVerifies.kernelNotUniversalFalsity
#print axioms StrongPerimetralTurning.UniformNumberedVerifies.kernelImpossibleSelfApplication
#print axioms StrongPerimetralTurning.uniformKernelSeedSound
#print axioms StrongPerimetralTurning.uniformKernelNonDiagonalRejectionProof
#print axioms StrongPerimetralTurning.uniformKernelProofRejectionFamilyIsInhabited
#print axioms StrongPerimetralTurning.uniformKernelProofRejectionFamilyExclusionRejected
#print axioms StrongPerimetralTurning.uniformKernelGodelSyntax
#print axioms StrongPerimetralTurning.uniformKernelGodelInterpretation
#print axioms StrongPerimetralTurning.uniformKernelExecutedGodelLink
#print axioms StrongPerimetralTurning.uniformKernelProducedSentence_is_proofRejectionFamily
#print axioms StrongPerimetralTurning.uniformKernelProducedSentence_is_totalSeedGodelSentence
#print axioms StrongPerimetralTurning.uniformTotalSeedAdmitsKernelProducedSentence
#print axioms StrongPerimetralTurning.uniformKernelProducedSentence_is_godelOnlySeedGodelSentence
#print axioms StrongPerimetralTurning.uniformGodelOnlySeedAdmitsKernelProducedSentence
#print axioms StrongPerimetralTurning.UniformExecutedDiagonalCollision
#print axioms StrongPerimetralTurning.uniformExecutedDiagonalCollision
#print axioms StrongPerimetralTurning.uniformKernelGlobalClosureForcesProducedIdentification
#print axioms StrongPerimetralTurning.uniformKernelTotalizingRegimeForcesProducedIdentification
#print axioms StrongPerimetralTurning.uniformKernelProducedWitnessRejectsGlobalClosure
#print axioms StrongPerimetralTurning.uniformKernelProducedWitnessRejectsTotalizingRegime
#print axioms StrongPerimetralTurning.UniformGodelDiagonalPerimetralConclusion
#print axioms StrongPerimetralTurning.uniformGodelDiagonalPerimetralTheorem
#print axioms StrongPerimetralTurning.CheckedSentenceProof
#print axioms StrongPerimetralTurning.CheckedSentenceEquivalence
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.encodeUnary_injective
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.encodeSentence_injective
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.toGodelSyntax
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundGodelSystem.toGodelInterpretation
#print axioms StrongPerimetralTurning.effectiveGodelExecutedLink
#print axioms StrongPerimetralTurning.EffectiveGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.effectiveGodelPerimetralCorrespondence
/- AXIOM_AUDIT_END -/
