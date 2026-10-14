import StrongPerimetralTurning

set_option linter.defProp false
set_option linter.checkUnivs false

/-!
# Object-arithmetic Gödel correspondence

The imported effective interface is deliberately representation-neutral.  To
make the Godel correspondence checkable without confusing a separate
equivalence datatype with an object-language theorem, the following bridge
fixes the ordinary first-order language of arithmetic.  Its terms contain
zero, successor, addition and multiplication; its formulas contain equality,
falsity, implication, conjunction, universal quantification and existential
quantification with constructive sigma semantics.  Arity is tracked in the
type, so sentences and unary formulas cannot be interchanged.

An arithmetic presentation below supplies executable numbering, numeral
substitution and proof checking.  Its diagonal law is not a semantic equality:
it is a checked proof of the object-language biconditional.  Soundness then
provides the two truth transports, while the proof calculus supplies the two
proof transports.  The historical interface keeps representation of
unprovability as an explicit hypothesis.  The strengthened R1 interface below
instead receives an object proof relation and its pointwise semantic
correctness, constructs provability and unprovability, and derives both
historical laws.  Neither interface receives truth or non-provability of the
produced Godel sentence; both are derived after adaptation to the executed
constitutive chain.
-/

namespace StrongPerimetralTurning

/-! ## Constitutive strengthening outside the foundational module

The historical executed link remains unchanged in `StrongPerimetralTurning`.
This module proves that every complete history of that link pins the canonical
exit, then builds a separate proof-relevant perimeter whose resources contain
the exact production and certified witness.  The arithmetic correspondence
below uses this strengthened presentation; it does not reinterpret the legacy
`Unit` presentation as evidence of global participation. -/

def arithmeticCanonicalExecutedGodelRegimeExit
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    ExecutedGodelRegimeExit coding unprovabilityFormula interpretation :=
  executeGodelRegimeExit coding unprovabilityFormula interpretation
    (certifyExecutedGodelWitness coding unprovabilityFormula interpretation
      (executeGodelSentenceProduction
        (executeGodelDiagonalProduction coding unprovabilityFormula)))

def ArithmeticExecutedGodelConstitutiveCanonical
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula} :
    ExecutedGodelConstitutiveState coding unprovabilityFormula interpretation →
      Prop
  | .received => True
  | .diagonalized diagonal =>
      diagonal =
        executeGodelDiagonalProduction coding unprovabilityFormula
  | .sentenceProduced production =>
      production =
        executeGodelSentenceProduction
          (executeGodelDiagonalProduction coding unprovabilityFormula)
  | .witnessProduced witness =>
      witness =
        certifyExecutedGodelWitness coding unprovabilityFormula interpretation
          (executeGodelSentenceProduction
            (executeGodelDiagonalProduction coding unprovabilityFormula))
  | .regimeExited exit =>
      exit =
        arithmeticCanonicalExecutedGodelRegimeExit coding
          unprovabilityFormula interpretation

theorem arithmeticExecutedGodelHistory_isCanonical
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {state :
      ExecutedGodelConstitutiveState coding unprovabilityFormula
        interpretation}
    (history :
      History (@ExecutedGodelConstitutiveStep coding unprovabilityFormula
        interpretation) .received state) :
    ArithmeticExecutedGodelConstitutiveCanonical state := by
  induction history with
  | root => trivial
  | extend _ step inductionHypothesis =>
      cases step with
      | diagonalize => rfl
      | selfApply diagonal =>
          simp only [ArithmeticExecutedGodelConstitutiveCanonical]
            at inductionHypothesis ⊢
          rw [inductionHypothesis]
      | certify production =>
          simp only [ArithmeticExecutedGodelConstitutiveCanonical]
            at inductionHypothesis ⊢
          rw [inductionHypothesis]
      | «continue» witness =>
          simp only [ArithmeticExecutedGodelConstitutiveCanonical]
            at inductionHypothesis ⊢
          rw [inductionHypothesis]
          rfl

theorem ExecutedGodelDiagonalPerimetralLink.arithmeticHistoryPinsExit
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation) :
    link.exit =
      arithmeticCanonicalExecutedGodelRegimeExit coding
        unprovabilityFormula interpretation :=
  arithmeticExecutedGodelHistory_isCanonical link.history

inductive ArithmeticExecutedGodelPerimeterResource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) : Type _
  | produced
      (production :
        ExecutedGodelSentenceProduction coding unprovabilityFormula) :
      ArithmeticExecutedGodelPerimeterResource witness
  | certified
      (certifiedWitness :
        ExecutedGodelWitness coding unprovabilityFormula interpretation) :
      ArithmeticExecutedGodelPerimeterResource witness
  | continued
      (retainedWitness :
        ExecutedGodelWitness coding unprovabilityFormula interpretation) :
      ArithmeticExecutedGodelPerimeterResource witness

inductive ArithmeticExecutedGodelPerimeterCompatibility
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ArithmeticExecutedGodelPerimeterResource witness →
      ArithmeticExecutedGodelPerimeterResource witness → Type _
  | atResource (resource : ArithmeticExecutedGodelPerimeterResource witness) :
      ArithmeticExecutedGodelPerimeterCompatibility witness resource resource
  | productionToCertification :
      ArithmeticExecutedGodelPerimeterCompatibility witness
        (.produced witness.production) (.certified witness)
  | certificationToContinuation :
      ArithmeticExecutedGodelPerimeterCompatibility witness
        (.certified witness) (.continued witness)
  | continuationToProduction :
      ArithmeticExecutedGodelPerimeterCompatibility witness
        (.continued witness) (.produced witness.production)

def arithmeticExecutedGodelNode
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation)
    (resource : ArithmeticExecutedGodelPerimeterResource witness) :
    LocalNode (ArithmeticExecutedGodelPerimeterResource witness)
      (ArithmeticExecutedGodelPerimeterResource witness)
      (ArithmeticExecutedGodelPerimeterCompatibility witness)
      (ExecutedGodelWitness coding unprovabilityFormula interpretation)
      (fun candidate => PLift (candidate = witness)) :=
  { explicit := resource
    implicit := resource
    difference := witness
    provenance := ⟨rfl⟩
    internallyCompatible := .atResource resource }

def arithmeticExecutedGodelPerimeter
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    PerimeterSpine (ArithmeticExecutedGodelPerimeterCompatibility witness)
      (arithmeticExecutedGodelNode witness (.produced witness.production)) :=
  .advance
    (nextNode := arithmeticExecutedGodelNode witness (.certified witness))
    .productionToCertification
    (.advance
      (nextNode := arithmeticExecutedGodelNode witness (.continued witness))
      .certificationToContinuation
      (.boundary
        (arithmeticExecutedGodelNode witness (.continued witness))))

def arithmeticExecutedGodelProductionPosition
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPosition (arithmeticExecutedGodelPerimeter witness) := by
  unfold arithmeticExecutedGodelPerimeter
  exact .here

def arithmeticExecutedGodelCertificationPosition
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPosition (arithmeticExecutedGodelPerimeter witness) := by
  unfold arithmeticExecutedGodelPerimeter
  exact .later .here

def arithmeticExecutedGodelProductionPrecedesCertification
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPrecedes (arithmeticExecutedGodelPerimeter witness)
      (arithmeticExecutedGodelProductionPosition witness)
      (arithmeticExecutedGodelCertificationPosition witness) := by
  unfold arithmeticExecutedGodelPerimeter
    arithmeticExecutedGodelProductionPosition
    arithmeticExecutedGodelCertificationPosition
  exact .here_later .here

def arithmeticExecutedGodelCircularPresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    CircularPresentation :=
  { Explicit := ArithmeticExecutedGodelPerimeterResource witness
    Implicit := ArithmeticExecutedGodelPerimeterResource witness
    Compatible := ArithmeticExecutedGodelPerimeterCompatibility witness
    Difference :=
      ExecutedGodelWitness coding unprovabilityFormula interpretation
    Provenance := fun candidate => PLift (candidate = witness)
    initialNode :=
      arithmeticExecutedGodelNode witness (.produced witness.production)
    perimeter := arithmeticExecutedGodelPerimeter witness
    perimeterPositive := by
      unfold arithmeticExecutedGodelPerimeter
      exact .here
    finalJunction := by
      unfold arithmeticExecutedGodelPerimeter
      exact .continuationToProduction
    Endpoint := Type _
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

structure ArithmeticExecutedGodelRegimeParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) where
  continuation :
    RootedGeneratedHistory
      (arithmeticExecutedGodelCircularPresentation witness)
  continuationIsCanonical :
    continuation =
      oneStepAfterPerimeter
        (arithmeticExecutedGodelCircularPresentation witness)
  locallyExact :
    ExactNonClosingRealization
      (arithmeticExecutedGodelCircularPresentation witness) continuation

def arithmeticExecutedGodelRegimeParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ArithmeticExecutedGodelRegimeParticipation witness :=
  { continuation :=
      oneStepAfterPerimeter
        (arithmeticExecutedGodelCircularPresentation witness)
    continuationIsCanonical := rfl
    locallyExact :=
      oneStepAfterPerimeter_nonClosingRealization
        (arithmeticExecutedGodelCircularPresentation witness) }

def ArithmeticExecutedGodelRegimeParticipation.globalClosureToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (participation : ArithmeticExecutedGodelRegimeParticipation witness) :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation witness)
        participation.continuation →
      ExecutedGodelProducedCompleteness witness := by
  intro closure
  have strictContinuation :
      StrictConstitutivePrefix
        (perimeterDeployment
          (arithmeticExecutedGodelCircularPresentation witness))
        participation.continuation := by
    rw [participation.continuationIsCanonical]
    exact
      oneStepAfterPerimeterStrict
        (arithmeticExecutedGodelCircularPresentation witness)
  exact (closure strictContinuation).toProducedCompleteness

structure ArithmeticExecutedGodelGlobalParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation) : Type _ where
  historyPinsConsumedExit :
    link.exit =
      arithmeticCanonicalExecutedGodelRegimeExit coding
        unprovabilityFormula interpretation
  perimeterParticipation :
    ArithmeticExecutedGodelRegimeParticipation link.exit.witness
  productionPrecedesCertificationInContinuation :
    History.OccurrencePrecedes
      (perimeterParticipation.locallyExact.realize
        (arithmeticExecutedGodelProductionPosition link.exit.witness))
      (perimeterParticipation.locallyExact.realize
        (arithmeticExecutedGodelCertificationPosition link.exit.witness))
  globalClosureFactorsThroughProducedCompleteness :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation link.exit.witness)
        perimeterParticipation.continuation →
      ExecutedGodelProducedCompleteness link.exit.witness

def ExecutedGodelDiagonalPerimetralLink.arithmeticGlobalParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation) :
    ArithmeticExecutedGodelGlobalParticipation link := by
  let perimeterParticipation :=
    arithmeticExecutedGodelRegimeParticipation link.exit.witness
  exact
    { historyPinsConsumedExit := link.arithmeticHistoryPinsExit
      perimeterParticipation := perimeterParticipation
      productionPrecedesCertificationInContinuation :=
        perimeterParticipation.locallyExact.preservesPrecedence
          (arithmeticExecutedGodelProductionPrecedesCertification
            link.exit.witness)
      globalClosureFactorsThroughProducedCompleteness :=
        perimeterParticipation.globalClosureToProducedCompleteness }

def ArithmeticExecutedGodelGlobalParticipation.rejectGlobalClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation}
    (participation : ArithmeticExecutedGodelGlobalParticipation link) :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation link.exit.witness)
        participation.perimeterParticipation.continuation → False :=
  fun closure =>
    Empty.elim
      (link.exit.witness.rejectProducedCompleteness
        (participation.globalClosureFactorsThroughProducedCompleteness
          closure))

def ArithmeticExecutedGodelGlobalParticipation.rejectTotalizingRegime
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation}
    (participation : ArithmeticExecutedGodelGlobalParticipation link) :
    CircularRefinement
        (arithmeticExecutedGodelCircularPresentation link.exit.witness)
        participation.perimeterParticipation.continuation → False :=
  fun refinement =>
    participation.rejectGlobalClosure
      (circularRefinement_soundSpecification refinement).trajectory

inductive FirstOrderArithmeticTerm (arity : Nat) : Type where
  | variable : Fin arity → FirstOrderArithmeticTerm arity
  | zero : FirstOrderArithmeticTerm arity
  | successor :
      FirstOrderArithmeticTerm arity → FirstOrderArithmeticTerm arity
  | addition :
      FirstOrderArithmeticTerm arity →
        FirstOrderArithmeticTerm arity → FirstOrderArithmeticTerm arity
  | multiplication :
      FirstOrderArithmeticTerm arity →
        FirstOrderArithmeticTerm arity → FirstOrderArithmeticTerm arity

namespace FirstOrderArithmeticTerm

def numeral {arity : Nat} : Nat → FirstOrderArithmeticTerm arity
  | 0 => .zero
  | number + 1 => .successor (numeral number)

def evaluate
    {arity : Nat}
    (assignment : Nat → Nat) : FirstOrderArithmeticTerm arity → Nat
  | .variable index => assignment index.val
  | .zero => 0
  | .successor term => evaluate assignment term + 1
  | .addition left right =>
      evaluate assignment left + evaluate assignment right
  | .multiplication left right =>
      evaluate assignment left * evaluate assignment right

end FirstOrderArithmeticTerm

inductive FirstOrderArithmeticFormula : Nat → Type where
  | equal {arity : Nat} :
      FirstOrderArithmeticTerm arity →
        FirstOrderArithmeticTerm arity → FirstOrderArithmeticFormula arity
  | falsity {arity : Nat} : FirstOrderArithmeticFormula arity
  | implication {arity : Nat} :
      FirstOrderArithmeticFormula arity →
        FirstOrderArithmeticFormula arity → FirstOrderArithmeticFormula arity
  | conjunction {arity : Nat} :
      FirstOrderArithmeticFormula arity →
        FirstOrderArithmeticFormula arity → FirstOrderArithmeticFormula arity
  | universal {arity : Nat} :
      FirstOrderArithmeticFormula (arity + 1) →
        FirstOrderArithmeticFormula arity
  | existential {arity : Nat} :
      FirstOrderArithmeticFormula (arity + 1) →
        FirstOrderArithmeticFormula arity

namespace FirstOrderArithmeticFormula

def extendAssignment
    (value : Nat) (assignment : Nat → Nat) : Nat → Nat
  | 0 => value
  | previous + 1 => assignment previous

def unaryAssignment (value : Nat) : Nat → Nat :=
  extendAssignment value (fun _ => 0)

def binaryAssignment (first second : Nat) : Nat → Nat :=
  extendAssignment first (unaryAssignment second)

def Truth
    {arity : Nat}
    (assignment : Nat → Nat) : FirstOrderArithmeticFormula arity → Type
  | .equal left right =>
      PLift
        (FirstOrderArithmeticTerm.evaluate assignment left =
          FirstOrderArithmeticTerm.evaluate assignment right)
  | .falsity => Empty
  | .implication antecedent consequent =>
      Truth assignment antecedent → Truth assignment consequent
  | .conjunction left right => Truth assignment left × Truth assignment right
  | .universal body =>
      (value : Nat) →
        Truth (extendAssignment value assignment) body
  | .existential body =>
      Σ value : Nat, Truth (extendAssignment value assignment) body

def sentenceTruth (sentence : FirstOrderArithmeticFormula 0) : Type :=
  Truth (fun _ => 0) sentence

def biconditional
    (left right : FirstOrderArithmeticFormula 0) :
    FirstOrderArithmeticFormula 0 :=
  .conjunction (.implication left right) (.implication right left)

def negation
    {arity : Nat}
    (formula : FirstOrderArithmeticFormula arity) :
    FirstOrderArithmeticFormula arity :=
  .implication formula .falsity

def provabilityFormula
    (proofRelationFormula : FirstOrderArithmeticFormula 2) :
    FirstOrderArithmeticFormula 1 :=
  /- The new bound variable is index 0 (proof code); the previous free
     variable becomes index 1 (sentence code). -/
  .existential proofRelationFormula

def unprovabilityFormula
    (proofRelationFormula : FirstOrderArithmeticFormula 2) :
    FirstOrderArithmeticFormula 1 :=
  negation (provabilityFormula proofRelationFormula)

end FirstOrderArithmeticFormula

abbrev CheckedArithmeticProof
    (encodeSentence : FirstOrderArithmeticFormula 0 → Nat)
    (proofCheck : Nat → Nat → Bool)
    (sentence : FirstOrderArithmeticFormula 0) : Type :=
  CheckedSentenceProof encodeSentence proofCheck sentence

/- This is the exact soundness-based arithmetic hypothesis package used by
   the bridge.  It describes a proof calculus on the fixed first-order
   arithmetic language.  In particular, `diagonalIffProof` is an accepted
   derivation of an object formula, not a free-standing meta-equivalence. -/
structure EffectivelyPresentedSoundArithmeticTheory where
  encodeUnary : FirstOrderArithmeticFormula 1 → Nat
  decodeUnary : Nat → Option (FirstOrderArithmeticFormula 1)
  decodeUnary_encode :
    (formula : FirstOrderArithmeticFormula 1) →
      decodeUnary (encodeUnary formula) = some formula
  encodeSentence : FirstOrderArithmeticFormula 0 → Nat
  decodeSentence : Nat → Option (FirstOrderArithmeticFormula 0)
  decodeSentence_encode :
    (sentence : FirstOrderArithmeticFormula 0) →
      decodeSentence (encodeSentence sentence) = some sentence
  substituteNumeral :
    FirstOrderArithmeticFormula 1 → Nat → FirstOrderArithmeticFormula 0
  diagonalize :
    FirstOrderArithmeticFormula 1 → FirstOrderArithmeticFormula 1
  proofCheck : Nat → Nat → Bool
  diagonalIffProof :
    (target source : FirstOrderArithmeticFormula 1) →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional
          (substituteNumeral (diagonalize target) (encodeUnary source))
          (substituteNumeral target
            (encodeSentence (substituteNumeral source (encodeUnary source)))))
  iffProofForward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck left →
      CheckedArithmeticProof encodeSentence proofCheck right
  iffProofBackward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck right →
      CheckedArithmeticProof encodeSentence proofCheck left
  proofSound :
    {sentence : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck sentence →
        FirstOrderArithmeticFormula.sentenceTruth sentence
  unprovabilityFormula : FirstOrderArithmeticFormula 1
  representsUnprovabilityForward :
    (sentence : FirstOrderArithmeticFormula 0) →
      FirstOrderArithmeticFormula.sentenceTruth
        (substituteNumeral unprovabilityFormula (encodeSentence sentence)) →
      CheckedArithmeticProof encodeSentence proofCheck sentence → Empty
  representsUnprovabilityBackward :
    (sentence : FirstOrderArithmeticFormula 0) →
      (CheckedArithmeticProof encodeSentence proofCheck sentence → Empty) →
      FirstOrderArithmeticFormula.sentenceTruth
        (substituteNumeral unprovabilityFormula (encodeSentence sentence))

/- This R1 package makes the proof predicate explicit.  It receives semantic
   correctness of a binary object formula relative to the same Boolean proof
   checker used by `CheckedArithmeticProof`, semantic correctness of numeral
   substitution, and the ordinary logical strength needed to derive every
   reflexive closed equality.  It does not receive either historical
   unprovability law, nor any fact about the produced diagonal sentence. -/
structure SemanticallyDefinedProofArithmeticTheory where
  encodeUnary : FirstOrderArithmeticFormula 1 → Nat
  decodeUnary : Nat → Option (FirstOrderArithmeticFormula 1)
  decodeUnary_encode :
    (formula : FirstOrderArithmeticFormula 1) →
      decodeUnary (encodeUnary formula) = some formula
  encodeSentence : FirstOrderArithmeticFormula 0 → Nat
  decodeSentence : Nat → Option (FirstOrderArithmeticFormula 0)
  decodeSentence_encode :
    (sentence : FirstOrderArithmeticFormula 0) →
      decodeSentence (encodeSentence sentence) = some sentence
  substituteNumeral :
    FirstOrderArithmeticFormula 1 → Nat → FirstOrderArithmeticFormula 0
  substituteNumeralTruthForward :
    (formula : FirstOrderArithmeticFormula 1) →
      (value : Nat) →
        FirstOrderArithmeticFormula.sentenceTruth
            (substituteNumeral formula value) →
          FirstOrderArithmeticFormula.Truth
            (FirstOrderArithmeticFormula.unaryAssignment value) formula
  substituteNumeralTruthBackward :
    (formula : FirstOrderArithmeticFormula 1) →
      (value : Nat) →
        FirstOrderArithmeticFormula.Truth
            (FirstOrderArithmeticFormula.unaryAssignment value) formula →
          FirstOrderArithmeticFormula.sentenceTruth
            (substituteNumeral formula value)
  diagonalize :
    FirstOrderArithmeticFormula 1 → FirstOrderArithmeticFormula 1
  proofCheck : Nat → Nat → Bool
  diagonalIffProof :
    (target source : FirstOrderArithmeticFormula 1) →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional
          (substituteNumeral (diagonalize target) (encodeUnary source))
          (substituteNumeral target
            (encodeSentence (substituteNumeral source (encodeUnary source)))))
  iffProofForward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck left →
      CheckedArithmeticProof encodeSentence proofCheck right
  iffProofBackward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck right →
      CheckedArithmeticProof encodeSentence proofCheck left
  proofSound :
    {sentence : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck sentence →
        FirstOrderArithmeticFormula.sentenceTruth sentence
  equalityReflexivityProof :
    (term : FirstOrderArithmeticTerm 0) →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.equal term term)
  proofRelationFormula : FirstOrderArithmeticFormula 2
  proofRelationTruthForward :
    (proofCode sentenceCode : Nat) →
      FirstOrderArithmeticFormula.Truth
          (FirstOrderArithmeticFormula.binaryAssignment
            proofCode sentenceCode)
          proofRelationFormula →
        PLift (proofCheck proofCode sentenceCode = true)
  proofRelationTruthBackward :
    (proofCode sentenceCode : Nat) →
      PLift (proofCheck proofCode sentenceCode = true) →
        FirstOrderArithmeticFormula.Truth
          (FirstOrderArithmeticFormula.binaryAssignment
            proofCode sentenceCode)
          proofRelationFormula

def SemanticallyDefinedProofArithmeticTheory.provabilityFormula
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    FirstOrderArithmeticFormula 1 :=
  FirstOrderArithmeticFormula.provabilityFormula
    theory.proofRelationFormula

def SemanticallyDefinedProofArithmeticTheory.unprovabilityFormula
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    FirstOrderArithmeticFormula 1 :=
  FirstOrderArithmeticFormula.unprovabilityFormula
    theory.proofRelationFormula

def SemanticallyDefinedProofArithmeticTheory.checkedProof_implies_provabilityTruth
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck sentence →
      FirstOrderArithmeticFormula.sentenceTruth
        (theory.substituteNumeral theory.provabilityFormula
          (theory.encodeSentence sentence)) := by
  intro proof
  rcases proof with ⟨proofCode, verification⟩
  exact
    theory.substituteNumeralTruthBackward
      theory.provabilityFormula (theory.encodeSentence sentence)
      ⟨proofCode,
        theory.proofRelationTruthBackward
          proofCode (theory.encodeSentence sentence) verification⟩

def SemanticallyDefinedProofArithmeticTheory.provabilityTruth_implies_checkedProof
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    FirstOrderArithmeticFormula.sentenceTruth
        (theory.substituteNumeral theory.provabilityFormula
          (theory.encodeSentence sentence)) →
      CheckedArithmeticProof theory.encodeSentence theory.proofCheck
        sentence := by
  intro truthWitness
  have provabilityTruth :=
    theory.substituteNumeralTruthForward
      theory.provabilityFormula (theory.encodeSentence sentence) truthWitness
  rcases provabilityTruth with ⟨proofCode, relationTruth⟩
  exact
    ⟨proofCode,
      theory.proofRelationTruthForward
        proofCode (theory.encodeSentence sentence) relationTruth⟩

def SemanticallyDefinedProofArithmeticTheory.unprovabilityTruth_implies_noProof
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    FirstOrderArithmeticFormula.sentenceTruth
        (theory.substituteNumeral theory.unprovabilityFormula
          (theory.encodeSentence sentence)) →
      CheckedArithmeticProof theory.encodeSentence theory.proofCheck sentence →
        Empty := by
  intro unprovabilitySentenceTruth proof
  have unprovabilityTruth :=
    theory.substituteNumeralTruthForward
      theory.unprovabilityFormula (theory.encodeSentence sentence)
      unprovabilitySentenceTruth
  have provabilitySentenceTruth :=
    theory.checkedProof_implies_provabilityTruth sentence proof
  have provabilityTruth :=
    theory.substituteNumeralTruthForward
      theory.provabilityFormula (theory.encodeSentence sentence)
      provabilitySentenceTruth
  exact unprovabilityTruth provabilityTruth

def SemanticallyDefinedProofArithmeticTheory.noProof_implies_unprovabilityTruth
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    (CheckedArithmeticProof theory.encodeSentence theory.proofCheck sentence →
      Empty) →
    FirstOrderArithmeticFormula.sentenceTruth
      (theory.substituteNumeral theory.unprovabilityFormula
        (theory.encodeSentence sentence)) := by
  intro noProof
  apply theory.substituteNumeralTruthBackward
  intro provabilityTruth
  have provabilitySentenceTruth :=
    theory.substituteNumeralTruthBackward
      theory.provabilityFormula (theory.encodeSentence sentence)
      provabilityTruth
  exact
    noProof
      (theory.provabilityTruth_implies_checkedProof
        sentence provabilitySentenceTruth)

def SemanticallyDefinedProofArithmeticTheory.toEffectivelyPresentedSoundArithmeticTheory
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    EffectivelyPresentedSoundArithmeticTheory :=
  { encodeUnary := theory.encodeUnary
    decodeUnary := theory.decodeUnary
    decodeUnary_encode := theory.decodeUnary_encode
    encodeSentence := theory.encodeSentence
    decodeSentence := theory.decodeSentence
    decodeSentence_encode := theory.decodeSentence_encode
    substituteNumeral := theory.substituteNumeral
    diagonalize := theory.diagonalize
    proofCheck := theory.proofCheck
    diagonalIffProof := theory.diagonalIffProof
    iffProofForward := theory.iffProofForward
    iffProofBackward := theory.iffProofBackward
    proofSound := theory.proofSound
    unprovabilityFormula := theory.unprovabilityFormula
    representsUnprovabilityForward :=
      theory.unprovabilityTruth_implies_noProof
    representsUnprovabilityBackward :=
      theory.noProof_implies_unprovabilityTruth }

def arithmeticEquivalenceCheck
    (theory : EffectivelyPresentedSoundArithmeticTheory)
    (certificateCode leftCode rightCode : Nat) : Bool :=
  match theory.decodeSentence leftCode with
  | none => false
  | some left =>
      match theory.decodeSentence rightCode with
      | none => false
      | some right =>
          theory.proofCheck certificateCode
            (theory.encodeSentence
              (FirstOrderArithmeticFormula.biconditional left right))

def EffectivelyPresentedSoundArithmeticTheory.equivalenceIsBiconditionalProof
    (theory : EffectivelyPresentedSoundArithmeticTheory)
    {left right : FirstOrderArithmeticFormula 0}
    (equivalence :
      CheckedSentenceEquivalence theory.encodeSentence
        (arithmeticEquivalenceCheck theory) left right) :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      (FirstOrderArithmeticFormula.biconditional left right) := by
  rcases equivalence with ⟨certificateCode, ⟨verification⟩⟩
  exact
    ⟨certificateCode, ⟨by
      simpa [arithmeticEquivalenceCheck,
        theory.decodeSentence_encode left,
        theory.decodeSentence_encode right] using verification⟩⟩

def EffectivelyPresentedSoundArithmeticTheory.toEffectiveGodelSystem
    (theory : EffectivelyPresentedSoundArithmeticTheory) :
    EffectivelyPresentedSoundGodelSystem :=
  { UnaryFormula := FirstOrderArithmeticFormula 1
    Sentence := FirstOrderArithmeticFormula 0
    encodeUnary := theory.encodeUnary
    decodeUnary := theory.decodeUnary
    decodeUnary_encode := theory.decodeUnary_encode
    encodeSentence := theory.encodeSentence
    decodeSentence := theory.decodeSentence
    decodeSentence_encode := theory.decodeSentence_encode
    substitute := theory.substituteNumeral
    diagonalize := theory.diagonalize
    proofCheck := theory.proofCheck
    equivalenceCheck := arithmeticEquivalenceCheck theory
    diagonalizeExact := by
      intro target source
      rcases theory.diagonalIffProof target source with
        ⟨certificateCode, ⟨verification⟩⟩
      exact
        ⟨certificateCode, ⟨by
          simpa [arithmeticEquivalenceCheck,
            theory.decodeSentence_encode] using verification⟩⟩
    proofForward := by
      intro left right equivalence proof
      exact theory.iffProofForward
        (theory.equivalenceIsBiconditionalProof equivalence) proof
    proofBackward := by
      intro left right equivalence proof
      exact theory.iffProofBackward
        (theory.equivalenceIsBiconditionalProof equivalence) proof
    Truth := FirstOrderArithmeticFormula.sentenceTruth
    proofSound := theory.proofSound
    equivalenceTruthForward := by
      intro left right equivalence leftTruth
      have biconditionalTruth :=
        theory.proofSound
          (theory.equivalenceIsBiconditionalProof equivalence)
      exact biconditionalTruth.1 leftTruth
    equivalenceTruthBackward := by
      intro left right equivalence rightTruth
      have biconditionalTruth :=
        theory.proofSound
          (theory.equivalenceIsBiconditionalProof equivalence)
      exact biconditionalTruth.2 rightTruth
    unprovabilityFormula := theory.unprovabilityFormula
    representsUnprovabilityForward :=
      theory.representsUnprovabilityForward
    representsUnprovabilityBackward :=
      theory.representsUnprovabilityBackward }

abbrev arithmeticGodelExecutedLink
    (theory : EffectivelyPresentedSoundArithmeticTheory) :=
  effectiveGodelExecutedLink theory.toEffectiveGodelSystem

structure ArithmeticGodelPerimetralCorrespondence
    (theory : EffectivelyPresentedSoundArithmeticTheory) where
  effective :
    EffectiveGodelPerimetralCorrespondence theory.toEffectiveGodelSystem
  diagonalCertificateIsObjectBiconditional :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      (FirstOrderArithmeticFormula.biconditional
        effective.execution.exit.witness.production.sentence
        (theory.substituteNumeral theory.unprovabilityFormula
          (theory.encodeSentence
            effective.execution.exit.witness.production.sentence)))
  producedSentenceIsTrueInStandardArithmeticSemantics :
    FirstOrderArithmeticFormula.sentenceTruth
      effective.execution.exit.witness.production.sentence
  producedSentenceHasNoCheckedDerivation :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      effective.execution.exit.witness.production.sentence → Empty
  producedSentenceRejectsSemanticCompleteness :
    ExecutedGodelProducedCompleteness
      effective.execution.exit.witness → Empty
  executedHistoryPinsTheConsumedExit :
    effective.execution.exit =
      arithmeticCanonicalExecutedGodelRegimeExit
        theory.toEffectiveGodelSystem.toGodelSyntax
        theory.unprovabilityFormula
        theory.toEffectiveGodelSystem.toGodelInterpretation
  executedGlobalParticipation :
    ArithmeticExecutedGodelGlobalParticipation effective.execution
  affirmativeContinuationIsStrict :
    StrictConstitutivePrefix
      (perimeterDeployment
        (arithmeticExecutedGodelCircularPresentation
          effective.execution.exit.witness))
      executedGlobalParticipation.perimeterParticipation.continuation
  affirmativeContinuationIsLocallyExact :
    ExactNonClosingRealization
      (arithmeticExecutedGodelCircularPresentation
        effective.execution.exit.witness)
      executedGlobalParticipation.perimeterParticipation.continuation
  specifiedGlobalClosureFactorsThroughProducedCompleteness :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation
          effective.execution.exit.witness)
        executedGlobalParticipation.perimeterParticipation.continuation →
      ExecutedGodelProducedCompleteness
        effective.execution.exit.witness
  specifiedGlobalClosureIsImpossible :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation
          effective.execution.exit.witness)
        executedGlobalParticipation.perimeterParticipation.continuation →
      False
  specifiedTotalizingRegimeIsImpossible :
    CircularRefinement
      (arithmeticExecutedGodelCircularPresentation
        effective.execution.exit.witness)
      executedGlobalParticipation.perimeterParticipation.continuation → False

structure SemanticallyDefinedArithmeticGodelPerimetralConclusion
    (theory : SemanticallyDefinedProofArithmeticTheory) where
  correspondence :
    ArithmeticGodelPerimetralCorrespondence
      theory.toEffectivelyPresentedSoundArithmeticTheory
  producedSentenceIsNotAReflexiveEquality :
    (term : FirstOrderArithmeticTerm 0) →
      correspondence.effective.execution.exit.witness.production.sentence =
          FirstOrderArithmeticFormula.equal term term →
        Empty

def arithmeticGodelPerimetralCorrespondence
    (theory : EffectivelyPresentedSoundArithmeticTheory) :
    ArithmeticGodelPerimetralCorrespondence theory := by
  let effective :=
    effectiveGodelPerimetralCorrespondence theory.toEffectiveGodelSystem
  let participation := effective.execution.arithmeticGlobalParticipation
  exact
    { effective := effective
      diagonalCertificateIsObjectBiconditional :=
        theory.equivalenceIsBiconditionalProof
          effective.producedFixedPoint
      producedSentenceIsTrueInStandardArithmeticSemantics :=
        effective.producedSentenceIsTrue
      producedSentenceHasNoCheckedDerivation :=
        effective.producedSentenceIsUnprovable
      producedSentenceRejectsSemanticCompleteness :=
        effective.semanticCompletenessAtProducedSentenceIsImpossible
      executedHistoryPinsTheConsumedExit :=
        effective.execution.arithmeticHistoryPinsExit
      executedGlobalParticipation := participation
      affirmativeContinuationIsStrict := by
        rw [participation.perimeterParticipation.continuationIsCanonical]
        exact
          oneStepAfterPerimeterStrict
            (arithmeticExecutedGodelCircularPresentation
              effective.execution.exit.witness)
      affirmativeContinuationIsLocallyExact :=
        participation.perimeterParticipation.locallyExact
      specifiedGlobalClosureFactorsThroughProducedCompleteness :=
        participation.globalClosureFactorsThroughProducedCompleteness
      specifiedGlobalClosureIsImpossible :=
        participation.rejectGlobalClosure
      specifiedTotalizingRegimeIsImpossible :=
        participation.rejectTotalizingRegime }

abbrev SemanticallyDefinedArithmeticGodelPerimetralCorrespondence
    (theory : SemanticallyDefinedProofArithmeticTheory) :=
  ArithmeticGodelPerimetralCorrespondence
    theory.toEffectivelyPresentedSoundArithmeticTheory

def semanticallyDefinedArithmeticGodelPerimetralCorrespondence
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    SemanticallyDefinedArithmeticGodelPerimetralCorrespondence theory :=
  arithmeticGodelPerimetralCorrespondence
    theory.toEffectivelyPresentedSoundArithmeticTheory

def semanticallyDefinedArithmeticGodelPerimetralConclusion
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    SemanticallyDefinedArithmeticGodelPerimetralConclusion theory := by
  let correspondence :=
    semanticallyDefinedArithmeticGodelPerimetralCorrespondence theory
  refine
    { correspondence := correspondence
      producedSentenceIsNotAReflexiveEquality := ?_ }
  intro term equality
  apply correspondence.producedSentenceHasNoCheckedDerivation
  rw [equality]
  exact theory.equalityReflexivityProof term

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.arithmeticCanonicalExecutedGodelRegimeExit
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelConstitutiveCanonical
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelHistory_isCanonical
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink.arithmeticHistoryPinsExit
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelPerimeterResource
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelPerimeterCompatibility
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelNode
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelPerimeter
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelProductionPosition
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelCertificationPosition
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelProductionPrecedesCertification
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelCircularPresentation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelRegimeParticipation
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelRegimeParticipation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelRegimeParticipation.globalClosureToProducedCompleteness
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelGlobalParticipation
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink.arithmeticGlobalParticipation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelGlobalParticipation.rejectGlobalClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelGlobalParticipation.rejectTotalizingRegime
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.numeral
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.evaluate
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.extendAssignment
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.unaryAssignment
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.binaryAssignment
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.Truth
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.sentenceTruth
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.biconditional
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.negation
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.provabilityFormula
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.unprovabilityFormula
#print axioms StrongPerimetralTurning.CheckedArithmeticProof
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.provabilityFormula
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.unprovabilityFormula
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.checkedProof_implies_provabilityTruth
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.provabilityTruth_implies_checkedProof
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.unprovabilityTruth_implies_noProof
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.noProof_implies_unprovabilityTruth
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.toEffectivelyPresentedSoundArithmeticTheory
#print axioms StrongPerimetralTurning.arithmeticEquivalenceCheck
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory.equivalenceIsBiconditionalProof
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory.toEffectiveGodelSystem
#print axioms StrongPerimetralTurning.arithmeticGodelExecutedLink
#print axioms StrongPerimetralTurning.ArithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.semanticallyDefinedArithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelPerimetralConclusion
#print axioms StrongPerimetralTurning.semanticallyDefinedArithmeticGodelPerimetralConclusion
/- AXIOM_AUDIT_END -/
