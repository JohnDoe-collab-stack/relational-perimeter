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
   checker used by `CheckedArithmeticProof`, and semantic correctness of
   numeral substitution.  It does not receive either historical
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
  affirmativeContinuationIsStrict :
    StrictConstitutivePrefix
      (perimeterDeployment
        (executedGodelCircularPresentation
          effective.execution.exit.witness))
      effective.execution.exit.continuation
  affirmativeContinuationIsLocallyExact :
    ExactNonClosingRealization
      (executedGodelCircularPresentation
        effective.execution.exit.witness)
      effective.execution.exit.continuation
  specifiedTotalizingRegimeIsImpossible :
    CircularRefinement
      (executedGodelCircularPresentation
        effective.execution.exit.witness)
      effective.execution.exit.continuation → False

def arithmeticGodelPerimetralCorrespondence
    (theory : EffectivelyPresentedSoundArithmeticTheory) :
    ArithmeticGodelPerimetralCorrespondence theory := by
  let effective :=
    effectiveGodelPerimetralCorrespondence theory.toEffectiveGodelSystem
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
      affirmativeContinuationIsStrict := effective.continuationIsStrict
      affirmativeContinuationIsLocallyExact :=
        effective.continuationIsLocallyExact
      specifiedTotalizingRegimeIsImpossible :=
        effective.specifiedTotalizingRegimeIsImpossible }

abbrev SemanticallyDefinedArithmeticGodelPerimetralCorrespondence
    (theory : SemanticallyDefinedProofArithmeticTheory) :=
  ArithmeticGodelPerimetralCorrespondence
    theory.toEffectivelyPresentedSoundArithmeticTheory

def semanticallyDefinedArithmeticGodelPerimetralCorrespondence
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    SemanticallyDefinedArithmeticGodelPerimetralCorrespondence theory :=
  arithmeticGodelPerimetralCorrespondence
    theory.toEffectivelyPresentedSoundArithmeticTheory

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
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
/- AXIOM_AUDIT_END -/
