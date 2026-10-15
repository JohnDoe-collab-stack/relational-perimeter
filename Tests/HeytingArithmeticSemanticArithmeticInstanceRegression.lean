import RelationalPerimeter.Constitution.HeytingArithmeticSemanticArithmeticInstance

/-!
# Concrete semantic-arithmetic HA regression gate

This downstream module checks the exact E2 realization: both complete coding
round trips, identity of the Boolean checker, the two directions of its
represented binary proof relation, the reflexive positive case, the derived
Gödel conclusion and diagnostic, and preservation of the pre-existing HA
instance.
-/

namespace RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic

def namedSemanticArithmeticTheory : SemanticallyDefinedProofArithmeticTheory :=
  heytingArithmeticSemanticallyDefinedProofArithmeticTheory

theorem unaryCodingRoundTrip
    (formula : FirstOrderArithmeticFormula 1) :
    namedSemanticArithmeticTheory.decodeUnary
        (namedSemanticArithmeticTheory.encodeUnary formula) =
      some formula :=
  namedSemanticArithmeticTheory.decodeUnary_encode formula

theorem sentenceCodingRoundTrip
    (sentence : FirstOrderArithmeticFormula 0) :
    namedSemanticArithmeticTheory.decodeSentence
        (namedSemanticArithmeticTheory.encodeSentence sentence) =
      some sentence :=
  namedSemanticArithmeticTheory.decodeSentence_encode sentence

theorem namedCheckerIsHA
    (proofCode sentenceCode : Nat) :
    namedSemanticArithmeticTheory.proofCheck proofCode sentenceCode =
      haProofCheck proofCode sentenceCode :=
  heytingArithmeticSemanticArithmeticProofCheck_eq proofCode sentenceCode

theorem namedProofRelationIsRootTranslation :
    namedSemanticArithmeticTheory.proofRelationFormula.toScoped =
      informativeHistoryProofFormula TheoryHistory.root :=
  firstOrderProofRelationPresentation_translation

def namedProofRelationPresentation : FirstOrderProofRelationPresentation :=
  firstOrderProofRelationPresentation

def reflexiveZeroArithmeticProof :
    CheckedArithmeticProof namedSemanticArithmeticTheory.encodeSentence
      namedSemanticArithmeticTheory.proofCheck
      arithmeticReflexiveZeroSentence :=
  namedSemanticArithmeticTheory.equalityReflexivityProof
    FirstOrderArithmeticTerm.zero

theorem reflexiveZeroArithmeticProofIsAccepted :
    namedSemanticArithmeticTheory.proofCheck reflexiveZeroArithmeticProof.1
        (namedSemanticArithmeticTheory.encodeSentence
          arithmeticReflexiveZeroSentence) = true :=
  reflexiveZeroArithmeticProof.2.down

def namedSemanticArithmeticConclusion :
    SemanticallyDefinedArithmeticGodelPerimetralConclusion
      namedSemanticArithmeticTheory :=
  heytingArithmeticSemanticallyDefinedArithmeticGodelConclusion

def namedSemanticArithmeticDiagnostic :
    SemanticallyDefinedArithmeticGodelDiagnostic
      namedSemanticArithmeticTheory :=
  heytingArithmeticSemanticallyDefinedArithmeticGodelDiagnostic

def namedProducedSentenceUnprovability :=
  namedSemanticArithmeticConclusion.correspondence.producedSentenceHasNoCheckedDerivation

def namedProducedNegationUnprovability :=
  namedSemanticArithmeticConclusion.producedNegationHasNoCheckedDerivation

def namedProducedContinuationIsStrict :=
  namedSemanticArithmeticDiagnostic.producedContinuationRemainsStrict

def historicalHAInstanceStillAvailable : EffectivelyPresentedSoundGodelSystem :=
  heytingArithmeticEffectiveGodelSystem

end RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedSemanticArithmeticTheory
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.unaryCodingRoundTrip
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.sentenceCodingRoundTrip
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedCheckerIsHA
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedProofRelationIsRootTranslation
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedProofRelationPresentation
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.reflexiveZeroArithmeticProof
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.reflexiveZeroArithmeticProofIsAccepted
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedSemanticArithmeticConclusion
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedSemanticArithmeticDiagnostic
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedProducedSentenceUnprovability
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedProducedNegationUnprovability
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.namedProducedContinuationIsStrict
#print axioms RelationalPerimeter.Tests.HeytingArithmeticSemanticArithmeticInstanceRegression.historicalHAInstanceStillAvailable
/- AXIOM_AUDIT_END -/
