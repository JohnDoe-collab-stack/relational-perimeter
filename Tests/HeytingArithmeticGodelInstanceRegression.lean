import RelationalPerimeter.Constitution.HeytingArithmeticGodelInstance

/-!
# Named Heyting-arithmetic Gödel regression gate

This downstream module checks four independent obligations of the concrete
instance: an HA derivation survives encoding and executable verification; the
classical double-negation rule tag is rejected by the HA dispatcher; the
produced diagonal sentence is both true and unprovable; and its constitutive
continuation remains strict while causal closure is impossible.
-/

namespace RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic

set_option maxRecDepth 1000000

def reflexiveZeroSentence : Sentence :=
  { raw := (numeralEqualityFormula 0 0 0).raw
    isScoped := (numeralEqualityFormula 0 0 0).isScoped }

def reflexiveZeroCheckedProof :
    CheckedSentenceProof Sentence.quote haProofCheck reflexiveZeroSentence :=
  haCheckedProofOfDerivation (numeralEqualityProof 0 0 0 rfl)

theorem reflexiveZeroCertificateIsAccepted :
    haProofCheck reflexiveZeroCheckedProof.1 reflexiveZeroSentence.quote =
      true :=
  reflexiveZeroCheckedProof.2.down

theorem doubleNegationRuleHasTagTwentyTwo :
    ProofRuleTag.doubleNegationElimination.code = 22 := by
  rfl

theorem doubleNegationTagIsRejectedByHADispatcher
    (historyCode archiveCode lineIndex : Nat)
    (tagExact :
      proofCheckRuleValue archiveCode lineIndex =
        ProofRuleTag.doubleNegationElimination.code) :
    PRFunction.checkProofLineRules.run
        (proofCheckInputs historyCode archiveCode lineIndex) = 0 :=
  PRFunction.checkProofLineRules_rejects_doubleNegationTag
    historyCode archiveCode lineIndex
      (tagExact.trans doubleNegationRuleHasTagTwentyTwo)

def namedHeytingArithmeticSystem : EffectivelyPresentedSoundGodelSystem :=
  heytingArithmeticEffectiveGodelSystem

def namedHeytingArithmeticCorrespondence :
    EffectiveGodelPerimetralCorrespondence namedHeytingArithmeticSystem :=
  heytingArithmeticGodelPerimetralCorrespondence

def namedProducedSentenceTruth :=
  heytingArithmeticGodelPerimetralCorrespondence.producedSentenceIsTrue

def namedProducedSentenceUnprovability :=
  heytingArithmeticGodelPerimetralCorrespondence.producedSentenceIsUnprovable

def namedProducedNegationUnprovability :=
  heytingArithmeticProducedNegationIsUnprovable

def namedStrictContinuation :=
  heytingArithmeticStrictContinuation

def namedCausalParticipation :=
  heytingArithmeticCausalParticipation

def namedExecutedOccurrenceCorrespondence :=
  heytingArithmeticExecutedOccurrenceCorrespondence

theorem namedExecutedSelfApplyImmediatelyPrecedesCertify :
    History.OccurrenceNext
      namedExecutedOccurrenceCorrespondence.executed.selfApplyOccurrence
      namedExecutedOccurrenceCorrespondence.executed.certifyOccurrence :=
  namedExecutedOccurrenceCorrespondence.executedSelfApplyNextCertify

theorem namedExecutedOutputsAreThePerimeterResources :
    namedExecutedOccurrenceCorrespondence.executed.production =
        heytingArithmeticExecutedGodelLink.exit.witness.production ∧
      namedExecutedOccurrenceCorrespondence.executed.witness =
        heytingArithmeticExecutedGodelLink.exit.witness :=
  ⟨namedExecutedOccurrenceCorrespondence.selfApplyConstitutesProduction,
    namedExecutedOccurrenceCorrespondence.certifyConstitutesCertification⟩

def namedCausalClosureRejection :=
  heytingArithmeticCausalClosureIsImpossible

def namedDirectedClosureRejection :=
  heytingArithmeticDirectedClosureIsImpossible

end RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.reflexiveZeroCheckedProof
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.reflexiveZeroCertificateIsAccepted
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.doubleNegationRuleHasTagTwentyTwo
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.doubleNegationTagIsRejectedByHADispatcher
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedHeytingArithmeticSystem
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedHeytingArithmeticCorrespondence
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedProducedSentenceTruth
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedProducedSentenceUnprovability
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedProducedNegationUnprovability
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedStrictContinuation
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedCausalParticipation
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedExecutedOccurrenceCorrespondence
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedExecutedSelfApplyImmediatelyPrecedesCertify
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedExecutedOutputsAreThePerimeterResources
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedCausalClosureRejection
#print axioms RelationalPerimeter.Tests.HeytingArithmeticGodelInstanceRegression.namedDirectedClosureRejection
/- AXIOM_AUDIT_END -/
