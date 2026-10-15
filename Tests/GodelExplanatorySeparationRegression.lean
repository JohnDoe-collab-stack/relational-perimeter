import RelationalPerimeter.Constitution.GodelExplanatorySeparation
import Tests.GodelCorrespondenceScopeRegression

/-!
# Regression for the Gödel explanatory separation

This test keeps three obligations together without changing their scope:
the concrete HA anchor has an explicit checked proof, that anchor remains
distinct from the produced diagonal sentence, and the proofless abstract
countermodel cannot construct the new positive boundary.  It also reuses the
pre-existing causal and closure results of the countermodel instead of
redefining it.
-/

namespace RelationalPerimeter.Tests.GodelExplanatorySeparationRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic
open RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression

def namedSelectiveBoundary :
    EffectiveGodelSelectiveBoundary heytingArithmeticEffectiveGodelSystem :=
  heytingArithmeticGodelSelectiveBoundary

def namedAnchorProof :
    CheckedSentenceProof Sentence.quote haProofCheck haReflexiveZeroSentence :=
  heytingArithmeticReflexiveZeroCheckedProof

def namedAnchorTruth : haTruth haReflexiveZeroSentence :=
  heytingArithmeticReflexiveZeroTruth

def namedAnchorCompleteness :
    DirectedSemanticCompletenessAt haTruth
      (CheckedSentenceProof Sentence.quote haProofCheck)
      haReflexiveZeroSentence :=
  heytingArithmeticReflexiveZeroCompleteness

theorem namedAnchorDiffersFromProduced :
    haReflexiveZeroSentence ≠
      (heytingArithmeticGodelPerimetralCorrespondence.execution.exit.witness).production.sentence :=
  heytingArithmeticReflexiveZeroDiffersFromProduced

def namedSelectiveContrast :
    EffectiveGodelSelectiveBoundary.SelectiveContrast namedSelectiveBoundary :=
  heytingArithmeticSelectiveContrast

def namedBoundaryDoesNotReduceToProducedCompleteness :
    (EffectiveGodelSelectiveBoundary heytingArithmeticEffectiveGodelSystem →
      ExecutedGodelProducedCompleteness
        heytingArithmeticGodelPerimetralCorrespondence.execution.exit.witness) →
      Empty :=
  heytingArithmeticBoundaryDoesNotReduceToProducedCompleteness

def degenerateSelectiveBoundaryIsImpossible :
    EffectiveGodelSelectiveBoundary abstractDegenerateSystem → Empty :=
  prooflessSystemRejectsSelectiveBoundary abstractDegenerateSystem
    (fun sentence proof =>
      False.elim
        (abstractInterfaceDoesNotImplyAnyProofExists sentence proof))

def degenerateOldCorrespondenceStillExists :
    EffectiveGodelPerimetralCorrespondence abstractDegenerateSystem :=
  abstractDegenerateCorrespondence

def degenerateOldCausalParticipationStillExists :
    ArithmeticExecutedGodelCausalParticipation
      abstractDegenerateCorrespondence.execution :=
  abstractDegenerateCausalParticipation

def degenerateOldStrictContinuationStillExists :
    StrictConstitutivePrefix
      (perimeterDeployment
        (ArithmeticExecutedGodelPresentation
          abstractDegenerateCorrespondence.execution))
      abstractDegenerateCausalParticipation.continuation :=
  abstractDegenerateTurningProducesStrictContinuation

def degenerateOldClosureRejectionStillExists :
    CircularClosureMeaning
        (ArithmeticExecutedGodelPresentation
          abstractDegenerateCorrespondence.execution)
        abstractDegenerateCausalParticipation.continuation → Empty :=
  abstractDegenerateSpecifiedClosureIsRejectedByProducedFixedPoint

end RelationalPerimeter.Tests.GodelExplanatorySeparationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedSelectiveBoundary
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedAnchorProof
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedAnchorTruth
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedAnchorCompleteness
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedAnchorDiffersFromProduced
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedSelectiveContrast
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.namedBoundaryDoesNotReduceToProducedCompleteness
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.degenerateSelectiveBoundaryIsImpossible
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.degenerateOldCorrespondenceStillExists
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.degenerateOldCausalParticipationStillExists
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.degenerateOldStrictContinuationStillExists
#print axioms RelationalPerimeter.Tests.GodelExplanatorySeparationRegression.degenerateOldClosureRejectionStillExists
/- AXIOM_AUDIT_END -/
