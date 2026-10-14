import RelationalPerimeter.Constitution.ArithmeticGodelCorrespondence

/-!
# Scope regression for the abstract Gödel adapter

This test deliberately preserves the smallest countermodel accepted by
`EffectivelyPresentedSoundGodelSystem`.  Its purpose is to prevent that
abstract compatibility interface from being cited as a realization of a
non-trivial arithmetic theory.  The stronger public arithmetic entry point is
`SemanticallyDefinedProofArithmeticTheory`, whose substitution and proof
relation laws are not fields of this countermodel.
-/

namespace RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression

open StrongPerimetralTurning

def abstractDegenerateSystem : EffectivelyPresentedSoundGodelSystem :=
  { UnaryFormula := Unit
    Sentence := Unit
    encodeUnary := fun _ => 0
    decodeUnary := fun _ => some ()
    decodeUnary_encode := fun _ => rfl
    encodeSentence := fun _ => 0
    decodeSentence := fun _ => some ()
    decodeSentence_encode := fun _ => rfl
    substitute := fun _ _ => ()
    diagonalize := fun _ => ()
    proofCheck := fun _ _ => false
    equivalenceCheck := fun _ _ _ => true
    diagonalizeExact := fun _ _ => ⟨0, ⟨rfl⟩⟩
    proofForward := fun _ proof => nomatch proof.2.down
    proofBackward := fun _ proof => nomatch proof.2.down
    Truth := fun _ => Unit
    proofSound := fun proof => nomatch proof.2.down
    equivalenceTruthForward := fun _ truth => truth
    equivalenceTruthBackward := fun _ truth => truth
    unprovabilityFormula := ()
    representsUnprovabilityForward :=
      fun _ _ proof => nomatch proof.2.down
    representsUnprovabilityBackward := fun _ _ => () }

def abstractDegenerateCorrespondence :
    EffectiveGodelPerimetralCorrespondence abstractDegenerateSystem :=
  effectiveGodelPerimetralCorrespondence abstractDegenerateSystem

theorem abstractInterfaceDoesNotImplyAnyProofExists
    (sentence : Unit) :
    CheckedSentenceProof abstractDegenerateSystem.encodeSentence
      abstractDegenerateSystem.proofCheck sentence → False :=
  fun proof => nomatch proof.2.down

theorem abstractDegenerateHistoryStillPinsItsExactExit :
    abstractDegenerateCorrespondence.execution.exit =
      arithmeticCanonicalExecutedGodelRegimeExit
        abstractDegenerateSystem.toGodelSyntax
        abstractDegenerateSystem.unprovabilityFormula
        abstractDegenerateSystem.toGodelInterpretation :=
  abstractDegenerateCorrespondence.execution.arithmeticHistoryPinsExit

def abstractDegenerateCausalParticipation :
    ArithmeticExecutedGodelCausalParticipation
      abstractDegenerateCorrespondence.execution :=
  abstractDegenerateCorrespondence.execution.arithmeticCausalParticipation

theorem abstractDegenerateContinuationIsProducedByTurning :
    abstractDegenerateCausalParticipation.continuation =
      appendGenerated abstractDegenerateCausalParticipation.turning.deployment
        abstractDegenerateCausalParticipation.turning.continuesFreelyBeyondPerimeter :=
  abstractDegenerateCausalParticipation.continuationIsTurningExtension

def abstractDegenerateTurningProducesStrictContinuation :
    StrictConstitutivePrefix
      (perimeterDeployment
        (ArithmeticExecutedGodelPresentation
          abstractDegenerateCorrespondence.execution))
      abstractDegenerateCausalParticipation.continuation :=
  abstractDegenerateCausalParticipation.strictTurningContinuation

def abstractDegenerateCausalContinuationIsLocallyExact :
    ExactNonClosingRealization
      (ArithmeticExecutedGodelPresentation
        abstractDegenerateCorrespondence.execution)
      abstractDegenerateCausalParticipation.continuation :=
  abstractDegenerateCausalParticipation.locallyExact

theorem abstractDegenerateProductionPrecedesCertification :
    History.OccurrencePrecedes
      abstractDegenerateCausalParticipation.productionOccurrence
      abstractDegenerateCausalParticipation.certificationOccurrence :=
  abstractDegenerateCausalParticipation.productionPrecedesCertification

theorem abstractDegenerateResidualIsDistinctFromBothInteriorOccurrences :
    abstractDegenerateCausalParticipation.labelled.extension.oldOccurrence
          (arithmeticExecutedGodelProductionPosition
            abstractDegenerateCorrespondence.execution.exit.witness) ≠
        abstractDegenerateCausalParticipation.labelled.extension.newOccurrence
          abstractDegenerateCausalParticipation.residualOccurrence ∧
      abstractDegenerateCausalParticipation.labelled.extension.oldOccurrence
          (arithmeticExecutedGodelCertificationPosition
            abstractDegenerateCorrespondence.execution.exit.witness) ≠
        abstractDegenerateCausalParticipation.labelled.extension.newOccurrence
          abstractDegenerateCausalParticipation.residualOccurrence :=
  ⟨abstractDegenerateCausalParticipation.residualDiffersFromProduction,
    abstractDegenerateCausalParticipation.residualDiffersFromCertification⟩

def abstractDegenerateFinalInterpretationCarriesHistoricalProvenance :
    (ArithmeticExecutedGodelPresentation
      abstractDegenerateCorrespondence.execution).Provenance
      (ArithmeticExecutedGodelPresentation
        abstractDegenerateCorrespondence.execution).perimeter.finalNode.difference :=
  abstractDegenerateCausalParticipation.historicalProvenance

def abstractDegenerateSpecifiedClosureFactorsThroughHistoricalProvenance :
    CircularClosureMeaning
        (ArithmeticExecutedGodelPresentation
          abstractDegenerateCorrespondence.execution)
        abstractDegenerateCausalParticipation.continuation →
      ExecutedGodelProducedCompleteness
        abstractDegenerateCorrespondence.execution.exit.witness :=
  fun closure =>
    abstractDegenerateCausalParticipation.causalClosureToProducedCompleteness
      (abstractDegenerateCausalParticipation.circularClosureToCausalClosure
        closure)

def abstractDegenerateSpecifiedClosureIsRejectedByProducedFixedPoint :
    CircularClosureMeaning
        (ArithmeticExecutedGodelPresentation
          abstractDegenerateCorrespondence.execution)
        abstractDegenerateCausalParticipation.continuation → Empty :=
  abstractDegenerateCausalParticipation.rejectSpecifiedClosure

/- The directed semantic-completeness obligation is not contradictory by
   itself.  A sentence already proved by the corrected kernel admits the map
   from truth to proof, independently of how many proof witnesses it has. -/
abbrev kernelDecidedSentence : NumberedSentence :=
  .apply .theoremFormula 0

def kernelDecidedSentenceProof :
    UniformNumberedProof UniformKernelSeed kernelDecidedSentence :=
  ⟨godelPair 5 (NumberedProofCode.theoremIntroduction 0),
    .admitted (.theoremIntroduction 0)⟩

def kernelDecidedSentenceTruth :
    uniformNumberedSentenceTruth UniformKernelSeed kernelDecidedSentence :=
  UniformNumberedProof.sound uniformKernelSeedSound kernelDecidedSentenceProof

def kernelDecidedSentenceSupportsDirectedCompleteness :
    DirectedSemanticCompletenessAt
      (uniformNumberedSentenceTruth UniformKernelSeed)
      (UniformNumberedProof UniformKernelSeed)
      kernelDecidedSentence :=
  fun _ => kernelDecidedSentenceProof

end RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateSystem
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateCorrespondence
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractInterfaceDoesNotImplyAnyProofExists
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateHistoryStillPinsItsExactExit
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateCausalParticipation
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateContinuationIsProducedByTurning
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateTurningProducesStrictContinuation
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateCausalContinuationIsLocallyExact
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateProductionPrecedesCertification
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateResidualIsDistinctFromBothInteriorOccurrences
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateFinalInterpretationCarriesHistoricalProvenance
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateSpecifiedClosureFactorsThroughHistoricalProvenance
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateSpecifiedClosureIsRejectedByProducedFixedPoint
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.kernelDecidedSentence
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.kernelDecidedSentenceProof
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.kernelDecidedSentenceTruth
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.kernelDecidedSentenceSupportsDirectedCompleteness
/- AXIOM_AUDIT_END -/
