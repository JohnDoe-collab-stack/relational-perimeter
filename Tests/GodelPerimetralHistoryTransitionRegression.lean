import RelationalPerimeter.Constitution.HeytingArithmetic.GodelPerimetralHistoryTransition
import RelationalPerimeter.Constitution.GodelExplanatorySeparation

/-!
# Regression for the perimetral Gödel history transition

This gate checks the constitutive dependency added to the HA history tower.
The exact production, certification and residual occurrences are consumed in
that order.  Certification and residual continuation carry the same Gödel
witness but yield distinct phase observations, so the observation family
cannot factor through the witness, the source stage, or `Unit`.

The proof-theoretic check is intentionally asymmetric.  Every derivation of
the produced boundary in its successor history uses the newest postulate.  The
already derivable sentence `0 = 0`, when added instead, has a preserved
derivation that does not use that newest postulate.  The general equivalence
test records that this diagnostic is exactly source non-derivability.  The
additional constitutive result is tested separately: certification and
residual continuation cannot factor through the source terminal facts alone.
-/

namespace RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic

def rootParticipation : StagePerimetralParticipation rootGodelHistoryStage :=
  rootGodelHistoryStage.perimetralParticipation

def rootCertifiedProgression :
    CertifiedPerimetralGodelHistoryProgression
      rootParticipatingGodelHistoryStage :=
  certifiedPerimetralGodelHistoryProgression _

/-- Scope control: the old product-shaped progression and its exact rejection
remain reproducible when both perimetral slots are replaced by `Unit`. -/
def UnitStagewiseProgressionShell
    (source : SoundGodelHistoryStage) : Type :=
  GodelHistoryProgression source × Unit × Unit

def rootUnitStagewiseProgressionShell :
    UnitStagewiseProgressionShell rootGodelHistoryStage :=
  ⟨godelHistoryProgression rootGodelHistoryStage, (), ()⟩

def rootUnitStagewiseShellStillRejectsExactBoundary :
    (SourceSentenceProofAtTarget rootGodelHistoryStage -> Empty) -> Empty :=
  rootUnitStagewiseProgressionShell.1.rejectsSourceBoundaryExclusion

theorem rootProductionReadoutIsExact :
    implicitRead rootParticipation.productionOccurrence.locatedStep.source =
      .source (.produced rootGodelHistoryStage.producedWitness.production) :=
  productionOccurrenceReturnedImplicit_exact _ _

theorem rootCertificationReadoutIsExact :
    implicitRead rootParticipation.certificationOccurrence.locatedStep.source =
      .source (.certified rootGodelHistoryStage.producedWitness) :=
  certificationOccurrenceReturnedImplicit_exact _ _

theorem rootResidualReadoutIsExact :
    implicitRead
      (rootParticipation.labelled.extension.newOccurrence
        rootParticipation.residualOccurrence).locatedStep.source =
      .source (.continued rootGodelHistoryStage.producedWitness) :=
  residualOccurrenceReturnedImplicit_exact _ _

theorem rootCertificationAndResidualCarrySameWitness :
    implicitRead rootParticipation.certificationOccurrence.locatedStep.source =
        .source (.certified rootGodelHistoryStage.producedWitness) ∧
      implicitRead
          (rootParticipation.labelled.extension.newOccurrence
            rootParticipation.residualOccurrence).locatedStep.source =
        .source (.continued rootGodelHistoryStage.producedWitness) :=
  ⟨rootCertificationReadoutIsExact, rootResidualReadoutIsExact⟩

theorem rootResidualAvailableResourceIsExact :
    residualOccurrenceAvailableResource rootGodelHistoryStage
        rootParticipation =
      some (.retained rootGodelHistoryStage.producedWitness) :=
  residualOccurrenceAvailableResource_exact _ _

theorem rootProductionWaits :
    stageAdvanceFromReturnedImplicit rootGodelHistoryStage
      (implicitRead rootParticipation.productionOccurrence.locatedStep.source) =
        some (.waiting) :=
  productionOccurrenceWaits _ _

theorem rootCertificationAuthorizesExactAdvance :
    stageAdvanceFromReturnedImplicit rootGodelHistoryStage
      (implicitRead rootParticipation.certificationOccurrence.locatedStep.source) =
        some (.authorized rootGodelHistoryStage.advance) :=
  certificationOccurrenceAdvancesExactly _ _

theorem rootResidualRetainsExactAdvance :
    stageAdvanceFromReturnedImplicit rootGodelHistoryStage
      (implicitRead
        (rootParticipation.labelled.extension.newOccurrence
          rootParticipation.residualOccurrence).locatedStep.source) =
      some (.retained rootGodelHistoryStage.advance) :=
  residualOccurrenceRetainsExactly _ _

theorem rootRetainedResourceRemainsRetained :
    stageAdvanceFromAvailableResource rootGodelHistoryStage
        (.retained rootGodelHistoryStage.producedWitness) =
      .retained rootGodelHistoryStage.advance := by
  cases rootGodelHistoryStage
  rfl

def rootOccurrenceAdvanceDoesNotFactorThroughUnit
    (factor : Unit ->
      Option (StageAdvanceState SoundGodelHistoryStage))
    (productionFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead rootParticipation.productionOccurrence.locatedStep.source) =
        factor ())
    (certificationFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead rootParticipation.certificationOccurrence.locatedStep.source) =
        factor ()) : Empty :=
  rootCertifiedProgression.phaseDoesNotFactorThroughUnit
    factor productionFactors certificationFactors

def rootWitnessPhaseDoesNotFactor
    (factor :
      ExecutedGodelWitness rootGodelHistoryStage.system.toGodelSyntax
        rootGodelHistoryStage.system.unprovabilityFormula
        rootGodelHistoryStage.system.toGodelInterpretation ->
      Option (StageAdvanceState SoundGodelHistoryStage))
    (certificationFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            rootParticipation.certificationOccurrence.locatedStep.source) =
        factor rootGodelHistoryStage.producedWitness)
    (residualFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            (rootParticipation.labelled.extension.newOccurrence
              rootParticipation.residualOccurrence).locatedStep.source) =
        factor rootGodelHistoryStage.producedWitness) :
    Empty :=
  rootCertifiedProgression.phaseDoesNotFactorThroughWitness
    factor certificationFactors residualFactors

def rootTerminalFactsPhaseDoesNotFactor
    (factor : SourceTerminalGodelFacts rootGodelHistoryStage ->
      Option (StageAdvanceState SoundGodelHistoryStage))
    (certificationFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            rootParticipation.certificationOccurrence.locatedStep.source) =
        factor (sourceTerminalGodelFacts rootGodelHistoryStage))
    (residualFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            (rootParticipation.labelled.extension.newOccurrence
              rootParticipation.residualOccurrence).locatedStep.source) =
        factor (sourceTerminalGodelFacts rootGodelHistoryStage)) :
    Empty :=
  rootCertifiedProgression.phaseDoesNotFactorThroughTerminalFacts
    factor certificationFactors residualFactors

def rootStagePhaseDoesNotFactor
    (factor : SoundGodelHistoryStage ->
      Option (StageAdvanceState SoundGodelHistoryStage))
    (certificationFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            rootParticipation.certificationOccurrence.locatedStep.source) =
        factor rootGodelHistoryStage)
    (residualFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            (rootParticipation.labelled.extension.newOccurrence
              rootParticipation.residualOccurrence).locatedStep.source) =
        factor rootGodelHistoryStage) :
    Empty :=
  stagePhaseDoesNotFactorThroughStage _ _ factor certificationFactors
    residualFactors

def rootUnitPhaseDoesNotFactor
    (factor : Unit -> Option (StageAdvanceState SoundGodelHistoryStage))
    (certificationFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            rootParticipation.certificationOccurrence.locatedStep.source) =
        factor ())
    (residualFactors :
      stageAdvanceFromReturnedImplicit rootGodelHistoryStage
          (implicitRead
            (rootParticipation.labelled.extension.newOccurrence
              rootParticipation.residualOccurrence).locatedStep.source) =
        factor ()) :
    Empty :=
  stagePhaseDoesNotFactorThroughUnit _ _ factor certificationFactors
    residualFactors

/-! The three phase consumers reject every out-of-order substitution. -/

theorem rootProducedConsumerRejectsCertification :
    consumeProducedStageResource
        (.certified rootGodelHistoryStage.producedWitness) =
      none :=
  rfl

theorem rootProducedConsumerRejectsResidual :
    consumeProducedStageResource
        (.retained rootGodelHistoryStage.producedWitness) =
      none :=
  rfl

theorem rootCertifiedConsumerRejectsProduction :
    consumeCertifiedStageResource
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        (.produced rootGodelHistoryStage.producedWitness.production) =
      none :=
  rfl

theorem rootCertifiedConsumerRejectsResidual :
    consumeCertifiedStageResource
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        (.retained rootGodelHistoryStage.producedWitness) =
      none :=
  rfl

def rootTransitionAuthorization :
    StageTransitionAuthorization SoundGodelHistoryStage :=
  ⟨rootGodelHistoryStage.advance⟩

def rootProducedStageResource :
    Option
      (StageAvailablePerimeterResource
        rootGodelHistoryStage.system.toGodelSyntax
        rootGodelHistoryStage.system.unprovabilityFormula
        rootGodelHistoryStage.system.toGodelInterpretation) :=
  some (.produced rootGodelHistoryStage.producedWitness.production)

def rootCertifiedStageResource :
    Option
      (StageAvailablePerimeterResource
        rootGodelHistoryStage.system.toGodelSyntax
        rootGodelHistoryStage.system.unprovabilityFormula
        rootGodelHistoryStage.system.toGodelInterpretation) :=
  some (.certified rootGodelHistoryStage.producedWitness)

def rootRetainedStageResource :
    Option
      (StageAvailablePerimeterResource
        rootGodelHistoryStage.system.toGodelSyntax
        rootGodelHistoryStage.system.unprovabilityFormula
        rootGodelHistoryStage.system.toGodelInterpretation) :=
  some (.retained rootGodelHistoryStage.producedWitness)

theorem rootRetainedConsumerRejectsProduction :
    consumeRetainedStageResource rootTransitionAuthorization
        ((.produced rootGodelHistoryStage.producedWitness.production) :
          StageAvailablePerimeterResource
            rootGodelHistoryStage.system.toGodelSyntax
            rootGodelHistoryStage.system.unprovabilityFormula
            rootGodelHistoryStage.system.toGodelInterpretation) =
      none :=
  rfl

theorem rootRetainedConsumerRejectsRepeatedCertification :
    consumeRetainedStageResource rootTransitionAuthorization
        (.certified rootGodelHistoryStage.producedWitness) =
      none :=
  rfl

theorem rootRetainedConsumerCompletes :
    consumeRetainedStageResource rootTransitionAuthorization
        (.retained rootGodelHistoryStage.producedWitness) =
      some ⟨rootGodelHistoryStage.advance⟩ :=
  rfl

theorem rootResourceTraceCompletes :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        rootProducedStageResource rootCertifiedStageResource
        rootRetainedStageResource =
      some ⟨rootGodelHistoryStage.advance⟩ :=
  rfl

theorem rootResourceTraceRejectsOmittedProduction :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        none rootCertifiedStageResource rootRetainedStageResource =
      none :=
  rfl

theorem rootResourceTraceRejectsOmittedCertification :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        rootProducedStageResource none rootRetainedStageResource =
      none :=
  rfl

theorem rootResourceTraceRejectsOmittedResidual :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        rootProducedStageResource rootCertifiedStageResource none =
      none :=
  rfl

theorem rootResourceTraceRejectsResidualBeforeCertification :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        rootProducedStageResource rootRetainedStageResource
        rootCertifiedStageResource =
      none :=
  rfl

theorem rootResourceTraceRejectsResidualReplacingCertification :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        rootProducedStageResource rootRetainedStageResource
        rootRetainedStageResource =
      none :=
  rfl

theorem rootResourceTraceRejectsRepeatedCertification :
    runStageTransitionResources
        (extendStageFromCertifiedWitness rootGodelHistoryStage)
        rootProducedStageResource rootCertifiedStageResource
        rootCertifiedStageResource =
      none :=
  rfl

theorem rootCanonicalTransitionCompletesExactly :
    runCompletedStageTransition rootGodelHistoryStage rootParticipation =
      some ⟨rootGodelHistoryStage.advance⟩ :=
  runCompletedStageTransition_exact _ _

theorem rootCompletedTargetIsExact :
    completedStageTarget rootCertifiedProgression.1 =
      rootGodelHistoryStage.advance :=
  completedStageOutcome_target_eq_advance _ _ _

def rootProgressionAtCompletedTarget :
    GodelHistoryProgressionAtTarget rootGodelHistoryStage
      (completedStageTarget rootCertifiedProgression.1) :=
  rootCertifiedProgression.progressionAtTarget

def rootLegacyProgressionCompatibility :
    GodelHistoryProgression rootGodelHistoryStage :=
  rootCertifiedProgression.progression

theorem rootTowerSuccessorUsesCompletedTarget :
    perimetralGodelHistoryStage 1 = rootCertifiedProgression.target :=
  rfl

theorem rootCertifiedTargetIsExact :
    certifiedTarget rootGodelHistoryStage rootParticipation =
      rootGodelHistoryStage.advance :=
  certifiedTarget_eq_advance _ _

theorem rootCertifiedProgressionTargetIsExecutedAdvance :
    rootCertifiedProgression.target =
      rootParticipatingGodelHistoryStage.advance :=
  certifiedPerimetralGodelHistoryProgression_target_eq_advance _

theorem perimetralTowerStageZeroIsOriginal :
    (perimetralGodelHistoryStage 0).1 = godelHistoryStage 0 :=
  perimetralGodelHistoryStage_stage_eq 0

theorem perimetralTowerStageOneIsOriginal :
    (perimetralGodelHistoryStage 1).1 = godelHistoryStage 1 :=
  perimetralGodelHistoryStage_stage_eq 1

theorem perimetralTowerStageTwoIsOriginal :
    (perimetralGodelHistoryStage 2).1 = godelHistoryStage 2 :=
  perimetralGodelHistoryStage_stage_eq 2

theorem rootProducedBoundaryUsesNewest :
    SourceBoundaryUsesNewestAtAdvance rootGodelHistoryStage :=
  sourceBoundaryUsesNewestAtAdvance rootGodelHistoryStage

theorem rootProducedBoundaryUsesNewestIffSourceUnprovable :
    SourceBoundaryUsesNewestAtAdvance rootGodelHistoryStage ↔
      ¬ HistoryProvable rootGodelHistoryStage.history
        rootGodelHistoryStage.producedSentence :=
  sourceBoundaryUsesNewestAtAdvance_iff_sourceUnprovable _

theorem rootCanonicalProducedBoundaryProofUsesNewest :
    historyDerivationUsesNewest
      (historyDerivationOfCheckedProof rootGodelHistoryStage.advance.history
        rootCertifiedProgression.progression.sourceSentenceProvableAtTarget) =
      true :=
  rootCertifiedProgression.sourceSentenceProofUsesNewest

def rootZeroDerivation :
    Derivation LogicMode.intuitionistic TheoryHistory.root.theory
      FormulaContext.nil haReflexiveZeroSentence.scopedFormula :=
  haDerivationToHistory TheoryHistory.root (numeralEqualityProof 0 0 0 rfl)

def rootZeroSoundExtension :
    SoundTheoryHistory
      (TheoryHistory.extend TheoryHistory.root haReflexiveZeroSentence) :=
  rootSoundTheoryHistory.extend heytingArithmeticReflexiveZeroTruth

def rootZeroDerivationAfterZeroExtension :
    Derivation LogicMode.intuitionistic
      (TheoryHistory.extend TheoryHistory.root haReflexiveZeroSentence).theory
      FormulaContext.nil haReflexiveZeroSentence.scopedFormula :=
  historyDerivationPreserve rootZeroDerivation

theorem rootZeroDerivationAvoidsNewest :
    historyDerivationUsesNewest rootZeroDerivationAfterZeroExtension = false :=
  rfl

def reflexiveZeroExtensionFailsBoundaryNecessity :
    BoundaryUsesNewestAfterExtension TheoryHistory.root
      haReflexiveZeroSentence -> Empty := by
  intro requiresNewest
  have contradiction := requiresNewest rootZeroDerivationAfterZeroExtension
  rw [rootZeroDerivationAvoidsNewest] at contradiction
  cases contradiction

/-- Scope control for R1: `usesNewest` also holds for the stipulated false
sentence, precisely because the sound root history does not derive it. -/
theorem rootFalseSentenceRequiresNewest :
    BoundaryUsesNewestAfterExtension TheoryHistory.root falseSentence :=
  (boundaryUsesNewestAfterExtension_iff_sourceUnprovable _ _).2 (by
    intro ⟨proof⟩
    exact
      historyDerivation_sound rootSoundTheoryHistory proof
        emptyEnvironment trivial)

end RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootParticipation
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedProgression
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.UnitStagewiseProgressionShell
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootUnitStagewiseProgressionShell
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootUnitStagewiseShellStillRejectsExactBoundary
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProductionReadoutIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertificationReadoutIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResidualReadoutIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertificationAndResidualCarrySameWitness
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResidualAvailableResourceIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProductionWaits
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertificationAuthorizesExactAdvance
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResidualRetainsExactAdvance
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootRetainedResourceRemainsRetained
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootOccurrenceAdvanceDoesNotFactorThroughUnit
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootWitnessPhaseDoesNotFactor
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootTerminalFactsPhaseDoesNotFactor
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootStagePhaseDoesNotFactor
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootUnitPhaseDoesNotFactor
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProducedConsumerRejectsCertification
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProducedConsumerRejectsResidual
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedConsumerRejectsProduction
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedConsumerRejectsResidual
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootTransitionAuthorization
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProducedStageResource
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedStageResource
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootRetainedStageResource
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootRetainedConsumerRejectsProduction
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootRetainedConsumerRejectsRepeatedCertification
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootRetainedConsumerCompletes
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceCompletes
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceRejectsOmittedProduction
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceRejectsOmittedCertification
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceRejectsOmittedResidual
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceRejectsResidualBeforeCertification
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceRejectsResidualReplacingCertification
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootResourceTraceRejectsRepeatedCertification
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCanonicalTransitionCompletesExactly
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCompletedTargetIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProgressionAtCompletedTarget
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootLegacyProgressionCompatibility
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootTowerSuccessorUsesCompletedTarget
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedTargetIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedProgressionTargetIsExecutedAdvance
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.perimetralTowerStageZeroIsOriginal
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.perimetralTowerStageOneIsOriginal
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.perimetralTowerStageTwoIsOriginal
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProducedBoundaryUsesNewest
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProducedBoundaryUsesNewestIffSourceUnprovable
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCanonicalProducedBoundaryProofUsesNewest
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroDerivation
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroSoundExtension
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroDerivationAfterZeroExtension
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroDerivationAvoidsNewest
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.reflexiveZeroExtensionFailsBoundaryNecessity
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootFalseSentenceRequiresNewest
/- AXIOM_AUDIT_END -/
