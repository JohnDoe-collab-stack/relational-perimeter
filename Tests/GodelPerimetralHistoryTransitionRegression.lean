import RelationalPerimeter.Constitution.HeytingArithmetic.GodelPerimetralHistoryTransition
import RelationalPerimeter.Constitution.GodelExplanatorySeparation

/-!
# Regression for the perimetral Gödel history transition

This gate checks the constitutive dependency added to the HA history tower.
The exact production occurrence leaves the transition waiting, whereas the
exact certification occurrence authorizes the successor.  The two outcomes
therefore cannot factor through `Unit`.

The proof-theoretic check is intentionally asymmetric.  Every derivation of
the produced boundary in its successor history uses the newest postulate.  The
already derivable sentence `0 = 0`, when added instead, has a preserved
derivation that does not use that newest postulate.  Thus the dependency is not a
mere consequence of extending a history by an arbitrary true sentence.
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
remain reproducible when both perimetral slots are replaced by `Unit`.  The
new necessity result therefore rests on the occurrence-driven action below,
not on retrospectively strengthening that old projection. -/
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

def BoundaryUsesNewestAfterExtension
    (history : TheoryHistory)
    (newest : Sentence) : Prop :=
  ∀ proof : Derivation LogicMode.intuitionistic
      (TheoryHistory.extend history newest).theory
      FormulaContext.nil newest.scopedFormula,
    historyDerivationUsesNewest proof = true

def reflexiveZeroExtensionFailsBoundaryNecessity :
    BoundaryUsesNewestAfterExtension TheoryHistory.root
      haReflexiveZeroSentence -> Empty := by
  intro requiresNewest
  have contradiction := requiresNewest rootZeroDerivationAfterZeroExtension
  rw [rootZeroDerivationAvoidsNewest] at contradiction
  cases contradiction

end RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootParticipation
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedProgression
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.UnitStagewiseProgressionShell
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootUnitStagewiseProgressionShell
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootUnitStagewiseShellStillRejectsExactBoundary
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProductionReadoutIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertificationReadoutIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProductionWaits
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertificationAuthorizesExactAdvance
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootRetainedResourceRemainsRetained
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootOccurrenceAdvanceDoesNotFactorThroughUnit
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedTargetIsExact
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCertifiedProgressionTargetIsExecutedAdvance
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.perimetralTowerStageZeroIsOriginal
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.perimetralTowerStageOneIsOriginal
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.perimetralTowerStageTwoIsOriginal
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootProducedBoundaryUsesNewest
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootCanonicalProducedBoundaryProofUsesNewest
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroDerivation
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroSoundExtension
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroDerivationAfterZeroExtension
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.rootZeroDerivationAvoidsNewest
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.BoundaryUsesNewestAfterExtension
#print axioms RelationalPerimeter.Tests.GodelPerimetralHistoryTransitionRegression.reflexiveZeroExtensionFailsBoundaryNecessity
/- AXIOM_AUDIT_END -/
