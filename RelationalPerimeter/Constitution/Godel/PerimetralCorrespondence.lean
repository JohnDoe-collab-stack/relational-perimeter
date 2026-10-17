import RelationalPerimeter.Constitution.Godel.PositiveExecutionCore

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Perimetral realization of an executed Godel witness

The diagonal sentence and its certification are produced by `Diagonal` before
this module constructs a circular presentation.  The affirmative perimeter and
its canonical continuation are constructed independently of any admission.

The terminal rejection deliberately follows the positive operational path

`CircularRefinement.realizesFinal`
  -> bilateral closure attempt
  -> totalization
  -> contraction kernel
  -> endpoint identification
  -> `Truth(G) -> Proof(G)`
  -> `Empty`
  -> `False`.

In particular, the central path below never projects the negative field of the
presentation, the obstruction stored in the closure attachment, or the
negative eliminator of `ContractedClosureDifference`.
-/

namespace StrongPerimetralTurning

universe uA uB uC uP uV

inductive ExecutedGodelPerimeterResource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    Type _
  | produced :
      ExecutedGodelSentenceProduction coding unprovabilityFormula ->
        ExecutedGodelPerimeterResource witness
  | certified :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
        ExecutedGodelPerimeterResource witness
  | continued :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
        ExecutedGodelPerimeterResource witness

inductive ExecutedGodelPerimeterCompatible
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ExecutedGodelPerimeterResource witness ->
      ExecutedGodelPerimeterResource witness -> Type _
  | atResource (resource : ExecutedGodelPerimeterResource witness) :
      ExecutedGodelPerimeterCompatible witness resource resource
  | productionToCertification :
      ExecutedGodelPerimeterCompatible witness
        (.produced witness.production) (.certified witness)
  | certificationToContinuation :
      ExecutedGodelPerimeterCompatible witness
        (.certified witness) (.continued witness)
  | continuationToProduction :
      ExecutedGodelPerimeterCompatible witness
        (.continued witness) (.produced witness.production)

def godelPerimeterNode
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation)
    (resource : ExecutedGodelPerimeterResource witness) :
    LocalNode
      (ExecutedGodelPerimeterResource witness)
      (ExecutedGodelPerimeterResource witness)
      (ExecutedGodelPerimeterCompatible witness)
      (ExecutedGodelWitness coding unprovabilityFormula interpretation)
      (fun candidate => PLift (candidate = witness)) :=
  { explicit := resource
    implicit := resource
    difference := witness
    provenance := .up rfl
    internallyCompatible := .atResource resource }

def godelPerimeter
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    PerimeterSpine (ExecutedGodelPerimeterCompatible witness)
      (godelPerimeterNode witness (.produced witness.production)) :=
  PerimeterSpine.advance
    (node := godelPerimeterNode witness (.produced witness.production))
    (nextNode := godelPerimeterNode witness (.certified witness))
    (.productionToCertification)
    (PerimeterSpine.advance
      (node := godelPerimeterNode witness (.certified witness))
      (nextNode := godelPerimeterNode witness (.continued witness))
      (.certificationToContinuation)
      (.boundary (godelPerimeterNode witness (.continued witness))))

def godelProductionPosition
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPosition (godelPerimeter witness) :=
  .here

def godelCertificationPosition
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPosition (godelPerimeter witness) :=
  .later .here

def godelProductionNextCertification
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingNext (godelPerimeter witness)
      (godelProductionPosition witness)
      (godelCertificationPosition witness) :=
  .here_next

structure ExecutedGodelTotalLoop
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) where
  endpointIdentification :
    interpretation.Truth witness.production.sentence =
      coding.Proof witness.production.sentence
  token : Unit

def ExecutedGodelTotalLoop.toProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (loop : ExecutedGodelTotalLoop witness) :
    ExecutedGodelProducedCompleteness witness :=
  fun truthWitness => Eq.mp loop.endpointIdentification truthWitness

def godelCircularPresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    CircularPresentation :=
  { Explicit := ExecutedGodelPerimeterResource witness
    Implicit := ExecutedGodelPerimeterResource witness
    Compatible := ExecutedGodelPerimeterCompatible witness
    Difference :=
      ExecutedGodelWitness coding unprovabilityFormula interpretation
    Provenance := fun candidate => PLift (candidate = witness)
    initialNode :=
      godelPerimeterNode witness (.produced witness.production)
    perimeter := godelPerimeter witness
    perimeterPositive := .here
    finalJunction := .continuationToProduction
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
      { endpointIdentification := equality
        token := () }
    loopContractsInitialDifference := fun loop =>
      loop.endpointIdentification
    rejectInitialContraction := fun _provenance contraction =>
      Empty.elim
        (witness.unprovable (Eq.mp contraction witness.trueWitness)) }

theorem godelInitialDifference_is_witness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    (godelCircularPresentation witness).initialNode.difference = witness :=
  rfl

def godelInitialProvenance
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    (godelCircularPresentation witness).Provenance
      (godelCircularPresentation witness).initialNode.difference :=
  by
    change PLift (_ = witness)
    exact PLift.up rfl

theorem godelProvenance_retains_witness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness candidate :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (provenance :
      (godelCircularPresentation witness).Provenance candidate) :
    candidate = witness :=
  provenance.down

structure ExecutedGodelPerimetralOccurrenceCorrespondence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  executed : ExecutedGodelProductionOccurrences execution
  productionIsWitnessProduction :
    executed.production = execution.witness.production
  diagonalizeSelfApplyDistinct :
    executed.diagonalizeOccurrence ≠ executed.selfApplyOccurrence
  selfApplyCertifyDistinct :
    executed.selfApplyOccurrence ≠ executed.certifyOccurrence
  perimeterProduction :
    NonClosingPosition (godelPerimeter execution.witness)
  perimeterCertification :
    NonClosingPosition (godelPerimeter execution.witness)
  perimeterProductionIsCanonical :
    perimeterProduction = godelProductionPosition execution.witness
  perimeterCertificationIsCanonical :
    perimeterCertification = godelCertificationPosition execution.witness
  perimeterProductionNextCertification :
    NonClosingNext (godelPerimeter execution.witness)
      perimeterProduction perimeterCertification
  productionResourceExact :
    (godelCircularPresentation execution.witness).initialNode.explicit =
      ExecutedGodelPerimeterResource.produced executed.production

def executedGodelPerimetralOccurrenceCorrespondenceFromCore
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (core : GodelPositiveExecutionCore execution) :
    ExecutedGodelPerimetralOccurrenceCorrespondence execution := by
  let executed := core.occurrences
  have productionExact :
      executed.production = execution.witness.production := by
    exact core.productionIsWitnessProduction
  exact
    { executed := executed
      productionIsWitnessProduction := productionExact
      diagonalizeSelfApplyDistinct :=
        executed.diagonalizeNextSelfApply.toPrecedes.ne
      selfApplyCertifyDistinct :=
        executed.selfApplyNextCertify.toPrecedes.ne
      perimeterProduction := godelProductionPosition execution.witness
      perimeterCertification := godelCertificationPosition execution.witness
      perimeterProductionIsCanonical := rfl
      perimeterCertificationIsCanonical := rfl
      perimeterProductionNextCertification :=
        godelProductionNextCertification execution.witness
      productionResourceExact := by
        change
          ExecutedGodelPerimeterResource.produced
              execution.witness.production =
            ExecutedGodelPerimeterResource.produced executed.production
        rw [productionExact] }

def executedGodelPerimetralOccurrenceCorrespondence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ExecutedGodelPerimetralOccurrenceCorrespondence execution :=
  executedGodelPerimetralOccurrenceCorrespondenceFromCore
    (godelPositiveExecutionCore execution)

abbrev godelPerimetralPresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    CircularPresentation :=
  godelCircularPresentation execution.witness

abbrev godelPerimetralContinuation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    RootedGeneratedHistory (godelPerimetralPresentation execution) :=
  oneStepAfterPerimeter (godelPerimetralPresentation execution)

theorem godelContinuation_sourceResource_is_continued
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    implicitRead
        (perimeterEndpoint (godelPerimetralPresentation execution)) =
      ReturnedImplicit.source
        (ExecutedGodelPerimeterResource.continued execution.witness) := by
  change implicitAt
      (perimeterEndpoint (godelPerimetralPresentation execution)).1 = _
  rw [perimeterEndpoint_cursor_boundary]
  rfl

theorem godelContinuation_sourceDifference_is_witness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    boundaryDifferenceReadout
        (perimeterEndpoint
          (godelPerimetralPresentation execution)).2.2 =
      ReturnedDifference.source execution.witness := by
  change differenceAtCursor
      (perimeterEndpoint (godelPerimetralPresentation execution)).1 = _
  rw [perimeterEndpoint_cursor_boundary]
  rfl

def godelContinuation_sourceProvenance_retains_witness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    PLift
      ((godelPerimetralPresentation execution).perimeter.finalNode.difference =
        execution.witness) := by
  change PLift (execution.witness = execution.witness)
  exact PLift.up rfl

def godelContinuationSourceProvenanceAtWitness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ReturnedProvenance (godelPerimetralPresentation execution)
      (ReturnedDifference.source execution.witness) :=
  Eq.mp
    (congrArg (ReturnedProvenance (godelPerimetralPresentation execution))
      (godelContinuation_sourceDifference_is_witness execution))
    (boundaryProvenanceReadout
      (perimeterEndpoint (godelPerimetralPresentation execution)).2.2)

def godelContinuationGeneratedStep
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GeneratedStep
      (perimeterEndpoint (godelPerimetralPresentation execution))
      (generate_after_perimeter
        (godelPerimetralPresentation execution)).1 :=
  (generate_after_perimeter (godelPerimetralPresentation execution)).2

theorem godelContinuation_targetResource_is_firstFree
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    explicitRead
        (generate_after_perimeter
          (godelPerimetralPresentation execution)).1 =
      ReturnedExplicit.formed (.beyond .first) := by
  change explicitAt
      (generate_after_perimeter
        (godelPerimetralPresentation execution)).1.1 = _
  rw [generate_after_perimeter_is_beyond]
  rfl

theorem godelContinuation_compatibility_is_leaveBoundary
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    HEq (godelContinuationGeneratedStep execution).compatibility
      (ReturnedCompatible.leaveBoundary
        (godelPerimetralPresentation execution).perimeter.finalNode) := by
  exact (godelContinuationGeneratedStep execution).compatibilityWitnessExact.trans
    (by
      rw [perimeterEndpoint_cursor_boundary]
      rfl)

theorem godelFinalJunction_is_continuationToProduction
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    HEq (godelPerimetralPresentation execution).finalJunction
      (ExecutedGodelPerimeterCompatible.continuationToProduction
        (witness := execution.witness)) := by
  rfl

structure GodelAffirmativeConstitution
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  occurrenceCorrespondence :
    ExecutedGodelPerimetralOccurrenceCorrespondence execution
  whole :
    ExactPerimeterRealization (godelPerimetralPresentation execution)
      (perimeterDeployment (godelPerimetralPresentation execution))
  labelledContinuation :
    FaithfullyLabelledPerimeterExtension
      (godelPerimetralPresentation execution)
      (godelPerimetralContinuation execution)
  positiveContinuation :
    PositiveContinuation labelledContinuation.extension
  strictContinuation :
    StrictConstitutivePrefix
      (perimeterDeployment (godelPerimetralPresentation execution))
      (godelPerimetralContinuation execution)
  sourceResourceExact :
    implicitRead
        (perimeterEndpoint (godelPerimetralPresentation execution)) =
      ReturnedImplicit.source
        (ExecutedGodelPerimeterResource.continued execution.witness)
  sourceDifferenceExact :
    boundaryDifferenceReadout
        (perimeterEndpoint
          (godelPerimetralPresentation execution)).2.2 =
      ReturnedDifference.source execution.witness
  sourceProvenanceAtWitness :
    ReturnedProvenance (godelPerimetralPresentation execution)
      (ReturnedDifference.source execution.witness)
  targetResourceExact :
    explicitRead
        (generate_after_perimeter
          (godelPerimetralPresentation execution)).1 =
      ReturnedExplicit.formed (.beyond .first)
  actionCompatibilityExact :
    HEq (godelContinuationGeneratedStep execution).compatibility
      (ReturnedCompatible.leaveBoundary
        (godelPerimetralPresentation execution).perimeter.finalNode)
  finalJunctionExact :
    HEq (godelPerimetralPresentation execution).finalJunction
      (ExecutedGodelPerimeterCompatible.continuationToProduction
        (witness := execution.witness))
  productionOccurrence :
    History.Occurrence (godelPerimetralContinuation execution).history
  certificationOccurrence :
    History.Occurrence (godelPerimetralContinuation execution).history
  continuationOccurrence :
    History.Occurrence (godelPerimetralContinuation execution).history
  productionOccurrenceIsOld :
    productionOccurrence =
      labelledContinuation.extension.oldOccurrence
        (godelProductionPosition execution.witness)
  certificationOccurrenceIsOld :
    certificationOccurrence =
      labelledContinuation.extension.oldOccurrence
        (godelCertificationPosition execution.witness)
  productionCertificationDistinct :
    productionOccurrence ≠ certificationOccurrence
  productionContinuationDistinct :
    productionOccurrence ≠ continuationOccurrence
  certificationContinuationDistinct :
    certificationOccurrence ≠ continuationOccurrence

def godelAffirmativeConstitutionFromCore
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (core : GodelPositiveExecutionCore execution) :
    GodelAffirmativeConstitution execution := by
  let labelled :=
    oneStepFaithfullyLabelledExtension
      (godelPerimetralPresentation execution)
  let positive :=
    oneStepAfterPerimeter_positiveContinuation
      (godelPerimetralPresentation execution)
  let newInContinuation : History.Occurrence labelled.continuation :=
    transportOccurrence positive.historyExact.symm
      positive.path.lastOccurrence
  exact
  { occurrenceCorrespondence :=
      executedGodelPerimetralOccurrenceCorrespondenceFromCore core
    whole := perimeterRealization (godelPerimetralPresentation execution)
    labelledContinuation := labelled
    positiveContinuation := positive
    strictContinuation :=
      oneStepAfterPerimeterStrict (godelPerimetralPresentation execution)
    sourceResourceExact :=
      godelContinuation_sourceResource_is_continued execution
    sourceDifferenceExact :=
      godelContinuation_sourceDifference_is_witness execution
    sourceProvenanceAtWitness :=
      godelContinuationSourceProvenanceAtWitness execution
    targetResourceExact :=
      godelContinuation_targetResource_is_firstFree execution
    actionCompatibilityExact :=
      godelContinuation_compatibility_is_leaveBoundary execution
    finalJunctionExact :=
      godelFinalJunction_is_continuationToProduction execution
    productionOccurrence :=
      labelled.extension.oldOccurrence
        (godelProductionPosition execution.witness)
    certificationOccurrence :=
      labelled.extension.oldOccurrence
        (godelCertificationPosition execution.witness)
    continuationOccurrence :=
      labelled.extension.newOccurrence newInContinuation
    productionOccurrenceIsOld := rfl
    certificationOccurrenceIsOld := rfl
    productionCertificationDistinct := by
      intro equality
      have positionEquality :=
        labelled.extension.oldOccurrence_injective equality
      exact (godelProductionNextCertification execution.witness).toPrecedes.ne
        positionEquality
    productionContinuationDistinct :=
      labelled.extension.old_new_occurrences_disjoint
        (godelProductionPosition execution.witness) newInContinuation
    certificationContinuationDistinct :=
      labelled.extension.old_new_occurrences_disjoint
        (godelCertificationPosition execution.witness) newInContinuation }

def godelAffirmativeConstitution
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelAffirmativeConstitution execution :=
  godelAffirmativeConstitutionFromCore (godelPositiveExecutionCore execution)

abbrev GodelPositiveSameRegimeAdmission
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    Type _ :=
  Sigma fun refinement :
      CircularRefinement (godelPerimetralPresentation execution)
        (godelPerimetralContinuation execution) =>
    PositiveContinuation refinement.extension

def godelFinalInterpretationOf
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    FinalClosureInterpretation (godelPerimetralPresentation execution)
      (godelPerimetralContinuation execution) :=
  finalClosureInterpretation
    (finalBoundaryOccurrence admission.1.toLabelled admission.2)

def godelBilateralClosureAttemptOf
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    BilateralClosureAttemptAt (godelFinalInterpretationOf admission) :=
  admission.1.realizesFinal admission.2

def godelExplicitTotalizationOf
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ExplicitTotalization (godelPerimetralPresentation execution) :=
  (godelBilateralClosureAttemptOf admission).explicitTotalization

def godelImplicitTotalizationOf
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ImplicitTotalization (godelPerimetralPresentation execution) :=
  (godelBilateralClosureAttemptOf admission).implicitTotalization

def godelExplicitKernelOf
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ExplicitContractionKernel (godelPerimetralPresentation execution) :=
  (godelExplicitTotalizationOf admission).toContractionKernel

def godelImplicitKernelOf
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ImplicitContractionKernel (godelPerimetralPresentation execution) :=
  (godelImplicitTotalizationOf admission).toContractionKernel

def godelExplicitKernelToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (kernel : ExplicitContractionKernel (godelCircularPresentation witness)) :
    ExecutedGodelProducedCompleteness witness :=
  by
    have endpointEquality :=
      (explicitKernelContractsClosureDifference kernel).endpointContraction
    change interpretation.Truth witness.production.sentence =
      coding.Proof witness.production.sentence at endpointEquality
    exact fun truthWitness => Eq.mp endpointEquality truthWitness

def godelImplicitKernelToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (kernel : ImplicitContractionKernel (godelCircularPresentation witness)) :
    ExecutedGodelProducedCompleteness witness :=
  by
    have endpointEquality :=
      (implicitKernelContractsClosureDifference kernel).endpointContraction
    change interpretation.Truth witness.production.sentence =
      coding.Proof witness.production.sentence at endpointEquality
    exact fun truthWitness => Eq.mp endpointEquality truthWitness

def godelExplicitAdmissionToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ExecutedGodelProducedCompleteness execution.witness :=
  godelExplicitKernelToProducedCompleteness
    (godelExplicitKernelOf admission)

def godelImplicitAdmissionToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ExecutedGodelProducedCompleteness execution.witness :=
  godelImplicitKernelToProducedCompleteness
    (godelImplicitKernelOf admission)

def godelExplicitKernelToTotalLoop
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (kernel : ExplicitContractionKernel (godelCircularPresentation witness)) :
    (godelCircularPresentation witness).TotalLoop :=
  (explicitKernelContractsClosureDifference kernel).toTotalLoop

def godelImplicitKernelToTotalLoop
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (kernel : ImplicitContractionKernel (godelCircularPresentation witness)) :
    (godelCircularPresentation witness).TotalLoop :=
  (implicitKernelContractsClosureDifference kernel).toTotalLoop

def rejectGodelExplicitAdmissionToEmpty
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : Empty :=
  execution.witness.unprovable
    (godelExplicitAdmissionToProducedCompleteness admission
      execution.witness.trueWitness)

def rejectGodelImplicitAdmissionToEmpty
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : Empty :=
  execution.witness.unprovable
    (godelImplicitAdmissionToProducedCompleteness admission
      execution.witness.trueWitness)

def rejectGodelExplicitSameRegimeAdmission
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : False :=
  Empty.elim (rejectGodelExplicitAdmissionToEmpty admission)

def rejectGodelImplicitSameRegimeAdmission
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : False :=
  Empty.elim (rejectGodelImplicitAdmissionToEmpty admission)

structure ExecutedGodelPerimetralCorrespondence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  producedDiagonalSentenceIsExact :
    execution.witness.production.sentence =
      godelSentence coding unprovabilityFormula
  exactFixedPoint :
    coding.ProvableIff execution.witness.production.sentence
      (coding.substitute unprovabilityFormula
        (coding.quoteSentence execution.witness.production.sentence))
  producedTruth :
    interpretation.Truth execution.witness.production.sentence
  producedUnprovability :
    coding.Proof execution.witness.production.sentence -> Empty
  presentationIsBuiltFromWitness :
    godelPerimetralPresentation execution =
      godelCircularPresentation execution.witness
  affirmative : GodelAffirmativeConstitution execution
  positiveWhole :
    ExactPerimeterRealization (godelPerimetralPresentation execution)
      (perimeterDeployment (godelPerimetralPresentation execution))
  strictContinuation :
    StrictConstitutivePrefix
      (perimeterDeployment (godelPerimetralPresentation execution))
      (godelPerimetralContinuation execution)
  finalInterpretationOf :
    GodelPositiveSameRegimeAdmission execution ->
      FinalClosureInterpretation (godelPerimetralPresentation execution)
        (godelPerimetralContinuation execution)
  sameRegimeAdmissionToBilateralAttempt :
    (admission : GodelPositiveSameRegimeAdmission execution) ->
      BilateralClosureAttemptAt (finalInterpretationOf admission)
  admissionToExplicitContractionKernel :
    GodelPositiveSameRegimeAdmission execution ->
      ExplicitContractionKernel (godelPerimetralPresentation execution)
  explicitKernelToProducedCompleteness :
    ExplicitContractionKernel (godelPerimetralPresentation execution) ->
      ExecutedGodelProducedCompleteness execution.witness
  explicitAdmissionToCompleteness :
    GodelPositiveSameRegimeAdmission execution ->
      ExecutedGodelProducedCompleteness execution.witness
  implicitAdmissionToCompleteness :
    GodelPositiveSameRegimeAdmission execution ->
      ExecutedGodelProducedCompleteness execution.witness
  explicitAdmissionToEmpty :
    GodelPositiveSameRegimeAdmission execution -> Empty
  implicitAdmissionToEmpty :
    GodelPositiveSameRegimeAdmission execution -> Empty
  explicitAdmissionRejected :
    GodelPositiveSameRegimeAdmission execution -> False
  implicitAdmissionRejected :
    GodelPositiveSameRegimeAdmission execution -> False

def executedGodelPerimetralCorrespondence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ExecutedGodelPerimetralCorrespondence execution := by
  let affirmative := godelAffirmativeConstitution execution
  exact
  { producedDiagonalSentenceIsExact :=
      execution.witness.production.sentence_is_godelSentence
    exactFixedPoint := execution.witness.fixedPoint
    producedTruth := execution.witness.trueWitness
    producedUnprovability := execution.witness.unprovable
    presentationIsBuiltFromWitness := rfl
    affirmative := affirmative
    positiveWhole := affirmative.whole
    strictContinuation := affirmative.strictContinuation
    finalInterpretationOf := fun admission =>
      godelFinalInterpretationOf admission
    sameRegimeAdmissionToBilateralAttempt := fun admission =>
      godelBilateralClosureAttemptOf admission
    admissionToExplicitContractionKernel := fun admission =>
      godelExplicitKernelOf admission
    explicitKernelToProducedCompleteness := fun kernel =>
      godelExplicitKernelToProducedCompleteness kernel
    explicitAdmissionToCompleteness := fun admission =>
      godelExplicitAdmissionToProducedCompleteness admission
    implicitAdmissionToCompleteness := fun admission =>
      godelImplicitAdmissionToProducedCompleteness admission
    explicitAdmissionToEmpty := fun admission =>
      rejectGodelExplicitAdmissionToEmpty admission
    implicitAdmissionToEmpty := fun admission =>
      rejectGodelImplicitAdmissionToEmpty admission
    explicitAdmissionRejected := fun admission =>
      rejectGodelExplicitSameRegimeAdmission admission
    implicitAdmissionRejected := fun admission =>
      rejectGodelImplicitSameRegimeAdmission admission }

def effectiveGodelPerimetralCorrespondence
    (system : EffectivelyPresentedSoundGodelSystem) :
    ExecutedGodelPerimetralCorrespondence (effectiveGodelExecution system) :=
  executedGodelPerimetralCorrespondence (effectiveGodelExecution system)

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.ExecutedGodelPerimeterResource
#print axioms StrongPerimetralTurning.ExecutedGodelPerimeterCompatible
#print axioms StrongPerimetralTurning.godelPerimeterNode
#print axioms StrongPerimetralTurning.godelPerimeter
#print axioms StrongPerimetralTurning.godelProductionPosition
#print axioms StrongPerimetralTurning.godelCertificationPosition
#print axioms StrongPerimetralTurning.godelProductionNextCertification
#print axioms StrongPerimetralTurning.ExecutedGodelTotalLoop
#print axioms StrongPerimetralTurning.ExecutedGodelTotalLoop.toProducedCompleteness
#print axioms StrongPerimetralTurning.godelCircularPresentation
#print axioms StrongPerimetralTurning.godelInitialDifference_is_witness
#print axioms StrongPerimetralTurning.godelInitialProvenance
#print axioms StrongPerimetralTurning.godelProvenance_retains_witness
#print axioms StrongPerimetralTurning.ExecutedGodelPerimetralOccurrenceCorrespondence
#print axioms StrongPerimetralTurning.executedGodelPerimetralOccurrenceCorrespondenceFromCore
#print axioms StrongPerimetralTurning.executedGodelPerimetralOccurrenceCorrespondence
#print axioms StrongPerimetralTurning.godelPerimetralPresentation
#print axioms StrongPerimetralTurning.godelPerimetralContinuation
#print axioms StrongPerimetralTurning.godelContinuation_sourceResource_is_continued
#print axioms StrongPerimetralTurning.godelContinuation_sourceDifference_is_witness
#print axioms StrongPerimetralTurning.godelContinuation_sourceProvenance_retains_witness
#print axioms StrongPerimetralTurning.godelContinuationSourceProvenanceAtWitness
#print axioms StrongPerimetralTurning.godelContinuationGeneratedStep
#print axioms StrongPerimetralTurning.godelContinuation_targetResource_is_firstFree
#print axioms StrongPerimetralTurning.godelContinuation_compatibility_is_leaveBoundary
#print axioms StrongPerimetralTurning.godelFinalJunction_is_continuationToProduction
#print axioms StrongPerimetralTurning.GodelAffirmativeConstitution
#print axioms StrongPerimetralTurning.godelAffirmativeConstitutionFromCore
#print axioms StrongPerimetralTurning.godelAffirmativeConstitution
#print axioms StrongPerimetralTurning.GodelPositiveSameRegimeAdmission
#print axioms StrongPerimetralTurning.godelFinalInterpretationOf
#print axioms StrongPerimetralTurning.godelBilateralClosureAttemptOf
#print axioms StrongPerimetralTurning.godelExplicitTotalizationOf
#print axioms StrongPerimetralTurning.godelImplicitTotalizationOf
#print axioms StrongPerimetralTurning.godelExplicitKernelOf
#print axioms StrongPerimetralTurning.godelImplicitKernelOf
#print axioms StrongPerimetralTurning.godelExplicitKernelToProducedCompleteness
#print axioms StrongPerimetralTurning.godelImplicitKernelToProducedCompleteness
#print axioms StrongPerimetralTurning.godelExplicitAdmissionToProducedCompleteness
#print axioms StrongPerimetralTurning.godelImplicitAdmissionToProducedCompleteness
#print axioms StrongPerimetralTurning.godelExplicitKernelToTotalLoop
#print axioms StrongPerimetralTurning.godelImplicitKernelToTotalLoop
#print axioms StrongPerimetralTurning.rejectGodelExplicitAdmissionToEmpty
#print axioms StrongPerimetralTurning.rejectGodelImplicitAdmissionToEmpty
#print axioms StrongPerimetralTurning.rejectGodelExplicitSameRegimeAdmission
#print axioms StrongPerimetralTurning.rejectGodelImplicitSameRegimeAdmission
#print axioms StrongPerimetralTurning.ExecutedGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.executedGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.effectiveGodelPerimetralCorrespondence
/- AXIOM_AUDIT_END -/
