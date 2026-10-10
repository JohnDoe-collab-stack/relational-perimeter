import Tests.LocalAlignment.DocumentaryControlMeasuredTransport
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFeedback

/-! Assemble the original sequential stage from actual controlled schedules,
searches and transport outputs. Original stage references occur only in
erased proof fields. Deferred assignment readers remain a declared boundary. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def sourceFromInput (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery) :
    GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source :=
  ⟨input.assignment, by
    have same : discovery = canonicalStageDiscovery (depth + 1) :=
      Option.some.inj (canonicalFound.symm.trans (canonicalStageDiscovery_found _))
    change StructuralDecisionsHold input.assignment (scheduleFromDiscovery discovery).entry.source.context.decisions
    rw [same]; exact (sequentialSourceContinuation depth input).property⟩

theorem source_accepted (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery) :
    GeneratedStructuralBranchAccept (scheduleFromDiscovery discovery).entry.source
      (sourceFromInput depth input discovery canonicalFound) := by
  have same : discovery = canonicalStageDiscovery (depth + 1) :=
    Option.some.inj (canonicalFound.symm.trans (canonicalStageDiscovery_found _))
  cases same; exact sequentialSourceContinuation_accepted depth input

def nextFromApplication (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (validated : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery))
    (execution : ExecutedDiscoverySchedule validated)
    (application : AppliedDiscoveryExecution execution (sourceFromInput depth input discovery canonicalFound)) :
    SequentialAssignment (depth + 1) := by
  have same : discovery = canonicalStageDiscovery (depth + 1) :=
    Option.some.inj (canonicalFound.symm.trans (canonicalStageDiscovery_found _))
  have outputReference : application.output.1 =
      (applyDiscoveryExecution
        (executeValidatedDiscoverySchedule
          (validateDiscoverySchedule (scheduleFromDiscovery (canonicalStageDiscovery (depth + 1)))))
        (sequentialSourceContinuation depth input)).output.1 := by
    rw [application.assignment_from_returned_code, applyDiscoveryExecution_assignment,
      executedDiscoverySchedule_code]
    change Assignment.flipAt discovery.var input.assignment = _
    rw [same]; rfl
  let reader := readTransportedAssignment discovery.1
    execution.code (sourceFromInput depth input discovery canonicalFound) input.reader
  let indexedReader := Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) reader
    (congrArg Subtype.val application.outputExact).symm
  exact
    { assignment := application.output.1
      reader := indexedReader
      zeroTrue := by rw [outputReference]; exact returnedAssignment_zeroTrue depth input
      futureSelectedFalse := by rw [outputReference]; exact returnedAssignment_futureSelectedFalse depth input
      futureAnchorTrue := by rw [outputReference]; exact returnedAssignment_futureAnchorTrue depth input }

def fromParts (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction = (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (stored : StoredLocalSchedule discovery)
    (storedActual : stored = recorded.outcome.produceStoredSchedule discovery found)
    (validation : MeasuredScheduleValidation stored) (_validationActual : validation = validateStoredSchedule stored)
    (measured : MeasuredScheduleExecution validation) (_measuredActual : measured = executeStoredSchedule validation)
    (validated : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery))
    (validatedActual : validated = validation.validated)
    (execution : ExecutedDiscoverySchedule validated)
    (executionActual : HEq execution measured.execution)
    (source : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (sourceActual : source = sourceFromInput depth input discovery canonicalFound)
    (application : AppliedDiscoveryExecution execution source)
    (applicationActual : application = applyDiscoveryExecution execution source)
    (next : SequentialAssignment (depth + 1))
    (nextActual : HEq next (nextFromApplication depth input discovery canonicalFound validated execution
      (Eq.rec (motive := fun source _ => AppliedDiscoveryExecution execution source) application sourceActual))) :
    SequentialStageRun depth input :=
  { generation := generation, discoveryRun := recorded, extractionExact := extractionExact
    discovery := discovery, discoveryRunFound := found, discoveryExact := canonicalFound
    discoveryWorkLeCanonical := workLeCanonical
    storedSchedule := stored, storedScheduleExact := storedActual
    measuredValidation := validation, measuredExecution := measured
    schedule := scheduleFromDiscovery discovery, scheduleExact := rfl
    validated := validated, validatedFromMeasured := by cases validatedActual; rfl
    execution := execution, executionFromMeasured := executionActual
    sourceContinuation := source
    sourceAssignmentExact := by rw [sourceActual]; rfl
    sourceAccepted := sourceActual.symm ▸ source_accepted depth input discovery canonicalFound
    application := application, outputAccepted := application.preservesAccept
      (sourceActual.symm ▸ source_accepted depth input discovery canonicalFound)
    next := next
    nextAssignmentExact := by cases sourceActual; cases nextActual; rfl
    nextReaderExact := by
      cases sourceActual; cases nextActual; cases applicationActual; rfl
    nextReaderWorkExact := by
      cases sourceActual; cases nextActual; cases applicationActual; intro query; rfl }

theorem from_parts_actual (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction = (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (stored : StoredLocalSchedule discovery)
    (storedActual : stored = recorded.outcome.produceStoredSchedule discovery found)
    (validation : MeasuredScheduleValidation stored) (validationActual : validation = validateStoredSchedule stored)
    (measured : MeasuredScheduleExecution validation) (measuredActual : measured = executeStoredSchedule validation)
    (validated : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery))
    (validatedActual : validated = validation.validated)
    (execution : ExecutedDiscoverySchedule validated) (executionActual : HEq execution measured.execution)
    (source : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (sourceActual : source = sourceFromInput depth input discovery canonicalFound)
    (application : AppliedDiscoveryExecution execution source)
    (applicationActual : application = applyDiscoveryExecution execution source)
    (next : SequentialAssignment (depth + 1))
    (nextActual : HEq next (nextFromApplication depth input discovery canonicalFound validated execution
      (Eq.rec (motive := fun source _ => AppliedDiscoveryExecution execution source) application sourceActual))) :
    fromParts depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical
      stored storedActual validation validationActual measured measuredActual validated validatedActual
      execution executionActual source sourceActual application applicationActual next nextActual =
    executeSequentialStageFromActiveRecorded depth input generation recorded extractionExact
      discovery found canonicalFound workLeCanonical := by
  cases storedActual; cases validationActual; cases measuredActual; cases validatedActual
  cases executionActual; cases sourceActual; cases applicationActual; cases nextActual
  rfl

def code (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction = (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total) :
    Code Label (Actual (executeSequentialStageFromActiveRecorded depth input generation recorded extractionExact
      discovery found canonicalFound workLeCanonical)) :=
  (ControlMeasuredSchedule.storedCode recorded.outcome discovery found).bind (fun stored =>
  (ControlMeasuredSchedule.validationCode stored.1).bind (fun validation =>
  (ControlMeasuredSchedule.validatedCode validation.1).bind (fun validated =>
  (ControlMeasuredSchedule.executionCode validation.1).bind (fun measured =>
  (ControlMeasuredSchedule.executedCode measured.1).bind (fun execution =>
  .step .masterConstructionReturn (fun _ =>
    let source := sourceFromInput depth input discovery canonicalFound
    let indexedExecution := Eq.rec (motive := fun validated _ => ExecutedDiscoverySchedule validated)
      execution.1 validated.2.symm
    have actualExecution : HEq indexedExecution measured.1.execution := by
      obtain ⟨_, actual⟩ := execution; cases actual
      obtain ⟨_, actual⟩ := validated; cases actual; rfl
    (ControlMeasuredTransport.applicationCode indexedExecution source).bind (fun application =>
      .step .controlClosure (fun _ =>
        let next := nextFromApplication depth input discovery canonicalFound validated.1 indexedExecution application.1
        .step .masterConstructionReturn (fun _ =>
          .done ⟨fromParts depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical
            stored.1 stored.2 validation.1 validation.2 measured.1 measured.2 validated.1 validated.2
            indexedExecution actualExecution source rfl application.1 application.2 next HEq.rfl,
            from_parts_actual depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical
              stored.1 stored.2 validation.1 validation.2 measured.1 measured.2 validated.1 validated.2
              indexedExecution actualExecution source rfl application.1 application.2 next HEq.rfl⟩)))))))))

theorem finite (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction = (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total) :
    Finite (code depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical) := by
  apply finite_bind (ControlMeasuredSchedule.stored_finite _ _ _); intro stored
  apply finite_bind (ControlMeasuredSchedule.validation_finite _); intro validation
  apply finite_bind (ControlMeasuredSchedule.validated_finite _); intro validated
  apply finite_bind (ControlMeasuredSchedule.execution_finite _); intro measured
  apply finite_bind (ControlMeasuredSchedule.executed_finite _); intro execution
  apply finite_step
  apply finite_bind (ControlMeasuredTransport.application_finite _ _); intro application
  exact finite_step _ _ (finite_step _ _ (finite_done _))

end ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.sourceFromInput
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.source_accepted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.nextFromApplication
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialStage.finite
/- AXIOM_AUDIT_END -/
