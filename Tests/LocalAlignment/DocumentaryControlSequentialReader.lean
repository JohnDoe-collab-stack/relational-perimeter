import Tests.LocalAlignment.DocumentaryControlSequentialStage
import Tests.LocalAlignment.DocumentaryControlMeasuredTransportReader

/-! Form the original sequential stage and its executable measured reader
together, from the actual application. No selected bit is read here. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData
open ControlMeasuredAssignmentReader ControlSequentialStage

structure Produced {depth : Nat} {input : SequentialAssignment depth}
    (expected : SequentialStageRun depth input) where
  stage : Actual expected
  reader : Reader stage.1.next.reader

theorem cast_reader_heq {left right : Assignment} (reader : MeasuredAssignment left)
    (same : left = right) : HEq
      (Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) reader same) reader := by
  cases same; rfl

theorem next_reader_exact (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (stored : StoredLocalSchedule discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (validated : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery))
    (execution : ExecutedDiscoverySchedule validated)
    (application : AppliedDiscoveryExecution execution (sourceFromInput depth input discovery canonicalFound)) :
    HEq (nextFromApplication depth input discovery stored canonicalFound validated execution application).reader
      (readTransportedAssignment discovery.var execution.code
        (sourceFromInput depth input discovery canonicalFound) input.reader) := by
  dsimp only [nextFromApplication]
  exact (cast_reader_heq _ _).trans (heq_of_eq
    (ControlScheduleCache.reader_actual stored execution
      (sourceFromInput depth input discovery canonicalFound) input.reader))

@[inline] def cachedReader {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} (stored : StoredLocalSchedule discovery)
    {validation : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery)}
    (execution : ExecutedDiscoverySchedule validation)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment received.1) :
    MeasuredAssignment (((execution.code.eval (generatedStructuralFlipAtAction root discovery.var)).map received).1) :=
  let actualInput := ControlScheduleCache.input stored received
  have assignmentExact : actualInput.1 = received.1 := by
    rcases stored with ⟨entry, actual⟩; cases actual; rfl
  let cachedInput := Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) readInput assignmentExact.symm
  let actualReader := fun query => readTransportedAssignment discovery.var
    (ControlScheduleCache.program stored execution) actualInput cachedInput query
  have outputExact :
      (((ControlScheduleCache.program stored execution).eval (generatedStructuralFlipAtAction root discovery.var)).map actualInput).1 =
        ((execution.code.eval (generatedStructuralFlipAtAction root discovery.var)).map received).1 := by
    rcases stored with ⟨entry, actual⟩; cases actual; rfl
  Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) actualReader outputExact

theorem cached_reader_actual {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} (stored : StoredLocalSchedule discovery)
    {validation : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery)}
    (execution : ExecutedDiscoverySchedule validation)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment received.1) :
    cachedReader stored execution received readInput = ControlScheduleCache.reader stored execution received readInput := rfl

def nextCached (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (stored : StoredLocalSchedule discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (validated : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery))
    (execution : ExecutedDiscoverySchedule validated)
    (application : AppliedDiscoveryExecution execution (sourceFromInput depth input discovery canonicalFound)) :
    SequentialAssignment (depth + 1) :=
  let reader := fun query => cachedReader stored execution
    (sourceFromInput depth input discovery canonicalFound) input.reader query
  let indexedReader := Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) reader
    (congrArg Subtype.val application.outputExact).symm
  { assignment := application.output.1, reader := indexedReader
    zeroTrue := (nextFromApplication depth input discovery stored canonicalFound validated execution application).zeroTrue
    futureSelectedFalse := (nextFromApplication depth input discovery stored canonicalFound validated execution application).futureSelectedFalse
    futureAnchorTrue := (nextFromApplication depth input discovery stored canonicalFound validated execution application).futureAnchorTrue }

theorem next_cached_actual (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (stored : StoredLocalSchedule discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (validated : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery))
    (execution : ExecutedDiscoverySchedule validated)
    (application : AppliedDiscoveryExecution execution (sourceFromInput depth input discovery canonicalFound)) :
    nextCached depth input discovery stored canonicalFound validated execution application =
      nextFromApplication depth input discovery stored canonicalFound validated execution application := rfl

def code (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction = (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (reader : Reader input.reader) :
    Code Label (Produced (executeSequentialStageFromActiveRecorded depth input generation recorded extractionExact
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
    (ControlMeasuredTransportReader.applicationCode stored.1 indexedExecution source input.reader reader).bind
      (fun application => .step .controlClosure (fun _ =>
        let next := nextCached depth input discovery stored.1 canonicalFound validated.1
          indexedExecution application.application.1
        let realized := retarget
          (congrArg Subtype.val application.application.1.outputExact).symm
          (next_reader_exact depth input discovery stored.1 canonicalFound validated.1 indexedExecution
            application.application.1).symm application.reader
        .step .masterConstructionReturn (fun _ =>
          let stage : Actual (executeSequentialStageFromActiveRecorded depth input generation recorded extractionExact
              discovery found canonicalFound workLeCanonical) :=
            ⟨fromParts depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical
              stored.1 stored.2 validation.1 validation.2 measured.1 measured.2 validated.1 validated.2
              indexedExecution actualExecution source rfl application.application.1 application.application.2 next HEq.rfl,
              from_parts_actual depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical
                stored.1 stored.2 validation.1 validation.2 measured.1 measured.2 validated.1 validated.2
                indexedExecution actualExecution source rfl application.application.1 application.application.2 next HEq.rfl⟩
          .step .executionPayload (fun _ => .done ⟨stage, realized⟩))))))))))

theorem finite (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction = (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (reader : Reader input.reader) :
    Finite (code depth input generation recorded extractionExact discovery found canonicalFound workLeCanonical reader) := by
  apply finite_bind (ControlMeasuredSchedule.stored_finite _ _ _); intro stored
  apply finite_bind (ControlMeasuredSchedule.validation_finite _); intro validation
  apply finite_bind (ControlMeasuredSchedule.validated_finite _); intro validated
  apply finite_bind (ControlMeasuredSchedule.execution_finite _); intro measured
  apply finite_bind (ControlMeasuredSchedule.executed_finite _); intro execution
  apply finite_step
  apply finite_bind (ControlMeasuredTransportReader.application_finite _ _ _ _ _); intro application
  apply finite_step; apply finite_step; apply finite_step; exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.cast_reader_heq
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.next_reader_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.cachedReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.cached_reader_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.nextCached
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.next_cached_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSequentialReader.finite
/- AXIOM_AUDIT_END -/
