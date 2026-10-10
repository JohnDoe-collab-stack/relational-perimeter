import Tests.LocalAlignment.DocumentaryControlMeasuredDiscovery
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.StoredLocalSchedule

/-! The stored schedule consumes the produced endpoints. Its two searches
run separately as in the original, using the controlled relation search. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def storedCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    (outcome : RecordedDiscoveryOutcome state) (discovery : EndogenousFlipDiscovery state)
    (found : outcome.discovered? = some discovery) :
    Code Label (Actual (outcome.produceStoredSchedule discovery found)) :=
  .step .masterConstructionCell (fun _ => match returned : outcome.produced? with
    | none => False.elim (by
        unfold RecordedDiscoveryOutcome.discovered? at found
        rw [returned] at found; cases found)
    | some produced =>
      have same : (⟨produced.1, produced.2.discovery⟩ : EndogenousFlipDiscovery state) = discovery := by
        unfold RecordedDiscoveryOutcome.discovered? at found
        rw [returned] at found; exact Option.some.inj found
      .step .masterConstructionReturn (fun _ => .done
        ⟨⟨produced.2.entry, by rw [← same]; exact produced.2.entry_exact⟩,
          by
            unfold RecordedDiscoveryOutcome.produceStoredSchedule
            split
            · rename_i failed; rw [returned] at failed; cases failed
            · rename_i other otherReturned
              have exactProduced : produced = other := Option.some.inj (returned.symm.trans otherReturned)
              cases exactProduced; rfl⟩))

theorem stored_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    (outcome : RecordedDiscoveryOutcome state) (discovery : EndogenousFlipDiscovery state)
    (found : outcome.discovered? = some discovery) : Finite (storedCode outcome discovery found) := by
  apply finite_step; split
  · exact False.elim (by
      unfold RecordedDiscoveryOutcome.discovered? at found
      rename_i returned; rw [returned] at found; cases found)
  · exact finite_step _ _ (finite_done _)

def validationCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} (stored : StoredLocalSchedule discovery) :
    Code Label (Actual (validateStoredSchedule stored)) :=
  (ControlMeasuredDiscovery.relationCode stored.entry.var stored.entry.source stored.entry.target).bind
    (fun searched => .step .masterConstructionReturn (fun _ =>
      .done ⟨⟨searched.1, searched.2⟩, by obtain ⟨_, actual⟩ := searched; cases actual; rfl⟩))

theorem validation_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} (stored : StoredLocalSchedule discovery) :
    Finite (validationCode stored) := by
  apply finite_bind (ControlMeasuredDiscovery.relation_finite _ _ _); intro searched
  exact finite_step _ _ (finite_done _)

def validationRunCode {root : Cnf} (entry : ConstitutedLocalWitness root)
    (search : MeasuredRelationRun entry.var entry.source entry.target) :
    Code Label (Actual (validationFromMeasuredSearch entry search)) :=
  .step .masterConstructionCell (fun _ => match found : search.result with
    | none => .done ⟨⟨false, 1, 1⟩, by rw [validationFromMeasuredSearch, found]⟩
    | some _ => .done ⟨⟨true, 1, 1⟩, by rw [validationFromMeasuredSearch, found]⟩)

theorem validation_run_finite {root : Cnf} (entry : ConstitutedLocalWitness root)
    (search : MeasuredRelationRun entry.var entry.source entry.target) :
    Finite (validationRunCode entry search) := by
  apply finite_step; split <;> exact finite_done _

def validatedFromRun {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    (validation : MeasuredScheduleValidation stored) (run : SearchableCodeValidationRun)
    (actual : run = validationFromMeasuredSearch stored.entry validation.search) :
    ValidatedDiscoverySchedule (scheduleFromDiscovery discovery) :=
  { run := run
    runExact := actual.trans validation.validated.runExact
    success := by rw [actual]; exact validation.validated.success }

theorem validated_from_run_actual {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    (validation : MeasuredScheduleValidation stored) (run : SearchableCodeValidationRun)
    (actual : run = validationFromMeasuredSearch stored.entry validation.search) :
    validatedFromRun validation run actual = validation.validated := by cases actual; rfl

def validatedCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    (validation : MeasuredScheduleValidation stored) : Code Label (Actual validation.validated) :=
  (validationRunCode stored.entry validation.search).bind (fun run =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨validatedFromRun validation run.1 run.2, validated_from_run_actual _ _ _⟩))

theorem validated_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    (validation : MeasuredScheduleValidation stored) : Finite (validatedCode validation) := by
  apply finite_bind (validation_run_finite _ _); intro run
  exact finite_step _ _ (finite_done _)

def executionCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    (validation : MeasuredScheduleValidation stored) : Code Label (Actual (executeStoredSchedule validation)) :=
  (ControlMeasuredDiscovery.relationCode stored.entry.var stored.entry.source stored.entry.target).bind
    (fun searched => .step .masterConstructionReturn (fun _ =>
      .done ⟨⟨searched.1, searched.2⟩, by obtain ⟨_, actual⟩ := searched; cases actual; rfl⟩))

theorem execution_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    (validation : MeasuredScheduleValidation stored) : Finite (executionCode validation) := by
  apply finite_bind (ControlMeasuredDiscovery.relation_finite _ _ _); intro searched
  exact finite_step _ _ (finite_done _)

def executionRunCode {root : Cnf} (entry : ConstitutedLocalWitness root)
    (search : MeasuredRelationRun entry.var entry.source entry.target) :
    Code Label (Actual (executionFromMeasuredSearch entry search)) :=
  .step .masterConstructionCell (fun _ => match found : search.result with
    | none => .step .masterConstructionReturn (fun _ => .done
      ⟨⟨none, ⟨1, 0⟩⟩, by rw [executionFromMeasuredSearch, found]⟩)
    | some relation => .step .controlClosure (fun _ =>
      let code := TransportClosure.ofGenerator relation
      .step .masterConstructionReturn (fun _ => .done
        ⟨⟨some code, ⟨1, 0⟩⟩, by rw [executionFromMeasuredSearch, found]⟩)))

theorem execution_run_finite {root : Cnf} (entry : ConstitutedLocalWitness root)
    (search : MeasuredRelationRun entry.var entry.source entry.target) :
    Finite (executionRunCode entry search) := by
  apply finite_step; split
  · exact finite_step _ _ (finite_done _)
  · exact finite_step _ _ (finite_step _ _ (finite_done _))

theorem indexed_run_exact {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    {validation : MeasuredScheduleValidation stored} (execution : MeasuredScheduleExecution validation)
    (run : ClosureSearchRun (GeneratedStructuralFlipAtRelation stored.entry.var)
      stored.entry.source stored.entry.target)
    (actual : run = executionFromMeasuredSearch stored.entry execution.search) :
    Eq.rec (motive := fun entry _ => ClosureSearchRun
      (GeneratedStructuralFlipAtRelation entry.var) entry.source entry.target) run stored.entryExact =
      (scheduleFromDiscovery discovery).entry.executionRun := by
  cases actual
  cases stored with
  | mk entry entryExact =>
    cases entryExact
    change executionFromMeasuredSearch _ execution.search = _
    rw [execution.searchExact]
    exact executionFromMeasuredSearch_exact _

def executedCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    {validation : MeasuredScheduleValidation stored} (execution : MeasuredScheduleExecution validation) :
    Code Label (Actual execution.execution) :=
  (executionRunCode stored.entry execution.search).bind (fun run =>
    .step .masterConstructionCell (fun _ =>
      let indexed := Eq.rec
        (motive := fun entry _ => ClosureSearchRun
          (GeneratedStructuralFlipAtRelation entry.var) entry.source entry.target) run.1 stored.entryExact
      have exactRun : indexed = (scheduleFromDiscovery discovery).entry.executionRun :=
        indexed_run_exact execution run.1 run.2
      match found : indexed.code? with
      | none => False.elim ((scheduleFromDiscovery discovery).entry.executionRun_found
          (Eq.trans (congrArg ClosureSearchRun.code? exactRun).symm found))
      | some returned => .step .masterConstructionReturn (fun _ =>
        let result : ExecutedDiscoverySchedule validation.validated :=
          { run := indexed, runExact := exactRun, code := returned, codeExact := found
            producedState := stored.entry.target
            producedStateExact := congrArg ConstitutedLocalWitness.target stored.entryExact }
        .done ⟨result, executedDiscoverySchedule_unique _ _⟩)))

theorem executed_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {stored : StoredLocalSchedule discovery}
    {validation : MeasuredScheduleValidation stored} (execution : MeasuredScheduleExecution validation) :
    Finite (executedCode execution) := by
  apply finite_bind (execution_run_finite _ _); intro run
  apply finite_step; dsimp only; split
  · exact False.elim ((scheduleFromDiscovery discovery).entry.executionRun_found
      (Eq.trans (congrArg ClosureSearchRun.code? (indexed_run_exact execution run.1 run.2)).symm
        (by assumption)))
  · exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.storedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.stored_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validation_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validationRunCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validation_run_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validatedFromRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validated_from_run_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validatedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.validated_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.executionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.execution_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.executionRunCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.execution_run_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.indexed_run_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.executedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredSchedule.executed_finite
/- AXIOM_AUDIT_END -/
