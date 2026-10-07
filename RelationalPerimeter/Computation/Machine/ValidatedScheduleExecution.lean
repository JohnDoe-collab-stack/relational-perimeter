import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.StoredLocalSchedule

/-! Consume the search returned by schedule validation. No new search or
persistent runtime data is introduced by this structural raccord. -/
set_option autoImplicit false
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution
open SAT

def executeValidation {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    MeasuredScheduleExecution validation :=
  ⟨validation.search, validation.searchExact⟩

theorem executeValidation_search {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    (executeValidation validation).search = validation.search := rfl

theorem executeValidation_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    executeValidation validation = executeStoredSchedule validation := by
  cases validation with
  | mk search searchExact => cases searchExact; rfl

theorem executeValidation_execution_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    (executeValidation validation).execution = (executeStoredSchedule validation).execution :=
  congrArg (fun execution : MeasuredScheduleExecution validation => execution.execution)
    (executeValidation_exact validation)

def validateAndExecute {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) :
    ExecutedDiscoverySchedule (validateStoredSchedule stored).validated :=
  let validation := validateStoredSchedule stored
  (executeValidation validation).execution

theorem validateAndExecute_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) :
    validateAndExecute stored = (executeStoredSchedule (validateStoredSchedule stored)).execution :=
  executeValidation_execution_exact (validateStoredSchedule stored)

theorem validateAndExecute_run {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) :
    (validateAndExecute stored).run = Eq.rec
      (motive := fun entry _ => ClosureSearchRun
        (GeneratedStructuralFlipAtRelation entry.var) entry.source entry.target)
      (executionFromMeasuredSearch stored.entry (validateStoredSchedule stored).search)
      stored.entryExact := by
  have measuredExact : Eq.rec
      (motive := fun entry _ => ClosureSearchRun
        (GeneratedStructuralFlipAtRelation entry.var) entry.source entry.target)
      (executionFromMeasuredSearch stored.entry (validateStoredSchedule stored).search)
      stored.entryExact = (scheduleFromDiscovery discovery).entry.executionRun := by
    rw [(validateStoredSchedule stored).searchExact]
    cases stored with
    | mk entry entryExact =>
      cases entryExact
      exact executionFromMeasuredSearch_exact _
  exact (validateAndExecute stored).runExact.trans measuredExact.symm

theorem validateAndExecute_code {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) :
    (validateAndExecute stored).run.code? = some (validateAndExecute stored).code :=
  (validateAndExecute stored).codeExact

theorem validateAndExecute_endpoint {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) :
    (validateAndExecute stored).producedState = stored.entry.target :=
  (validateAndExecute stored).producedStateExact.trans
    (congrArg ConstitutedLocalWitness.target stored.entryExact).symm

end ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.executeValidation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.executeValidation_search
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.executeValidation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.executeValidation_execution_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.validateAndExecute
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.validateAndExecute_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.validateAndExecute_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.validateAndExecute_code
#print axioms ConstitutiveSearch.EndogenousDecomposition.ValidatedScheduleExecution.validateAndExecute_endpoint
/- AXIOM_AUDIT_END -/
