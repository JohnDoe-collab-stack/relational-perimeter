import Tests.LocalAlignment.DocumentaryControlMeasuredSchedule
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAssignment

/-! Retarget executable transport indices to the actual stored endpoints.
The equalities only change indices; no discovery schedule is reconstructed.
The assignment reader remains the original deferred reader, whose inner
query work is a separate obligation. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache
open SAT EndogenousDecomposition
variable {root : Cnf} {state : GeneratedStructuralBranchContext root}
  {discovery : EndogenousFlipDiscovery state}
  {validation : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery)}

def program (stored : StoredLocalSchedule discovery) (execution : ExecutedDiscoverySchedule validation) :
    TransportCode (GeneratedStructuralFlipAtRelation discovery.1) stored.entry.source stored.entry.target := by
  rcases stored with ⟨entry, actual⟩; cases actual; exact execution.code

def input (stored : StoredLocalSchedule discovery)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source) :
    GeneratedStructuralBranchContinuation stored.entry.source := by
  rcases stored with ⟨entry, actual⟩; cases actual; exact received

def originalRun (stored : StoredLocalSchedule discovery) (execution : ExecutedDiscoverySchedule validation)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (run : MeasuredTransportApplication (generatedStructuralFlipAtAction root discovery.1)
      (program stored execution) (input stored received)) :
    MeasuredTransportApplication (generatedStructuralFlipAtAction root discovery.1) execution.code received := by
  rcases stored with ⟨entry, actual⟩; cases actual; exact run

theorem original_run_actual (stored : StoredLocalSchedule discovery) (execution : ExecutedDiscoverySchedule validation)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (run : MeasuredTransportApplication (generatedStructuralFlipAtAction root discovery.1)
      (program stored execution) (input stored received))
    (actual : run = applyMeasuredTransportCode (generatedStructuralFlipAtAction root discovery.1)
      (program stored execution) (input stored received)) :
    originalRun stored execution received run =
      applyMeasuredTransportCode (generatedStructuralFlipAtAction root discovery.1) execution.code received := by
  rcases stored with ⟨entry, exact⟩; cases exact; cases actual; rfl

def reader (stored : StoredLocalSchedule discovery) (execution : ExecutedDiscoverySchedule validation)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment received.1) :
    MeasuredAssignment (((execution.code.eval (generatedStructuralFlipAtAction root discovery.1)).map received).1) :=
  let actualInput := input stored received
  have assignmentExact : actualInput.1 = received.1 := by
    rcases stored with ⟨entry, actual⟩; cases actual; rfl
  let cachedInput := Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) readInput assignmentExact.symm
  let actualReader := readTransportedAssignment discovery.1 (program stored execution) actualInput cachedInput
  have outputExact :
      (((program stored execution).eval (generatedStructuralFlipAtAction root discovery.1)).map actualInput).1 =
        ((execution.code.eval (generatedStructuralFlipAtAction root discovery.1)).map received).1 := by
    rcases stored with ⟨entry, actual⟩; cases actual; rfl
  Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) actualReader outputExact

theorem reader_actual (stored : StoredLocalSchedule discovery) (execution : ExecutedDiscoverySchedule validation)
    (received : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment received.1) :
    reader stored execution received readInput = readTransportedAssignment discovery.1 execution.code received readInput := by
  rcases stored with ⟨entry, actual⟩; cases actual; rfl

end ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache.program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache.input
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache.originalRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache.original_run_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache.reader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlScheduleCache.reader_actual
/- AXIOM_AUDIT_END -/
