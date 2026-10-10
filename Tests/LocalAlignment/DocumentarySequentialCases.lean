import Tests.LocalAlignment.DocumentarySequentialCapture
import Tests.LocalAlignment.DocumentaryMemoryCases

/-! Closure at the public master origin, plus boundary rejections for the
declared positive reader class. These cases do not encode the other master fields. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.SequentialCases
open Resources SAT EndogenousDecomposition PortableAssignment AssignmentCapture SequentialCapture

theorem initial : Ready ProgramCases.start.dossier.cursor := ⟨rfl, True.intro⟩

theorem actual_program :
    SequentialPortable.restoreAt ProgramCases.actual.1.dossier.cursor.depth
      (SequentialPortable.save ProgramCases.actual.1.dossier.cursor.depth
        (cursor ProgramCases.actual.1.dossier.cursor)) =
      some ProgramCases.actual.1.dossier.cursor.assignment :=
  program_bytes_exact ProgramCases.actual.2 initial

theorem unsuitable_program :
    SequentialPortable.restoreAt ProgramCases.wrongActual.1.dossier.cursor.depth
      (SequentialPortable.save ProgramCases.wrongActual.1.dossier.cursor.depth
        (cursor ProgramCases.wrongActual.1.dossier.cursor)) =
      some ProgramCases.wrongActual.1.dossier.cursor.assignment :=
  program_bytes_exact ProgramCases.wrongActual.2 initial

theorem blocked_program :
    SequentialPortable.restoreAt ProgramCases.sourceBlockedActual.1.dossier.cursor.depth
      (SequentialPortable.save ProgramCases.sourceBlockedActual.1.dossier.cursor.depth
        (cursor ProgramCases.sourceBlockedActual.1.dossier.cursor)) =
      some ProgramCases.sourceBlockedActual.1.dossier.cursor.assignment :=
  program_bytes_exact ProgramCases.sourceBlockedActual.2 initial

theorem every_master_cursor (count : Nat) :
    let finish := (MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish
    SequentialPortable.restoreAt finish.depth (SequentialPortable.save finish.depth (cursor finish)) =
      some finish.assignment :=
  restore_exact _ (executed_ready count _ initial)

theorem every_program_trace {slots} {script : Program.Script Cases.context DeductionCases.policy [] slots}
    {finish : Program.Frame Cases.sources Cases.contract DeductionCases.policy slots}
    (trace : Program.Execution ProgramCases.start script finish) :
    SequentialPortable.restoreAt finish.dossier.cursor.depth
      (SequentialPortable.save finish.dossier.cursor.depth (cursor finish.dossier.cursor)) =
      some finish.dossier.cursor.assignment :=
  program_bytes_exact trace initial

theorem every_adaptive_trace {slots policy feed}
    {script : Program.Script Cases.context DeductionCases.policy [] slots}
    {finish : Adaptive.Session Cases.sources Cases.contract DeductionCases.policy Nat slots}
    (trace : Adaptive.Execution policy feed AdaptiveCases.start script finish) :
    SequentialPortable.restoreAt finish.frame.dossier.cursor.depth
      (SequentialPortable.save finish.frame.dossier.cursor.depth (cursor finish.frame.dossier.cursor)) =
      some finish.frame.dossier.cursor.assignment :=
  adaptive_bytes_exact trace initial

theorem every_memory_trace {requests finish}
    (trace : Memory.Execution MemoryCases.boot requests finish) :
    SequentialPortable.restoreAt finish.session.frame.dossier.cursor.depth
      (SequentialPortable.save finish.session.frame.dossier.cursor.depth (cursor finish.session.frame.dossier.cursor)) =
      some finish.session.frame.dossier.cursor.assignment :=
  memory_bytes_exact trace initial

theorem every_typed_future {requests finish}
    (trace : Memory.Execution MemoryCases.boot requests finish) {Result : Type u}
    (future : SequentialAssignment finish.session.frame.dossier.cursor.depth → Result) :
    (SequentialPortable.restoreAt finish.session.frame.dossier.cursor.depth
      (SequentialPortable.save finish.session.frame.dossier.cursor.depth (cursor finish.session.frame.dossier.cursor))).map future =
      some (future finish.session.frame.dossier.cursor.assignment) :=
  SequentialPortable.all_typed_consumers (SequentialCapture.formed _ (memory_ready trace initial)) future

theorem actual_retained_state :
    restoreState ProgramCases.actual.1.dossier.cursor (program_ready ProgramCases.actual.2 initial)
      (SequentialPortable.save ProgramCases.actual.1.dossier.cursor.depth
        (cursor ProgramCases.actual.1.dossier.cursor)) rfl =
      some (⟨ProgramCases.actual.1.dossier.cursor.assignment,
        ProgramCases.actual.1.dossier.cursor.state⟩ : Coupled ProgramCases.actual.1.dossier.cursor.depth) :=
  restored_state_exact _ _

theorem zero_rejected : SequentialPortable.validate (0, [.flip 0]) = none := rfl

/-- Safety of this finite recipe class is sufficient; it is not a complete
decision procedure for arbitrary valid SequentialAssignment values. -/
theorem cancelling_zero_rejected :
    SequentialPortable.validate (0, [.flip 0, .flip 0]) = none := rfl

theorem next_variable_rejected : SequentialPortable.validate (1, [.flip 12]) = none := rfl
theorem beyond_next_rejected : SequentialPortable.validate (1, [.flip 13]) = none := rfl
theorem older_variable_admitted :
    (SequentialPortable.validate (1, [.flip 10])).isSome = true := rfl
theorem visits_admitted :
    (SequentialPortable.validate (0, [.visit, .visit])).isSome = true := rfl
theorem different_depth_rejected :
    SequentialPortable.restoreAt 2 (SequentialPortable.save 1 [.flip 10]) = none := rfl
theorem unknown_version_rejected :
    SequentialPortable.load (ControlCodec.bytes [89, 2, 0, 0]) = none := rfl

end ConstitutiveSearch.Agent.Local.Documentary.SequentialCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.initial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.actual_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.unsuitable_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.blocked_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.every_master_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.every_program_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.every_adaptive_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.every_memory_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.every_typed_future
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.actual_retained_state
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.zero_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.cancelling_zero_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.next_variable_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.beyond_next_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.older_variable_admitted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.visits_admitted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.different_depth_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.unknown_version_rejected
/- AXIOM_AUDIT_END -/
