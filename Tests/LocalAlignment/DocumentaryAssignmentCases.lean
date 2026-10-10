import Tests.LocalAlignment.DocumentaryAssignmentCapture
import Tests.LocalAlignment.DocumentaryMemoryCases

/-! Instances on actual shared documentary executions and reader separators.
These equalities cover the reader component, not master/present byte loading. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases
open Resources SAT EndogenousDecomposition PortableAssignment AssignmentCapture

theorem initial : Correct ProgramCases.start.dossier.cursor := rfl

theorem actual_program :
    AssignmentCodec.restore (AssignmentCodec.save (cursor ProgramCases.actual.1.dossier.cursor)) =
      some (sequential ProgramCases.actual.1.dossier.cursor.assignment) :=
  program_bytes_exact ProgramCases.actual.2 initial

theorem unsuitable_program :
    AssignmentCodec.restore (AssignmentCodec.save (cursor ProgramCases.wrongActual.1.dossier.cursor)) =
      some (sequential ProgramCases.wrongActual.1.dossier.cursor.assignment) :=
  program_bytes_exact ProgramCases.wrongActual.2 initial

theorem blocked_program :
    AssignmentCodec.restore (AssignmentCodec.save (cursor ProgramCases.sourceBlockedActual.1.dossier.cursor)) =
      some (sequential ProgramCases.sourceBlockedActual.1.dossier.cursor.assignment) :=
  program_bytes_exact ProgramCases.sourceBlockedActual.2 initial

theorem every_master_cursor (count : Nat) :
    AssignmentCodec.restore (AssignmentCodec.save
      (cursor (MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish)) =
      some (sequential (MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish.assignment) :=
  restore_exact _ (executed_correct count _ initial)

theorem every_program_trace {slots} {script : Program.Script Cases.context DeductionCases.policy [] slots}
    {finish : Program.Frame Cases.sources Cases.contract DeductionCases.policy slots}
    (trace : Program.Execution ProgramCases.start script finish) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor finish.dossier.cursor)) =
      some (sequential finish.dossier.cursor.assignment) :=
  program_bytes_exact trace initial

theorem every_adaptive_trace {slots policy feed}
    {script : Program.Script Cases.context DeductionCases.policy [] slots}
    {finish : Adaptive.Session Cases.sources Cases.contract DeductionCases.policy Nat slots}
    (trace : Adaptive.Execution policy feed AdaptiveCases.start script finish) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor finish.frame.dossier.cursor)) =
      some (sequential finish.frame.dossier.cursor.assignment) :=
  adaptive_bytes_exact trace initial

theorem every_memory_trace {requests finish}
    (trace : Memory.Execution MemoryCases.boot requests finish) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor finish.session.frame.dossier.cursor)) =
      some (sequential finish.session.frame.dossier.cursor.assignment) :=
  memory_bytes_exact trace initial

theorem every_memory_query {requests finish}
    (trace : Memory.Execution MemoryCases.boot requests finish) (queries : List Var) :
    (AssignmentCodec.restore (AssignmentCodec.save (cursor finish.session.frame.dossier.cursor))).map
      (fun data => readQueries data queries) =
      some (readQueries (sequential finish.session.frame.dossier.cursor.assignment) queries) :=
  AssignmentCodec.all_loaded_queries (formed _ (memory_correct trace initial)) queries

theorem identity_reflect {root : Cnf} (source : GeneratedStructuralBranchContext root)
    (selected : Var) (prior : Code) :
    reflect (selected := selected) selected (TransportCode.identity source) prior = .visit :: prior := rfl

theorem composition_reflect {root : Cnf} {source target : GeneratedStructuralBranchContext root}
    {selected : Var} (relation : GeneratedStructuralFlipAtRelation selected source target) (prior : Code) :
    reflect selected (.compose (.identity source) (.atom relation)) prior =
      .visit :: .flip selected :: .visit :: prior := rfl

theorem same_bits_extra_visit (query : Var) :
    (interpret [.visit]).assignment query = (interpret []).assignment query := rfl

theorem initial_read_work : readQueries (interpret []) [0] = ([true], ⟨3, 0⟩) := rfl

theorem extra_visit_read_work : readQueries (interpret [.visit]) [0] = ([true], ⟨4, 0⟩) := rfl

theorem same_bits_different_work :
    (readQueries (interpret [.visit]) [0]).2.nodes ≠ (readQueries (interpret []) [0]).2.nodes := by
  change 4 ≠ 3
  decide

theorem any_code_bytes (code : Code) : AssignmentCodec.load (AssignmentCodec.save code) = some code :=
  AssignmentCodec.byte_roundtrip code

theorem unknown_command : AssignmentCodec.readCommand (2, none) = none := rfl

theorem missing_flip : AssignmentCodec.readCommand (1, none) = none := rfl

theorem extra_visit_port : AssignmentCodec.readCommand (0, some 10) = none := rfl

theorem invalid_alphabet : AssignmentCodec.load [7] = none := rfl

end ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.initial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.actual_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.unsuitable_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.blocked_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.every_master_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.every_program_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.every_adaptive_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.every_memory_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.every_memory_query
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.identity_reflect
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.composition_reflect
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.same_bits_extra_visit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.initial_read_work
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.extra_visit_read_work
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.same_bits_different_work
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.any_code_bytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.unknown_command
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.missing_flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.extra_visit_port
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCases.invalid_alphabet
/- AXIOM_AUDIT_END -/
