import Tests.LocalAlignment.DocumentaryMasterFormationExecution
import Tests.LocalAlignment.DocumentaryMasterObservation
import Tests.LocalAlignment.DocumentaryMemoryCases

/-! Instances of recipe restoration and membership on the existing actual
executions, including blocked and unsuitable cases. Record bytes below encode
only opcodes and ports, not the complete master cursor or its environment. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases
open Resources EndogenousDecomposition MasterFormation MasterFormationExecution

def initial : Formed ProgramCases.start.dossier.cursor.support := .given _

theorem every_master_cursor (count : Nat) :
    (cursor (MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish
      (executed_formed count ProgramCases.start.dossier.cursor initial)).restore =
      (MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish :=
  cursor_exact _ _

theorem actual_program : Nonempty (Formed ProgramCases.actual.1.dossier.cursor.support) :=
  program_formed ProgramCases.actual.2 initial

theorem unsuitable_program : Nonempty (Formed ProgramCases.wrongActual.1.dossier.cursor.support) :=
  program_formed ProgramCases.wrongActual.2 initial

theorem blocked_program : Nonempty (Formed ProgramCases.sourceBlockedActual.1.dossier.cursor.support) :=
  program_formed ProgramCases.sourceBlockedActual.2 initial

theorem every_adaptive_policy (policy : Adaptive.Policy Nat) (feed : Nat → Adaptive.Signal) :
    Nonempty (Formed (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).1.frame.dossier.cursor.support) :=
  adaptive_formed (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).2 initial

theorem every_memory_future (requests : List (Memory.Request Nat)) :
    Nonempty (Formed (Memory.run MemoryCases.boot requests).1.session.frame.dossier.cursor.support) :=
  memory_formed (Memory.run MemoryCases.boot requests).2 initial

/-- The passed finite trace is authoritative. Its final frame is kept abstract,
so proving membership does not kernel-reduce a closed historical master run. -/
theorem every_program_trace {slots} {script : Program.Script Cases.context DeductionCases.policy [] slots}
    {finish : Program.Frame Cases.sources Cases.contract DeductionCases.policy slots}
    (trace : Program.Execution ProgramCases.start script finish) :
    Nonempty (Formed finish.dossier.cursor.support) := program_formed trace initial

theorem every_adaptive_trace {slots policy feed}
    {script : Program.Script Cases.context DeductionCases.policy [] slots}
    {finish : Adaptive.Session Cases.sources Cases.contract DeductionCases.policy Nat slots}
    (trace : Adaptive.Execution policy feed AdaptiveCases.start script finish) :
    Nonempty (Formed finish.frame.dossier.cursor.support) := adaptive_formed trace initial

theorem every_memory_trace {requests finish}
    (trace : Memory.Execution MemoryCases.boot requests finish) :
    Nonempty (Formed finish.session.frame.dossier.cursor.support) := memory_formed trace initial

theorem any_record_bytes (record : MasterOperations.Record) :
    MasterOperations.loadRecord (MasterOperations.saveRecord record) = some record :=
  MasterOperations.record_byte_roundtrip record

theorem unknown_opcode : MasterOperations.readRecord (7, [0]) = none := rfl

theorem extra_single_port : MasterOperations.readRecord (0, [2, 2]) = none := rfl

theorem missing_double_port : MasterOperations.readRecord (1, [0]) = none := rfl

theorem invalid_byte_alphabet : MasterOperations.loadRecord [7] = none := rfl

theorem equal_ports_remain_ordered :
    (MasterOperations.Record.nextFresh 2 2).fields = (6, [2, 2]) := rfl

end ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.initial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.every_master_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.actual_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.unsuitable_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.blocked_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.every_adaptive_policy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.every_memory_future
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.any_record_bytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.unknown_opcode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.extra_single_port
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.missing_double_port
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.invalid_byte_alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.equal_ports_remain_ordered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.every_program_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.every_adaptive_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationCases.every_memory_trace
/- AXIOM_AUDIT_END -/
