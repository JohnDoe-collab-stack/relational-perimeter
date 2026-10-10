import Tests.LocalAlignment.DocumentaryStatePortable
import Tests.LocalAlignment.DocumentarySequentialCapture

/-! The complete threaded-state codec consumes the current retained state and
the reader code already captured by the existing resource traversal. It is
closed along all existing finite program, adaptive and memory executions. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.StateCapture
open Resources EndogenousDecomposition PortableAssignment

def record (before : MasterResources.Cursor) (ready : SequentialCapture.Ready before) : StatePortable.Record :=
  StatePortable.capture before.state (SequentialCapture.formed before ready)

def save (before : MasterResources.Cursor) (ready : SequentialCapture.Ready before) : List UInt8 :=
  StatePortable.save before.state (SequentialCapture.formed before ready)

theorem restored_exact (before : MasterResources.Cursor) (ready : SequentialCapture.Ready before) :
    StatePortable.restore (save before ready) =
      some (⟨before.depth, before.assignment, before.state⟩ : StatePortable.Loaded) :=
  StatePortable.restored_exact before.state (SequentialCapture.formed before ready)

theorem all_consumers (before : MasterResources.Cursor) (ready : SequentialCapture.Ready before)
    {Result : Type u} (future : StatePortable.Loaded → Result) :
    (StatePortable.restore (save before ready)).map future =
      some (future ⟨before.depth, before.assignment, before.state⟩) := by
  rw [restored_exact]
  rfl

theorem finite_master (count : Nat) (before : MasterResources.Cursor) (ready : SequentialCapture.Ready before) :
    StatePortable.restore (save (MasterResources.executeWithReferences count before).finish
      (SequentialCapture.executed_ready count before ready)) =
      some (⟨(MasterResources.executeWithReferences count before).finish.depth,
        (MasterResources.executeWithReferences count before).finish.assignment,
        (MasterResources.executeWithReferences count before).finish.state⟩ : StatePortable.Loaded) :=
  restored_exact _ _

theorem program {context sources contract rules initial final start script finish}
    (actual : @Program.Execution context sources contract rules initial final start script finish)
    (ready : SequentialCapture.Ready start.dossier.cursor) :
    StatePortable.restore (save finish.dossier.cursor (SequentialCapture.program_ready actual ready)) =
      some (⟨finish.dossier.cursor.depth, finish.dossier.cursor.assignment, finish.dossier.cursor.state⟩ :
        StatePortable.Loaded) :=
  restored_exact _ _

theorem adaptive {context sources contract rules Context policy feed initial final start script finish}
    (actual : @Adaptive.Execution context sources contract rules Context policy feed initial final start script finish)
    (ready : SequentialCapture.Ready start.frame.dossier.cursor) :
    StatePortable.restore (save finish.frame.dossier.cursor (SequentialCapture.adaptive_ready actual ready)) =
      some (⟨finish.frame.dossier.cursor.depth, finish.frame.dossier.cursor.assignment,
        finish.frame.dossier.cursor.state⟩ : StatePortable.Loaded) :=
  restored_exact _ _

theorem memory {context sources contract rules Context final before requests finish}
    (actual : @Memory.Execution context sources contract rules Context final before requests finish)
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor) :
    StatePortable.restore (save finish.session.frame.dossier.cursor (SequentialCapture.memory_ready actual ready)) =
      some (⟨finish.session.frame.dossier.cursor.depth, finish.session.frame.dossier.cursor.assignment,
        finish.session.frame.dossier.cursor.state⟩ : StatePortable.Loaded) :=
  restored_exact _ _

/-- Read the history already retained by the last executed prefix constructor.
The root constructor carries its source as an erased dependent index; it does
not supply a retained history value to this runtime projection. -/
def prefixHistory : {source : CausalConstitutiveState} →
    ConstitutedOperationalPrefix source →
      Option (StrongPerimetralTurning.RootedGeneratedHistory StrongPerimetralTurning.Example.examplePresentation)
  | _, .root _ => none
  | _, .advance _ stage _ => some stage.next.constitutedHistory

def history (before : MasterResources.Cursor) :=
  prefixHistory before.context

theorem history_restored_exact (before : MasterResources.Cursor) :
    (history before).bind (fun value =>
      HistoryPortable.restore StrongPerimetralTurning.Example.examplePresentation (HistoryPortable.save value)) =
      history before := by
  cases found : history before with
  | none => rfl
  | some value => exact HistoryPortable.restored_exact value


end ConstitutiveSearch.Agent.Local.Documentary.StateCapture

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.prefixHistory
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.history
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.history_restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.all_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.finite_master
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.adaptive
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StateCapture.memory
/- AXIOM_AUDIT_END -/
