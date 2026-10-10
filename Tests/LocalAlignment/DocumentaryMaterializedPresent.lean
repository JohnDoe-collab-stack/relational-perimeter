import Tests.LocalAlignment.DocumentaryMasterPayload
import Tests.LocalAlignment.DocumentaryPortableMemory

/-! Full typed present restoration with a materialized master formation tree.
The cursor, dossier evidence, store, bindings, queue, context, clock and summary
belong to the same payload. The master and control data are not byte-encoded. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent
open Resources Program Adaptive

structure FrameData {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (slots : List Specification) where
  master : MasterPayload.CursorData
  memory : Documentary.Memory sources contract
  store : Deduction.Store sources contract rules
  bindings : Snapshot.Bindings store slots

def frame {context sources contract rules slots}
    (before : @Snapshot.FrameData context sources contract rules slots) : FrameData sources contract rules slots :=
  ⟨MasterPayload.cursor before.dossier.cursor, before.dossier.memory, before.store, before.bindings⟩

def FrameData.restore {context sources contract rules slots}
    (data : @FrameData context sources contract rules slots) : Snapshot.FrameData sources contract rules slots :=
  ⟨⟨data.master.restore, data.memory⟩, data.store, data.bindings⟩

theorem frame_exact {context sources contract rules slots}
    (before : @Snapshot.FrameData context sources contract rules slots) : (frame before).restore = before := by
  cases before with
  | mk dossier store bindings =>
      cases dossier with
      | mk cursor memory =>
          dsimp only [frame, FrameData.restore]
          rw [MasterPayload.cursor_exact]

structure SessionData {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (Context : Type) (slots : List Specification) where
  frame : FrameData sources contract rules slots
  context : Context
  round : Nat
  last : Option Summary

def session {context sources contract rules Context slots}
    (before : @Snapshot.SessionData context sources contract rules Context slots) :
    SessionData sources contract rules Context slots :=
  ⟨frame before.frame, before.context, before.round, before.last⟩

def SessionData.restore {context sources contract rules Context slots}
    (data : @SessionData context sources contract rules Context slots) :
    Snapshot.SessionData sources contract rules Context slots :=
  ⟨data.frame.restore, data.context, data.round, data.last⟩

theorem session_exact {context sources contract rules Context slots}
    (before : @Snapshot.SessionData context sources contract rules Context slots) : (session before).restore = before := by
  cases before with
  | mk frame context round last =>
      dsimp only [session, SessionData.restore]
      rw [frame_exact]

structure PresentData {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (Context : Type) (final : List Specification) where
  slots : List Specification
  session : SessionData sources contract rules Context slots
  remaining : Script context rules slots final

def present {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final) :
    PresentData sources contract rules Context final :=
  ⟨before.slots, session before.session, before.remaining⟩

def PresentData.restore {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) :
    Snapshot.PresentData sources contract rules Context final :=
  ⟨data.slots, data.session.restore, data.remaining⟩

theorem present_exact {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final) : (present before).restore = before := by
  cases before with
  | mk slots session remaining =>
      dsimp only [present, PresentData.restore]
      rw [session_exact]

/-- Exact payload equality preserves every declared future, including progress
with new quotations, inspection, status and reset, and its positive trace. -/
theorem all_futures {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (requests : List (Memory.Request Context)) :
    HEq (Memory.run (present before).restore requests) (Memory.run before requests) := by
  rw [present_exact]

theorem future_events {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (requests : List (Memory.Request Context)) :
    (Memory.run (present before).restore requests).2.events = (Memory.run before requests).2.events := by
  rw [present_exact]

def accomplishment {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (possible : Snapshot.Accomplishable before) : Snapshot.Accomplishable (present before).restore := by
  rw [present_exact]
  exact possible

end ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.FrameData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.FrameData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.frame_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.SessionData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.session
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.SessionData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.session_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.PresentData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.PresentData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.present_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.all_futures
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.future_events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MaterializedPresent.accomplishment
/- AXIOM_AUDIT_END -/
