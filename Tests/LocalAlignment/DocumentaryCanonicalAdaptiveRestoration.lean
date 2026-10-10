import Tests.LocalAlignment.DocumentaryPortableStore
import Tests.LocalAlignment.DocumentaryMemory

/-! The canonical store restoration component covers arbitrary total adaptive
policies, including retained extra productions and reset contexts. This does not
serialize the other components of the adaptive present. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration
open Resources Program CanonicalRestoration

theorem fallback_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed sources contract rules before.store)
    (instruction : Instruction context rules slots spec)
    (route : Adaptive.Route) (inspection : Option Adaptive.Readout) :
    Nonempty (Formed sources contract rules (Adaptive.fallback before instruction route inspection).next.store) :=
  step_formed before prior instruction (Program.step before instruction) rfl

theorem diverted_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed sources contract rules before.store)
    (instruction proposed : Instruction context rules slots spec) :
    Nonempty (Formed sources contract rules (Adaptive.diverted before instruction proposed).next.store) := by
  rcases step_formed before prior proposed (Program.step before proposed) rfl with ⟨first⟩
  exact step_formed (Adaptive.dropHead (Program.step before proposed).next) first instruction _ rfl

theorem dispatch_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed sources contract rules before.store)
    (instruction : Instruction context rules slots spec) (proposal : Option Adaptive.Proposal) :
    Nonempty (Formed sources contract rules (Adaptive.dispatch before instruction proposal).next.store) := by
  cases proposal with
  | none => exact fallback_formed before prior instruction _ _
  | some proposal =>
      cases proposal <;> cases instruction
      all_goals dsimp only [Adaptive.dispatch]
      all_goals repeat first
        | exact step_formed _ prior _ _ rfl
        | exact fallback_formed _ prior _ _ _
        | exact diverted_formed _ prior _ _
        | split

theorem turn_formed {context sources contract rules Context slots spec}
    (policy : Adaptive.Policy Context) (before : @Adaptive.Session context sources contract rules Context slots)
    (prior : Formed sources contract rules before.frame.store)
    (signal : Adaptive.Signal) (instruction : Instruction context rules slots spec)
    (turn : Adaptive.Turn before instruction) (actual : turn = Adaptive.takeTurn policy before signal instruction) :
    Nonempty (Formed sources contract rules turn.next.frame.store) := by
  cases actual
  exact dispatch_formed before.frame prior instruction (Adaptive.selection policy before signal instruction).2

theorem execution_formed {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Formed sources contract rules start.frame.store) :
    Nonempty (Formed sources contract rules finish.frame.store) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons turn actual rest ih =>
      rcases turn_formed _ _ initial _ _ turn actual with ⟨next⟩
      exact ih next

theorem execution_byte_roundtrip {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Formed sources contract rules start.frame.store) :
    PortableStore.load sources contract rules (PortableStore.save finish.frame.store) = .ok finish.frame.store := by
  rcases execution_formed trace initial with ⟨formed⟩
  exact PortableStore.byte_roundtrip formed

theorem memory_step_formed {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (prior : Formed sources contract rules before.session.frame.store)
    (request : Memory.Request Context) (transition : Memory.Transition before request)
    (actual : transition = Memory.step before request) :
    Nonempty (Formed sources contract rules transition.next.session.frame.store) := by
  cases actual
  cases request with
  | inspect index => exact ⟨prior⟩
  | status => exact ⟨prior⟩
  | reset policy => exact ⟨prior⟩
  | progress policy signal =>
      rcases before with ⟨slots, session, queue⟩
      cases queue with
      | done => exact ⟨prior⟩
      | cons instruction tail =>
          exact turn_formed policy session.restore prior signal instruction _ rfl

theorem memory_execution_formed {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Formed sources contract rules before.session.frame.store) :
    Nonempty (Formed sources contract rules finish.session.frame.store) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons transition actual rest ih =>
      rcases memory_step_formed _ initial _ transition actual with ⟨next⟩
      exact ih next

theorem memory_execution_byte_roundtrip {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Formed sources contract rules before.session.frame.store) :
    PortableStore.load sources contract rules (PortableStore.save finish.session.frame.store) =
      .ok finish.session.frame.store := by
  rcases memory_execution_formed trace initial with ⟨formed⟩
  exact PortableStore.byte_roundtrip formed

end ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.fallback_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.diverted_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.dispatch_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.turn_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.execution_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.execution_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.memory_step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.memory_execution_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalAdaptiveRestoration.memory_execution_byte_roundtrip
/- AXIOM_AUDIT_END -/
