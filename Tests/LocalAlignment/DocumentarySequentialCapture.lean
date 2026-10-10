import Tests.LocalAlignment.DocumentarySequentialPortable
import Tests.LocalAlignment.DocumentaryAssignmentCapture

/-! Closure of the validated dependent assignment class along actual executions.
Typed state coupling consumes the retained environment, which is still supplied:
it is not a byte decoder for that environment or for the complete cursor. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture
open Resources EndogenousDecomposition PortableAssignment Program
open AssignmentCapture

def Ready (before : MasterResources.Cursor) : Prop :=
  Correct before ∧ SequentialPortable.Safe before.depth (cursor before)

def formed (before : MasterResources.Cursor) (actual : Ready before) :
    SequentialPortable.Formed before.assignment := ⟨cursor before, actual.2, actual.1⟩

theorem initial_ready {depth} (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    Ready (MasterResources.initialCursor state past fresh) := ⟨rfl, True.intro⟩

theorem next_ready (before : MasterResources.Cursor) (actual : Ready before) :
    Ready before.next := by
  constructor
  · exact next_correct before actual.1
  · change SequentialPortable.Safe (before.depth + 1) (cursor before.next)
    rw [next_code]
    exact SequentialPortable.stage_safe before.head.stage (cursor before) actual.2

theorem variable_next_ready (before : MasterResources.Cursor) (actual : Ready before) :
    Ready (VariableMaster.nextCursor before) := next_ready before actual

theorem executed_ready (count : Nat) (before : MasterResources.Cursor) (actual : Ready before) :
    Ready (MasterResources.executeWithReferences count before).finish := by
  induction count generalizing before with
  | zero => exact actual
  | succ count ih => exact ih before.next (next_ready before actual)

theorem restore_exact (before : MasterResources.Cursor) (actual : Ready before) :
    SequentialPortable.restoreAt before.depth (SequentialPortable.save before.depth (cursor before)) =
      some before.assignment :=
  SequentialPortable.restore_at_exact (formed before actual)

theorem stage_ready {context before sources contract demand left right}
    (actual : Ready before)
    (stage : @Master.Stage context before sources contract demand left right) :
    Ready stage.next := by
  have same : stage.next = VariableMaster.nextCursor before := stage.head.nextExact
  rw [same]
  exact variable_next_ready before actual

theorem quotation_ready {context sources contract rules slots}
    (before : @Frame context sources contract rules slots)
    (actual : Ready before.dossier.cursor) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) :
    Ready (Program.quotationStep before task produced).next.dossier.cursor := by
  rcases produced with ⟨stage, decision⟩
  cases decision <;> exact stage_ready actual stage

theorem step_ready {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Ready before.dossier.cursor)
    (instruction : Instruction context rules slots spec)
    (produced : Program.Step before instruction) (actual : produced = Program.step before instruction) :
    Ready produced.next.dossier.cursor := by
  cases actual
  cases instruction with
  | quotation task => exact quotation_ready before prior task (Dossier.step before.dossier task)
  | conclusion request leftSlot rightSlot demand =>
      rw [MasterFormationExecution.conclusion_cursor]
      exact prior

theorem program_ready {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Ready start.dossier.cursor) : Ready finish.dossier.cursor := by
  induction trace with
  | done => exact initial
  | cons produced actual rest ih => exact ih (step_ready _ initial _ produced actual)

theorem fallback_ready {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots) (prior : Ready before.dossier.cursor)
    (instruction : Instruction context rules slots spec)
    (route : Adaptive.Route) (inspection : Option Adaptive.Readout) :
    Ready (Adaptive.fallback before instruction route inspection).next.dossier.cursor :=
  step_ready before prior instruction (Program.step before instruction) rfl

theorem diverted_ready {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots) (prior : Ready before.dossier.cursor)
    (instruction proposed : Instruction context rules slots spec) :
    Ready (Adaptive.diverted before instruction proposed).next.dossier.cursor := by
  have first := step_ready before prior proposed (Program.step before proposed) rfl
  exact step_ready (Adaptive.dropHead (Program.step before proposed).next) first instruction _ rfl

theorem dispatch_ready {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Ready before.dossier.cursor)
    (instruction : Instruction context rules slots spec) (proposal : Option Adaptive.Proposal) :
    Ready (Adaptive.dispatch before instruction proposal).next.dossier.cursor := by
  generalize actual : Adaptive.dispatch before instruction proposal = effect
  cases proposal with
  | none => cases actual; exact fallback_ready before prior instruction _ _
  | some proposal =>
      cases proposal with
      | current => cases actual; exact step_ready before prior instruction _ rfl
      | reverseSources =>
          cases instruction with
          | quotation task => cases actual; exact step_ready before prior (.quotation (Adaptive.reverseTask task)) _ rfl
          | conclusion request left right demand => cases actual; exact fallback_ready before prior _ _ _
      | inspect index =>
          dsimp only [Adaptive.dispatch] at actual
          split at actual
          · cases actual; exact fallback_ready before prior instruction _ _
          · split at actual
            · cases actual; exact fallback_ready before prior instruction _ _
            · cases actual; exact fallback_ready before prior instruction _ _
      | quote left right =>
          cases instruction with
          | conclusion request leftRef rightRef demand => cases actual; exact fallback_ready before prior _ _ _
          | quotation task =>
              dsimp only [Adaptive.dispatch] at actual
              split at actual
              · cases actual; exact step_ready before prior (.quotation task) _ rfl
              · split at actual
                · cases actual; exact step_ready before prior (.quotation (Adaptive.reverseTask task)) _ rfl
                · split at actual
                  · cases actual; exact fallback_ready before prior _ _ _
                  · split at actual
                    · cases actual; exact fallback_ready before prior _ _ _
                    · cases actual; exact diverted_ready before prior _ _
      | deduce rule left right =>
          cases instruction with
          | quotation task => cases actual; exact fallback_ready before prior _ _ _
          | conclusion request leftRef rightRef demand =>
              dsimp only [Adaptive.dispatch] at actual
              split at actual
              · cases actual; exact step_ready before prior _ _ rfl
              · split at actual
                · cases actual; exact fallback_ready before prior _ _ _
                · split at actual
                  · cases actual; exact fallback_ready before prior _ _ _
                  · split at actual
                    · cases actual; exact fallback_ready before prior _ _ _
                    · cases actual; exact diverted_ready before prior _ _

theorem turn_ready {context sources contract rules Context slots spec}
    (policy : Adaptive.Policy Context) (before : @Adaptive.Session context sources contract rules Context slots)
    (prior : Ready before.frame.dossier.cursor)
    (signal : Adaptive.Signal) (instruction : Instruction context rules slots spec)
    (turn : Adaptive.Turn before instruction) (actual : turn = Adaptive.takeTurn policy before signal instruction) :
    Ready turn.next.frame.dossier.cursor := by
  cases actual
  exact dispatch_ready before.frame prior instruction (Adaptive.selection policy before signal instruction).2

theorem adaptive_ready {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Ready start.frame.dossier.cursor) : Ready finish.frame.dossier.cursor := by
  induction trace with
  | done => exact initial
  | cons turn actual rest ih => exact ih (turn_ready _ _ initial _ _ turn actual)

theorem memory_step_ready {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (prior : Ready before.session.frame.dossier.cursor)
    (request : Memory.Request Context) (transition : Memory.Transition before request)
    (actual : transition = Memory.step before request) :
    Ready transition.next.session.frame.dossier.cursor := by
  cases actual
  cases request with
  | inspect index => exact prior
  | status => exact prior
  | reset policy => exact prior
  | progress policy signal =>
      rcases before with ⟨slots, session, queue⟩
      cases queue with
      | done => exact prior
      | cons instruction tail => exact turn_ready policy session.restore prior signal instruction _ rfl

theorem memory_ready {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Ready before.session.frame.dossier.cursor) :
    Ready finish.session.frame.dossier.cursor := by
  induction trace with
  | done => exact initial
  | cons transition actual rest ih => exact ih (memory_step_ready _ initial _ transition actual)

theorem program_bytes_exact {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Ready start.dossier.cursor) :
    SequentialPortable.restoreAt finish.dossier.cursor.depth
      (SequentialPortable.save finish.dossier.cursor.depth (cursor finish.dossier.cursor)) =
      some finish.dossier.cursor.assignment :=
  restore_exact _ (program_ready trace initial)

theorem adaptive_bytes_exact {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Ready start.frame.dossier.cursor) :
    SequentialPortable.restoreAt finish.frame.dossier.cursor.depth
      (SequentialPortable.save finish.frame.dossier.cursor.depth (cursor finish.frame.dossier.cursor)) =
      some finish.frame.dossier.cursor.assignment :=
  restore_exact _ (adaptive_ready trace initial)

theorem memory_bytes_exact {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Ready before.session.frame.dossier.cursor) :
    SequentialPortable.restoreAt finish.session.frame.dossier.cursor.depth
      (SequentialPortable.save finish.session.frame.dossier.cursor.depth (cursor finish.session.frame.dossier.cursor)) =
      some finish.session.frame.dossier.cursor.assignment :=
  restore_exact _ (memory_ready trace initial)

abbrev Coupled (depth : Nat) :=
  (assignment : SequentialAssignment depth) × ThreadedConstitutiveState depth assignment

/-- Install the decoded assignment as the state's executable field. Generation,
search seed, decisions and provenance are read from the retained environment. -/
def incorporateState {depth} {left right : SequentialAssignment depth} (same : left = right)
    (state : ThreadedConstitutiveState depth right) : ThreadedConstitutiveState depth left :=
  { threadedAssignment := left
    threadedAssignmentExact := rfl
    generation := state.generation
    searchSeed := state.searchSeed
    searchSeedExact := state.searchSeedExact
    decisions := state.decisions
    provenance := state.provenance
    provenanceExact := state.provenanceExact
    decisionsHold := same.symm ▸ state.decisionsHold }

theorem coupled_exact {depth} {left right : SequentialAssignment depth} (same : left = right)
    (state : ThreadedConstitutiveState depth right) :
    (⟨left, incorporateState same state⟩ : Coupled depth) = ⟨right, state⟩ := by
  cases same
  cases state with
  | mk retained retainedExact generation searchSeed searchSeedExact decisions provenance provenanceExact decisionsHold =>
      cases retainedExact
      rfl

/-- The bytes are loaded; the environment is received from the retained master. -/
def restoreState (before : MasterResources.Cursor) (ready : Ready before)
    (bytes : List UInt8) (bytesExact : bytes = SequentialPortable.save before.depth (cursor before)) :
    Option (Coupled before.depth) :=
  match loaded : SequentialPortable.restoreAt before.depth bytes with
  | none => none
  | some assignment =>
      let same : assignment = before.assignment :=
        Option.some.inj (loaded.symm.trans (bytesExact ▸ restore_exact before ready))
      some ⟨assignment, incorporateState same before.state⟩

theorem restored_state_exact (before : MasterResources.Cursor) (ready : Ready before) :
    restoreState before ready (SequentialPortable.save before.depth (cursor before)) rfl =
      some (⟨before.assignment, before.state⟩ : Coupled before.depth) := by
  unfold restoreState
  split
  · rename_i failed
    have impossible := (restore_exact before ready).symm.trans failed
    cases impossible
  · rename_i assignment loaded
    exact congrArg some (coupled_exact
      (Option.some.inj (loaded.symm.trans (restore_exact before ready))) before.state)

theorem all_state_consumers (before : MasterResources.Cursor) (ready : Ready before)
    {Result : Type u} (future : Coupled before.depth → Result) :
    (restoreState before ready (SequentialPortable.save before.depth (cursor before)) rfl).map future =
      some (future ⟨before.assignment, before.state⟩) := by
  rw [restored_state_exact]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.Ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.initial_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.next_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.variable_next_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.executed_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.restore_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.stage_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.quotation_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.step_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.program_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.fallback_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.diverted_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.dispatch_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.turn_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.adaptive_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.memory_step_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.memory_ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.program_bytes_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.adaptive_bytes_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.memory_bytes_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.Coupled
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.incorporateState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.coupled_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.restoreState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.restored_state_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialCapture.all_state_consumers
/- AXIOM_AUDIT_END -/
