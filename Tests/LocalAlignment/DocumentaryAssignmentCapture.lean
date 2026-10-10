import Tests.LocalAlignment.DocumentaryAssignmentCodec
import Tests.LocalAlignment.DocumentaryMasterFormationExecution

/-! Capture from the actual retained master values, not from replayed heads.
Each retained head supplies its own returned transport code. Exactness follows
on the actual finite master/documentary traces from a correctly represented
seed. This reads one component, not the master formation or full present. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture
open Resources EndogenousDecomposition PortableAssignment Program

def retained : (kinds : List MasterResources.Kind) → Values MasterResources.Value kinds → Code
  | [], _ => []
  | kind :: kinds, values =>
      let prior := retained kinds values.2
      match kind with
      | .head _ _ => reflect values.1.down.stage.discovery.var
          values.1.down.stage.execution.code prior
      | .source _ _ | .prefix _ | .fresh _ | .discovery _ | .application _ | .decomposition _ _ _ => prior

def cursor (before : MasterResources.Cursor) : Code := retained before.kinds before.support.values

def Correct (before : MasterResources.Cursor) : Prop :=
  interpret (cursor before) = sequential before.assignment

def formed (before : MasterResources.Cursor) (actual : Correct before) :
    Formed (sequential before.assignment) := ⟨cursor before, actual⟩

theorem initial_correct {depth} (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    Correct (MasterResources.initialCursor state past fresh) := rfl

theorem next_code (before : MasterResources.Cursor) :
    cursor before.next = reflect before.head.stage.discovery.var before.head.stage.execution.code
      (cursor before) := rfl

theorem next_correct (before : MasterResources.Cursor) (actual : Correct before) :
    Correct before.next := by
  rw [Correct, next_code]
  exact stage_recipe_exact before.head.stage (cursor before) actual

theorem variable_next_correct (before : MasterResources.Cursor) (actual : Correct before) :
    Correct (VariableMaster.nextCursor before) :=
  next_correct before actual

theorem executed_correct (count : Nat) (before : MasterResources.Cursor) (actual : Correct before) :
    Correct (MasterResources.executeWithReferences count before).finish := by
  induction count generalizing before with
  | zero => exact actual
  | succ count ih => exact ih before.next (next_correct before actual)

theorem restore_exact (before : MasterResources.Cursor) (actual : Correct before) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor before)) =
      some (sequential before.assignment) :=
  AssignmentCodec.formed_roundtrip (formed before actual)

theorem stage_correct {context before sources contract demand left right}
    (actual : Correct before)
    (stage : @Master.Stage context before sources contract demand left right) :
    Correct stage.next := by
  have same : stage.next = VariableMaster.nextCursor before := stage.head.nextExact
  rw [same]
  exact variable_next_correct before actual

theorem quotation_correct {context sources contract rules slots}
    (before : @Frame context sources contract rules slots)
    (actual : Correct before.dossier.cursor) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) :
    Correct (Program.quotationStep before task produced).next.dossier.cursor := by
  rcases produced with ⟨stage, decision⟩
  cases decision <;> exact stage_correct actual stage

theorem step_correct {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Correct before.dossier.cursor)
    (instruction : Instruction context rules slots spec)
    (produced : Program.Step before instruction) (actual : produced = Program.step before instruction) :
    Correct produced.next.dossier.cursor := by
  cases actual
  cases instruction with
  | quotation task => exact quotation_correct before prior task (Dossier.step before.dossier task)
  | conclusion request leftSlot rightSlot demand =>
      rw [MasterFormationExecution.conclusion_cursor]
      exact prior

theorem program_correct {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Correct start.dossier.cursor) : Correct finish.dossier.cursor := by
  induction trace with
  | done => exact initial
  | cons produced actual rest ih => exact ih (step_correct _ initial _ produced actual)

theorem fallback_correct {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots) (prior : Correct before.dossier.cursor)
    (instruction : Instruction context rules slots spec)
    (route : Adaptive.Route) (inspection : Option Adaptive.Readout) :
    Correct (Adaptive.fallback before instruction route inspection).next.dossier.cursor :=
  step_correct before prior instruction (Program.step before instruction) rfl

theorem diverted_correct {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots) (prior : Correct before.dossier.cursor)
    (instruction proposed : Instruction context rules slots spec) :
    Correct (Adaptive.diverted before instruction proposed).next.dossier.cursor := by
  have first := step_correct before prior proposed (Program.step before proposed) rfl
  exact step_correct (Adaptive.dropHead (Program.step before proposed).next) first instruction _ rfl

theorem dispatch_correct {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Correct before.dossier.cursor)
    (instruction : Instruction context rules slots spec) (proposal : Option Adaptive.Proposal) :
    Correct (Adaptive.dispatch before instruction proposal).next.dossier.cursor := by
  generalize actual : Adaptive.dispatch before instruction proposal = effect
  cases proposal with
  | none => cases actual; exact fallback_correct before prior instruction _ _
  | some proposal =>
      cases proposal with
      | current => cases actual; exact step_correct before prior instruction _ rfl
      | reverseSources =>
          cases instruction with
          | quotation task => cases actual; exact step_correct before prior (.quotation (Adaptive.reverseTask task)) _ rfl
          | conclusion request left right demand => cases actual; exact fallback_correct before prior _ _ _
      | inspect index =>
          dsimp only [Adaptive.dispatch] at actual
          split at actual
          · cases actual; exact fallback_correct before prior instruction _ _
          · split at actual
            · cases actual; exact fallback_correct before prior instruction _ _
            · cases actual; exact fallback_correct before prior instruction _ _
      | quote left right =>
          cases instruction with
          | conclusion request leftRef rightRef demand => cases actual; exact fallback_correct before prior _ _ _
          | quotation task =>
              dsimp only [Adaptive.dispatch] at actual
              split at actual
              · cases actual; exact step_correct before prior (.quotation task) _ rfl
              · split at actual
                · cases actual; exact step_correct before prior (.quotation (Adaptive.reverseTask task)) _ rfl
                · split at actual
                  · cases actual; exact fallback_correct before prior _ _ _
                  · split at actual
                    · cases actual; exact fallback_correct before prior _ _ _
                    · cases actual; exact diverted_correct before prior _ _
      | deduce rule left right =>
          cases instruction with
          | quotation task => cases actual; exact fallback_correct before prior _ _ _
          | conclusion request leftRef rightRef demand =>
              dsimp only [Adaptive.dispatch] at actual
              split at actual
              · cases actual; exact step_correct before prior _ _ rfl
              · split at actual
                · cases actual; exact fallback_correct before prior _ _ _
                · split at actual
                  · cases actual; exact fallback_correct before prior _ _ _
                  · split at actual
                    · cases actual; exact fallback_correct before prior _ _ _
                    · cases actual; exact diverted_correct before prior _ _

theorem turn_correct {context sources contract rules Context slots spec}
    (policy : Adaptive.Policy Context) (before : @Adaptive.Session context sources contract rules Context slots)
    (prior : Correct before.frame.dossier.cursor)
    (signal : Adaptive.Signal) (instruction : Instruction context rules slots spec)
    (turn : Adaptive.Turn before instruction) (actual : turn = Adaptive.takeTurn policy before signal instruction) :
    Correct turn.next.frame.dossier.cursor := by
  cases actual
  exact dispatch_correct before.frame prior instruction (Adaptive.selection policy before signal instruction).2

theorem adaptive_correct {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Correct start.frame.dossier.cursor) : Correct finish.frame.dossier.cursor := by
  induction trace with
  | done => exact initial
  | cons turn actual rest ih => exact ih (turn_correct _ _ initial _ _ turn actual)

theorem memory_step_correct {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (prior : Correct before.session.frame.dossier.cursor)
    (request : Memory.Request Context) (transition : Memory.Transition before request)
    (actual : transition = Memory.step before request) :
    Correct transition.next.session.frame.dossier.cursor := by
  cases actual
  cases request with
  | inspect index => exact prior
  | status => exact prior
  | reset policy => exact prior
  | progress policy signal =>
      rcases before with ⟨slots, session, queue⟩
      cases queue with
      | done => exact prior
      | cons instruction tail => exact turn_correct policy session.restore prior signal instruction _ rfl

theorem memory_correct {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Correct before.session.frame.dossier.cursor) :
    Correct finish.session.frame.dossier.cursor := by
  induction trace with
  | done => exact initial
  | cons transition actual rest ih => exact ih (memory_step_correct _ initial _ transition actual)

theorem program_bytes_exact {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Correct start.dossier.cursor) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor finish.dossier.cursor)) =
      some (sequential finish.dossier.cursor.assignment) :=
  restore_exact _ (program_correct trace initial)

theorem adaptive_bytes_exact {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Correct start.frame.dossier.cursor) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor finish.frame.dossier.cursor)) =
      some (sequential finish.frame.dossier.cursor.assignment) :=
  restore_exact _ (adaptive_correct trace initial)

theorem memory_bytes_exact {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Correct before.session.frame.dossier.cursor) :
    AssignmentCodec.restore (AssignmentCodec.save (cursor finish.session.frame.dossier.cursor)) =
      some (sequential finish.session.frame.dossier.cursor.assignment) :=
  restore_exact _ (memory_correct trace initial)

end ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.retained
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.Correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.initial_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.next_code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.next_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.variable_next_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.executed_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.restore_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.stage_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.quotation_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.step_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.program_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.fallback_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.diverted_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.dispatch_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.turn_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.adaptive_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.memory_step_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.memory_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.program_bytes_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.adaptive_bytes_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCapture.memory_bytes_exact
/- AXIOM_AUDIT_END -/
