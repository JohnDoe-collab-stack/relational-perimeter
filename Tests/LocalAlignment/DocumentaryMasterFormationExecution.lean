import Tests.LocalAlignment.DocumentaryMasterFormation
import Tests.LocalAlignment.DocumentaryMemory

/-! The recipe class covers actual finite documentary, adaptive and memory
executions. These logical membership witnesses consume the actual shared steps;
they are not an executable byte loader or a no-replay runtime certificate
builder. Master values and dependent environments remain to be encoded. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution
open Resources Program EndogenousDecomposition MasterFormation

def stage_formed {context cursor sources contract demand left right}
    (prior : Formed cursor.support)
    (stage : @Master.Stage context cursor sources contract demand left right) :
    Formed stage.next.support := by
  have same : stage.next = VariableMaster.nextCursor cursor := stage.head.nextExact
  exact same.symm ▸ next_formed cursor prior

def quotation_formed {context sources contract rules slots}
    (before : @Frame context sources contract rules slots)
    (prior : Formed before.dossier.cursor.support) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) :
    Formed (Program.quotationStep before task produced).next.dossier.cursor.support := by
  rcases produced with ⟨stage, decision⟩
  cases decision <;> exact stage_formed prior stage

theorem deduction_cursor {context sources contract rules slots left right}
    (before : @Frame context sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    (Program.deductionStep before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision).next.dossier.cursor = before.dossier.cursor := by
  cases decision <;> rfl

theorem conclusion_cursor {context sources contract rules slots left right}
    (before : @Frame context sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand) :
    (Program.step before (.conclusion request leftSlot rightSlot demand)).next.dossier.cursor =
      before.dossier.cursor := by
  dsimp only [Program.step]
  split
  · rfl
  · split
    · rfl
    · exact deduction_cursor before request leftSlot rightSlot demand _ _ _ _ _

theorem step_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed before.dossier.cursor.support)
    (instruction : Instruction context rules slots spec)
    (produced : Program.Step before instruction) (actual : produced = Program.step before instruction) :
    Nonempty (Formed produced.next.dossier.cursor.support) := by
  cases actual
  cases instruction with
  | quotation task => exact ⟨quotation_formed before prior task (Dossier.step before.dossier task)⟩
  | conclusion request leftSlot rightSlot demand =>
      rw [conclusion_cursor]
      exact ⟨prior⟩

theorem program_formed {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Formed start.dossier.cursor.support) : Nonempty (Formed finish.dossier.cursor.support) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons produced actual rest ih =>
      rcases step_formed _ initial _ produced actual with ⟨next⟩
      exact ih next

theorem fallback_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed before.dossier.cursor.support)
    (instruction : Instruction context rules slots spec)
    (route : Adaptive.Route) (inspection : Option Adaptive.Readout) :
    Nonempty (Formed (Adaptive.fallback before instruction route inspection).next.dossier.cursor.support) :=
  step_formed before prior instruction (Program.step before instruction) rfl

theorem diverted_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed before.dossier.cursor.support)
    (instruction proposed : Instruction context rules slots spec) :
    Nonempty (Formed (Adaptive.diverted before instruction proposed).next.dossier.cursor.support) := by
  rcases step_formed before prior proposed (Program.step before proposed) rfl with ⟨first⟩
  exact step_formed (Adaptive.dropHead (Program.step before proposed).next) first instruction _ rfl

theorem dispatch_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (prior : Formed before.dossier.cursor.support)
    (instruction : Instruction context rules slots spec) (proposal : Option Adaptive.Proposal) :
    Nonempty (Formed (Adaptive.dispatch before instruction proposal).next.dossier.cursor.support) := by
  generalize actual : Adaptive.dispatch before instruction proposal = effect
  cases proposal with
  | none => cases actual; exact fallback_formed before prior instruction _ _
  | some proposal =>
      cases proposal with
      | current => cases actual; exact step_formed before prior instruction _ rfl
      | reverseSources =>
          cases instruction with
          | quotation task => cases actual; exact step_formed before prior (.quotation (Adaptive.reverseTask task)) _ rfl
          | conclusion request left right demand => cases actual; exact fallback_formed before prior _ _ _
      | inspect index =>
          dsimp only [Adaptive.dispatch] at actual
          split at actual
          · cases actual; exact fallback_formed before prior instruction _ _
          · split at actual
            · cases actual; exact fallback_formed before prior instruction _ _
            · cases actual; exact fallback_formed before prior instruction _ _
      | quote left right =>
          cases instruction with
          | conclusion request leftRef rightRef demand => cases actual; exact fallback_formed before prior _ _ _
          | quotation task =>
              dsimp only [Adaptive.dispatch] at actual
              split at actual
              · cases actual; exact step_formed before prior (.quotation task) _ rfl
              · split at actual
                · cases actual; exact step_formed before prior (.quotation (Adaptive.reverseTask task)) _ rfl
                · split at actual
                  · cases actual; exact fallback_formed before prior _ _ _
                  · split at actual
                    · cases actual; exact fallback_formed before prior _ _ _
                    · cases actual; exact diverted_formed before prior _ _
      | deduce rule left right =>
          cases instruction with
          | quotation task => cases actual; exact fallback_formed before prior _ _ _
          | conclusion request leftRef rightRef demand =>
              dsimp only [Adaptive.dispatch] at actual
              split at actual
              · cases actual; exact step_formed before prior _ _ rfl
              · split at actual
                · cases actual; exact fallback_formed before prior _ _ _
                · split at actual
                  · cases actual; exact fallback_formed before prior _ _ _
                  · split at actual
                    · cases actual; exact fallback_formed before prior _ _ _
                    · cases actual; exact diverted_formed before prior _ _

theorem turn_formed {context sources contract rules Context slots spec}
    (policy : Adaptive.Policy Context) (before : @Adaptive.Session context sources contract rules Context slots)
    (prior : Formed before.frame.dossier.cursor.support)
    (signal : Adaptive.Signal) (instruction : Instruction context rules slots spec)
    (turn : Adaptive.Turn before instruction) (actual : turn = Adaptive.takeTurn policy before signal instruction) :
    Nonempty (Formed turn.next.frame.dossier.cursor.support) := by
  cases actual
  exact dispatch_formed before.frame prior instruction (Adaptive.selection policy before signal instruction).2

theorem adaptive_formed {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Formed start.frame.dossier.cursor.support) : Nonempty (Formed finish.frame.dossier.cursor.support) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons turn actual rest ih =>
      rcases turn_formed _ _ initial _ _ turn actual with ⟨next⟩
      exact ih next

theorem memory_step_formed {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (prior : Formed before.session.frame.dossier.cursor.support)
    (request : Memory.Request Context) (transition : Memory.Transition before request)
    (actual : transition = Memory.step before request) :
    Nonempty (Formed transition.next.session.frame.dossier.cursor.support) := by
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

theorem memory_formed {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Formed before.session.frame.dossier.cursor.support) :
    Nonempty (Formed finish.session.frame.dossier.cursor.support) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons transition actual rest ih =>
      rcases memory_step_formed _ initial _ transition actual with ⟨next⟩
      exact ih next

theorem program_payload_exact {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Formed start.dossier.cursor.support) :
    ∃ formed : Formed finish.dossier.cursor.support,
      (cursor finish.dossier.cursor formed).restore = finish.dossier.cursor := by
  rcases program_formed trace initial with ⟨formed⟩
  exact ⟨formed, cursor_exact _ formed⟩

theorem adaptive_payload_exact {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Formed start.frame.dossier.cursor.support) :
    ∃ formed : Formed finish.frame.dossier.cursor.support,
      (cursor finish.frame.dossier.cursor formed).restore = finish.frame.dossier.cursor := by
  rcases adaptive_formed trace initial with ⟨formed⟩
  exact ⟨formed, cursor_exact _ formed⟩

theorem memory_payload_exact {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Formed before.session.frame.dossier.cursor.support) :
    ∃ formed : Formed finish.session.frame.dossier.cursor.support,
      (cursor finish.session.frame.dossier.cursor formed).restore = finish.session.frame.dossier.cursor := by
  rcases memory_formed trace initial with ⟨formed⟩
  exact ⟨formed, cursor_exact _ formed⟩

end ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.stage_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.quotation_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.deduction_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.conclusion_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.program_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.fallback_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.diverted_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.dispatch_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.turn_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.adaptive_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.memory_step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.memory_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.program_payload_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.adaptive_payload_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormationExecution.memory_payload_exact
/- AXIOM_AUDIT_END -/
