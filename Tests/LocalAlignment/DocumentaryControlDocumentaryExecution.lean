import Tests.LocalAlignment.DocumentaryControlFrameExecution
import Tests.LocalAlignment.DocumentaryControlCompactExecution

/-! Public terminal entry with positive compact instrumentation. The source is
exactly the complete received frame program; its original Step, next Frame,
readers, master and constitutive witnesses remain the whole output value.
Initial source/master/past/fresh are inputs, not reconstructed bootstrap data.
Every successor carries its actual realization. D3 envelopes are separate. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution
open Resources EndogenousDecomposition Program Snapshot Control ControlBindings ControlMasterData ControlDeferred
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification} {spec : Specification}
universe u

abbrev Source (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before) :=
  ControlFrameExecution.code before instruction realized

def execute (sourceFuel finalBudget : Nat) (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before) :=
  ControlCompactExecution.execute sourceFuel finalBudget (Source before instruction realized)

def runCtl (sourceFuel finalBudget : Nat) (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before) :=
  ControlCompactExecution.runCtl sourceFuel finalBudget (Source before instruction realized)

theorem ctl_sound (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before)
    {sourceFuel finalBudget output path tape}
    (actual : runCtl sourceFuel finalBudget before instruction realized = some (output, path, tape)) :
    ControlCompactData.Model (Source before instruction realized) sourceFuel output path tape ∧
      tape.cost ≤ finalBudget ∧ output = ControlCompactData.observation (Control.execute sourceFuel (Source before instruction realized)) :=
  ControlCompactExecution.ctl_sound actual

theorem ctl_complete (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before)
    {sourceFuel finalBudget output path tape}
    (trace : ControlCompactData.Model (Source before instruction realized) sourceFuel output path tape)
    (within : tape.cost ≤ finalBudget) :
    runCtl sourceFuel finalBudget before instruction realized = some (output, path, tape) :=
  ControlCompactExecution.ctl_complete trace within

theorem ctl_mono (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before)
    {sourceFuel finalBudget output path tape larger}
    (actual : runCtl sourceFuel finalBudget before instruction realized = some (output, path, tape))
    (increase : finalBudget ≤ larger) :
    runCtl sourceFuel larger before instruction realized = some (output, path, tape) :=
  ControlCompactExecution.ctl_mono actual increase

theorem finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before)
    (sourceFuel : Nat) :
    ∃ budget output path tape, runCtl sourceFuel budget before instruction realized = some (output, path, tape) :=
  ControlCompactExecution.finite _ sourceFuel

theorem successful_program {Value : Type u} (code : Code Label Value) (ends : Finite code) :
    ∃ (sourceFuel budget : Nat) (output : ControlCompactData.Output Value) (path : ControlCompactData.Path) (tape : ControlRunner.Tape),
      ControlCompactExecution.runCtl sourceFuel budget code = some (some output, path, tape) := by
  obtain ⟨sourceFuel, value, labels, sourceActual⟩ := Control.finite_complete ends
  cases sourceFound : Control.execute sourceFuel code with
  | none =>
    have absent : Control.runCtl sourceFuel code = none :=
      congrArg (fun received => received.map (fun result => (result.value, result.labels))) sourceFound
    have impossible : (none : Option (Value × List Label)) = some (value, labels) := absent.symm.trans sourceActual
    cases impossible
  | some result =>
    obtain ⟨output, path, tape, realized⟩ := ControlCompactData.has_model code sourceFuel
    have same : output = some (⟨result.value, result.labels⟩ : ControlCompactData.Output Value) :=
      realized.source_exact.trans (congrArg ControlCompactData.observation sourceFound)
    cases same
    exact ⟨sourceFuel, tape.cost, _, path, tape, ControlCompactExecution.ctl_complete realized (Nat.le_refl _)⟩

theorem successful_finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before) :
    ∃ (sourceFuel budget : Nat) (result : ControlCompactData.Output (ControlFrameExecution.Produced before instruction)) (path : ControlCompactData.Path) (tape : ControlRunner.Tape),
      runCtl sourceFuel budget before instruction realized = some (some result, path, tape) :=
  successful_program _ (ControlFrameExecution.finite _ _ realized)

theorem whole_step (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before)
    {sourceFuel budget result path tape}
    (_actual : runCtl sourceFuel budget before instruction realized = some (some result, path, tape)) :
    result.value.step.1 = Program.step before.restore instruction := result.value.step.2

theorem whole_next (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : ControlFrameExecution.Realized before)
    {sourceFuel budget result path tape}
    (_actual : runCtl sourceFuel budget before instruction realized = some (some result, path, tape)) :
    result.value.next.1 = Snapshot.frame result.value.step.1.next := result.value.next.2

theorem successor_finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (_realized : ControlFrameExecution.Realized before)
    (produced : ControlFrameExecution.Produced before instruction)
    {nextSpec : Specification} (nextInstruction : Instruction context rules (spec :: slots) nextSpec) :
    ∃ (sourceFuel budget : Nat) (result : ControlCompactData.Output
      (ControlFrameExecution.Produced produced.next.1 nextInstruction)) (path : ControlCompactData.Path) (tape : ControlRunner.Tape),
      runCtl sourceFuel budget produced.next.1 nextInstruction produced.realized = some (some result, path, tape) :=
  successful_finite _ _ produced.realized

def initial {depth : Nat}
    (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (sources : Support SourceValue context) (contract : Contract) (rules : Deduction.Policy) :
    FrameData sources contract rules [] :=
  ⟨⟨MasterResources.initialCursor state past fresh, Documentary.empty sources contract⟩,
    ⟨[], Deduction.empty sources contract rules⟩, .nil⟩

structure InitialProduced {depth : Nat}
    (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (sources : Support SourceValue context) (contract : Contract) (rules : Deduction.Policy) where
  frame : Actual (initial state past fresh sources contract rules)
  realized : ControlFrameExecution.Realized frame.1

@[inline] def cursorFromReceivedState {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (kinds : List MasterResources.Kind)
    (support : Support MasterResources.Value kinds)
    (source : Ref kinds (.source depth assignment))
    (sourceActual : (support.read source).down = state)
    (past : Ref kinds (.prefix state)) (fresh : Ref kinds (.fresh state)) : MasterResources.Cursor :=
  ⟨depth, assignment, kinds, support, source, sourceActual.symm ▸ past, sourceActual.symm ▸ fresh⟩

def initialCode {depth : Nat}
    (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (sources : Support SourceValue context) (contract : Contract) (rules : Deduction.Policy) :
    Code Label (InitialProduced state past fresh sources contract rules) :=
  .step .formationValues (fun _ =>
    let values : Values MasterResources.Value [.fresh state, .prefix state, .source depth (initialSequentialAssignment depth)] :=
      (⟨⟨fresh⟩⟩, ⟨past⟩, ⟨state⟩, PUnit.unit)
    .step .formationWitness (fun _ =>
      let support : Support MasterResources.Value _ := ⟨values, .given values⟩
      .step .formationResources (fun _ =>
        let cursor : MasterResources.Cursor :=
          cursorFromReceivedState state _ support (.prior (.prior .here)) rfl (.prior .here) .here
        .step .masterNextCursor (fun _ =>
          let frame : Actual (initial state past fresh sources contract rules) :=
            ⟨⟨⟨cursor, Documentary.empty sources contract⟩,
                ⟨[], Deduction.empty sources contract rules⟩, .nil⟩, rfl⟩
          .step .formationResources (fun _ =>
            (ControlFrameExecution.formCode frame.1 (AssignmentCapture.initial_correct state past fresh) .empty).bind
              (fun realized => .step .executionPayload (fun _ => .done ⟨frame, realized⟩)))))))

theorem initial_finite {depth : Nat}
    (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (sources : Support SourceValue context) (contract : Contract) (rules : Deduction.Policy) :
    Finite (initialCode state past fresh sources contract rules) := by
  apply finite_step; apply finite_step; apply finite_step; apply finite_step; apply finite_step
  apply finite_bind (ControlFrameExecution.form_finite _ _ _); intro realized
  exact finite_step _ _ (finite_done _)

def initialExecute {depth : Nat} (sourceFuel finalBudget : Nat)
    (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (sources : Support SourceValue context) (contract : Contract) (rules : Deduction.Policy) :=
  ControlCompactExecution.execute sourceFuel finalBudget (initialCode state past fresh sources contract rules)

theorem initial_successful_finite {depth : Nat}
    (state : ThreadedConstitutiveState depth (initialSequentialAssignment depth))
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (sources : Support SourceValue context) (contract : Contract) (rules : Deduction.Policy) :
    ∃ (sourceFuel budget : Nat) (result : ControlCompactData.Output
      (InitialProduced state past fresh sources contract rules)) (path : ControlCompactData.Path) (tape : ControlRunner.Tape),
      ControlCompactExecution.runCtl sourceFuel budget (initialCode state past fresh sources contract rules) = some (some result, path, tape) :=
  successful_program _ (initial_finite state past fresh sources contract rules)

end ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.Source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.runCtl
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.ctl_sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.ctl_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.ctl_mono
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.successful_program
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.successful_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.whole_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.whole_next
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.successor_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.initial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.InitialProduced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.cursorFromReceivedState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.initialCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.initial_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.initialExecute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDocumentaryExecution.initial_successful_finite
/- AXIOM_AUDIT_END -/
