import Tests.LocalAlignment.DocumentaryControlMasterData

/-! Meter the source evaluator's calls, frames, trace constructors and result
packets. This is an abstract allocation model, not a physical heap bound.
This historical CPS prototype remains separate from the final ControlRunner.
Its added admin branch preserves source business behavior; its amplified
administrative cost is not the final D2 implementation. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration
open Control ControlBindings ControlMasterData
universe u v

def eventLabel : Event → Label
  | .compose => .controlCompose
  | .call => .controlCall
  | .closure => .controlClosure
  | .frame => .controlFrame
  | .trace => .controlTrace
  | .result => .controlResult
  | .allocation => .formationResources

def bindCode {Value : Type u} {Next : Type v}
    (code : Code Label Value) (continuation : Value → Code Label Next) : Code Label Next :=
  .step .controlCompose (fun _ => match code with
    | .done value => .step .controlCall (fun _ => continuation value)
    | .step label next => .step .controlClosure (fun _ =>
      .step label (fun _ => bindCode (next ()) continuation))
    | .admin event next _forwards => .step .controlClosure (fun _ =>
      .step (eventLabel event) (fun _ => bindCode (next ()) continuation)))

theorem bind_finite {Value : Type u} {Next : Type v}
    {code : Code Label Value} {continuation : Value → Code Label Next}
    (first : Finite code) (every : ∀ value, Finite (continuation value)) :
    Finite (bindCode code continuation) := by
  obtain ⟨value, labels, ⟨trace⟩⟩ := first
  induction trace with
  | done => exact finite_step _ _ (finite_step _ _ (every _))
  | step rest previous =>
    exact finite_step _ _ (finite_step _ _ (finite_step _ _ previous))
  | admin rest previous =>
    exact finite_step _ _ (finite_step _ _ (finite_step _ _ previous))

def executeCode {Value : Type u} (fuel : Nat) (code : Code Label Value) :
    Code Label (Actual (Control.execute fuel code)) :=
  .step .controlInspect (fun _ => match code with
    | .done value => .step .controlTrace (fun _ =>
      let labels : List Label := []
      .step .controlWitness (fun _ =>
        let trace : Eval (.done value) labels value := .done
        .step .controlResult (fun _ => .done
          ⟨some ⟨value, labels, trace, Nat.zero_le fuel⟩, by cases fuel <;> rfl⟩)))
    | .step label next => match fuel with
      | 0 => .step .controlResult (fun _ => .done ⟨none, rfl⟩)
      | remaining + 1 => .step .controlCall (fun _ =>
        let nextCode := next ()
        .step .controlFrame (fun _ =>
          bindCode (executeCode remaining nextCode) (fun returned => match received : returned.1 with
            | none => .step .controlResult (fun _ => .done
              ⟨none, by rw [Control.execute, ← returned.2, received]⟩)
            | some actual => .step .controlFrame (fun _ =>
              .step .controlTrace (fun _ =>
                let labels := label :: actual.labels
                .step .controlWitness (fun _ =>
                  let trace : Eval (.step label next) labels actual.value := .step actual.trace
                  .step .controlResult (fun _ => .done
                    ⟨some ⟨actual.value, labels, trace, Nat.succ_le_succ actual.bounded⟩,
                      by rw [Control.execute, ← returned.2, received]⟩)))))))
    | .admin event next _forwards => .step (eventLabel event) (fun _ =>
        .step .controlCall (fun _ =>
          let nextCode := next ()
          .step .controlFrame (fun _ =>
            bindCode (executeCode fuel nextCode) (fun returned => match received : returned.1 with
              | none => .step .controlResult (fun _ => .done
                ⟨none, by rw [Control.execute, ← returned.2, received]⟩)
              | some actual => .step .controlFrame (fun _ =>
                .step .controlWitness (fun _ =>
                  let trace : Eval (.admin event next _forwards) actual.labels actual.value := .admin actual.trace
                  .step .controlResult (fun _ => .done
                    ⟨some ⟨actual.value, actual.labels, trace, actual.bounded⟩,
                      by rw [Control.execute, ← returned.2, received]⟩))))))))
termination_by structural code

theorem execute_finite {Value : Type u} (fuel : Nat) (code : Code Label Value) :
    Finite (executeCode fuel code) := by
  induction code generalizing fuel with
  | done value =>
    rw [executeCode.eq_def]
    repeat apply finite_step
    exact finite_done _
  | step label next previous =>
    rw [executeCode.eq_def]
    apply finite_step
    cases fuel with
    | zero => exact finite_step _ _ (finite_done _)
    | succ remaining =>
      apply finite_step; apply finite_step
      apply bind_finite (previous () remaining)
      intro returned; split
      · exact finite_step _ _ (finite_done _)
      · repeat apply finite_step
        exact finite_done _
  | admin event next forwards previous =>
    rw [executeCode.eq_def]
    repeat apply finite_step
    apply bind_finite (previous () fuel)
    intro returned; split
    · exact finite_step _ _ (finite_done _)
    · repeat apply finite_step
      exact finite_done _

theorem source_result {Value : Type u} (fuel : Nat) (code : Code Label Value)
    (budget : Nat) (actual : Result (executeCode fuel code) budget) :
    actual.value.1 = Control.execute fuel code := actual.value.2

theorem sufficient_budget {Value : Type u} (fuel : Nat) (code : Code Label Value) :
    ∃ (budget : Nat) (result : Actual (Control.execute fuel code)) (labels : List Label),
      runCtl budget (executeCode fuel code) = some (result, labels) :=
  finite_complete (execute_finite fuel code)


end ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.eventLabel
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.bindCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.bind_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.executeCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.execute_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.source_result
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministration.sufficient_budget
/- AXIOM_AUDIT_END -/
