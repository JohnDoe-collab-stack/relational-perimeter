import Tests.LocalAlignment.DocumentaryControlCompletion
import Tests.LocalAlignment.DocumentaryControlStageCeilingExecution

/-! The concrete seed closes the initial reader hypothesis. Its continuation
passes through the same actual stage payload, whose paid applications return
both the whole original Application and its actual ceiling. Completion consumes
that returned Reader and continuation directly; no native ceiling is invoked. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 16000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCeilingCompletion
open Resources SAT Selection Control ControlBindings EndogenousDecomposition

def executedDecideCode {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (payload : ControlStageCeilingExecution.Payload stage) : Code Label (ControlCompletion.Decision stage memory) :=
  (ControlSeedApplication.code (VariableMaster.selected stage.head) stage.leftCheck.flag stage.rightCheck.flag).bind (fun produced =>
    match produced with
    | .blocked impossible found => .step .citationDecision (fun _ => .done
        ⟨.blocked
          (fun permission meets => impossible false (stage.leftCheck.complete permission meets))
          (fun permission meets => impossible true (stage.rightCheck.complete permission meets)), by
            unfold Master.decide; rw [← found]⟩)
    | .viable assignment accepted reader limited found =>
      .step .citationInput (fun _ =>
        let input : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
            [GeneratedStructuralBranchContext.root stage.formula] := .head ⟨assignment, True.intro⟩
        .step .citationPreservation (fun _ =>
          (payload.execution.forward input 1 reader limited).bind (fun paid =>
            let applied := paid.application
            have retainedAccepted : FrontierAccept (generatedStructuralBranchSystem stage.formula)
                stage.reduction.retained applied.continuation.1 :=
              applied.continuation.2.symm ▸ payload.execution.original.preservation.forward.preservesAccept input accepted
            (ControlCompletion.executedCompleteCode stage memory applied.continuation.1 retainedAccepted applied.reader).bind (fun packet =>
              .step .citationDecision (fun _ => .done ⟨.complete packet.1, by
                have continuationExact : applied.continuation.1 = stage.preservation.forward.map input :=
                  applied.continuation.2.trans
                    (congrArg (fun preservation => preservation.forward.map input) (ControlStageCeilingExecution.preservation_exact stage payload))
                have completionExact : Master.complete stage memory applied.continuation.1 retainedAccepted =
                    Master.complete stage memory (stage.preservation.forward.map input)
                      (stage.preservation.forward.preservesAccept input accepted) :=
                  ControlCompletion.completion_same_continuation stage memory _ _ _ _ continuationExact
                unfold Master.decide; rw [← found]
                exact congrArg Master.Decision.complete (packet.2.trans completionExact)⟩))))))

theorem executed_decide_finite {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (payload : ControlStageCeilingExecution.Payload stage) :
    Finite (executedDecideCode stage memory payload) := by
  apply finite_bind (ControlFrontierCeilingApplication.finite_of_within (ControlSeedApplication.bounded _ _ _)); intro produced
  cases produced with
  | blocked impossible found => exact finite_step _ _ (finite_done _)
  | viable assignment accepted reader limited found =>
      apply finite_step; apply finite_step
      apply finite_bind (payload.execution.forward_finite _ _ _ _); intro paid
      apply finite_bind
        (ControlFrontierCeilingApplication.finite_of_within (ControlCompletion.executed_complete_bounded _ _ _ _ _))
      intro packet
      exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlCeilingCompletion

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCeilingCompletion.executedDecideCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCeilingCompletion.executed_decide_finite
/- AXIOM_AUDIT_END -/
