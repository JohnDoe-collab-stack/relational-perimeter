import Tests.LocalAlignment.DocumentaryControlFrontierCeilingEvaluation
import Tests.LocalAlignment.DocumentaryControlFrontierCeilingOpening
import Tests.LocalAlignment.DocumentaryControlStageExecution

/-! The stage keeps its original complete payload and the executable ceiling
realization formed from the same received opening and retained reduction. The
original and controlled payloads share exactly the same original executor. -/
set_option genInjectivity false
set_option maxHeartbeats 16000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlStageCeilingExecution
open SAT Control ControlBindings ControlMasterData EndogenousDecomposition ControlFrontierCeilingApplication

structure Payload {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) where
  original : ControlStageExecution.Payload stage
  execution : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
    [GeneratedStructuralBranchContext.root stage.formula] stage.reduction.retained
  executionExact : execution.original = original.execution

theorem preservation_exact {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (payload : Payload stage) : payload.execution.original.preservation = stage.preservation :=
  (congrArg ControlFrontierApplication.ExecutablePreservation.preservation payload.executionExact).trans
    payload.original.preservationExact

def code {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (opening : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
      [GeneratedStructuralBranchContext.root stage.formula] stage.opening.frontier)
    (openingExact : opening.original.preservation = stage.opening.preservation) : Code Label (Payload stage) :=
  .step .stagePreservation (fun _ =>
    (ControlFrontierCeilingEvaluation.code stage.formula (VariableMaster.selected stage.head) stage.reduction.code).bind
      (fun reduced =>
        (transCode opening reduced.1).bind (fun composed =>
          .step .executionPayload (fun _ =>
            let original : ControlStageExecution.Payload stage :=
              ⟨composed.1.original, composed.2.trans
                ((congrArg (fun preserved => preserved.trans reduced.1.original.preservation) openingExact).trans
                  (congrArg (AcceptedFrontierPreservation.trans stage.opening.preservation) reduced.2))⟩
            .step .formationResources (fun _ =>
              .done ⟨original, composed.1, rfl⟩)))))

theorem finite {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (opening : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
      [GeneratedStructuralBranchContext.root stage.formula] stage.opening.frontier)
    (openingExact : opening.original.preservation = stage.opening.preservation) :
    Finite (code stage opening openingExact) := by
  apply finite_step
  apply finite_bind (ControlFrontierCeilingEvaluation.finite _ _ _); intro reduced
  apply finite_bind (trans_finite opening reduced.1); intro composed
  apply finite_step; apply finite_step
  exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlStageCeilingExecution

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageCeilingExecution.Payload
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageCeilingExecution.preservation_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageCeilingExecution.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageCeilingExecution.finite
/- AXIOM_AUDIT_END -/
