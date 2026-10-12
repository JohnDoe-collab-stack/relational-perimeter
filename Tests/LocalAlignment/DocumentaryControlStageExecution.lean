import Tests.LocalAlignment.DocumentaryControlFrontierExecutableEvaluation
import Tests.LocalAlignment.DocumentaryControlFrontierExecutableOpening

/-! The stage's executable preservation composes its received opening payload
with the executable evaluation of its actually retained reduction code. It
does not recreate the opening, normalize again, or call the native evaluator. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution
open SAT Control ControlBindings ControlMasterData EndogenousDecomposition ControlFrontierApplication

structure Payload {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) where
  execution : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
    [GeneratedStructuralBranchContext.root stage.formula] stage.reduction.retained
  preservationExact : execution.preservation = stage.preservation

def code {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (opening : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
      [GeneratedStructuralBranchContext.root stage.formula] stage.opening.frontier)
    (openingExact : opening.preservation = stage.opening.preservation) : Code Label (Payload stage) :=
  .step .stagePreservation (fun _ =>
    (ControlFrontierExecutableEvaluation.code stage.formula (VariableMaster.selected stage.head) stage.reduction.code).bind
      (fun reduced =>
        (transCode opening reduced.1).bind (fun composed =>
          .done ⟨composed.1, composed.2.trans
            ((congrArg (fun preserved => preserved.trans reduced.1.preservation) openingExact).trans
              (congrArg (AcceptedFrontierPreservation.trans stage.opening.preservation) reduced.2))⟩)))

def bound {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) : Nat :=
  (ControlFrontierExecutableEvaluation.bound stage.reduction.code + 7) + 1

theorem bounded {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (opening : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
      [GeneratedStructuralBranchContext.root stage.formula] stage.opening.frontier)
    (openingExact : opening.preservation = stage.opening.preservation) :
    Within (code stage opening openingExact) (bound stage) := by
  apply within_step
  apply within_bind (ControlFrontierExecutableEvaluation.bounded _ _ _); intro reduced
  apply within_bind (more := 0) (trans_bounded opening reduced.1); intro composed
  exact within_done _

theorem finite {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (opening : ExecutablePreservation stage.formula (VariableMaster.selected stage.head)
      [GeneratedStructuralBranchContext.root stage.formula] stage.opening.frontier)
    (openingExact : opening.preservation = stage.opening.preservation) :
    Finite (code stage opening openingExact) := by
  obtain ⟨value, labels, trace, _⟩ := bounded stage opening openingExact
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution.Payload
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStageExecution.finite
/- AXIOM_AUDIT_END -/
