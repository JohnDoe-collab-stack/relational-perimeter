import Tests.LocalAlignment.DocumentaryControlFrontierEvaluation

/-! The complete stage preservation is formed from the actual retained route
and the opening preservation already stored in the same stage. Its formation
bound does not evaluate the native preservation; bound computation itself and
later map applications remain distinct obligations. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlStagePreservation
open SAT Control ControlBindings ControlMasterData EndogenousDecomposition

def code {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) :
    Code Label (Actual stage.preservation) :=
  .step .stagePreservation (fun _ =>
    (ControlFrontierEvaluation.code stage.formula (VariableMaster.selected stage.head) stage.reduction.code).bind
      (fun reduced =>
        (ControlFrontierOpening.transCode stage.opening.preservation reduced.1).bind (fun composed =>
          .done ⟨composed.1, by
            obtain ⟨_, actual⟩ := composed; cases actual
            obtain ⟨_, actual⟩ := reduced; cases actual
            rfl⟩)))

def bound {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) : Nat :=
  (ControlFrontierEvaluation.bound stage.formula (VariableMaster.selected stage.head) stage.reduction.code + 3) + 1

theorem bounded {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) :
    Within (code stage) (bound stage) := by
  apply within_step
  apply within_bind (ControlFrontierEvaluation.bounded _ _ _); intro reduced
  apply within_bind (more := 0) (ControlFrontierOpening.trans_bounded stage.opening.preservation reduced.1); intro composed
  exact within_done _

theorem finite {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) : Finite (code stage) := by
  obtain ⟨value, labels, trace, _⟩ := bounded stage
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlStagePreservation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStagePreservation.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStagePreservation.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStagePreservation.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStagePreservation.finite
/- AXIOM_AUDIT_END -/
