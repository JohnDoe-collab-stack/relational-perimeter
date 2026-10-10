import Tests.LocalAlignment.DocumentaryControlArithmetic
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredRealization

/-! Paid list assembly and work arithmetic. The counters are outputs of these
operations, not an after-the-fact traversal of a native result. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData
open Control ControlBindings EndogenousDecomposition
universe u

abbrev Actual {α : Type u} (expected : α) := {value : α // value = expected}

def appendCode {α : Type u} (left right : List α) : Code Label (Actual (left ++ right)) :=
  .step .listAppendCell (fun _ => match left with
    | [] => .done ⟨right, rfl⟩
    | head :: rest => (appendCode rest right).bind (fun tail =>
      .step .listAppendReturn (fun _ => .done ⟨head :: tail.1, congrArg (List.cons head) tail.2⟩)))

theorem append_finite {α : Type u} (left right : List α) : Finite (appendCode left right) := by
  induction left with
  | nil => exact finite_step _ _ (finite_done _)
  | cons head rest previous =>
    apply finite_step
    apply finite_bind previous
    intro tail
    exact finite_step _ _ (finite_done _)

def workCode (left right : ComparisonWork) : Code Label (Actual (left.add right)) :=
  (ControlArithmetic.addCode left.nodes right.nodes).bind (fun nodes =>
    (ControlArithmetic.addCode left.labelSteps right.labelSteps).bind (fun labels =>
      .step .masterWorkPacket (fun _ => .done
        ⟨⟨nodes.1, labels.1⟩, by
          obtain ⟨_, actual⟩ := nodes; cases actual
          obtain ⟨_, actual⟩ := labels; cases actual; rfl⟩)))

theorem work_finite (left right : ComparisonWork) : Finite (workCode left right) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded left.nodes right.nodes
    exact ⟨value, labels, trace⟩
  · intro nodes
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded left.labelSteps right.labelSteps
      exact ⟨value, labels, trace⟩
    · intro labels
      exact finite_step _ _ (finite_done _)

def consCode {α : Type} {head : α} {tail : List α}
    (producedHead : MeasuredValue head) (producedTail : MeasuredValue tail) :
    Code Label (Actual (measuredCons producedHead producedTail)) :=
  (workCode producedHead.work producedTail.work).bind (fun work =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨⟨producedHead.value :: producedTail.value,
          by rw [producedHead.valueExact, producedTail.valueExact], work.1.visit⟩,
        by obtain ⟨_, actual⟩ := work; cases actual; rfl⟩))

theorem cons_finite {α : Type} {head : α} {tail : List α}
    (producedHead : MeasuredValue head) (producedTail : MeasuredValue tail) :
    Finite (consCode producedHead producedTail) := by
  apply finite_bind (work_finite producedHead.work producedTail.work)
  intro work
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.Actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.appendCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.append_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.workCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.work_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.consCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterData.cons_finite
/- AXIOM_AUDIT_END -/
