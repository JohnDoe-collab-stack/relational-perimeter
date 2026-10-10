import Tests.LocalAlignment.DocumentaryControlMeasuredTransformation

/-! Actual residual lists feed actual child contexts and their generated
witnesses. The paid traversal keeps the native tail-before-head order. -/
set_option genInjectivity false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def containsCode (target : Literal) (clause : Clause) : Code Label (Actual (containsMeasuredLiteral target clause)) :=
  .step .masterConstructionCell (fun _ =>
    match (motive := (input : Clause) → Code Label (Actual (containsMeasuredLiteral target input))) clause with
    | [] => .done ⟨⟨false, rfl, ⟨1, 0⟩⟩, rfl⟩
    | literal :: rest => (ControlMeasuredComparison.literalCode literal target).bind (fun compared =>
      match found : compared.1.result with
      | .isTrue same => .step .masterConstructionReturn (fun _ => .done
        ⟨⟨true, by rw [Clause.containsLiteral, if_pos same], compared.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := compared; cases actual; rw [containsMeasuredLiteral, found]⟩)
      | .isFalse different => (containsCode target rest).bind (fun tail =>
        (workCode compared.1.work tail.1.work).bind (fun work =>
        .step .masterConstructionReturn (fun _ => .done
          ⟨⟨tail.1.value, by rw [Clause.containsLiteral, if_neg different, tail.1.valueExact], work.1.visit⟩,
            by obtain ⟨_, actual⟩ := work; cases actual
               obtain ⟨_, actual⟩ := tail; cases actual
               obtain ⟨_, actual⟩ := compared; cases actual
               rw [containsMeasuredLiteral, found] <;> rfl⟩)))))
termination_by structural clause

theorem contains_finite (target : Literal) (clause : Clause) : Finite (containsCode target clause) := by
  induction clause with
  | nil => exact finite_step _ _ (finite_done _)
  | cons literal rest previous =>
    apply finite_step; apply finite_bind (ControlMeasuredComparison.literal_finite _ _); intro compared
    split
    · exact finite_step _ _ (finite_done _)
    · apply finite_bind previous; intro tail
      apply finite_bind (work_finite _ _); intro work
      exact finite_step _ _ (finite_done _)

def residualCode (selected : Var) (value : Bool) (formula : Cnf) :
    Code Label (Actual (constructMeasuredResidual selected value formula)) :=
  .step .masterConstructionCell (fun _ =>
    match (motive := (input : Cnf) → Code Label (Actual (constructMeasuredResidual selected value input))) formula with
    | [] => .done ⟨⟨[], rfl, ⟨1, 0⟩⟩, rfl⟩
    | clause :: rest => (residualCode selected value rest).bind (fun tail =>
      .step .masterConstructionReturn (fun _ =>
        let literal := Literal.forValue selected value
        (containsCode literal clause).bind (fun contains =>
        (workCode tail.1.work contains.1.work).bind (fun work =>
        .step .masterConstructionReturn (fun _ => match found : contains.1.value with
          | true => .done ⟨⟨tail.1.value, by
              rw [branchResidual_cons_hit clause rest selected value
                (Eq.trans contains.1.valueExact.symm found)]
              exact tail.1.valueExact, work.1.visit⟩, by
                obtain ⟨_, actual⟩ := work; cases actual
                obtain ⟨_, actual⟩ := contains; cases actual
                obtain ⟨_, actual⟩ := tail; cases actual
                rw [constructMeasuredResidual]
                split
                · rfl
                · rename_i hit
                  cases (found.symm.trans hit : true = false)⟩
          | false => .done ⟨⟨clause :: tail.1.value, by
              rw [branchResidual_cons_miss clause rest selected value
                (Eq.trans contains.1.valueExact.symm found)]
              exact congrArg (List.cons clause) tail.1.valueExact, work.1.visit⟩, by
                obtain ⟨_, actual⟩ := work; cases actual
                obtain ⟨_, actual⟩ := contains; cases actual
                obtain ⟨_, actual⟩ := tail; cases actual
                rw [constructMeasuredResidual]
                split
                · rename_i hit
                  cases (found.symm.trans hit : false = true)
                · rfl⟩))))))
termination_by structural formula

theorem residual_finite (selected : Var) (value : Bool) (formula : Cnf) :
    Finite (residualCode selected value formula) := by
  induction formula with
  | nil => exact finite_step _ _ (finite_done _)
  | cons clause rest previous =>
    apply finite_step; apply finite_bind previous; intro tail
    apply finite_step; apply finite_bind (contains_finite _ _); intro contains
    apply finite_bind (work_finite _ _); intro work
    apply finite_step; split <;> exact finite_done _

def childDataCode {root : Cnf} (parent : GeneratedStructuralBranchContext root)
    (selected : Var) (value : Bool) (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (residual : MeasuredValue (branchResidual parent.context.formula selected value)) :
    Code Label (Actual (childFromMeasuredResidual parent selected value fresh residual)) :=
  .step .formationValues (fun _ =>
    let context : StructuralBranchContext := ⟨residual.value, ⟨selected, value⟩ :: parent.context.decisions⟩
    have same : context = structuralChildContext parent.context selected value := by
      change StructuralBranchContext.mk residual.value _ = _
      rw [residual.valueExact]; rfl
    .step .formationWitness (fun _ =>
      let generated : StructuralGeneratedFrom root context :=
        Eq.rec (motive := fun context _ => StructuralGeneratedFrom root context)
          (.child parent.generated selected value fresh) same.symm
      .step .masterConstructionReturn (fun _ => .done ⟨⟨context, generated⟩, rfl⟩)))

theorem child_data_finite {root : Cnf} (parent : GeneratedStructuralBranchContext root)
    (selected : Var) (value : Bool) (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (residual : MeasuredValue (branchResidual parent.context.formula selected value)) :
    Finite (childDataCode parent selected value fresh residual) :=
  finite_step _ _ (finite_step _ _ (finite_step _ _ (finite_done _)))

def childCode {root : Cnf} (parent : GeneratedStructuralBranchContext root)
    (selected : Var) (value : Bool) (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    Code Label (Actual (constructMeasuredChild parent selected value fresh)) :=
  (residualCode selected value parent.context.formula).bind (fun residual =>
    (childDataCode parent selected value fresh residual.1).bind (fun child =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨⟨child.1, (Eq.trans child.2 (childFromMeasuredResidual_exact parent selected value fresh residual.1)),
          residual.1.work.visit⟩, by
        obtain ⟨_, actual⟩ := child; cases actual
        obtain ⟨_, actual⟩ := residual; cases actual; rfl⟩)))

theorem child_finite {root : Cnf} (parent : GeneratedStructuralBranchContext root)
    (selected : Var) (value : Bool) (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    Finite (childCode parent selected value fresh) := by
  apply finite_bind (residual_finite _ _ _); intro residual
  apply finite_bind (child_data_finite _ _ _ _ _); intro child
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.containsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.contains_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.residualCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.residual_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.childDataCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.child_data_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.childCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredState.child_finite
/- AXIOM_AUDIT_END -/
