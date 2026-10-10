import Tests.LocalAlignment.DocumentaryControlMeasuredComparison

/-! The transformations use paid comparator outputs and build their returned
lists from the actual recursive outputs. Freshness stops at the first hit. -/
set_option genInjectivity false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData ControlMeasuredComparison

def literalCode (selected : Var) (literal : Literal) : Code Label (Actual (flipMeasuredLiteral selected literal)) := .step .masterConstructionCell (fun _ => match (motive := (input : Literal) → Code Label (Actual (flipMeasuredLiteral selected input))) literal with
    | .positive label => (unaryCode label selected).bind (fun labels =>
      .step .masterConstructionReturn (fun _ => match found : labels.1.result with
        | .isTrue same => .done ⟨⟨.negative label,
            by rw [Literal.flipAt, if_pos same], labels.1.work.visit⟩,
            by obtain ⟨_, actual⟩ := labels; cases actual; rw [flipMeasuredLiteral, found]⟩
        | .isFalse different => .done ⟨⟨.positive label,
            by rw [Literal.flipAt, if_neg different], labels.1.work.visit⟩,
            by obtain ⟨_, actual⟩ := labels; cases actual; rw [flipMeasuredLiteral, found]⟩))
    | .negative label => (unaryCode label selected).bind (fun labels =>
      .step .masterConstructionReturn (fun _ => match found : labels.1.result with
        | .isTrue same => .done ⟨⟨.positive label,
            by rw [Literal.flipAt, if_pos same], labels.1.work.visit⟩,
            by obtain ⟨_, actual⟩ := labels; cases actual; rw [flipMeasuredLiteral, found]⟩
        | .isFalse different => .done ⟨⟨.negative label,
            by rw [Literal.flipAt, if_neg different], labels.1.work.visit⟩,
            by obtain ⟨_, actual⟩ := labels; cases actual; rw [flipMeasuredLiteral, found]⟩)))

theorem literal_finite (selected : Var) (literal : Literal) : Finite (literalCode selected literal) := by
  cases literal <;> apply finite_step <;> apply finite_bind (unary_finite _ _) <;>
    intro labels <;> apply finite_step <;> split <;> exact finite_done _

def clauseCode (selected : Var) (clause : Clause) : Code Label (Actual (flipMeasuredClause selected clause)) := .step .masterConstructionCell (fun _ => match (motive := (input : Clause) → Code Label (Actual (flipMeasuredClause selected input))) clause with
    | [] => .done ⟨⟨[], rfl, ⟨1, 0⟩⟩, rfl⟩
    | literal :: rest => (literalCode selected literal).bind (fun head =>
      (clauseCode selected rest).bind (fun tail =>
      (consCode head.1 tail.1).bind (fun actual => .done ⟨actual.1, by
        obtain ⟨_, exact⟩ := actual; cases exact
        obtain ⟨_, exact⟩ := tail; cases exact
        obtain ⟨_, exact⟩ := head; cases exact; rfl⟩))))

termination_by structural clause

theorem clause_finite (selected : Var) (clause : Clause) : Finite (clauseCode selected clause) := by
  induction clause with
  | nil => exact finite_step _ _ (finite_done _)
  | cons literal rest previous =>
    apply finite_step; apply finite_bind (literal_finite _ _); intro head
    apply finite_bind previous; intro tail
    apply finite_bind (cons_finite _ _); intro actual; exact finite_done _

def cnfCode (selected : Var) (formula : Cnf) : Code Label (Actual (flipMeasuredCnf selected formula)) := .step .masterConstructionCell (fun _ => match (motive := (input : Cnf) → Code Label (Actual (flipMeasuredCnf selected input))) formula with
    | [] => .done ⟨⟨[], rfl, ⟨1, 0⟩⟩, rfl⟩
    | clause :: rest => (clauseCode selected clause).bind (fun head =>
      (cnfCode selected rest).bind (fun tail =>
      (consCode head.1 tail.1).bind (fun actual => .done ⟨actual.1, by
        obtain ⟨_, exact⟩ := actual; cases exact
        obtain ⟨_, exact⟩ := tail; cases exact
        obtain ⟨_, exact⟩ := head; cases exact; rfl⟩))))

termination_by structural formula

theorem cnf_finite (selected : Var) (formula : Cnf) : Finite (cnfCode selected formula) := by
  induction formula with
  | nil => exact finite_step _ _ (finite_done _)
  | cons clause rest previous =>
    apply finite_step; apply finite_bind (clause_finite _ _); intro head
    apply finite_bind previous; intro tail
    apply finite_bind (cons_finite _ _); intro actual; exact finite_done _

def decisionCode (selected : Var) (decision : StructuralBranchDecision) :
    Code Label (Actual (flipMeasuredDecision selected decision)) :=
  (unaryCode decision.var selected).bind (fun labels =>
    .step .masterConstructionReturn (fun _ => match found : labels.1.result with
      | .isTrue same => .done ⟨⟨⟨decision.var, !decision.value⟩,
          by rw [StructuralBranchDecision.flipAt, if_pos same], labels.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := labels; cases actual; rw [flipMeasuredDecision, found]⟩
      | .isFalse different => .done ⟨⟨decision,
          by rw [StructuralBranchDecision.flipAt, if_neg different], labels.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := labels; cases actual; rw [flipMeasuredDecision, found]⟩))

theorem decision_finite (selected : Var) (decision : StructuralBranchDecision) :
    Finite (decisionCode selected decision) := by
  apply finite_bind (unary_finite _ _); intro labels
  apply finite_step; split <;> exact finite_done _

def historyCode (selected : Var) (history : List StructuralBranchDecision) :
    Code Label (Actual (flipMeasuredHistory selected history)) := .step .masterConstructionCell (fun _ => match (motive := (input : List StructuralBranchDecision) → Code Label (Actual (flipMeasuredHistory selected input))) history with
    | [] => .done ⟨⟨[], rfl, ⟨1, 0⟩⟩, rfl⟩
    | decision :: rest => (decisionCode selected decision).bind (fun head =>
      (historyCode selected rest).bind (fun tail =>
      (consCode head.1 tail.1).bind (fun actual => .done ⟨actual.1, by
        obtain ⟨_, exact⟩ := actual; cases exact
        obtain ⟨_, exact⟩ := tail; cases exact
        obtain ⟨_, exact⟩ := head; cases exact; rfl⟩))))

termination_by structural history

theorem history_finite (selected : Var) (history : List StructuralBranchDecision) :
    Finite (historyCode selected history) := by
  induction history with
  | nil => exact finite_step _ _ (finite_done _)
  | cons decision rest previous =>
    apply finite_step; apply finite_bind (decision_finite _ _); intro head
    apply finite_bind previous; intro tail
    apply finite_bind (cons_finite _ _); intro actual; exact finite_done _

def freshnessCode (selected : Var) (history : List StructuralBranchDecision) :
    Code Label (Actual (checkMeasuredFreshness selected history)) := .step .masterConstructionCell (fun _ => match (motive := (input : List StructuralBranchDecision) → Code Label (Actual (checkMeasuredFreshness selected input))) history with
    | [] => .done ⟨⟨true, rfl, ⟨1, 0⟩⟩, rfl⟩
    | decision :: rest => (unaryCode decision.var selected).bind (fun labels =>
      match found : labels.1.result with
      | .isTrue same => .step .masterConstructionReturn (fun _ => .done
        ⟨⟨false, by rw [structuralDecisionsAvoidCheck, if_pos same], labels.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := labels; cases actual; rw [checkMeasuredFreshness, found]⟩)
      | .isFalse different => (freshnessCode selected rest).bind (fun tail =>
        (workCode labels.1.work tail.1.work).bind (fun work =>
        .step .masterConstructionReturn (fun _ => .done
          ⟨⟨tail.1.value, by rw [tail.1.valueExact, structuralDecisionsAvoidCheck, if_neg different], work.1.visit⟩,
            by obtain ⟨_, actual⟩ := work; cases actual
               obtain ⟨_, actual⟩ := tail; cases actual
               obtain ⟨_, actual⟩ := labels; cases actual
               rw [checkMeasuredFreshness, found] <;> rfl⟩)))))

termination_by structural history

theorem freshness_finite (selected : Var) (history : List StructuralBranchDecision) :
    Finite (freshnessCode selected history) := by
  induction history with
  | nil => exact finite_step _ _ (finite_done _)
  | cons decision rest previous =>
    apply finite_step; apply finite_bind (unary_finite _ _); intro labels
    split
    · exact finite_step _ _ (finite_done _)
    · apply finite_bind previous; intro tail
      apply finite_bind (work_finite _ _); intro work
      exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.literalCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.literal_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.clauseCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.clause_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.cnfCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.cnf_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.decisionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.decision_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.historyCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.history_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.freshnessCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransformation.freshness_finite
/- AXIOM_AUDIT_END -/
