import Tests.LocalAlignment.DocumentaryControlMasterData

/-! Paid structural comparators return the whole original measured decision.
Unary constructor inspection, result assembly and work additions are explicit.
No native comparator is used to choose a branch in this interpreter. -/
set_option genInjectivity false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def unaryCode : (left right : Nat) → Code Label (Actual (compareUnary left right))
  | left, right => .step .naturalComparison (fun _ => match left, right with
    | 0, 0 => .done ⟨⟨.isTrue rfl, ⟨0, 1⟩⟩, rfl⟩
    | 0, _ + 1 => .done ⟨⟨.isFalse (by intro h; cases h), ⟨0, 1⟩⟩, rfl⟩
    | _ + 1, 0 => .done ⟨⟨.isFalse (by intro h; cases h), ⟨0, 1⟩⟩, rfl⟩
    | left + 1, right + 1 => (unaryCode left right).bind (fun prior =>
      .step .masterConstructionReturn (fun _ =>
        let result := match prior.1.result with
          | .isTrue same => .isTrue (congrArg Nat.succ same)
          | .isFalse different => .isFalse (fun same => different (Nat.succ.inj same))
        .done ⟨⟨result, ⟨0, prior.1.work.labelSteps + 1⟩⟩,
          by obtain ⟨_, actual⟩ := prior; cases actual; rfl⟩)))

theorem unary_finite (left right : Nat) : Finite (unaryCode left right) := by
  induction left generalizing right with
  | zero => cases right <;> exact finite_step _ _ (finite_done _)
  | succ left previous =>
    cases right with
    | zero => exact finite_step _ _ (finite_done _)
    | succ right =>
      apply finite_step; apply finite_bind (previous right); intro prior
      exact finite_step _ _ (finite_done _)

def listCode {α : Type} (compare : (left right : α) → MeasuredEquality left right)
    (controlled : (left right : α) → Code Label (Actual (compare left right))) :
    (left right : List α) → Code Label (Actual (compareMeasuredList compare left right))
  | left, right => .step .masterConstructionCell (fun _ => match left, right with
    | [], [] => .done ⟨⟨.isTrue rfl, ⟨1, 0⟩⟩, rfl⟩
    | [], _ :: _ => .done ⟨⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩, rfl⟩
    | _ :: _, [] => .done ⟨⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩, rfl⟩
    | left :: leftRest, right :: rightRest => (controlled left right).bind (fun head =>
      match found : head.1.result with
      | .isFalse different => .step .masterConstructionReturn (fun _ => .done
        ⟨⟨.isFalse (fun same => different (List.cons.inj same).1), head.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := head; cases actual
             rw [compareMeasuredList, found]⟩)
      | .isTrue same => (listCode compare controlled leftRest rightRest).bind (fun tail =>
        (workCode head.1.work tail.1.work).bind (fun work =>
        .step .masterConstructionReturn (fun _ =>
          let result := match tail.1.result with
            | .isTrue restSame => .isTrue (by cases same; cases restSame; rfl)
            | .isFalse different => .isFalse (fun equal => different (List.cons.inj equal).2)
          .done ⟨⟨result, work.1.visit⟩, by
            obtain ⟨_, actual⟩ := work; cases actual
            obtain ⟨_, actual⟩ := tail; cases actual
            obtain ⟨_, actual⟩ := head; cases actual
            rw [compareMeasuredList, found]; rfl⟩)))))

theorem list_finite {α : Type} (compare : (left right : α) → MeasuredEquality left right)
    (controlled : (left right : α) → Code Label (Actual (compare left right)))
    (closed : ∀ left right, Finite (controlled left right)) (left right : List α) :
    Finite (listCode compare controlled left right) := by
  induction left generalizing right with
  | nil => cases right <;> exact finite_step _ _ (finite_done _)
  | cons left leftRest previous =>
    cases right with
    | nil => exact finite_step _ _ (finite_done _)
    | cons right rightRest =>
      apply finite_step; apply finite_bind (closed left right); intro head
      dsimp only; split
      · exact finite_step _ _ (finite_done _)
      · apply finite_bind (previous rightRest); intro tail
        apply finite_bind (work_finite _ _); intro work
        exact finite_step _ _ (finite_done _)

def literalCode : (left right : Literal) → Code Label (Actual (compareMeasuredLiteral left right))
  | left, right => .step .masterConstructionCell (fun _ => match left, right with
    | .positive left, .positive right => (unaryCode left right).bind (fun compared =>
      .step .masterConstructionReturn (fun _ =>
        let result := match compared.1.result with
          | .isTrue same => .isTrue (congrArg Literal.positive same)
          | .isFalse different => .isFalse (by intro same; cases same; exact different rfl)
        .done ⟨⟨result, compared.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := compared; cases actual; rfl⟩))
    | .negative left, .negative right => (unaryCode left right).bind (fun compared =>
      .step .masterConstructionReturn (fun _ =>
        let result := match compared.1.result with
          | .isTrue same => .isTrue (congrArg Literal.negative same)
          | .isFalse different => .isFalse (by intro same; cases same; exact different rfl)
        .done ⟨⟨result, compared.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := compared; cases actual; rfl⟩))
    | .positive _, .negative _ => .done ⟨⟨.isFalse (by intro same; cases same), ⟨1, 0⟩⟩, rfl⟩
    | .negative _, .positive _ => .done ⟨⟨.isFalse (by intro same; cases same), ⟨1, 0⟩⟩, rfl⟩)

theorem literal_finite (left right : Literal) : Finite (literalCode left right) := by
  cases left <;> cases right <;> apply finite_step
  · apply finite_bind (unary_finite _ _); intro compared
    exact finite_step _ _ (finite_done _)
  · exact finite_done _
  · exact finite_done _
  · apply finite_bind (unary_finite _ _); intro compared
    exact finite_step _ _ (finite_done _)

def cnfCode (left right : Cnf) : Code Label (Actual (compareMeasuredCnf left right)) :=
  listCode (compareMeasuredList compareMeasuredLiteral) (listCode compareMeasuredLiteral literalCode) left right

theorem cnf_finite (left right : Cnf) : Finite (cnfCode left right) :=
  list_finite _ _ (list_finite _ _ literal_finite) left right

def boolCode : (left right : Bool) → Code Label (Actual (compareMeasuredBool left right))
  | left, right => .step .masterConstructionCell (fun _ => match left, right with
    | false, false => .done ⟨⟨.isTrue rfl, ⟨1, 0⟩⟩, rfl⟩
    | true, true => .done ⟨⟨.isTrue rfl, ⟨1, 0⟩⟩, rfl⟩
    | false, true => .done ⟨⟨.isFalse (by intro same; cases same), ⟨1, 0⟩⟩, rfl⟩
    | true, false => .done ⟨⟨.isFalse (by intro same; cases same), ⟨1, 0⟩⟩, rfl⟩)

theorem bool_finite (left right : Bool) : Finite (boolCode left right) := by
  cases left <;> cases right <;> exact finite_step _ _ (finite_done _)

def decisionCode (left right : StructuralBranchDecision) :
    Code Label (Actual (compareMeasuredDecision left right)) :=
  (unaryCode left.var right.var).bind (fun labels => match found : labels.1.result with
    | .isFalse different => .step .masterConstructionReturn (fun _ => .done
      ⟨⟨.isFalse (fun same => different (congrArg StructuralBranchDecision.var same)), labels.1.work.visit⟩,
        by obtain ⟨_, actual⟩ := labels; cases actual; rw [compareMeasuredDecision, found]⟩)
    | .isTrue labelSame => (boolCode left.value right.value).bind (fun values =>
      (workCode labels.1.work values.1.work).bind (fun work =>
      .step .masterConstructionReturn (fun _ =>
        let result := match values.1.result with
          | .isTrue valueSame => .isTrue (by
            cases left; cases right; cases labelSame; cases valueSame; rfl)
          | .isFalse different => .isFalse (fun same => different (congrArg StructuralBranchDecision.value same))
        .done ⟨⟨result, work.1.visit⟩, by
          obtain ⟨_, actual⟩ := work; cases actual
          obtain ⟨_, actual⟩ := values; cases actual
          obtain ⟨_, actual⟩ := labels; cases actual
          rw [compareMeasuredDecision, found]; rfl⟩))))

theorem decision_finite (left right : StructuralBranchDecision) : Finite (decisionCode left right) := by
  apply finite_bind (unary_finite _ _); intro labels
  dsimp only; split
  · exact finite_step _ _ (finite_done _)
  · apply finite_bind (bool_finite _ _); intro values
    apply finite_bind (work_finite _ _); intro work
    exact finite_step _ _ (finite_done _)

def historyCode (left right : List StructuralBranchDecision) : Code Label (Actual (compareMeasuredHistory left right)) :=
  listCode compareMeasuredDecision decisionCode left right

theorem history_finite (left right : List StructuralBranchDecision) : Finite (historyCode left right) :=
  list_finite _ _ decision_finite left right

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.unaryCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.unary_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.listCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.list_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.literalCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.literal_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.cnfCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.cnf_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.boolCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.bool_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.decisionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.decision_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.historyCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredComparison.history_finite
/- AXIOM_AUDIT_END -/
