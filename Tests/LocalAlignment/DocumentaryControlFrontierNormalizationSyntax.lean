import Tests.LocalAlignment.DocumentaryControlFrontierSyntax
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-! Paid syntax transformations and exact structural comparisons used by the
same global-flip relation finder. Bounds depend on received left syntax only;
they do not evaluate the finder or reconstruct an executed normalizer. -/
set_option genInjectivity false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax
open SAT Control ControlBindings ControlMasterData

def listCode {α : Type} (controlled : (left right : α) → Code Label (Decidable (left = right)))
    (left right : List α) : Code Label (Decidable (left = right)) :=
  .step .masterConstructionCell (fun _ => match left, right with
    | [], [] => .done (.isTrue rfl)
    | [], _ :: _ => .done (.isFalse (by intro same; cases same))
    | _ :: _, [] => .done (.isFalse (by intro same; cases same))
    | head :: rest, other :: others => (controlled head other).bind (fun compared => match compared with
      | .isFalse different => .step .masterConstructionReturn (fun _ =>
          .done (.isFalse (fun same => different (List.cons.inj same).1)))
      | .isTrue same => (listCode controlled rest others).bind (fun tail =>
          .step .masterConstructionReturn (fun _ => .done (match tail with
            | .isTrue tailSame => .isTrue (by cases same; cases tailSame; rfl)
            | .isFalse different => .isFalse (fun equal => different (List.cons.inj equal).2))))))

def listBound {α : Type} (headBound : α → Nat) : List α → Nat
  | [] => 1
  | head :: rest => (headBound head + (listBound headBound rest + 1)) + 1

theorem list_bounded {α : Type} (controlled : (left right : α) → Code Label (Decidable (left = right)))
    (headBound : α → Nat) (closed : ∀ left right, Within (controlled left right) (headBound left))
    (left right : List α) : Within (listCode controlled left right) (listBound headBound left) := by
  induction left generalizing right with
  | nil => cases right <;> exact within_step _ _ (within_done _)
  | cons head rest previous =>
      cases right with
      | nil =>
          apply within_step
          exact within_weaken (within_done _) (Nat.zero_le _)
      | cons other others =>
          apply within_step; apply within_bind (closed head other); intro compared
          cases compared with
          | isFalse different =>
              exact within_weaken (within_step _ _ (within_done _))
                (Nat.succ_le_succ (Nat.zero_le _))
          | isTrue same =>
              apply within_bind (previous others); intro tail
              exact within_step _ _ (within_done _)

def cnfCode (left right : Cnf) : Code Label (Decidable (left = right)) :=
  listCode (listCode ControlFrontierSyntax.literalCode) left right

def cnfBound (formula : Cnf) : Nat :=
  listBound (listBound ControlFrontierSyntax.literalBound) formula

theorem cnf_bounded (left right : Cnf) : Within (cnfCode left right) (cnfBound left) :=
  list_bounded _ _ (list_bounded _ _ ControlFrontierSyntax.literal_bounded) left right

def boolCode (left right : Bool) : Code Label (Decidable (left = right)) :=
  .step .controlInspect (fun _ => match left, right with
    | false, false => .done (.isTrue rfl)
    | true, true => .done (.isTrue rfl)
    | false, true => .done (.isFalse (fun same => Bool.noConfusion same))
    | true, false => .done (.isFalse (fun same => Bool.noConfusion same)))

theorem bool_bounded (left right : Bool) : Within (boolCode left right) 1 := by
  cases left <;> cases right <;> exact within_step _ _ (within_done _)

def decisionCode (left right : StructuralBranchDecision) : Code Label (Decidable (left = right)) :=
  (ControlPermission.equalCode left.var right.var).bind (fun compared => match compared with
    | .isFalse different => .step .masterConstructionReturn (fun _ =>
        .done (.isFalse (fun same => different (congrArg StructuralBranchDecision.var same))))
    | .isTrue labelsSame => (boolCode left.value right.value).bind (fun values =>
        .step .masterConstructionReturn (fun _ => .done (match values with
          | .isTrue valuesSame => .isTrue (by
              cases left; cases right; cases labelsSame; cases valuesSame; rfl)
          | .isFalse different => .isFalse (fun same => different (congrArg StructuralBranchDecision.value same))))))

def decisionBound (left : StructuralBranchDecision) : Nat :=
  ControlFrontierSyntax.equalBound left.var + (1 + 1)

theorem decision_bounded (left right : StructuralBranchDecision) :
    Within (decisionCode left right) (decisionBound left) := by
  apply within_bind (ControlFrontierSyntax.equal_bounded _ _); intro compared
  cases compared with
  | isFalse different =>
      exact within_weaken (within_step _ _ (within_done _)) (Nat.succ_le_succ (Nat.zero_le _))
  | isTrue same =>
      apply within_bind (bool_bounded _ _); intro values
      exact within_step _ _ (within_done _)

def historyCode (left right : List StructuralBranchDecision) : Code Label (Decidable (left = right)) :=
  listCode decisionCode left right

def historyBound (decisions : List StructuralBranchDecision) : Nat := listBound decisionBound decisions

theorem history_bounded (left right : List StructuralBranchDecision) :
    Within (historyCode left right) (historyBound left) := list_bounded _ _ decision_bounded left right

def mapCode {α β : Type} (function : α → β)
    (controlled : (input : α) → Code Label (Actual (function input))) (source : List α) :
    Code Label (Actual (source.map function)) :=
  .step .masterConstructionCell (fun _ => match source with
    | [] => .done ⟨[], rfl⟩
    | head :: rest => (controlled head).bind (fun produced =>
      (mapCode function controlled rest).bind (fun tail =>
      .step .masterConstructionReturn (fun _ => .done
        ⟨produced.1 :: tail.1, by rw [List.map_cons, produced.2, tail.2]⟩))))

theorem map_bounded {α β : Type} (function : α → β)
    (controlled : (input : α) → Code Label (Actual (function input)))
    (headBound : α → Nat) (closed : ∀ input, Within (controlled input) (headBound input)) (source : List α) :
    Within (mapCode function controlled source) (listBound headBound source) := by
  induction source with
  | nil => exact within_step _ _ (within_done _)
  | cons head rest previous =>
      apply within_step; apply within_bind (closed head); intro produced
      apply within_bind previous; intro tail
      exact within_step _ _ (within_done _)

def flipLiteralCode (selected : Var) (literal : Literal) : Code Label (Actual (Literal.flipAt selected literal)) :=
  .step .controlInspect (fun _ => match literal with
    | .positive label => (ControlPermission.equalCode label selected).bind (fun compared =>
        .step .masterConstructionReturn (fun _ => .done (match compared with
          | .isTrue same => ⟨.negative label, by rw [Literal.flipAt, if_pos same]⟩
          | .isFalse different => ⟨.positive label, by rw [Literal.flipAt, if_neg different]⟩)))
    | .negative label => (ControlPermission.equalCode label selected).bind (fun compared =>
        .step .masterConstructionReturn (fun _ => .done (match compared with
          | .isTrue same => ⟨.positive label, by rw [Literal.flipAt, if_pos same]⟩
          | .isFalse different => ⟨.negative label, by rw [Literal.flipAt, if_neg different]⟩))))

def flipLiteralBound : Literal → Nat
  | .positive label => (ControlFrontierSyntax.equalBound label + 1) + 1
  | .negative label => (ControlFrontierSyntax.equalBound label + 1) + 1

theorem flip_literal_bounded (selected : Var) (literal : Literal) :
    Within (flipLiteralCode selected literal) (flipLiteralBound literal) := by
  cases literal <;> apply within_step <;> apply within_bind (ControlFrontierSyntax.equal_bounded _ _) <;>
    intro compared <;> exact within_step _ _ (within_done _)

theorem clause_map_flip (selected : Var) (source : Clause) :
    source.map (Literal.flipAt selected) = Clause.flipAt selected source := by
  induction source with
  | nil => rfl
  | cons head rest previous => exact congrArg (List.cons (Literal.flipAt selected head)) previous

def flipClauseCode (selected : Var) (source : Clause) : Code Label (Actual (Clause.flipAt selected source)) :=
  (mapCode (Literal.flipAt selected) (flipLiteralCode selected) source).bind (fun actual =>
    .done ⟨actual.1, actual.2.trans (clause_map_flip selected source)⟩)

def flipClauseBound (source : Clause) : Nat := listBound flipLiteralBound source

theorem flip_clause_bounded (selected : Var) (source : Clause) :
    Within (flipClauseCode selected source) (flipClauseBound source) := by
  simpa only [Nat.add_zero, flipClauseCode, flipClauseBound] using
    (within_bind (more := 0) (map_bounded _ _ _ (flip_literal_bounded selected) source)
      (fun actual => within_done (⟨actual.1, actual.2.trans (clause_map_flip selected source)⟩ :
        Actual (Clause.flipAt selected source))))

theorem cnf_map_flip (selected : Var) (source : Cnf) :
    source.map (Clause.flipAt selected) = Cnf.flipAt selected source := by
  induction source with
  | nil => rfl
  | cons head rest previous => exact congrArg (List.cons (Clause.flipAt selected head)) previous

def flipCnfCode (selected : Var) (source : Cnf) : Code Label (Actual (Cnf.flipAt selected source)) :=
  (mapCode (Clause.flipAt selected) (flipClauseCode selected) source).bind (fun actual =>
    .done ⟨actual.1, actual.2.trans (cnf_map_flip selected source)⟩)

def flipCnfBound (source : Cnf) : Nat := listBound flipClauseBound source

theorem flip_cnf_bounded (selected : Var) (source : Cnf) :
    Within (flipCnfCode selected source) (flipCnfBound source) := by
  simpa only [Nat.add_zero, flipCnfCode, flipCnfBound] using
    (within_bind (more := 0) (map_bounded _ _ _ (flip_clause_bounded selected) source)
      (fun actual => within_done (⟨actual.1, actual.2.trans (cnf_map_flip selected source)⟩ :
        Actual (Cnf.flipAt selected source))))

def flipDecisionCode (selected : Var) (decision : StructuralBranchDecision) :
    Code Label (Actual (StructuralBranchDecision.flipAt selected decision)) :=
  (ControlPermission.equalCode decision.var selected).bind (fun compared =>
    .step .masterConstructionReturn (fun _ => .done (match compared with
      | .isTrue same => ⟨⟨decision.var, !decision.value⟩, by rw [StructuralBranchDecision.flipAt, if_pos same]⟩
      | .isFalse different => ⟨decision, by rw [StructuralBranchDecision.flipAt, if_neg different]⟩)))

def flipDecisionBound (decision : StructuralBranchDecision) : Nat :=
  ControlFrontierSyntax.equalBound decision.var + 1

theorem flip_decision_bounded (selected : Var) (decision : StructuralBranchDecision) :
    Within (flipDecisionCode selected decision) (flipDecisionBound decision) := by
  apply within_bind (ControlFrontierSyntax.equal_bounded _ _); intro compared
  exact within_step _ _ (within_done _)

theorem history_map_flip (selected : Var) (source : List StructuralBranchDecision) :
    source.map (StructuralBranchDecision.flipAt selected) = flipStructuralDecisionsAt selected source := by
  induction source with
  | nil => rfl
  | cons head rest previous => exact congrArg (List.cons (StructuralBranchDecision.flipAt selected head)) previous

def flipHistoryCode (selected : Var) (source : List StructuralBranchDecision) :
    Code Label (Actual (flipStructuralDecisionsAt selected source)) :=
  (mapCode (StructuralBranchDecision.flipAt selected) (flipDecisionCode selected) source).bind (fun actual =>
    .done ⟨actual.1, actual.2.trans (history_map_flip selected source)⟩)

def flipHistoryBound (source : List StructuralBranchDecision) : Nat := listBound flipDecisionBound source

theorem flip_history_bounded (selected : Var) (source : List StructuralBranchDecision) :
    Within (flipHistoryCode selected source) (flipHistoryBound source) := by
  simpa only [Nat.add_zero, flipHistoryCode, flipHistoryBound] using
    (within_bind (more := 0) (map_bounded _ _ _ (flip_decision_bounded selected) source)
      (fun actual => within_done (⟨actual.1, actual.2.trans (history_map_flip selected source)⟩ :
        Actual (flipStructuralDecisionsAt selected source))))

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.listCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.listBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.list_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.cnfCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.cnfBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.cnf_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.boolCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.bool_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.decisionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.decisionBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.decision_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.historyCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.historyBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.history_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.mapCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.map_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipLiteralCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipLiteralBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flip_literal_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.clause_map_flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipClauseCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipClauseBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flip_clause_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.cnf_map_flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipCnfCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipCnfBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flip_cnf_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipDecisionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipDecisionBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flip_decision_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.history_map_flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipHistoryCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flipHistoryBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSyntax.flip_history_bounded
/- AXIOM_AUDIT_END -/
