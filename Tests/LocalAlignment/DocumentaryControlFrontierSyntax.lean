import Tests.LocalAlignment.DocumentaryControlPermission
import Tests.LocalAlignment.DocumentaryControlMasterData

/-! Controlled residual syntax for the actual frontier opening. Each natural
comparison and each received clause/literal cell is visited explicitly. The
tail is produced before testing a head clause, as in the original branchSyntax.
Residual syntax and the positive CnfWeakening are returned together from the
same actual tail and check; each done/drop/keep formation is separately paid.
The bounds depend only on received syntax, not on a completed native opening. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax
open SAT Control ControlBindings ControlMasterData

def equalBound (left : Nat) : Nat := left + 1

theorem equal_labels_bound (left right : Nat) :
    (ControlPermission.equalLabels left right).length ≤ equalBound left := by
  induction left generalizing right with
  | zero => cases right <;> exact Nat.le_refl _
  | succ left previous =>
      cases right with
      | zero => exact Nat.succ_le_succ (Nat.zero_le _)
      | succ right => exact Nat.succ_le_succ (previous right)

theorem equal_bounded (left right : Nat) :
    Within (ControlPermission.equalCode left right) (equalBound left) :=
  ⟨_, _, ⟨ControlPermission.equalTrace left right⟩, equal_labels_bound left right⟩

def positiveDecision {left right : Var} : Decidable (left = right) →
    Decidable (Literal.positive left = Literal.positive right)
  | .isTrue same => .isTrue (congrArg Literal.positive same)
  | .isFalse different => .isFalse (fun same => different (Literal.positive.inj same))

def negativeDecision {left right : Var} : Decidable (left = right) →
    Decidable (Literal.negative left = Literal.negative right)
  | .isTrue same => .isTrue (congrArg Literal.negative same)
  | .isFalse different => .isFalse (fun same => different (Literal.negative.inj same))

def literalCode (left right : Literal) : Code Label (Decidable (left = right)) :=
  .step .controlInspect (fun _ => match left, right with
    | .positive left, .positive right =>
        (ControlPermission.equalCode left right).bind (fun same => .done (positiveDecision same))
    | .negative left, .negative right =>
        (ControlPermission.equalCode left right).bind (fun same => .done (negativeDecision same))
    | .positive _, .negative _ => .done (.isFalse (fun same => Literal.noConfusion same))
    | .negative _, .positive _ => .done (.isFalse (fun same => Literal.noConfusion same)))

def literalBound : Literal → Nat
  | .positive var => equalBound var + 1
  | .negative var => equalBound var + 1

theorem literal_bounded (left right : Literal) :
    Within (literalCode left right) (literalBound left) := by
  cases left <;> cases right
  · apply within_step
    simpa only [Nat.add_zero] using
      (within_bind (more := 0) (equal_bounded _ _) (fun compared => within_done (positiveDecision compared)))
  · apply within_step
    exact within_weaken (within_done _) (Nat.zero_le _)
  · apply within_step
    exact within_weaken (within_done _) (Nat.zero_le _)
  · apply within_step
    simpa only [Nat.add_zero] using
      (within_bind (more := 0) (equal_bounded _ _) (fun compared => within_done (negativeDecision compared)))

def containsCode (target : Literal) (clause : Clause) :
    Code Label (Actual (Clause.containsLiteral target clause)) :=
  .step .masterConstructionCell (fun _ => match clause with
    | [] => .done ⟨false, rfl⟩
    | literal :: rest => (literalCode literal target).bind (fun compared => match compared with
      | .isTrue same => .step .masterConstructionReturn (fun _ =>
          .done ⟨true, by rw [Clause.containsLiteral, if_pos same]⟩)
      | .isFalse different => (containsCode target rest).bind (fun tail =>
          .step .masterConstructionReturn (fun _ =>
            .done ⟨tail.1, by rw [Clause.containsLiteral, if_neg different]; exact tail.2⟩))))

def containsBound : Clause → Nat
  | [] => 1
  | literal :: rest => (literalBound literal + (containsBound rest + 1)) + 1

theorem contains_bounded (target : Literal) (clause : Clause) :
    Within (containsCode target clause) (containsBound clause) := by
  induction clause with
  | nil => exact within_step _ _ (within_done _)
  | cons literal rest previous =>
      apply within_step; apply within_bind (literal_bounded literal target)
      intro compared; cases compared with
      | isTrue same =>
          exact within_weaken (within_step _ _ (within_done _))
            (Nat.succ_le_succ (Nat.zero_le _))
      | isFalse different =>
          apply within_bind previous; intro tail
          exact within_step _ _ (within_done _)

abbrev Residual (selected : Var) (value : Bool) (formula : Cnf) :=
  Actual (Sigma.mk (branchResidual formula selected value) (branchWeakening formula selected value))

theorem residual_hit (selected : Var) (value : Bool) (clause : Clause) (rest : Cnf)
    (hit : Clause.containsLiteral (Literal.forValue selected value) clause = true) :
    Sigma.mk (branchResidual (clause :: rest) selected value) (branchWeakening (clause :: rest) selected value) =
      Sigma.mk (branchResidual rest selected value) (CnfWeakening.drop clause (branchWeakening rest selected value)) := by
  change (match Clause.containsLiteral (Literal.forValue selected value) clause with
    | true => ⟨branchResidual rest selected value, CnfWeakening.drop clause (branchWeakening rest selected value)⟩
    | false => ⟨clause :: branchResidual rest selected value, CnfWeakening.keep clause (branchWeakening rest selected value)⟩ :
      Sigma fun residual => CnfWeakening (clause :: rest) residual) = _
  rw [hit]

theorem residual_miss (selected : Var) (value : Bool) (clause : Clause) (rest : Cnf)
    (miss : Clause.containsLiteral (Literal.forValue selected value) clause = false) :
    Sigma.mk (branchResidual (clause :: rest) selected value) (branchWeakening (clause :: rest) selected value) =
      Sigma.mk (clause :: branchResidual rest selected value) (CnfWeakening.keep clause (branchWeakening rest selected value)) := by
  change (match Clause.containsLiteral (Literal.forValue selected value) clause with
    | true => ⟨branchResidual rest selected value, CnfWeakening.drop clause (branchWeakening rest selected value)⟩
    | false => ⟨clause :: branchResidual rest selected value, CnfWeakening.keep clause (branchWeakening rest selected value)⟩ :
      Sigma fun residual => CnfWeakening (clause :: rest) residual) = _
  rw [miss]

def residualCode (selected : Var) (value : Bool) (formula : Cnf) :
    Code Label (Residual selected value formula) :=
  .step .masterConstructionCell (fun _ => match formula with
    | [] => .step .formationWitness (fun _ => .done ⟨⟨[], .done⟩, rfl⟩)
    | clause :: rest => (residualCode selected value rest).bind (fun tail =>
      .step .formationValues (fun _ =>
        let literal := Literal.forValue selected value
        (containsCode literal clause).bind (fun checked =>
          .step .masterConstructionReturn (fun _ => match found : checked.1 with
            | true => .step .formationWitness (fun _ => .done
                ⟨⟨tail.1.1, .drop clause tail.1.2⟩, by
                  obtain ⟨_, tailActual⟩ := tail; cases tailActual
                  exact (residual_hit selected value clause rest (checked.2.symm.trans found)).symm⟩)
            | false => .step .formationWitness (fun _ => .done
                ⟨⟨clause :: tail.1.1, .keep clause tail.1.2⟩, by
                  obtain ⟨_, tailActual⟩ := tail; cases tailActual
                  exact (residual_miss selected value clause rest (checked.2.symm.trans found)).symm⟩))))))

def residualBound : Cnf → Nat
  | [] => 1 + 1
  | clause :: rest => (residualBound rest + ((containsBound clause + (1 + 1)) + 1)) + 1

theorem residual_bounded (selected : Var) (value : Bool) (formula : Cnf) :
    Within (residualCode selected value formula) (residualBound formula) := by
  induction formula with
  | nil => exact within_step _ _ (within_step _ _ (within_done _))
  | cons clause rest previous =>
      apply within_step; apply within_bind previous; intro tail
      apply within_step; apply within_bind (contains_bounded _ clause); intro checked
      apply within_step; split <;> exact within_step _ _ (within_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.equalBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.equal_labels_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.equal_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.positiveDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.negativeDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.literalCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.literalBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.literal_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.containsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.containsBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.contains_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.Residual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.residual_hit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.residual_miss
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.residualCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.residualBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierSyntax.residual_bounded
/- AXIOM_AUDIT_END -/
