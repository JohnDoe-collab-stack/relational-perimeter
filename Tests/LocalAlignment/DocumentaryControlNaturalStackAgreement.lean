import Tests.LocalAlignment.DocumentaryControlArithmetic
import Tests.LocalAlignment.DocumentaryControlReaderCeiling

/-! Historical arithmetic source definitions are retained exactly after only
renaming their declared/self-recursive identifiers. These are proof reference
producers; the production callbacks must never invoke them. All agreement
statements compare current positive stack code with these distinct references.
The historical producers serve only these agreement proofs. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement
open Control ControlBindings ControlMasterData ControlArithmetic ControlReaderCeiling
universe u
def historicalAddCode (left right : Nat) : Code Label (NaturalSum left right) :=
  .step .integerNaturalCell (fun _ => match right with
  | 0 => .done ⟨left, rfl⟩
  | right + 1 =>
      (historicalAddCode left right).bind (fun actual =>
        .step .integerNaturalReturn (fun _ =>
          .done ⟨actual.1 + 1, congrArg Nat.succ actual.2⟩)))
termination_by structural right

def historicalMaxCode (left right : Nat) : Code Label (Actual (max left right)) :=
  .step .integerNaturalCell (fun _ => match left, right with
    | 0, right => .done ⟨right, (maximum_zero_left right).symm⟩
    | left + 1, 0 => .done ⟨left + 1, (maximum_zero_right (left + 1)).symm⟩
    | left + 1, right + 1 => (historicalMaxCode left right).bind (fun produced =>
        .step .integerNaturalReturn (fun _ => .done
          ⟨produced.1 + 1, by rw [produced.2, maximum_succ]⟩)))
termination_by structural left

def old_add_trace (left : Nat) : (right : Nat) →
    Eval (historicalAddCode left right) (businessLabels right)
      (⟨left + right, rfl⟩ : ControlArithmetic.NaturalSum left right)
  | 0 => .step .done
  | right + 1 => relabel_trace (businessLabels_succ right).symm
      (.step ((old_add_trace left right).bind (.step .done)))
termination_by structural right => right

def old_max_trace : (left right : Nat) →
    Eval (historicalMaxCode left right) (businessLabels (min left right))
      (⟨max left right, rfl⟩ : Actual (max left right))
  | 0, right =>
      let actual : Actual (max 0 right) :=
        ⟨right, (ControlReaderCeiling.maximum_zero_left right).symm⟩
      let trace : Eval (historicalMaxCode 0 right)
          [Label.integerNaturalCell] actual := .step .done
      relabel_trace
        ((congrArg businessLabels (minimum_zero_left right)).trans businessLabels_zero).symm
        (canonical_trace actual trace)
  | left + 1, 0 =>
      let actual : Actual (max (left + 1) 0) :=
        ⟨left + 1, (ControlReaderCeiling.maximum_zero_right (left + 1)).symm⟩
      let trace : Eval (historicalMaxCode (left + 1) 0)
          [Label.integerNaturalCell] actual := .step .done
      relabel_trace
        ((congrArg businessLabels (minimum_zero_right (left + 1))).trans businessLabels_zero).symm
        (canonical_trace actual trace)
  | left + 1, right + 1 =>
      let actual : Actual (max (left + 1) (right + 1)) :=
        ⟨max left right + 1, (ControlReaderCeiling.maximum_succ left right).symm⟩
      let trace : Eval (historicalMaxCode (left + 1) (right + 1))
          (Label.integerNaturalCell :: (businessLabels (min left right) ++ [Label.integerNaturalReturn]))
          actual := .step ((old_max_trace left right).bind (.step .done))
      relabel_trace
        ((congrArg businessLabels (minimum_succ left right)).trans
          (businessLabels_succ (min left right))).symm
        (canonical_trace actual trace)
termination_by structural left _right => left

theorem same_business_observation {Value : Type u} {first second : Code Label Value}
    {labels : List Label} {value : Value} (original : Eval first labels value)
    (candidate : Eval second labels value) (fuel : Nat) :
    runCtl fuel second = runCtl fuel first := by
  cases Nat.decLe labels.length fuel with
  | isTrue enough =>
      rw [ctl_complete candidate fuel enough, ctl_complete original fuel enough]
  | isFalse notEnough =>
      have short := Nat.lt_of_not_ge notEnough
      rw [fuel_short candidate fuel short, fuel_short original fuel short]

theorem add_agreement (left right fuel : Nat) :
    runCtl fuel (ControlArithmetic.addCode left right) = runCtl fuel (historicalAddCode left right) :=
  same_business_observation (old_add_trace left right) (ControlArithmetic.add_trace left right) fuel

theorem max_agreement (left right fuel : Nat) :
    runCtl fuel (ControlReaderCeiling.maxCode left right) = runCtl fuel (historicalMaxCode left right) :=
  same_business_observation (old_max_trace left right) (ControlReaderCeiling.max_trace left right) fuel

end ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.historicalAddCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.historicalMaxCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.old_add_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.old_max_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.same_business_observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.add_agreement
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNaturalStackAgreement.max_agreement
/- AXIOM_AUDIT_END -/
