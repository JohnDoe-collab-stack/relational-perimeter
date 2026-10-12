import Tests.LocalAlignment.DocumentaryControlFrontierCeilingComposition

/-! The routing code actually retained by normalization is evaluated once.
Each node forms its original preservation and its executors together from the
actual child payloads. The bound traverses syntax, never native evaluation. -/
set_option genInjectivity false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingEvaluation
open SAT Control ControlBindings ControlMasterData ControlFrontierCeilingApplication

def code (formula : Cnf) (selected : Var)
    {source target : List (GeneratedStructuralBranchContext formula)}
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) :
    Code Label (Formed selected route.eval) :=
  .step .frontierEvaluationCell (fun _ => match route with
    | .identity source =>
      (identityCode formula selected source).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual))
    | .swap =>
      (swapCode formula selected).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual))
    | .absorbFirst relation =>
      (absorbFirstCode selected relation).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual))
    | .absorbSecond relation =>
      (absorbSecondCode selected relation).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual))
    | .prepend head child =>
      (code formula selected child).bind (fun received =>
        (prependCode (head := head) received.1).bind (fun actual =>
          .step .frontierEvaluationPacket (fun _ => .done ⟨actual.1, by
            exact actual.2.trans (congrArg (AcceptedFrontierPreservation.prepend (head := head)) received.2)⟩)))
    | .compose left right =>
      (code formula selected left).bind (fun first =>
        (code formula selected right).bind (fun second =>
          (transCode first.1 second.1).bind (fun actual =>
            .step .frontierEvaluationPacket (fun _ => .done ⟨actual.1, by
              exact actual.2.trans
                ((congrArg (fun value => value.trans second.1.original.preservation) first.2).trans
                  (congrArg (AcceptedFrontierPreservation.trans left.eval) second.2))⟩)))))
termination_by structural route

theorem finite (formula : Cnf) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) →
    Finite (code formula selected route)
  | _, _, .identity source => by
      rw [code]; apply finite_step; apply finite_bind (identity_finite formula selected source); intro actual
      exact finite_step _ _ (finite_done _)
  | _, _, .swap => by
      rw [code]; apply finite_step; apply finite_bind (swap_finite formula selected); intro actual
      exact finite_step _ _ (finite_done _)
  | _, _, .absorbFirst relation => by
      rw [code]; apply finite_step; apply finite_bind (absorb_first_finite selected relation); intro actual
      exact finite_step _ _ (finite_done _)
  | _, _, .absorbSecond relation => by
      rw [code]; apply finite_step; apply finite_bind (absorb_second_finite selected relation); intro actual
      exact finite_step _ _ (finite_done _)
  | _, _, .prepend head child => by
      rw [code]; apply finite_step; apply finite_bind (finite formula selected child); intro received
      apply finite_bind (prepend_finite (head := head) received.1); intro actual
      exact finite_step _ _ (finite_done _)
  | _, _, .compose left right => by
      rw [code]; apply finite_step; apply finite_bind (finite formula selected left); intro first
      apply finite_bind (finite formula selected right); intro second
      apply finite_bind (trans_finite first.1 second.1); intro actual
      exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingEvaluation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingEvaluation.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingEvaluation.finite
/- AXIOM_AUDIT_END -/
