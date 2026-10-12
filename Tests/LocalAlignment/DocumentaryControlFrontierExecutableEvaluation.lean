import Tests.LocalAlignment.DocumentaryControlFrontierApplicationAbsorption

/-! The routing code actually retained by normalization is evaluated once.
Each node forms its original preservation and its executors together from the
actual child payloads. The bound traverses syntax, never native evaluation. -/
set_option genInjectivity false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableEvaluation
open SAT Control ControlBindings ControlMasterData ControlFrontierApplication

def code (formula : Cnf) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) →
    Code Label (Formed selected route.eval)
  | _, _, .identity source => .step .frontierEvaluationCell (fun _ =>
      (identityCode formula selected source).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual)))
  | _, _, .swap => .step .frontierEvaluationCell (fun _ =>
      (swapCode formula selected).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual)))
  | _, _, .absorbFirst relation => .step .frontierEvaluationCell (fun _ =>
      (absorbFirstCode selected relation).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual)))
  | _, _, .absorbSecond relation => .step .frontierEvaluationCell (fun _ =>
      (absorbSecondCode selected relation).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual)))
  | _, _, .prepend head child => .step .frontierEvaluationCell (fun _ =>
      (code formula selected child).bind (fun received =>
        (prependCode (head := head) received.1).bind (fun actual =>
          .step .frontierEvaluationPacket (fun _ => .done ⟨actual.1, by
            exact actual.2.trans (congrArg (AcceptedFrontierPreservation.prepend (head := head)) received.2)⟩))))
  | _, _, .compose left right => .step .frontierEvaluationCell (fun _ =>
      (code formula selected left).bind (fun first =>
        (code formula selected right).bind (fun second =>
          (transCode first.1 second.1).bind (fun actual =>
            .step .frontierEvaluationPacket (fun _ => .done ⟨actual.1, by
              exact actual.2.trans
                ((congrArg (fun value => value.trans second.1.preservation) first.2).trans
                  (congrArg (AcceptedFrontierPreservation.trans left.eval) second.2))⟩)))))

def bound {formula : Cnf} {selected : Var} :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target → Nat
  | _, _, .identity _ => (7 + 1) + 1
  | _, _, .swap => (7 + 1) + 1
  | _, _, .absorbFirst _ => (10 + 1) + 1
  | _, _, .absorbSecond _ => (10 + 1) + 1
  | _, _, .prepend _ child => (bound child + (7 + 1)) + 1
  | _, _, .compose left right => (bound left + (bound right + (7 + 1))) + 1

theorem bounded (formula : Cnf) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) →
    Within (code formula selected route) (bound route)
  | _, _, .identity source => by
      apply within_step; apply within_bind (identity_bounded formula selected source); intro actual
      exact within_step _ _ (within_done _)
  | _, _, .swap => by
      apply within_step; apply within_bind (swap_bounded formula selected); intro actual
      exact within_step _ _ (within_done _)
  | _, _, .absorbFirst relation => by
      apply within_step; apply within_bind (absorb_first_bounded selected relation); intro actual
      exact within_step _ _ (within_done _)
  | _, _, .absorbSecond relation => by
      apply within_step; apply within_bind (absorb_second_bounded selected relation); intro actual
      exact within_step _ _ (within_done _)
  | _, _, .prepend head child => by
      apply within_step; apply within_bind (bounded formula selected child); intro received
      apply within_bind (more := 1) (prepend_bounded (head := head) received.1); intro actual
      exact within_step _ _ (within_done _)
  | _, _, .compose left right => by
      apply within_step; apply within_bind (bounded formula selected left); intro first
      apply within_bind (bounded formula selected right); intro second
      apply within_bind (trans_bounded first.1 second.1); intro actual
      exact within_step _ _ (within_done _)

theorem finite (formula : Cnf) (selected : Var)
    {source target : List (GeneratedStructuralBranchContext formula)}
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) :
    Finite (code formula selected route) := by
  obtain ⟨value, labels, trace, _⟩ := bounded formula selected route
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableEvaluation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableEvaluation.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableEvaluation.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableEvaluation.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableEvaluation.finite
/- AXIOM_AUDIT_END -/
