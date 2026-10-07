import RelationalPerimeter.Agents.ContinuationSignatures.Production

set_option genInjectivity false
namespace Tests.ContinuationSignatureMinimality
open ConstitutiveSearch ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition ConstitutiveSearch.ContinuationSignatures
variable {state : CausalConstitutiveState} {run : CausalConstitutiveStageExecution state}

theorem real_sources_forgotten (role : RelationalConstitutiveRoleStage run) :
    leftSource role ≠ pairedRightSource role ∧
      produceRoleSignature role (freeVariable run) (leftSource role) =
        produceRoleSignature role (freeVariable run) (pairedRightSource role) :=
  ⟨paired_sources_distinct role, paired_signatures_equal role _⟩

theorem necessary_distinction (role : RelationalConstitutiveRoleStage run)
    {Memory : Type} (realization : ExactRealization (roleReadContract role (freeVariable run)) Memory) :
    realization.project (variedLeftSource role) ≠ realization.project (leftSource role) :=
  varied_cannot_be_forgotten role realization

theorem no_constantly_projected_exact_realization (role : RelationalConstitutiveRoleStage run)
    {Memory : Type} (realization : ExactRealization (roleReadContract role (freeVariable run)) Memory)
    (fixed : Memory) : ¬ (∀ source, realization.project source = fixed) := by
  intro constant
  exact necessary_distinction role realization ((constant _).trans (constant _).symm)

theorem changed_partition_on_same_carrier (role : RelationalConstitutiveRoleStage run) :
    FutureEquivalent (roleReadContract role run.selected) (variedLeftSource role) (leftSource role) ∧
      ¬ FutureEquivalent (roleReadContract role (freeVariable run)) (variedLeftSource role) (leftSource role) :=
  ⟨(produceRoleSignature_exact role _ _ _).mp (resources_change_partition role).1,
    (varied_separator role).not_equivalent⟩

theorem preserved_acceptance (role : RelationalConstitutiveRoleStage run) (source : AcceptedRoleSource role) :
    GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh)
      (producedOutput role source) := producedOutput_accepted role source

end Tests.ContinuationSignatureMinimality
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ContinuationSignatureMinimality.real_sources_forgotten
#print axioms Tests.ContinuationSignatureMinimality.necessary_distinction
#print axioms Tests.ContinuationSignatureMinimality.no_constantly_projected_exact_realization
#print axioms Tests.ContinuationSignatureMinimality.changed_partition_on_same_carrier
#print axioms Tests.ContinuationSignatureMinimality.preserved_acceptance
/- AXIOM_AUDIT_END -/
