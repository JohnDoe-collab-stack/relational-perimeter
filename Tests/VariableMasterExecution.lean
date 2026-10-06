import RelationalPerimeter

set_option autoImplicit false
namespace Tests.VariableMasterExecution
open ConstitutiveSearch.EndogenousDecomposition
open VariableMaster

theorem actual_variable_width :
    (step Example.origin Example.formula (Example.incoming true)).frontier.length = 1 ∧
    (step Example.origin Example.formula (Example.incoming false)).frontier.length = 2 :=
  ⟨Example.grouped_width, Example.unresolved_width⟩

theorem whole_master_preserved (count : Nat) (previous : Bool) :
    (execute count Example.origin Example.formula (Example.incoming previous)).erasure =
      MasterResources.execute count Example.origin := Example.master_unchanged count previous

theorem propagated_preservation (count : Nat) (previous : Bool) :
    ConstitutiveSearch.FrontierViable (ConstitutiveSearch.SAT.generatedStructuralBranchSystem Example.formula)
      (Example.incoming previous) ↔
    ConstitutiveSearch.FrontierViable (ConstitutiveSearch.SAT.generatedStructuralBranchSystem Example.formula)
      (execute count Example.origin Example.formula (Example.incoming previous)).finish :=
  execute_viable_iff _ _ _ _

#eval Example.widths 1
#eval Example.widths 2
#eval Example.widths 3

end Tests.VariableMasterExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.VariableMasterExecution.actual_variable_width
#print axioms Tests.VariableMasterExecution.whole_master_preserved
#print axioms Tests.VariableMasterExecution.propagated_preservation
/- AXIOM_AUDIT_END -/
