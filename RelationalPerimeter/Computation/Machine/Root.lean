import RelationalPerimeter.Computation.Machine.MachineCertificate
import RelationalPerimeter.Computation.Machine.ConnectionSearch
import RelationalPerimeter.Computation.Machine.MemoryInvariant

/-! Public production root for configured actions and memory contracts. -/
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.all_futures_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.stageCertificate
#print axioms ConstitutiveSearch.ReconfigurableMachine.equal_present_different_futures
#print axioms ConstitutiveSearch.ConnectedFabric.failed_search_width_two
/- AXIOM_AUDIT_END -/
