import RelationalPerimeter.Agents.Neural.IncrementalChecker

namespace ConstitutiveSearch.NeuralAgent

example : publicReferenceTransitionProduction.targetState =
    publicReferenceUpdatedState :=
  publicReferenceTransitionProduction_target_exact

example : publicReferenceCheckedUpdate.execution =
    publicReferenceTransitionProduction.execution := by
  rfl

example : publicIncrementalCoreCheckedUpdate.execution =
    publicReferenceTransitionProduction.execution := by
  rfl

example : publicReferenceCheckedUpdate.next.state =
    publicReferenceTransitionProduction.targetState := by
  rfl

example : publicIncrementalCoreCheckedUpdate.next.state =
    publicReferenceTransitionProduction.targetState := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.TransitionProductionKernel
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.produceTransition
#print axioms ConstitutiveSearch.NeuralAgent.publicTransitionProductionKernel
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceTransitionProduction_target_exact
/- AXIOM_AUDIT_END -/
