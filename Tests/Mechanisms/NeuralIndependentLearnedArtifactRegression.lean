import RelationalPerimeter.Agents.Neural.IndependentLearnedArtifact

/-! Regression checks for the frozen independently learned artifact series. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example : independentLearnedInitialNetworkAccepted = true :=
  independentLearnedInitialNetwork_decodes

example : independentLearnedFirstSuccessorNetworkAccepted = true :=
  independentLearnedFirstSuccessorNetwork_decodes

example : independentLearnedSecondSuccessorNetworkAccepted = true :=
  independentLearnedSecondSuccessorNetwork_decodes

example : independentLearnedInitialNetwork.neurons.length = 6 := by
  rfl

example : independentLearnedFirstSuccessorNetwork.neurons.length = 7 := by
  rfl

example : independentLearnedSecondSuccessorNetwork.neurons.length = 8 := by
  rfl

example : independentLearnedInitialNetwork.outputs = [4, 3, 5] := by
  rfl

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedInitialNetwork_decodes
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFirstSuccessorNetwork_decodes
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedSecondSuccessorNetwork_decodes
/- AXIOM_AUDIT_END -/
