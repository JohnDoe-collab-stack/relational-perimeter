import RelationalPerimeter.Agents.Neural.IndependentCapabilityComparison

namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    independentCompleteComparisonBundle.referenceCombination.observation =
      computeIndependentReferenceObservation
        independentCompleteComparisonBundle.material :=
  independentCompleteComparisonBundle.referenceCombination.observationExact

example :
    independentCompleteComparisonBundle.referenceCombination.observation.alignedDecision =
      IndependentReferenceDecision.allow :=
  independentCompleteComparisonBundle.referenceCombination.alignedDecisionExact

example :
    independentCompleteComparisonBundle.referenceCombination.observation.bypassDecision =
      IndependentReferenceDecision.refuse :=
  independentCompleteComparisonBundle.referenceCombination.bypassDecisionExact

example :
    observeRuntimeSubmission learnedInitialCertifiedRuntime
      learnedAlignedRuntimeUpdate = .installed := by
  rfl

example :
    observeRuntimeSubmission learnedInitialCertifiedRuntime
      learnedBypassRuntimeUpdate = .rejected := by
  rfl

example :
    observeGenericIncremental learnedAlignedSerializedUpdate = .accepted := by
  rfl

example :
    observeGenericIncremental learnedBypassSerializedUpdate = .rejected := by
  rfl

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.computeIndependentReferenceObservation
#print axioms ConstitutiveSearch.NeuralAgent.runIndependentReferenceCombination
#print axioms ConstitutiveSearch.NeuralAgent.observeRuntimeSubmission
#print axioms ConstitutiveSearch.NeuralAgent.observeGenericIncremental
#print axioms ConstitutiveSearch.NeuralAgent.independentCompleteComparisonBundle
/- AXIOM_AUDIT_END -/
