import RelationalPerimeter.Agents.Neural.CompleteCapabilityComparison

namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    frozenCompleteComparisonBundle.material.base.currentTable
        frozenCompleteComparisonBundle.material.base.alignedCandidate =
      frozenCompleteComparisonBundle.material.base.currentTable
        frozenCompleteComparisonBundle.material.base.bypassCandidate :=
  frozenCompleteComparisonBundle.relational.currentTablesEqual

example :
    frozenCompleteComparisonBundle.relational.alignedOutcome ≠
      frozenCompleteComparisonBundle.relational.bypassOutcome :=
  frozenCompleteComparisonBundle.relational.outcomesDifferent

example :
    frozenCompleteComparisonBundle.referenceCombination.alignedMutationDecision =
      .allow :=
  frozenCompleteComparisonBundle.referenceCombination.alignedMutationDecisionExact

example :
    frozenCompleteComparisonBundle.referenceCombination.bypassMutationDecision =
      .refuse :=
  frozenCompleteComparisonBundle.referenceCombination.bypassMutationDecisionExact

example :
    frozenCompleteComparisonBundle.referenceCombination.alignedPreEffectDecision =
      .allow :=
  frozenCompleteComparisonBundle.referenceCombination.alignedPreEffectDecisionExact

example :
    frozenCompleteComparisonBundle.referenceCombination.bypassPreEffectDecision =
      .refuse :=
  frozenCompleteComparisonBundle.referenceCombination.bypassPreEffectDecisionExact

example :
    frozenCompleteComparisonBundle.fullRecheck.alignedDecision = .accept :=
  frozenCompleteComparisonBundle.fullRecheck.alignedDecisionExact

example :
    frozenCompleteComparisonBundle.fullRecheck.bypassDecision = .reject :=
  frozenCompleteComparisonBundle.fullRecheck.bypassDecisionExact

example : methodTranslationLedgers.length = 9 := by
  rfl

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.frozenCompleteComparisonBundle
#print axioms ConstitutiveSearch.NeuralAgent.runRelationalExecutionComparison
#print axioms ConstitutiveSearch.NeuralAgent.runReferenceCombination
#print axioms ConstitutiveSearch.NeuralAgent.runIndependentFullRecheckComparison
/- AXIOM_AUDIT_END -/
