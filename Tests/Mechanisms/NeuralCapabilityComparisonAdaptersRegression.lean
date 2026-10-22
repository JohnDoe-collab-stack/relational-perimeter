import RelationalPerimeter.Agents.Neural.CapabilityComparisonAdapters

/-!
# Regression checks for the six frozen comparison adapters

These checks exercise each typed adapter on the one frozen material package.
They do not execute or interpret the confirmatory comparison protocol.
-/
namespace Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression
open ConstitutiveSearch.NeuralAgent

def bundle : FrozenNeuralComparisonAdapterBundle :=
  frozenNeuralComparisonAdapterBundle

theorem extensional_tables_agree :
    bundle.extensional.alignedTable = bundle.extensional.bypassTable :=
  bundle.extensional.tablesEqual

theorem interventional_candidates_separate :
    bundle.interventional.alignedAuthorizationDependency = true /\
      bundle.interventional.bypassAuthorizationDependency = false :=
  ⟨bundle.interventional.alignedDependencyExact,
    bundle.interventional.bypassDependencyExact⟩

theorem shield_allows_aligned_and_refuses_bypass :
    bundle.shielding.alignedDecision = .allow /\
      bundle.shielding.bypassDecision = .refuse :=
  ⟨bundle.shielding.alignedDecisionExact,
    bundle.shielding.bypassDecisionExact⟩

theorem self_adaptive_installs_only_aligned :
    submitUpdate learnedInitialCertifiedRuntime learnedAlignedRuntimeUpdate =
        .ok bundle.selfAdaptive.installedRuntime /\
      submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
        .error .missingConstitutiveDependency :=
  ⟨bundle.selfAdaptive.alignedSubmissionExact,
    bundle.selfAdaptive.bypassSubmissionExact⟩

theorem learned_incremental_reports_no_transport :
    bundle.incremental.transportedStructuralCount = 0 /\
      learnedAlignedTargetAnalysis.transportedStructural = [] :=
  ⟨bundle.incremental.transportedStructuralCountExact,
    bundle.incremental.noLearnedReuseClaim⟩

theorem deployment_chain_contains_one_accepted_transition :
    bundle.deployment.transitionCount = 1 :=
  bundle.deployment.transitionCountExact

end Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.bundle
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.extensional_tables_agree
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.interventional_candidates_separate
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.shield_allows_aligned_and_refuses_bypass
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.self_adaptive_installs_only_aligned
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.learned_incremental_reports_no_transport
#print axioms Tests.Mechanisms.NeuralCapabilityComparisonAdaptersRegression.deployment_chain_contains_one_accepted_transition
/- AXIOM_AUDIT_END -/
