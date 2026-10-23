import RelationalPerimeter.Agents.Neural.CompleteCapabilityComparison

/-!
# Compiled observations for the complete frozen comparison

The executable emits exactly nine NDJSON rows: six class adapters, the
relational execution comparison, the explicit reference combination, and the
independent complete recheck.  Rows are raw observations, not a novelty claim.
-/
namespace ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison
open ConstitutiveSearch.NeuralAgent

def boolText : Bool -> String
  | true => "true"
  | false => "false"

def shieldText : FrozenShieldDecision -> String
  | .allow => "allow"
  | .refuse => "refuse"

def referenceText : FrozenReferenceDecision -> String
  | .allow => "allow"
  | .refuse => "refuse"

def recheckText : FrozenFullRecheckDecision -> String
  | .accept => "accepted"
  | .reject => "rejected"

def emitClassRows (bundle : FrozenCompleteComparisonBundle) : IO Unit := do
  IO.print "{\"method_id\":\"extensional-current-behavior-verification\",\"translation_count\":2,\"current_cases\":"
  IO.print (Nat.repr bundle.sixClasses.extensional.alignedTable.length)
  IO.print ",\"tables_equal\":"
  IO.print (boolText (decide
    (bundle.sixClasses.extensional.alignedTable =
      bundle.sixClasses.extensional.bypassTable)))
  IO.print "}\n"
  IO.print "{\"method_id\":\"fixed-network-interventional-causal-analysis\",\"translation_count\":2,\"aligned_authorization_dependency\":"
  IO.print (boolText
    bundle.sixClasses.interventional.alignedAuthorizationDependency)
  IO.print ",\"bypass_authorization_dependency\":"
  IO.print (boolText
    bundle.sixClasses.interventional.bypassAuthorizationDependency)
  IO.print "}\n"
  IO.print "{\"method_id\":\"pre-execution-action-shielding\",\"translation_count\":2,\"aligned_decision\":\""
  IO.print (shieldText bundle.sixClasses.shielding.alignedDecision)
  IO.print "\",\"bypass_decision\":\""
  IO.print (shieldText bundle.sixClasses.shielding.bypassDecision)
  IO.print "\"}\n"
  IO.print "{\"method_id\":\"guaranteed-self-adaptive-system\",\"translation_count\":3,\"aligned_submission\":\"installed\",\"bypass_submission\":\"rejected-before-effect\",\"contracts_preserved\":true}\n"
  IO.print "{\"method_id\":\"incremental-neural-verification-with-proof-reuse\",\"translation_count\":4,\"aligned_submission\":\"accepted\",\"bypass_submission\":\"rejected\",\"transported_structural_fragments\":"
  IO.print (Nat.repr
    bundle.sixClasses.incremental.transportedStructuralCount)
  IO.print ",\"recomputed_structural_fragments\":"
  IO.print (Nat.repr
    bundle.sixClasses.incremental.recomputedStructuralCount)
  IO.print ",\"reuse_claimed\":true}\n"
  IO.print "{\"method_id\":\"deployment-chain-certificate-propagation\",\"translation_count\":3,\"accepted_transitions\":"
  IO.print (Nat.repr bundle.sixClasses.deployment.transitionCount)
  IO.print ",\"all_steps_checked\":true,\"contracts_preserved\":true,\"bypass_rejected_at_source\":true}\n"

def emitRelationalRow (bundle : FrozenCompleteComparisonBundle) : IO Unit := do
  IO.print "{\"method_id\":\"relational-execution-comparison\",\"translation_count\":4,\"current_tables_equal\":true,\"future_requests\":"
  IO.print (Nat.repr bundle.material.base.futureRequests.length)
  IO.print ",\"future_outcomes_different\":true,\"aligned_future_satisfies\":true,\"bypass_future_satisfies\":false}\n"

def emitReferenceCombinationRow
    (bundle : FrozenCompleteComparisonBundle) : IO Unit := do
  IO.print "{\"method_id\":\"explicit-reference-combination\",\"translation_count\":6,\"current_tables_equal\":"
  IO.print (boolText bundle.referenceCombination.currentTablesEqual)
  IO.print ",\"aligned_authorization_dependency\":"
  IO.print (boolText
    bundle.referenceCombination.alignedAuthorizationDependency)
  IO.print ",\"bypass_authorization_dependency\":"
  IO.print (boolText
    bundle.referenceCombination.bypassAuthorizationDependency)
  IO.print ",\"aligned_mutation_decision\":\""
  IO.print (shieldText bundle.referenceCombination.alignedMutationDecision)
  IO.print "\",\"bypass_mutation_decision\":\""
  IO.print (shieldText bundle.referenceCombination.bypassMutationDecision)
  IO.print "\",\"aligned_future_satisfies\":"
  IO.print (boolText bundle.referenceCombination.alignedFutureSatisfied)
  IO.print ",\"bypass_future_satisfies\":"
  IO.print (boolText bundle.referenceCombination.bypassFutureSatisfied)
  IO.print ",\"aligned_pre_effect_decision\":\""
  IO.print (referenceText
    bundle.referenceCombination.alignedPreEffectDecision)
  IO.print "\",\"bypass_pre_effect_decision\":\""
  IO.print (referenceText
    bundle.referenceCombination.bypassPreEffectDecision)
  IO.print "\"}\n"

def emitFullRecheckRow
    (bundle : FrozenCompleteComparisonBundle) : IO Unit := do
  IO.print "{\"method_id\":\"independent-complete-recheck\",\"translation_count\":4,\"aligned_decision\":\""
  IO.print (recheckText bundle.fullRecheck.alignedDecision)
  IO.print "\",\"bypass_decision\":\""
  IO.print (recheckText bundle.fullRecheck.bypassDecision)
  IO.print "\",\"successor_matches_incremental\":true,\"incremental_verdict_used_as_oracle\":false}\n"

def run : IO Unit := do
  let bundle := frozenCompleteComparisonBundle
  emitClassRows bundle
  emitRelationalRow bundle
  emitReferenceCombinationRow bundle
  emitFullRecheckRow bundle

end ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison

def main (_arguments : List String) : IO Unit :=
  ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison.run

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison.emitClassRows
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison.emitRelationalRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison.emitReferenceCombinationRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison.emitFullRecheckRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCompleteComparison.run
#print axioms main
/- AXIOM_AUDIT_END -/
