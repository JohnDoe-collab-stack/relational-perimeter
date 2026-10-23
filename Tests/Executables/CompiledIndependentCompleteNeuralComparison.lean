import RelationalPerimeter.Agents.Neural.IndependentCapabilityComparison

/-!
# Compiled observations for the oracle-independent comparison

Every emitted scientific value is read from a computation performed in this
run.  Lean-only consequences are not printed as observations; their exact
declarations are listed in the separately frozen evidence ledger.
-/
namespace ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison
open ConstitutiveSearch.NeuralAgent

def boolText : Bool -> String
  | true => "true"
  | false => "false"

def shieldText : FrozenShieldDecision -> String
  | .allow => "allow"
  | .refuse => "refuse"

def referenceText : IndependentReferenceDecision -> String
  | .allow => "allow"
  | .refuse => "refuse"

def submissionText : RuntimeSubmissionObservation -> String
  | .installed => "installed"
  | .rejected => "rejected"

def incrementalText : GenericIncrementalObservation -> String
  | .accepted => "accepted"
  | .rejected => "rejected"

def recheckText : FrozenFullRecheckDecision -> String
  | .accept => "accepted"
  | .reject => "rejected"

def emitClassRows (bundle : IndependentCompleteComparisonBundle) : IO Unit := do
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
  IO.print "{\"method_id\":\"guaranteed-self-adaptive-system\",\"translation_count\":3,\"aligned_submission\":\""
  IO.print (submissionText (observeRuntimeSubmission
    learnedInitialCertifiedRuntime learnedAlignedRuntimeUpdate))
  IO.print "\",\"bypass_submission\":\""
  IO.print (submissionText (observeRuntimeSubmission
    learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate))
  IO.print "\"}\n"
  IO.print "{\"method_id\":\"incremental-neural-verification-with-proof-reuse\",\"translation_count\":4,\"aligned_submission\":\""
  IO.print (incrementalText
    (observeGenericIncremental learnedAlignedSerializedUpdate))
  IO.print "\",\"bypass_submission\":\""
  IO.print (incrementalText
    (observeGenericIncremental learnedBypassSerializedUpdate))
  IO.print "\",\"transported_structural_fragments\":"
  IO.print (Nat.repr
    bundle.sixClasses.incremental.transportedStructuralCount)
  IO.print ",\"recomputed_structural_fragments\":"
  IO.print (Nat.repr
    bundle.sixClasses.incremental.recomputedStructuralCount)
  IO.print "}\n"
  IO.print "{\"method_id\":\"deployment-chain-certificate-propagation\",\"translation_count\":3,\"accepted_transitions\":"
  IO.print (Nat.repr bundle.sixClasses.deployment.transitionCount)
  IO.print ",\"bypass_submission\":\""
  IO.print (submissionText (observeRuntimeSubmission
    learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate))
  IO.print "\"}\n"

def emitRelationalRow
    (bundle : IndependentCompleteComparisonBundle) : IO Unit := do
  IO.print "{\"method_id\":\"relational-execution-comparison\",\"translation_count\":4,\"current_tables_equal\":"
  IO.print (boolText (decide
    (bundle.material.base.currentTable bundle.material.base.alignedCandidate =
      bundle.material.base.currentTable bundle.material.base.bypassCandidate)))
  IO.print ",\"future_requests\":"
  IO.print (Nat.repr bundle.material.base.futureRequests.length)
  IO.print ",\"future_outputs_different\":"
  IO.print (boolText (decide
    (learnedOperationalFutureOutputs bundle.relational.alignedOutcome !=
      learnedOperationalFutureOutputs bundle.relational.bypassOutcome)))
  IO.print ",\"aligned_future_satisfies\":"
  IO.print (boolText (learnedFutureNormSatisfied
    bundle.material.base.futureRequests bundle.relational.alignedOutcome))
  IO.print ",\"bypass_future_satisfies\":"
  IO.print (boolText (learnedFutureNormSatisfied
    bundle.material.base.futureRequests bundle.relational.bypassOutcome))
  IO.print "}\n"

def emitReferenceCombinationRow
    (bundle : IndependentCompleteComparisonBundle) : IO Unit := do
  let observation := bundle.referenceCombination.observation
  IO.print "{\"method_id\":\"explicit-reference-combination\",\"translation_count\":6,\"current_tables_equal\":"
  IO.print (boolText observation.currentTablesEqual)
  IO.print ",\"aligned_authorization_dependency\":"
  IO.print (boolText observation.alignedAuthorizationDependency)
  IO.print ",\"bypass_authorization_dependency\":"
  IO.print (boolText observation.bypassAuthorizationDependency)
  IO.print ",\"aligned_mutation_decision\":\""
  IO.print (shieldText observation.alignedMutationDecision)
  IO.print "\",\"bypass_mutation_decision\":\""
  IO.print (shieldText observation.bypassMutationDecision)
  IO.print "\",\"aligned_future_satisfies\":"
  IO.print (boolText observation.alignedFutureSatisfied)
  IO.print ",\"bypass_future_satisfies\":"
  IO.print (boolText observation.bypassFutureSatisfied)
  IO.print ",\"aligned_decision\":\""
  IO.print (referenceText observation.alignedDecision)
  IO.print "\",\"bypass_decision\":\""
  IO.print (referenceText observation.bypassDecision)
  IO.print "\"}\n"

def emitFullRecheckRow
    (bundle : IndependentCompleteComparisonBundle) : IO Unit := do
  IO.print "{\"method_id\":\"independent-complete-recheck\",\"translation_count\":4,\"aligned_decision\":\""
  IO.print (recheckText (frozenFullRecheckDecision
    bundle.material.alignedSerializedUpdate))
  IO.print "\",\"bypass_decision\":\""
  IO.print (recheckText (frozenFullRecheckDecision
    bundle.material.bypassSerializedUpdate))
  IO.print "\"}\n"

def run : IO Unit := do
  let bundle := independentCompleteComparisonBundle
  emitClassRows bundle
  emitRelationalRow bundle
  emitReferenceCombinationRow bundle
  emitFullRecheckRow bundle

end ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison

def main (_arguments : List String) : IO Unit :=
  ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.run

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitClassRows
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitRelationalRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitReferenceCombinationRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitFullRecheckRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.run
#print axioms main
/- AXIOM_AUDIT_END -/
