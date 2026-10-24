import RelationalPerimeter.Agents.Neural.IndependentCapabilityProbeControls

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

def p2PathText : LearnedP2PathObservation -> String
  | .accepted => "accepted"
  | .rejected => "rejected"

def recheckText : FrozenFullRecheckDecision -> String
  | .accept => "accepted"
  | .reject => "rejected"

def emitClassRows
    (bundle : IndependentCompleteComparisonBundle)
    (p6 : LearnedP6SuccessiveComparisonOutput) : IO Unit := do
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
  IO.print ",\"p2_canonical_decoder_action\":\""
  IO.print (p2PathText
    (observeLearnedP2Path decodeIndependentLearnedProposal))
  IO.print "\",\"p2_admissible_modified_decoder_action\":\""
  IO.print (p2PathText
    (observeLearnedP2Path learnedP2AdmissibleDecoder))
  IO.print "\",\"p2_forbidden_modified_decoder_action\":\""
  IO.print (p2PathText
    (observeLearnedP2Path learnedP2ModifiedDecoder))
  IO.print "\",\"p2_admissible_empty_output_changed\":"
  IO.print (boolText
    (decide (learnedP2AdmissibleDecoder [] ≠
      decodeIndependentLearnedProposal [])))
  IO.print ",\"p2_forbidden_proposals_different\":"
  IO.print (boolText
    (decide (learnedP2ModifiedProposal ≠ learnedP2CanonicalProposal)))
  IO.print ",\"p2_local_recheck_agree\":"
  IO.print (boolText (decide
    (observeLearnedP2Path decodeIndependentLearnedProposal =
        recheckLearnedP2Path decodeIndependentLearnedProposal ∧
      observeLearnedP2Path learnedP2AdmissibleDecoder =
        recheckLearnedP2Path learnedP2AdmissibleDecoder ∧
      observeLearnedP2Path learnedP2ModifiedDecoder =
        recheckLearnedP2Path learnedP2ModifiedDecoder)))
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
  IO.print "\",\"p5_accepted_contract_change\":\""
  IO.print (submissionText (observeRuntimeSubmission
    learnedPostForgettingInitialRuntime
    learnedPostForgettingExtendedRuntimeUpdate))
  IO.print "\",\"p5_rejected_contract_change\":\""
  IO.print (submissionText (observeRuntimeSubmission
    learnedPostForgettingInitialRuntime
    (LearnedPostForgettingRuntimeUpdate.changeContract
      learnedPostForgettingExecutionReceipt learnedAlignedSerializedUpdate)))
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
  IO.print ",\"p6_successive_decision\":\""
  IO.print (incrementalText p6.incrementalDecision)
  IO.print "\",\"p6_successive_transported_structural_fragments\":"
  IO.print (Nat.repr p6.transportedStructuralCount)
  IO.print ",\"p6_successive_recomputed_structural_fragments\":"
  IO.print (Nat.repr p6.recomputedStructuralCount)
  IO.print ",\"p2_canonical_consumer\":\""
  IO.print (incrementalText (observeLearnedP2Incremental .canonical))
  IO.print "\",\"p2_admissible_consumer\":\""
  IO.print (incrementalText (observeLearnedP2Incremental .admissible))
  IO.print "\",\"p2_forbidden_consumer\":\""
  IO.print (incrementalText (observeLearnedP2Incremental .forbidden))
  IO.print "\",\"p3_allowed_contract_transition\":\""
  IO.print (incrementalText (observeGenericIncremental
    learnedAlignedSerializedUpdate))
  IO.print "\",\"p3_rejected_contract_transition\":\""
  IO.print (incrementalText (observeGenericIncremental
    learnedP3RejectedContractTransitionUpdate))
  IO.print "\",\"p5_accepted_contract_change\":\""
  IO.print (incrementalText (observePostForgettingIncremental
    learnedPostForgettingExtendedChangeRequest))
  IO.print "\",\"p5_rejected_contract_change\":\""
  IO.print (incrementalText (observePostForgettingIncremental
    (.changeContract learnedAlignedSerializedUpdate)))
  IO.print "\"}\n"
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
  IO.print ",\"p4_separator_nonempty\":"
  IO.print (boolText (decide
    (learnedAlignedBypassFutureSeparator.requests ≠ [])))
  IO.print ",\"p4_incorrect_forgetting_fff_collapses\":"
  IO.print (boolText (decide
    ((learnedP4IncorrectForgetting
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)).fff =
      (learnedP4IncorrectForgetting
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial)).fff)))
  IO.print ",\"p4_separator_reveals_required_distinction\":"
  IO.print (boolText (decide
    (learnedOperationalFutureOutputs bundle.relational.alignedOutcome ≠
      learnedOperationalFutureOutputs bundle.relational.bypassOutcome)))
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
    (bundle : IndependentCompleteComparisonBundle)
    (p6 : LearnedP6SuccessiveComparisonOutput) : IO Unit := do
  IO.print "{\"method_id\":\"independent-complete-recheck\",\"translation_count\":4,\"aligned_decision\":\""
  IO.print (recheckText (frozenFullRecheckDecision
    bundle.material.alignedSerializedUpdate))
  IO.print "\",\"bypass_decision\":\""
  IO.print (recheckText (frozenFullRecheckDecision
    bundle.material.bypassSerializedUpdate))
  IO.print "\",\"p2_canonical_consumer\":\""
  IO.print (incrementalText (observeLearnedP2FullRecheck .canonical))
  IO.print "\",\"p2_admissible_consumer\":\""
  IO.print (incrementalText (observeLearnedP2FullRecheck .admissible))
  IO.print "\",\"p2_forbidden_consumer\":\""
  IO.print (incrementalText (observeLearnedP2FullRecheck .forbidden))
  IO.print "\",\"p3_allowed_contract_transition\":\""
  IO.print (incrementalText (observeIndependentFullRecheck
    learnedAlignedSerializedUpdate))
  IO.print "\",\"p3_rejected_contract_transition\":\""
  IO.print (incrementalText (observeIndependentFullRecheck
    learnedP3RejectedContractTransitionUpdate))
  IO.print "\",\"p5_accepted_contract_change\":\""
  IO.print (incrementalText (observePostForgettingFullRecheck
    learnedPostForgettingExtendedChangeRequest))
  IO.print "\",\"p5_rejected_contract_change\":\""
  IO.print (incrementalText (observePostForgettingFullRecheck
    (.changeContract learnedAlignedSerializedUpdate)))
  IO.print "\",\"p6_successive_decision\":\""
  IO.print (incrementalText p6.fullRecheckDecision)
  IO.print "\"}\n"

def run : IO Unit := do
  let bundle := independentCompleteComparisonBundle
  let p6 := runLearnedP6SuccessiveComparison
  emitClassRows bundle p6
  emitRelationalRow bundle
  emitReferenceCombinationRow bundle
  emitFullRecheckRow bundle p6

end ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison

def main (_arguments : List String) : IO Unit :=
  ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.run

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitClassRows
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.p2PathText
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitRelationalRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitReferenceCombinationRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.emitFullRecheckRow
#print axioms ConstitutiveSearch.NeuralAgent.CompiledIndependentCompleteComparison.run
#print axioms main
/- AXIOM_AUDIT_END -/
