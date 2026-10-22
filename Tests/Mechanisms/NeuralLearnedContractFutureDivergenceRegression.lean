import RelationalPerimeter.Agents.Neural.LearnedContractFutureDivergence

/-!
Regression checks for the contract-indexed future divergence.  The aligned
and bypass candidates share the exact checked source and complete current
table.  The aligned outcome is read from the future fragment installed by the
closed runtime; the bypass outcome is calculated counterfactually by that same
target contract and is rejected before any successor exists.
-/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example : learnedRuntimeCurrentTable learnedAlignedCandidateAtInitial =
    learnedRuntimeCurrentTable learnedBypassCandidateAtInitial :=
  learnedAlignedBypass_currentTable_exact

example : EveryLearnedRuntimeCurrentVerifierAgrees :=
  everyLearnedRuntimeCurrentVerifierAgrees

example : learnedOperationalCounterfactualRequests ≠ [] :=
  learnedOperationalCounterfactualRequests_nonempty

example : learnedAlignedInstalledCoveredFutureWitness.outcome =
    learnedAlignedInstalledOperationalFuture
      learnedOperationalCounterfactualRequests :=
  learnedAlignedInstalledCoveredFutureWitness_outcome_exact

example : learnedOperationalFutureOutputs
      (learnedCandidateOperationalFuture learnedAlignedCandidateAtInitial
        learnedOperationalCounterfactualRequests) =
    learnedOperationalCounterfactualRequests.map (fun request =>
      executeSerializedArtifact
        learnedAlignedCandidateAtInitial.candidate.targetArtifact
        request.input) :=
  learnedCandidateOperationalFuture_outputs_are_pure
    learnedAlignedCandidateAtInitial
    learnedOperationalCounterfactualRequests

example : learnedFutureNormSatisfied
      learnedOperationalCounterfactualRequests
      (learnedAlignedInstalledOperationalFuture
        learnedOperationalCounterfactualRequests) = true :=
  learnedAlignedInstalledFuture_satisfies

example : learnedFutureNormSatisfied
      learnedOperationalCounterfactualRequests
      (learnedCandidateOperationalFuture learnedBypassCandidateAtInitial
        learnedOperationalCounterfactualRequests) = false :=
  learnedBypassCandidateFuture_violates

example : submitUpdate learnedInitialCertifiedRuntime
      learnedBypassRuntimeUpdate =
    .error .missingConstitutiveDependency :=
  learnedOperationalFutureDivergence.bypassRejectedBySameRuntime

example : Not (Exists fun next =>
    submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
      .ok next) :=
  learnedOperationalFutureDivergence.bypassHasNoInstalledSuccessor

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedBypass_currentTable_exact
#print axioms ConstitutiveSearch.NeuralAgent.everyLearnedRuntimeCurrentVerifierAgrees
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstalledCoveredFutureWitness_outcome_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedCandidateOperationalFuture_outputs_are_pure
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstalledFuture_satisfies
#print axioms ConstitutiveSearch.NeuralAgent.learnedBypassCandidateFuture_violates
#print axioms ConstitutiveSearch.NeuralAgent.learnedOperationalFutureDivergence
/- AXIOM_AUDIT_END -/
