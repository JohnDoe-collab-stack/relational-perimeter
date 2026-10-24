import RelationalPerimeter.Agents.Neural.LearnedRuntimeAdapter

/-!
# Future divergence inside the learned operational contract

The earlier finite counterfactual remains useful evidence, but it lived beside
the generic checked runtime.  This module closes that gap.  Both learned
candidates are indexed by the exact generic initial agent.  Their current
tables and their future outcomes are calculated by the same pure serialized
artifact interpreter.  The aligned future is additionally identified with the
future contract carried by the successor actually installed by `submitUpdate`.
The bypass future uses that same target contract counterfactually, while the
same closed runtime call rejects the bypass before any successor exists.

Admission and normative satisfaction remain distinct: the future contract
records whether a request is admitted, whereas `learnedFutureNormSatisfied`
checks the authorization-gated output requirement on the resulting outcome.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

/-! ## Exact candidates at the checked generic source -/

/-- A learned candidate at the exact initial agent produced by the generic
checker.  The source equality and admitted intent are positive data; neither
can be supplied after replacing the initial agent. -/
structure LearnedRuntimeCandidateAtInitial where
  private mk ::
  candidate : IndependentLearnedUpdateCandidate
  sourceExact :
    candidate.sourceArtifact = learnedInitialCheckedAgent.artifact.source
  admittedIntent : AdmittedIndependentLearnedIntent candidate.intent

def learnedAlignedCandidateAtInitial : LearnedRuntimeCandidateAtInitial :=
  .mk alignedUpdate rfl .preserveAuthorizedBehavior

def learnedBypassCandidateAtInitial : LearnedRuntimeCandidateAtInitial :=
  .mk bypassUpdate rfl .preserveAuthorizedBehavior

/-- Current behavior is read by executing the candidate's exact serialized
target.  No table is stored in the candidate or in the witness. -/
def learnedRuntimeCurrentTable
    (candidate : LearnedRuntimeCandidateAtInitial) :
    List (List Activation) :=
  learnedRuntimeDeclaredCurrentDomain.map
    (executeSerializedArtifact candidate.candidate.targetArtifact)

theorem learnedAlignedBypass_currentTable_exact :
    learnedRuntimeCurrentTable learnedAlignedCandidateAtInitial =
      learnedRuntimeCurrentTable learnedBypassCandidateAtInitial := by
  rfl

/-- The precise class of current-only verifiers used here: their result
factors exclusively through the complete declared current table. -/
structure LearnedRuntimeCurrentVerifier (Verdict : Type) where
  verdict : List (List Activation) -> Verdict

def EveryLearnedRuntimeCurrentVerifierAgrees : Prop :=
  forall (Verdict : Type) (verifier : LearnedRuntimeCurrentVerifier Verdict),
    verifier.verdict
        (learnedRuntimeCurrentTable learnedAlignedCandidateAtInitial) =
      verifier.verdict
        (learnedRuntimeCurrentTable learnedBypassCandidateAtInitial)

theorem everyLearnedRuntimeCurrentVerifierAgrees :
    EveryLearnedRuntimeCurrentVerifierAgrees := by
  intro Verdict verifier
  rw [learnedAlignedBypass_currentTable_exact]

/-! ## Outcomes of the exact proposed operational contract -/

abbrev LearnedOperationalFutureOutcome :=
  Outcome IndependentLearnedFutureEvent IndependentLearnedFutureObservation

def learnedOperationalCounterfactualRequests :
    List IndependentLearnedFutureInput :=
  [{ input := independentLearnedCounterfactualInput }]

def learnedOperationalCounterfactualRequirementRequests :
    List IndependentLearnedRequirementInput :=
  [independentLearnedCounterfactualInput.toRequirementInput]

theorem learnedOperationalCounterfactualRequests_nonempty :
    learnedOperationalCounterfactualRequests ≠ [] := by
  intro impossible
  cases impossible

def learnedCandidateFutureSource
    (candidate : LearnedRuntimeCandidateAtInitial) :
    LearnedAlignedOperationalContract.FutureSource :=
  { network := candidate.candidate.targetArtifact }

/-- Both proposed successors are interpreted by the exact future contract of
the aligned target contract.  This is a pure calculation and installs no
candidate. -/
def learnedCandidateOperationalFuture
    (candidate : LearnedRuntimeCandidateAtInitial)
    (requests : List IndependentLearnedFutureInput) :
    LearnedOperationalFutureOutcome :=
  LearnedAlignedOperationalContract.futureContract.outcome
    (learnedCandidateFutureSource candidate) requests

/-- Extract, without changing the contract semantics, the sequence of event
outputs calculated along an outcome. -/
def learnedOperationalFutureOutputs :
    LearnedOperationalFutureOutcome -> List (List Activation)
  | .stop _ => []
  | .step _ _ event tail =>
      event.outputs :: learnedOperationalFutureOutputs tail

theorem learnedCandidateOperationalFuture_outputs_are_pure
    (candidate : LearnedRuntimeCandidateAtInitial)
    (requests : List IndependentLearnedFutureInput) :
    learnedOperationalFutureOutputs
        (learnedCandidateOperationalFuture candidate requests) =
      requests.map (fun request =>
        executeSerializedArtifact candidate.candidate.targetArtifact
          request.input) := by
  induction requests with
  | nil => rfl
  | cons request rest inductionHypothesis =>
      simp only [learnedCandidateOperationalFuture,
        LearnedAlignedOperationalContract, learnedOperationalContract,
        independentLearnedFutureContract, FutureContract.outcome,
        learnedOperationalFutureOutputs, List.map_cons]
      exact congrArg
        (fun tail =>
          executeSerializedArtifact candidate.candidate.targetArtifact
              request.input :: tail)
        inductionHypothesis

/-- The source of the installed aligned runtime is the exact aligned candidate
artifact, not a separately supplied future source. -/
theorem learnedAlignedRuntime_futureSource_exact :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedCertifiedRuntime.current.state =
      learnedCandidateFutureSource learnedAlignedCandidateAtInitial := by
  rw [learnedAlignedRuntime_state_exact]
  rfl

def learnedAlignedInstalledOperationalFuture
    (requests : List IndependentLearnedFutureInput) :
    LearnedOperationalFutureOutcome :=
  LearnedAlignedOperationalContract.futureContract.outcome
    (LearnedAlignedOperationalContract.futureSourceOfState
      learnedAlignedCertifiedRuntime.current.state) requests

/-- The same future is present in the exact covered-future fragment installed
by the generic checker.  It is not reconstructed from a parallel candidate
certificate. -/
def learnedAlignedInstalledCoveredFutureWitness :
    LearnedAlignedOperationalContract.coveredFuture.Witness
      (LearnedAlignedOperationalContract.coveredFutureAt
        learnedAlignedCertifiedRuntime.current.state
        learnedOperationalCounterfactualRequirementRequests) :=
  learnedAlignedCertifiedRuntime.current.certificate.coveredFutureWitness
    learnedOperationalCounterfactualRequirementRequests

theorem learnedAlignedInstalledCoveredFutureWitness_outcome_exact :
    learnedAlignedInstalledCoveredFutureWitness.outcome =
      learnedAlignedInstalledOperationalFuture
        learnedOperationalCounterfactualRequests := by
  exact learnedAlignedInstalledCoveredFutureWitness.outcomeExact

theorem learnedAlignedInstalledFuture_is_candidateFuture
    (requests : List IndependentLearnedFutureInput) :
    learnedAlignedInstalledOperationalFuture requests =
      learnedCandidateOperationalFuture
        learnedAlignedCandidateAtInitial requests := by
  unfold learnedAlignedInstalledOperationalFuture
  unfold learnedCandidateOperationalFuture
  rw [learnedAlignedRuntime_futureSource_exact]

/-! ## Normative reading, separate from admission -/

def learnedFutureEventSatisfies
    (request : IndependentLearnedFutureInput)
    (event : IndependentLearnedFutureEvent) : Bool :=
  match event.outputs with
  | primary :: _ =>
      primary == independentLearnedExpectedPrimary request.input
  | [] => false

/-- Check the authorization-gated requirement on the outcome calculated by
the contract.  Structural mismatch or refusal is a failure.  This predicate
does not define admission and cannot install an artifact. -/
def learnedFutureNormSatisfied :
    List IndependentLearnedFutureInput ->
      LearnedOperationalFutureOutcome -> Bool
  | [] => fun outcome =>
      match outcome with
      | .stop _ => true
      | .step _ _ _ _ => false
  | request :: requests => fun outcome =>
      match outcome with
      | .stop _ => false
      | .step _ allowed event tail =>
          allowed && learnedFutureEventSatisfies request event &&
            learnedFutureNormSatisfied requests tail

theorem learnedAlignedInstalledFuture_satisfies :
    learnedFutureNormSatisfied learnedOperationalCounterfactualRequests
      (learnedAlignedInstalledOperationalFuture
        learnedOperationalCounterfactualRequests) = true := by
  unfold learnedAlignedInstalledOperationalFuture
  rw [learnedAlignedRuntime_state_exact]
  rfl

theorem learnedBypassCandidateFuture_violates :
    learnedFutureNormSatisfied learnedOperationalCounterfactualRequests
      (learnedCandidateOperationalFuture
        learnedBypassCandidateAtInitial
        learnedOperationalCounterfactualRequests) = false := by
  rfl

theorem learnedAlignedBypass_operationalFuture_different :
    learnedCandidateOperationalFuture learnedAlignedCandidateAtInitial
        learnedOperationalCounterfactualRequests ≠
      learnedCandidateOperationalFuture learnedBypassCandidateAtInitial
        learnedOperationalCounterfactualRequests := by
  intro same
  have outputsSame := congrArg learnedOperationalFutureOutputs same
  cases outputsSame

/-! ## One closed discriminating certificate -/

/-- A single package whose indices force the same generic initial agent,
meta-contract, current contract and runtime API throughout.  Current
indistinguishability, future divergence, aligned installation and bypass
rejection cannot be assembled from unrelated executions. -/
structure LearnedOperationalFutureDivergenceCertificate : Type 10 where
  private mk ::
  alignedCandidate : LearnedRuntimeCandidateAtInitial
  bypassCandidate : LearnedRuntimeCandidateAtInitial
  alignedCandidateExact :
    alignedCandidate = learnedAlignedCandidateAtInitial
  bypassCandidateExact :
    bypassCandidate = learnedBypassCandidateAtInitial
  sameAdmittedIntent :
    alignedCandidate.candidate.intent = bypassCandidate.candidate.intent
  currentTableExact :
    learnedRuntimeCurrentTable alignedCandidate =
      learnedRuntimeCurrentTable bypassCandidate
  everyCurrentVerifierAgrees : EveryLearnedRuntimeCurrentVerifierAgrees
  requests : List IndependentLearnedFutureInput
  requestsExact : requests = learnedOperationalCounterfactualRequests
  requestsNonempty : requests ≠ []
  alignedInstalledOutcome : LearnedOperationalFutureOutcome
  alignedInstalledOutcomeExact :
    alignedInstalledOutcome = learnedAlignedInstalledOperationalFuture requests
  alignedCoveredFutureWitness :
    LearnedAlignedOperationalContract.coveredFuture.Witness
      (LearnedAlignedOperationalContract.coveredFutureAt
        learnedAlignedCertifiedRuntime.current.state
        learnedOperationalCounterfactualRequirementRequests)
  alignedCoveredFutureWitnessExact :
    alignedCoveredFutureWitness = learnedAlignedInstalledCoveredFutureWitness
  alignedOutcomeComesFromCoveredFuture :
    alignedCoveredFutureWitness.outcome = alignedInstalledOutcome
  bypassCounterfactualOutcome : LearnedOperationalFutureOutcome
  bypassCounterfactualOutcomeExact :
    bypassCounterfactualOutcome =
      learnedCandidateOperationalFuture bypassCandidate requests
  alignedUsesPureSimulator :
    learnedOperationalFutureOutputs alignedInstalledOutcome =
      requests.map (fun request =>
        executeSerializedArtifact alignedCandidate.candidate.targetArtifact
          request.input)
  bypassUsesPureSimulator :
    learnedOperationalFutureOutputs bypassCounterfactualOutcome =
      requests.map (fun request =>
        executeSerializedArtifact bypassCandidate.candidate.targetArtifact
          request.input)
  alignedSatisfies :
    learnedFutureNormSatisfied requests alignedInstalledOutcome = true
  bypassViolates :
    learnedFutureNormSatisfied requests bypassCounterfactualOutcome = false
  outcomesDifferent : alignedInstalledOutcome ≠ bypassCounterfactualOutcome
  alignedInstalledByRuntime :
    submitUpdate learnedInitialCertifiedRuntime learnedAlignedRuntimeUpdate =
      .ok learnedAlignedCertifiedRuntime
  bypassRejectedBySameRuntime :
    submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency
  bypassHasNoInstalledSuccessor :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
        .ok next)

def learnedOperationalFutureDivergence :
    LearnedOperationalFutureDivergenceCertificate :=
  .mk learnedAlignedCandidateAtInitial learnedBypassCandidateAtInitial
    rfl rfl rfl learnedAlignedBypass_currentTable_exact
    everyLearnedRuntimeCurrentVerifierAgrees
    learnedOperationalCounterfactualRequests rfl
    learnedOperationalCounterfactualRequests_nonempty
    (learnedAlignedInstalledOperationalFuture
      learnedOperationalCounterfactualRequests)
    rfl
    learnedAlignedInstalledCoveredFutureWitness rfl
    learnedAlignedInstalledCoveredFutureWitness_outcome_exact
    (learnedCandidateOperationalFuture learnedBypassCandidateAtInitial
      learnedOperationalCounterfactualRequests)
    rfl
    (by
      rw [learnedAlignedInstalledFuture_is_candidateFuture]
      exact learnedCandidateOperationalFuture_outputs_are_pure
        learnedAlignedCandidateAtInitial
        learnedOperationalCounterfactualRequests)
    (learnedCandidateOperationalFuture_outputs_are_pure
      learnedBypassCandidateAtInitial
      learnedOperationalCounterfactualRequests)
    learnedAlignedInstalledFuture_satisfies
    learnedBypassCandidateFuture_violates
    (by
      intro same
      exact learnedAlignedBypass_operationalFuture_different
        ((learnedAlignedInstalledFuture_is_candidateFuture
          learnedOperationalCounterfactualRequests).symm.trans same))
    submitUpdate_learned_aligned_exact
    submitUpdate_learned_bypass_rejected
    learned_bypass_rejected_without_successor

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.LearnedRuntimeCandidateAtInitial
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedBypass_currentTable_exact
#print axioms ConstitutiveSearch.NeuralAgent.everyLearnedRuntimeCurrentVerifierAgrees
#print axioms ConstitutiveSearch.NeuralAgent.learnedOperationalCounterfactualRequests_nonempty
#print axioms ConstitutiveSearch.NeuralAgent.learnedCandidateOperationalFuture_outputs_are_pure
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_futureSource_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstalledCoveredFutureWitness_outcome_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstalledFuture_is_candidateFuture
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstalledFuture_satisfies
#print axioms ConstitutiveSearch.NeuralAgent.learnedBypassCandidateFuture_violates
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedBypass_operationalFuture_different
#print axioms ConstitutiveSearch.NeuralAgent.LearnedOperationalFutureDivergenceCertificate
#print axioms ConstitutiveSearch.NeuralAgent.learnedOperationalFutureDivergence
/- AXIOM_AUDIT_END -/
