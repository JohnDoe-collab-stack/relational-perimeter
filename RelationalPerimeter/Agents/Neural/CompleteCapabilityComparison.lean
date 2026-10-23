import RelationalPerimeter.Agents.Neural.CapabilityComparisonAdapters
import RelationalPerimeter.Agents.Neural.AutonomousCheckerClosure

/-!
# Complete frozen capability comparison

This module completes the six typed comparison adapters with three executable
comparators required by the frozen protocol: a relational execution
comparison, an explicit reference combination, and an independent complete
recheck.  All nine methods consume one exact material package.  The reference
combination recomputes its own observations and never receives the final
constitutive verdict or a target certificate.

Translation counts denote explicit conversions from the shared frozen
material into a method interface.  They are not runtime costs and they are not
used to rank methods.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- The v10 comparison material extends, without changing, the v9 material
with the two proof-free serialized updates required by both complete checking
paths. -/
structure FrozenCompleteComparisonMaterial : Type 4 where
  private mk ::
  base : FrozenNeuralComparisonMaterial
  alignedSerializedUpdate : LearnedSerializedConstitutiveUpdate
  bypassSerializedUpdate : LearnedSerializedConstitutiveUpdate
  baseExact : base = frozenNeuralComparisonMaterial
  alignedSerializedUpdateExact :
    alignedSerializedUpdate = learnedAlignedSerializedUpdate
  bypassSerializedUpdateExact :
    bypassSerializedUpdate = learnedBypassSerializedUpdate

def frozenCompleteComparisonMaterial : FrozenCompleteComparisonMaterial :=
  .mk frozenNeuralComparisonMaterial learnedAlignedSerializedUpdate
    learnedBypassSerializedUpdate rfl rfl rfl

/-! ## Relational comparison on current and future executions -/

structure RelationalExecutionComparisonOutput
    (material : FrozenCompleteComparisonMaterial) : Type 7 where
  currentTablesEqual :
    material.base.currentTable material.base.alignedCandidate =
      material.base.currentTable material.base.bypassCandidate
  requestsNonempty : material.base.futureRequests ≠ []
  alignedOutcome : LearnedOperationalFutureOutcome
  bypassOutcome : LearnedOperationalFutureOutcome
  alignedOutcomeExact :
    alignedOutcome = learnedCandidateOperationalFuture
      material.base.alignedCandidate material.base.futureRequests
  bypassOutcomeExact :
    bypassOutcome = learnedCandidateOperationalFuture
      material.base.bypassCandidate material.base.futureRequests
  outcomesDifferent : alignedOutcome ≠ bypassOutcome
  alignedSatisfies :
    learnedFutureNormSatisfied material.base.futureRequests alignedOutcome = true
  bypassViolates :
    learnedFutureNormSatisfied material.base.futureRequests bypassOutcome = false

def runRelationalExecutionComparison
    (material : FrozenCompleteComparisonMaterial) :
    RelationalExecutionComparisonOutput material := by
  let aligned := learnedCandidateOperationalFuture
    material.base.alignedCandidate material.base.futureRequests
  let bypass := learnedCandidateOperationalFuture
    material.base.bypassCandidate material.base.futureRequests
  refine
    { currentTablesEqual := ?_
      requestsNonempty := ?_
      alignedOutcome := aligned
      bypassOutcome := bypass
      alignedOutcomeExact := rfl
      bypassOutcomeExact := rfl
      outcomesDifferent := ?_
      alignedSatisfies := ?_
      bypassViolates := ?_ }
  · unfold FrozenNeuralComparisonMaterial.currentTable
    rw [material.base.currentDomainExact, material.base.alignedCandidateExact,
      material.base.bypassCandidateExact]
    exact learnedAlignedBypass_currentTable_exact
  · rw [material.base.futureRequestsExact]
    exact learnedOperationalCounterfactualRequests_nonempty
  · dsimp only [aligned, bypass]
    rw [material.base.alignedCandidateExact,
      material.base.bypassCandidateExact,
      material.base.futureRequestsExact]
    exact learnedAlignedBypass_operationalFuture_different
  · dsimp only [aligned]
    rw [material.base.alignedCandidateExact,
      material.base.futureRequestsExact,
      ← learnedAlignedInstalledFuture_is_candidateFuture]
    exact learnedAlignedInstalledFuture_satisfies
  · dsimp only [bypass]
    rw [material.base.bypassCandidateExact,
      material.base.futureRequestsExact]
    exact learnedBypassCandidateFuture_violates

/-! ## Reference combination without constitutive-oracle access -/

inductive FrozenReferenceDecision where
  | allow
  | refuse
  deriving DecidableEq

def learnedAlignedRuntimeSubmissionDecision : FrozenReferenceDecision :=
  match submitUpdate learnedInitialCertifiedRuntime learnedAlignedRuntimeUpdate with
  | .ok _ => .allow
  | .error _ => .refuse

def learnedBypassRuntimeSubmissionDecision : FrozenReferenceDecision :=
  match submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate with
  | .ok _ => .allow
  | .error _ => .refuse

/-- The reference combination executes six checks directly: current-table
comparison, intervention dependency, mutation admission, future-contract
satisfaction, and the two pre-effect submission decisions.  None of its fields
is a final constitutive checker verdict or a supplied target certificate. -/
structure ReferenceCombinationOutput
    (material : FrozenCompleteComparisonMaterial) : Type 7 where
  currentTablesEqual : Bool
  alignedAuthorizationDependency : Bool
  bypassAuthorizationDependency : Bool
  alignedMutationDecision : FrozenShieldDecision
  bypassMutationDecision : FrozenShieldDecision
  alignedFutureSatisfied : Bool
  bypassFutureSatisfied : Bool
  alignedPreEffectDecision : FrozenReferenceDecision
  bypassPreEffectDecision : FrozenReferenceDecision
  currentTablesEqualExact : currentTablesEqual = true
  alignedAuthorizationDependencyExact :
    alignedAuthorizationDependency = true
  bypassAuthorizationDependencyExact :
    bypassAuthorizationDependency = false
  alignedMutationDecisionExact : alignedMutationDecision = .allow
  bypassMutationDecisionExact : bypassMutationDecision = .refuse
  alignedFutureSatisfiedExact : alignedFutureSatisfied = true
  bypassFutureSatisfiedExact : bypassFutureSatisfied = false
  alignedPreEffectDecisionExact : alignedPreEffectDecision = .allow
  bypassPreEffectDecisionExact : bypassPreEffectDecision = .refuse

def runReferenceCombination
    (material : FrozenCompleteComparisonMaterial) :
    ReferenceCombinationOutput material := by
  refine
    { currentTablesEqual := decide
        (material.base.currentTable material.base.alignedCandidate =
          material.base.currentTable material.base.bypassCandidate)
      alignedAuthorizationDependency :=
        primaryAuthorizationConstitutivelyConsumed
          material.base.alignedCandidate.candidate.targetArtifact
      bypassAuthorizationDependency :=
        primaryAuthorizationConstitutivelyConsumed
          material.base.bypassCandidate.candidate.targetArtifact
      alignedMutationDecision :=
        frozenShieldDecision material.base.alignedCandidate.candidate
      bypassMutationDecision :=
        frozenShieldDecision material.base.bypassCandidate.candidate
      alignedFutureSatisfied := learnedFutureNormSatisfied
        material.base.futureRequests
        (learnedCandidateOperationalFuture material.base.alignedCandidate
          material.base.futureRequests)
      bypassFutureSatisfied := learnedFutureNormSatisfied
        material.base.futureRequests
        (learnedCandidateOperationalFuture material.base.bypassCandidate
          material.base.futureRequests)
      alignedPreEffectDecision := learnedAlignedRuntimeSubmissionDecision
      bypassPreEffectDecision := learnedBypassRuntimeSubmissionDecision
      currentTablesEqualExact := ?_
      alignedAuthorizationDependencyExact := ?_
      bypassAuthorizationDependencyExact := ?_
      alignedMutationDecisionExact := ?_
      bypassMutationDecisionExact := ?_
      alignedFutureSatisfiedExact := ?_
      bypassFutureSatisfiedExact := ?_
      alignedPreEffectDecisionExact := rfl
      bypassPreEffectDecisionExact := rfl }
  · apply decide_eq_true
    unfold FrozenNeuralComparisonMaterial.currentTable
    rw [material.base.currentDomainExact, material.base.alignedCandidateExact,
      material.base.bypassCandidateExact]
    exact learnedAlignedBypass_currentTable_exact
  · rw [material.base.alignedCandidateExact]
    rfl
  · rw [material.base.bypassCandidateExact]
    rfl
  · rw [material.base.alignedCandidateExact]
    rfl
  · rw [material.base.bypassCandidateExact]
    rfl
  · rw [material.base.alignedCandidateExact,
      material.base.futureRequestsExact,
      ← learnedAlignedInstalledFuture_is_candidateFuture]
    exact learnedAlignedInstalledFuture_satisfies
  · rw [material.base.bypassCandidateExact,
      material.base.futureRequestsExact]
    exact learnedBypassCandidateFuture_violates

/-! ## Independent complete recheck -/

inductive FrozenFullRecheckDecision where
  | accept
  | reject
  deriving DecidableEq

def frozenFullRecheckDecision
    (update : LearnedSerializedConstitutiveUpdate) :
    FrozenFullRecheckDecision :=
  match checkFullUpdate learnedFullRecheckEngine update with
  | .ok _ => .accept
  | .error _ => .reject

structure IndependentFullRecheckComparisonOutput
    (material : FrozenCompleteComparisonMaterial) : Type 8 where
  alignedSerializedUpdateExact :
    material.alignedSerializedUpdate = learnedAlignedSerializedUpdate
  bypassSerializedUpdateExact :
    material.bypassSerializedUpdate = learnedBypassSerializedUpdate
  alignedDecision : FrozenFullRecheckDecision
  bypassDecision : FrozenFullRecheckDecision
  alignedDecisionExact : alignedDecision = .accept
  bypassDecisionExact : bypassDecision = .reject
  alignedAccepted : LearnedFullUpdateAccepted learnedAlignedSerializedUpdate
  bypassRejected :
    checkFullUpdate learnedFullRecheckEngine learnedBypassSerializedUpdate =
      .error .unsupportedTargetArtifact
  alignedSuccessorMatchesIncremental :
    learnedAlignedGenericIncrementalSuccess.checked.next =
      learnedAlignedFullRecheckSuccess.checked.next
  acceptedWithoutIncrementalOracle :
    checkFullUpdate learnedFullRecheckEngine learnedAlignedSerializedUpdate =
      .ok learnedAlignedFullRecheckSuccess

def runIndependentFullRecheckComparison
    (material : FrozenCompleteComparisonMaterial) :
    IndependentFullRecheckComparisonOutput material :=
    { alignedSerializedUpdateExact := material.alignedSerializedUpdateExact
      bypassSerializedUpdateExact := material.bypassSerializedUpdateExact
      alignedDecision :=
        frozenFullRecheckDecision learnedAlignedSerializedUpdate
      bypassDecision := frozenFullRecheckDecision learnedBypassSerializedUpdate
      alignedDecisionExact := rfl
      bypassDecisionExact := rfl
      alignedAccepted :=
        ⟨learnedAlignedFullRecheckSuccess,
          checkLearnedAlignedFullUpdate_exact⟩
      bypassRejected := checkLearnedBypassFullUpdate_exact
      alignedSuccessorMatchesIncremental :=
        learnedAlignedIncrementalAndFullSuccessor_exact
      acceptedWithoutIncrementalOracle := checkLearnedAlignedFullUpdate_exact }

/-! ## Explicit translation ledger -/

inductive ComparisonTranslation where
  | artifact
  | currentDomain
  | interventions
  | futureRequests
  | contracts
  | serializedUpdates
  | versionCorrespondence
  | runtimeHistory
  deriving DecidableEq

structure MethodTranslationLedger where
  methodId : String
  translations : List ComparisonTranslation
  translationCount : Nat
  countExact : translationCount = translations.length

def methodTranslationLedgers : List MethodTranslationLedger :=
  [ { methodId := "extensional-current-behavior-verification"
      translations := [.artifact, .currentDomain]
      translationCount := 2
      countExact := rfl }
  , { methodId := "fixed-network-interventional-causal-analysis"
      translations := [.artifact, .interventions]
      translationCount := 2
      countExact := rfl }
  , { methodId := "pre-execution-action-shielding"
      translations := [.artifact, .contracts]
      translationCount := 2
      countExact := rfl }
  , { methodId := "guaranteed-self-adaptive-system"
      translations := [.artifact, .contracts, .serializedUpdates]
      translationCount := 3
      countExact := rfl }
  , { methodId := "incremental-neural-verification-with-proof-reuse"
      translations := [.artifact, .contracts, .serializedUpdates,
        .versionCorrespondence]
      translationCount := 4
      countExact := rfl }
  , { methodId := "deployment-chain-certificate-propagation"
      translations := [.artifact, .contracts, .runtimeHistory]
      translationCount := 3
      countExact := rfl }
  , { methodId := "relational-execution-comparison"
      translations := [.artifact, .currentDomain, .futureRequests, .contracts]
      translationCount := 4
      countExact := rfl }
  , { methodId := "explicit-reference-combination"
      translations := [.artifact, .currentDomain, .interventions,
        .futureRequests, .contracts, .serializedUpdates]
      translationCount := 6
      countExact := rfl }
  , { methodId := "independent-complete-recheck"
      translations := [.artifact, .contracts, .serializedUpdates,
        .versionCorrespondence]
      translationCount := 4
      countExact := rfl } ]

/-- The complete comparison bundle contains the six class adapters and the
three additional executable comparisons on one exact v10 material package. -/
structure FrozenCompleteComparisonBundle : Type 10 where
  material : FrozenCompleteComparisonMaterial
  sixClasses : FrozenNeuralComparisonAdapterBundle
  sixClassesMaterialExact : sixClasses.material = material.base
  relational : RelationalExecutionComparisonOutput material
  referenceCombination : ReferenceCombinationOutput material
  fullRecheck : IndependentFullRecheckComparisonOutput material
  translations : List MethodTranslationLedger
  translationsExact : translations = methodTranslationLedgers

def frozenCompleteComparisonBundle : FrozenCompleteComparisonBundle :=
  { material := frozenCompleteComparisonMaterial
    sixClasses := frozenNeuralComparisonAdapterBundle
    sixClassesMaterialExact := rfl
    relational := runRelationalExecutionComparison
      frozenCompleteComparisonMaterial
    referenceCombination := runReferenceCombination
      frozenCompleteComparisonMaterial
    fullRecheck := runIndependentFullRecheckComparison
      frozenCompleteComparisonMaterial
    translations := methodTranslationLedgers
    translationsExact := rfl }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.FrozenCompleteComparisonMaterial
#print axioms ConstitutiveSearch.NeuralAgent.RelationalExecutionComparisonOutput
#print axioms ConstitutiveSearch.NeuralAgent.runRelationalExecutionComparison
#print axioms ConstitutiveSearch.NeuralAgent.ReferenceCombinationOutput
#print axioms ConstitutiveSearch.NeuralAgent.runReferenceCombination
#print axioms ConstitutiveSearch.NeuralAgent.IndependentFullRecheckComparisonOutput
#print axioms ConstitutiveSearch.NeuralAgent.runIndependentFullRecheckComparison
#print axioms ConstitutiveSearch.NeuralAgent.MethodTranslationLedger
#print axioms ConstitutiveSearch.NeuralAgent.methodTranslationLedgers
#print axioms ConstitutiveSearch.NeuralAgent.FrozenCompleteComparisonBundle
#print axioms ConstitutiveSearch.NeuralAgent.frozenCompleteComparisonBundle
/- AXIOM_AUDIT_END -/
