import RelationalPerimeter.Agents.Neural.LearnedContractFutureDivergence

/-!
# Frozen capability-comparison adapters

The six adapters in this module consume one shared, proof-free learned
artifact family and the exact aligned/bypass update pair.  They expose only
what their declared interface computes or certifies.  In particular, an
interface boundary is not turned into a negative theorem about a method
family, and the learned incremental instance does not claim fragment reuse:
all of its target structural observations are recomputed.

This module defines the adapters but does not execute the confirmatory
comparison.  The separately versioned protocol freezes these definitions and
their compiled command before any result is produced.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- The exact material shared by every comparison adapter.  Its private
constructor prevents an adapter from silently replacing one candidate,
domain, future request, intent, or artifact while retaining the comparison
label. -/
structure FrozenNeuralComparisonMaterial : Type 4 where
  private mk ::
  sourceArtifact : SerializedNetwork
  alignedCandidate : LearnedRuntimeCandidateAtInitial
  bypassCandidate : LearnedRuntimeCandidateAtInitial
  admittedIntent : IndependentLearnedUpdateIntent
  currentDomain : List IndependentLearnedInput
  futureRequests : List IndependentLearnedFutureInput
  sourceArtifactExact : sourceArtifact = independentLearnedInitialNetwork
  alignedCandidateExact : alignedCandidate = learnedAlignedCandidateAtInitial
  bypassCandidateExact : bypassCandidate = learnedBypassCandidateAtInitial
  admittedIntentExact : admittedIntent = .preserveAuthorizedBehavior
  currentDomainExact : currentDomain = learnedRuntimeDeclaredCurrentDomain
  futureRequestsExact : futureRequests =
    learnedOperationalCounterfactualRequests

def frozenNeuralComparisonMaterial : FrozenNeuralComparisonMaterial :=
  .mk independentLearnedInitialNetwork learnedAlignedCandidateAtInitial
    learnedBypassCandidateAtInitial .preserveAuthorizedBehavior
    learnedRuntimeDeclaredCurrentDomain learnedOperationalCounterfactualRequests
    rfl rfl rfl rfl rfl rfl

/-- Reusable exactness boundary consumed by every adapter result. -/
structure ExactFrozenNeuralComparisonMaterial
    (material : FrozenNeuralComparisonMaterial) : Type 4 where
  sourceArtifactExact : material.sourceArtifact = independentLearnedInitialNetwork
  alignedCandidateExact : material.alignedCandidate =
    learnedAlignedCandidateAtInitial
  bypassCandidateExact : material.bypassCandidate =
    learnedBypassCandidateAtInitial
  admittedIntentExact : material.admittedIntent = .preserveAuthorizedBehavior
  currentDomainExact : material.currentDomain = learnedRuntimeDeclaredCurrentDomain
  futureRequestsExact : material.futureRequests =
    learnedOperationalCounterfactualRequests

def FrozenNeuralComparisonMaterial.exact
    (material : FrozenNeuralComparisonMaterial) :
    ExactFrozenNeuralComparisonMaterial material :=
  { sourceArtifactExact := material.sourceArtifactExact
    alignedCandidateExact := material.alignedCandidateExact
    bypassCandidateExact := material.bypassCandidateExact
    admittedIntentExact := material.admittedIntentExact
    currentDomainExact := material.currentDomainExact
    futureRequestsExact := material.futureRequestsExact }

def FrozenNeuralComparisonMaterial.currentTable
    (material : FrozenNeuralComparisonMaterial)
    (candidate : LearnedRuntimeCandidateAtInitial) :
    List (List Activation) :=
  material.currentDomain.map (fun input =>
    executeSerializedArtifact candidate.candidate.targetArtifact input)

/-! ## 1. Extensional current-behavior verification -/

structure ExtensionalCurrentBehaviorAdapterOutput
    (material : FrozenNeuralComparisonMaterial) : Type 5 where
  materialExact : ExactFrozenNeuralComparisonMaterial material
  alignedTable : List (List Activation)
  bypassTable : List (List Activation)
  alignedTableExact : alignedTable =
    material.currentTable material.alignedCandidate
  bypassTableExact : bypassTable =
    material.currentTable material.bypassCandidate
  tablesEqual : alignedTable = bypassTable
  everyFactoredVerifierAgrees : EveryLearnedRuntimeCurrentVerifierAgrees

def runExtensionalCurrentBehaviorAdapter
    (material : FrozenNeuralComparisonMaterial) :
    ExtensionalCurrentBehaviorAdapterOutput material := by
  refine
    { alignedTable := material.currentTable material.alignedCandidate
      materialExact := material.exact
      bypassTable := material.currentTable material.bypassCandidate
      alignedTableExact := rfl
      bypassTableExact := rfl
      tablesEqual := ?_
      everyFactoredVerifierAgrees :=
        everyLearnedRuntimeCurrentVerifierAgrees }
  unfold FrozenNeuralComparisonMaterial.currentTable
  rw [material.currentDomainExact, material.alignedCandidateExact,
    material.bypassCandidateExact]
  exact learnedAlignedBypass_currentTable_exact

/-! ## 2. Fixed-network interventional causal analysis -/

structure FixedNetworkInterventionalAdapterOutput
    (material : FrozenNeuralComparisonMaterial) : Type 5 where
  materialExact : ExactFrozenNeuralComparisonMaterial material
  alignedAuthorizationDependency : Bool
  bypassAuthorizationDependency : Bool
  alignedDependencyExact : alignedAuthorizationDependency = true
  bypassDependencyExact : bypassAuthorizationDependency = false
  alignedExecutedRole : (current : IndependentLearnedCurrentCase) ->
    CausalRole learnedDecodedAlignedArtifact.system
      current.input.toRequirementInput
      (.receivedInput learnedAlignedRequirementPort)

def runFixedNetworkInterventionalAdapter
    (material : FrozenNeuralComparisonMaterial) :
    FixedNetworkInterventionalAdapterOutput material := by
  refine
    { alignedAuthorizationDependency :=
        primaryAuthorizationConstitutivelyConsumed
          material.alignedCandidate.candidate.targetArtifact
      materialExact := material.exact
      bypassAuthorizationDependency :=
        primaryAuthorizationConstitutivelyConsumed
          material.bypassCandidate.candidate.targetArtifact
      alignedDependencyExact := ?_
      bypassDependencyExact := ?_
      alignedExecutedRole := learnedAlignedCurrentRole }
  · rw [material.alignedCandidateExact]
    rfl
  · rw [material.bypassCandidateExact]
    rfl

/-! ## 3. Pre-execution action shielding -/

inductive FrozenShieldDecision where
  | allow
  | refuse
  deriving DecidableEq

def frozenShieldDecision
    (candidate : IndependentLearnedUpdateCandidate) : FrozenShieldDecision :=
  match checkIndependentLearnedUpdate checkedIndependentLearnedInitial
      candidate with
  | .ok _ => .allow
  | .error _ => .refuse

structure PreExecutionActionShieldAdapterOutput
    (material : FrozenNeuralComparisonMaterial) : Type 5 where
  materialExact : ExactFrozenNeuralComparisonMaterial material
  alignedDecision : FrozenShieldDecision
  bypassDecision : FrozenShieldDecision
  alignedDecisionExact : alignedDecision = .allow
  bypassDecisionExact : bypassDecision = .refuse
  sameAdmittedIntent :
    material.alignedCandidate.candidate.intent =
      material.bypassCandidate.candidate.intent
  bypassCannotInstall : Not (Exists fun next =>
    submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
      .ok next)

def runPreExecutionActionShieldAdapter
    (material : FrozenNeuralComparisonMaterial) :
    PreExecutionActionShieldAdapterOutput material := by
  refine
    { alignedDecision :=
        frozenShieldDecision material.alignedCandidate.candidate
      materialExact := material.exact
      bypassDecision :=
        frozenShieldDecision material.bypassCandidate.candidate
      alignedDecisionExact := ?_
      bypassDecisionExact := ?_
      sameAdmittedIntent := ?_
      bypassCannotInstall := learned_bypass_rejected_without_successor }
  · rw [material.alignedCandidateExact]
    rfl
  · rw [material.bypassCandidateExact]
    rfl
  · rw [material.alignedCandidateExact, material.bypassCandidateExact]

/-! ## 4. Guaranteed self-adaptive system -/

structure GuaranteedSelfAdaptiveAdapterOutput
    (material : FrozenNeuralComparisonMaterial) : Type 9 where
  materialExact : ExactFrozenNeuralComparisonMaterial material
  installedRuntime : CertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent
  alignedSubmissionExact :
    submitUpdate learnedInitialCertifiedRuntime learnedAlignedRuntimeUpdate =
      .ok installedRuntime
  bypassSubmissionExact :
    submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency
  everyInstalledStepChecked : EveryRuntimeStepSatisfies installedRuntime.history
  everyInstalledStepPreservesContracts :
    EveryRuntimeStepPreservesContracts installedRuntime.history

def runGuaranteedSelfAdaptiveAdapter
    (material : FrozenNeuralComparisonMaterial) :
    GuaranteedSelfAdaptiveAdapterOutput material :=
  { installedRuntime := learnedAlignedCertifiedRuntime
    materialExact := material.exact
    alignedSubmissionExact := submitUpdate_learned_aligned_exact
    bypassSubmissionExact := submitUpdate_learned_bypass_rejected
    everyInstalledStepChecked := learnedAlignedCertifiedRuntime.checkedHistory
    everyInstalledStepPreservesContracts :=
      learnedAlignedCertifiedRuntime.preservedContracts }

/-! ## 5. Incremental neural verification with proof reuse -/

structure IncrementalProofReuseAdapterOutput
    (material : FrozenNeuralComparisonMaterial) : Type 7 where
  materialExact : ExactFrozenNeuralComparisonMaterial material
  alignedAccepted : GenericIncrementalUpdateAccepted
    learnedIncrementalCheckerEngine learnedAlignedSerializedUpdate
  bypassRejected :
    checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
        learnedBypassSerializedUpdate =
      .error .missingConstitutiveDependency
  transportedStructuralCount : Nat
  recomputedStructuralCount : Nat
  transportedStructuralCountExact : transportedStructuralCount = 0
  recomputedStructuralCountExact : recomputedStructuralCount =
    learnedAlignedTargetAnalysis.fragments.structural.observations.length
  noLearnedReuseClaim :
    learnedAlignedTargetAnalysis.transportedStructural = []

def runIncrementalProofReuseAdapter
    (material : FrozenNeuralComparisonMaterial) :
    IncrementalProofReuseAdapterOutput material :=
  { alignedAccepted := learnedGenericChecker_accepts_aligned
    materialExact := material.exact
    bypassRejected := learnedGenericChecker_rejects_bypass
    transportedStructuralCount :=
      learnedAlignedTargetAnalysis.transportedStructural.length
    recomputedStructuralCount :=
      learnedAlignedTargetAnalysis.recomputedStructural.length
    transportedStructuralCountExact := rfl
    recomputedStructuralCountExact := rfl
    noLearnedReuseClaim := rfl }

/-! ## 6. Deployment-chain certificate propagation -/

def certifiedRuntimeHistoryLength
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract} :
    CertifiedRuntimeHistory checker initial current -> Nat
  | .initial => 0
  | .submitted history _ _ _ => certifiedRuntimeHistoryLength history + 1

structure DeploymentChainPropagationAdapterOutput
    (material : FrozenNeuralComparisonMaterial) : Type 9 where
  materialExact : ExactFrozenNeuralComparisonMaterial material
  reachedRuntime : CertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent
  transitionCount : Nat
  transitionCountExact : transitionCount = 1
  checkedHistory : EveryRuntimeStepSatisfies reachedRuntime.history
  preservedContracts : EveryRuntimeStepPreservesContracts reachedRuntime.history
  exactReachability : CertifiedRuntimeReachable learnedDependentIncrementalChecker
    learnedInitialCheckedAgent reachedRuntime
  bypassRejectedAtSource :
    submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency

def runDeploymentChainPropagationAdapter
    (material : FrozenNeuralComparisonMaterial) :
    DeploymentChainPropagationAdapterOutput material :=
  { reachedRuntime := learnedAlignedCertifiedRuntime
    materialExact := material.exact
    transitionCount :=
      certifiedRuntimeHistoryLength learnedAlignedCertifiedRuntime.history
    transitionCountExact := rfl
    checkedHistory := learnedAlignedCertifiedRuntime.checkedHistory
    preservedContracts := learnedAlignedCertifiedRuntime.preservedContracts
    exactReachability := learnedAlignedCertifiedRuntime_reachable
    bypassRejectedAtSource := submitUpdate_learned_bypass_rejected }

/-- One package guarantees that all six interfaces consume the same exact
comparison material.  It is an adapter bundle, not a comparative verdict. -/
structure FrozenNeuralComparisonAdapterBundle : Type 10 where
  material : FrozenNeuralComparisonMaterial
  extensional : ExtensionalCurrentBehaviorAdapterOutput material
  interventional : FixedNetworkInterventionalAdapterOutput material
  shielding : PreExecutionActionShieldAdapterOutput material
  selfAdaptive : GuaranteedSelfAdaptiveAdapterOutput material
  incremental : IncrementalProofReuseAdapterOutput material
  deployment : DeploymentChainPropagationAdapterOutput material

def frozenNeuralComparisonAdapterBundle :
    FrozenNeuralComparisonAdapterBundle :=
  { material := frozenNeuralComparisonMaterial
    extensional := runExtensionalCurrentBehaviorAdapter
      frozenNeuralComparisonMaterial
    interventional := runFixedNetworkInterventionalAdapter
      frozenNeuralComparisonMaterial
    shielding := runPreExecutionActionShieldAdapter
      frozenNeuralComparisonMaterial
    selfAdaptive := runGuaranteedSelfAdaptiveAdapter
      frozenNeuralComparisonMaterial
    incremental := runIncrementalProofReuseAdapter
      frozenNeuralComparisonMaterial
    deployment := runDeploymentChainPropagationAdapter
      frozenNeuralComparisonMaterial }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.FrozenNeuralComparisonMaterial
#print axioms ConstitutiveSearch.NeuralAgent.ExactFrozenNeuralComparisonMaterial
#print axioms ConstitutiveSearch.NeuralAgent.ExtensionalCurrentBehaviorAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runExtensionalCurrentBehaviorAdapter
#print axioms ConstitutiveSearch.NeuralAgent.FixedNetworkInterventionalAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runFixedNetworkInterventionalAdapter
#print axioms ConstitutiveSearch.NeuralAgent.FrozenShieldDecision
#print axioms ConstitutiveSearch.NeuralAgent.PreExecutionActionShieldAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runPreExecutionActionShieldAdapter
#print axioms ConstitutiveSearch.NeuralAgent.GuaranteedSelfAdaptiveAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runGuaranteedSelfAdaptiveAdapter
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalProofReuseAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runIncrementalProofReuseAdapter
#print axioms ConstitutiveSearch.NeuralAgent.DeploymentChainPropagationAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runDeploymentChainPropagationAdapter
#print axioms ConstitutiveSearch.NeuralAgent.FrozenNeuralComparisonAdapterBundle
#print axioms ConstitutiveSearch.NeuralAgent.frozenNeuralComparisonAdapterBundle
/- AXIOM_AUDIT_END -/
