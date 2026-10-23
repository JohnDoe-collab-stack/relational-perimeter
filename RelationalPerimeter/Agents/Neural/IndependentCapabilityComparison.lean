import RelationalPerimeter.Agents.Neural.CompleteCapabilityComparison

/-!
# Oracle-independent complete capability comparison

The v10 comparison remains an immutable historical record.  This module is
the corrected production surface for its successor.  In particular, the
reference combination below is computed only from the current-table,
authorization-dependency, mutation-shield and future-contract observations.
It neither calls `submitUpdate` nor receives a runtime submission decision,
an incremental verdict, a complete-recheck verdict or a target certificate.

The executable successor emits only values recomputed from these typed
outputs.  Properties that exist only as Lean proofs are recorded separately
in the frozen evidence ledger; they are not printed as if they had been
observed by IO.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

inductive IndependentReferenceDecision where
  | allow
  | refuse
  deriving DecidableEq

/-- The decision rule of the reference combination.  Every argument is one
of the independently computed observations declared by the reference method;
there is deliberately no constitutive-checker or runtime-submission input. -/
def independentReferenceDecision
    (authorizationDependency : Bool)
    (mutationDecision : FrozenShieldDecision)
    (futureSatisfied : Bool) : IndependentReferenceDecision :=
  if authorizationDependency then
    match mutationDecision with
    | .allow => if futureSatisfied then .allow else .refuse
    | .refuse => .refuse
  else
    .refuse

/-- Proof-free observations computed by the independent reference method. -/
structure IndependentReferenceObservation
    (material : FrozenCompleteComparisonMaterial) : Type 7 where
  currentTablesEqual : Bool
  alignedAuthorizationDependency : Bool
  bypassAuthorizationDependency : Bool
  alignedMutationDecision : FrozenShieldDecision
  bypassMutationDecision : FrozenShieldDecision
  alignedFutureSatisfied : Bool
  bypassFutureSatisfied : Bool
  alignedDecision : IndependentReferenceDecision
  bypassDecision : IndependentReferenceDecision

/-- Compute the reference observations directly from the shared material.
This is the function whose transitive generated-code closure is audited. -/
def computeIndependentReferenceObservation
    (material : FrozenCompleteComparisonMaterial) :
    IndependentReferenceObservation material :=
  let currentTablesEqual := decide
    (material.base.currentTable material.base.alignedCandidate =
      material.base.currentTable material.base.bypassCandidate)
  let alignedAuthorizationDependency :=
    primaryAuthorizationConstitutivelyConsumed
      material.base.alignedCandidate.candidate.targetArtifact
  let bypassAuthorizationDependency :=
    primaryAuthorizationConstitutivelyConsumed
      material.base.bypassCandidate.candidate.targetArtifact
  let alignedMutationDecision :=
    frozenShieldDecision material.base.alignedCandidate.candidate
  let bypassMutationDecision :=
    frozenShieldDecision material.base.bypassCandidate.candidate
  let alignedFutureSatisfied := learnedFutureNormSatisfied
    material.base.futureRequests
    (learnedCandidateOperationalFuture material.base.alignedCandidate
      material.base.futureRequests)
  let bypassFutureSatisfied := learnedFutureNormSatisfied
    material.base.futureRequests
    (learnedCandidateOperationalFuture material.base.bypassCandidate
      material.base.futureRequests)
  { currentTablesEqual := currentTablesEqual
    alignedAuthorizationDependency := alignedAuthorizationDependency
    bypassAuthorizationDependency := bypassAuthorizationDependency
    alignedMutationDecision := alignedMutationDecision
    bypassMutationDecision := bypassMutationDecision
    alignedFutureSatisfied := alignedFutureSatisfied
    bypassFutureSatisfied := bypassFutureSatisfied
    alignedDecision := independentReferenceDecision
      alignedAuthorizationDependency alignedMutationDecision
      alignedFutureSatisfied
    bypassDecision := independentReferenceDecision
      bypassAuthorizationDependency bypassMutationDecision
      bypassFutureSatisfied }

/-- Proof-carrying closure of the observations.  The proofs identify the
result of the independent computation; none supplies an input to it. -/
structure IndependentReferenceCombinationOutput
    (material : FrozenCompleteComparisonMaterial) : Type 8 where
  observation : IndependentReferenceObservation material
  observationExact : observation =
    computeIndependentReferenceObservation material
  currentTablesEqualExact : observation.currentTablesEqual = true
  alignedAuthorizationDependencyExact :
    observation.alignedAuthorizationDependency = true
  bypassAuthorizationDependencyExact :
    observation.bypassAuthorizationDependency = false
  alignedMutationDecisionExact : observation.alignedMutationDecision = .allow
  bypassMutationDecisionExact : observation.bypassMutationDecision = .refuse
  alignedFutureSatisfiedExact : observation.alignedFutureSatisfied = true
  bypassFutureSatisfiedExact : observation.bypassFutureSatisfied = false
  alignedDecisionExact : observation.alignedDecision = .allow
  bypassDecisionExact : observation.bypassDecision = .refuse

def runIndependentReferenceCombination
    (material : FrozenCompleteComparisonMaterial) :
    IndependentReferenceCombinationOutput material := by
  let observation := computeIndependentReferenceObservation material
  refine
    { observation := observation
      observationExact := rfl
      currentTablesEqualExact := ?_
      alignedAuthorizationDependencyExact := ?_
      bypassAuthorizationDependencyExact := ?_
      alignedMutationDecisionExact := ?_
      bypassMutationDecisionExact := ?_
      alignedFutureSatisfiedExact := ?_
      bypassFutureSatisfiedExact := ?_
      alignedDecisionExact := ?_
      bypassDecisionExact := ?_ }
  · dsimp only [observation, computeIndependentReferenceObservation]
    apply decide_eq_true
    unfold FrozenNeuralComparisonMaterial.currentTable
    rw [material.base.currentDomainExact,
      material.base.alignedCandidateExact,
      material.base.bypassCandidateExact]
    exact learnedAlignedBypass_currentTable_exact
  · dsimp only [observation, computeIndependentReferenceObservation]
    rw [material.base.alignedCandidateExact]
    rfl
  · dsimp only [observation, computeIndependentReferenceObservation]
    rw [material.base.bypassCandidateExact]
    rfl
  · dsimp only [observation, computeIndependentReferenceObservation]
    rw [material.base.alignedCandidateExact]
    rfl
  · dsimp only [observation, computeIndependentReferenceObservation]
    rw [material.base.bypassCandidateExact]
    rfl
  · dsimp only [observation, computeIndependentReferenceObservation]
    rw [material.base.alignedCandidateExact,
      material.base.futureRequestsExact,
      ← learnedAlignedInstalledFuture_is_candidateFuture]
    exact learnedAlignedInstalledFuture_satisfies
  · dsimp only [observation, computeIndependentReferenceObservation]
    rw [material.base.bypassCandidateExact,
      material.base.futureRequestsExact]
    exact learnedBypassCandidateFuture_violates
  · dsimp only [observation, computeIndependentReferenceObservation,
      independentReferenceDecision]
    rw [material.base.alignedCandidateExact,
      material.base.futureRequestsExact,
      ← learnedAlignedInstalledFuture_is_candidateFuture]
    rfl
  · dsimp only [observation, computeIndependentReferenceObservation,
      independentReferenceDecision]
    rw [material.base.bypassCandidateExact]
    rfl

inductive RuntimeSubmissionObservation where
  | installed
  | rejected
  deriving DecidableEq

/-- Runtime submission is an observation for the self-adaptive adapter only;
it is intentionally absent from the reference-combination interface. -/
def observeRuntimeSubmission
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    (runtime : CertifiedRuntime checker initial)
    (update : checker.Update runtime.current) :
    RuntimeSubmissionObservation :=
  match submitUpdate runtime update with
  | .ok _ => .installed
  | .error _ => .rejected

inductive GenericIncrementalObservation where
  | accepted
  | rejected
  deriving DecidableEq

def observeGenericIncremental
    (update : LearnedSerializedConstitutiveUpdate) :
    GenericIncrementalObservation :=
  match checkGenericIncrementalUpdate learnedIncrementalCheckerEngine update with
  | .ok _ => .accepted
  | .error _ => .rejected

/-- Corrected nine-method bundle.  It deliberately does not contain the v10
reference result and therefore cannot evaluate that oracle-dependent path. -/
structure IndependentCompleteComparisonBundle : Type 10 where
  material : FrozenCompleteComparisonMaterial
  sixClasses : FrozenNeuralComparisonAdapterBundle
  sixClassesMaterialExact : sixClasses.material = material.base
  relational : RelationalExecutionComparisonOutput material
  referenceCombination : IndependentReferenceCombinationOutput material
  fullRecheck : IndependentFullRecheckComparisonOutput material
  translations : List MethodTranslationLedger
  translationsExact : translations = methodTranslationLedgers

def independentCompleteComparisonBundle :
    IndependentCompleteComparisonBundle :=
  { material := frozenCompleteComparisonMaterial
    sixClasses := frozenNeuralComparisonAdapterBundle
    sixClassesMaterialExact := rfl
    relational := runRelationalExecutionComparison
      frozenCompleteComparisonMaterial
    referenceCombination := runIndependentReferenceCombination
      frozenCompleteComparisonMaterial
    fullRecheck := runIndependentFullRecheckComparison
      frozenCompleteComparisonMaterial
    translations := methodTranslationLedgers
    translationsExact := rfl }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.IndependentReferenceDecision
#print axioms ConstitutiveSearch.NeuralAgent.independentReferenceDecision
#print axioms ConstitutiveSearch.NeuralAgent.IndependentReferenceObservation
#print axioms ConstitutiveSearch.NeuralAgent.computeIndependentReferenceObservation
#print axioms ConstitutiveSearch.NeuralAgent.IndependentReferenceCombinationOutput
#print axioms ConstitutiveSearch.NeuralAgent.runIndependentReferenceCombination
#print axioms ConstitutiveSearch.NeuralAgent.RuntimeSubmissionObservation
#print axioms ConstitutiveSearch.NeuralAgent.observeRuntimeSubmission
#print axioms ConstitutiveSearch.NeuralAgent.GenericIncrementalObservation
#print axioms ConstitutiveSearch.NeuralAgent.observeGenericIncremental
#print axioms ConstitutiveSearch.NeuralAgent.IndependentCompleteComparisonBundle
#print axioms ConstitutiveSearch.NeuralAgent.independentCompleteComparisonBundle
/- AXIOM_AUDIT_END -/
