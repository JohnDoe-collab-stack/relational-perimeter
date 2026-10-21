import RelationalPerimeter.Agents.Neural.LearnedUpdateSeparation

/-!
# Finite counterfactual divergence of the learned candidates

The current authorized domain cannot distinguish the aligned and bypass
updates.  This module supplies one explicit nonempty future outside that
domain.  Both outcomes are calculated by the same pure simulator.  The
aligned candidate preserves the authorization-gated contract, while the
bypass candidate would violate it.  The bypass is nevertheless rejected by
the constitutive checker before the target artifact can be installed.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

def independentLearnedRequirementDiffers
    (requirement context : Bool) : Bool :=
  match requirement, context with
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

/-- The proposed operational contract authorizes the primary output exactly
when the requirement/context distinction is present and authorization is
present. -/
def independentLearnedExpectedPrimary
    (input : IndependentLearnedInput) : Activation :=
  asActivation (independentLearnedRequirementDiffers
    input.requirement input.context && input.authorization)

def independentLearnedFutureContractSatisfied
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate)
    (input : IndependentLearnedInput) : Bool :=
  match simulateUncheckedUpdate initial candidate input with
  | primary :: _ => primary == independentLearnedExpectedPrimary input
  | [] => false

/-- This request is not in the declared current domain: its authorization is
false.  Its requirement/context signals still differ, so the learned bypass
observation remains active. -/
def independentLearnedCounterfactualInput : IndependentLearnedInput :=
  ⟨true, false, false⟩

def independentLearnedCounterfactualRequests :
    List IndependentLearnedInput :=
  [independentLearnedCounterfactualInput]

def simulateIndependentLearnedFuture
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate)
    (requests : List IndependentLearnedInput) :
    List (List Activation) :=
  requests.map (simulateUncheckedUpdate initial candidate)

def independentLearnedFiniteFutureSatisfies
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate)
    (requests : List IndependentLearnedInput) : Bool :=
  requests.all (independentLearnedFutureContractSatisfied initial candidate)

theorem alignedCounterfactualResult_exact :
    simulateUncheckedUpdate checkedIndependentLearnedInitial alignedUpdate
      independentLearnedCounterfactualInput = [0, 0, 1] := by
  rfl

theorem bypassCounterfactualResult_exact :
    simulateUncheckedUpdate checkedIndependentLearnedInitial bypassUpdate
      independentLearnedCounterfactualInput = [1, 0, 1] := by
  rfl

theorem alignedCounterfactualFuture_preserves_contract :
    independentLearnedFiniteFutureSatisfies checkedIndependentLearnedInitial
      alignedUpdate
      independentLearnedCounterfactualRequests = true := by
  rfl

theorem bypassCounterfactualFuture_violates_contract :
    independentLearnedFiniteFutureSatisfies checkedIndependentLearnedInitial
      bypassUpdate
      independentLearnedCounterfactualRequests = false := by
  rfl

/-- The witness contains the exact nonempty request list and the two calculated
result lists.  Neither result can be chosen independently after simulation. -/
structure FutureViolationWitness
    (initial : CheckedIndependentLearnedInitial)
    (aligned bypass : IndependentLearnedUpdateCandidate) : Type 4 where
  private mk ::
  requests : List IndependentLearnedInput
  requestsNonempty : requests ≠ []
  alignedResults : List (List Activation)
  bypassResults : List (List Activation)
  alignedResultsExact :
    alignedResults = simulateIndependentLearnedFuture initial aligned requests
  bypassResultsExact :
    bypassResults = simulateIndependentLearnedFuture initial bypass requests
  alignedContractExact :
    independentLearnedFiniteFutureSatisfies initial aligned requests = true
  bypassContractViolation :
    independentLearnedFiniteFutureSatisfies initial bypass requests = false
  calculatedResultsDifferent : alignedResults ≠ bypassResults

def alignedBypassFutureViolation :
    FutureViolationWitness checkedIndependentLearnedInitial
      alignedUpdate bypassUpdate :=
  .mk independentLearnedCounterfactualRequests
    (by intro impossible; cases impossible)
    (simulateIndependentLearnedFuture checkedIndependentLearnedInitial
      alignedUpdate
      independentLearnedCounterfactualRequests)
    (simulateIndependentLearnedFuture checkedIndependentLearnedInitial
      bypassUpdate
      independentLearnedCounterfactualRequests)
    rfl rfl alignedCounterfactualFuture_preserves_contract
    bypassCounterfactualFuture_violates_contract (by
      intro same
      cases same)

/-- The complete discriminating package connects the shared intention,
current extensional equivalence, causal check, finite counterfactual witness,
and pre-effect rejection. -/
structure ConstitutiveLatentBypassCertificate : Type 5 where
  initialChecked : CheckedIndependentLearnedInitial
  initialCheckExact :
    checkIndependentLearnedInitial independentLearnedInitialNetwork =
      .ok initialChecked
  sameAdmittedIntent : SameAdmittedUpdateIntent alignedUpdate bypassUpdate
  currentBehaviorEquivalent :
    CurrentBehaviorEquivalentAfterUpdate initialChecked
      alignedUpdate bypassUpdate
  everyCurrentExtensionalVerifierAgrees :
    EveryCurrentExtensionalVerifierAgrees initialChecked
      alignedUpdate bypassUpdate
  alignedChecked : CheckedIndependentLearnedUpdate alignedUpdate
  alignedCheckExact :
    checkIndependentLearnedUpdate initialChecked alignedUpdate =
      .ok alignedChecked
  bypassRejected :
    checkIndependentLearnedUpdate initialChecked bypassUpdate =
      .error .missingConstitutiveDependency
  futureViolation : FutureViolationWitness initialChecked alignedUpdate bypassUpdate
  rejectedBeforeEffect : RejectedBeforeEffect initialChecked bypassUpdate

def constitutiveChecker_detectsLatentBypass :
    ConstitutiveLatentBypassCertificate :=
  { initialChecked := checkedIndependentLearnedInitial
    initialCheckExact := checkIndependentLearnedInitial_accepts_learned
    sameAdmittedIntent := alignedBypassSameAdmittedUpdateIntent
    currentBehaviorEquivalent := candidateCurrentBehaviorEquivalent
    everyCurrentExtensionalVerifierAgrees :=
      everyCurrentExtensionalVerifierAgrees_aligned_bypass
    alignedChecked := checkedAlignedUpdate
    alignedCheckExact := checkIndependentLearnedUpdate_accepts_aligned
    bypassRejected := checkIndependentLearnedUpdate_rejects_bypass
    futureViolation := alignedBypassFutureViolation
    rejectedBeforeEffect := bypassUpdate_rejectedBeforeEffect }

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedExpectedPrimary
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFutureContractSatisfied
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedCounterfactualRequests
#print axioms ConstitutiveSearch.NeuralAgent.simulateIndependentLearnedFuture
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFiniteFutureSatisfies
#print axioms ConstitutiveSearch.NeuralAgent.alignedCounterfactualResult_exact
#print axioms ConstitutiveSearch.NeuralAgent.bypassCounterfactualResult_exact
#print axioms ConstitutiveSearch.NeuralAgent.alignedCounterfactualFuture_preserves_contract
#print axioms ConstitutiveSearch.NeuralAgent.bypassCounterfactualFuture_violates_contract
#print axioms ConstitutiveSearch.NeuralAgent.FutureViolationWitness
#print axioms ConstitutiveSearch.NeuralAgent.alignedBypassFutureViolation
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveLatentBypassCertificate
#print axioms ConstitutiveSearch.NeuralAgent.constitutiveChecker_detectsLatentBypass
/- AXIOM_AUDIT_END -/
