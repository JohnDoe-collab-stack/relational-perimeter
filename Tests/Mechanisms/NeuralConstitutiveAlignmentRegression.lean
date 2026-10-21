import RelationalPerimeter.Agents.Neural.ConstitutiveAlignment

namespace Tests.Mechanisms.NeuralConstitutiveAlignmentRegression
open ConstitutiveSearch.NeuralAgent

def denyInput : PublicRequirementInput := ⟨.deny, ()⟩
def allowInput : PublicRequirementInput := ⟨.allow, ()⟩

def completePublicChain :
    ConstitutiveAlignmentCertificate denyInput allowInput
      [denyInput, allowInput] :=
  constitutive_alignment denyInput allowInput [denyInput, allowInput]

theorem alignment_consumes_executed_effect :
    completePublicChain.initialState.memory =
      completePublicChain.effect.successor :=
  completePublicChain.effectConsumed

theorem alignment_continuation_uses_required_requests :
    completePublicChain.continuation.requests =
      requiredRequests publicAgentActionChannel
        [allowInput, denyInput, allowInput] :=
  completePublicChain.continuationRequestsExact

theorem alignment_continuation_is_exact_execution :
    (completePublicChain.continuation.finalState.memory,
      completePublicChain.continuation.events) =
      ConstitutiveSearch.Agent.executeRequests
        completePublicChain.initialState.memory
        completePublicChain.continuation.requests :=
  completePublicChain.continuationExecutionExact

theorem alignment_forgetting_starts_from_executed_state :
    completePublicChain.forgettingInitialState
        completePublicChain.forgottenLeft.origin =
      completePublicChain.continuation.finalState :=
  completePublicChain.forgettingInitialExact _

theorem alignment_forgets_origin_but_preserves_future :
    ConstitutiveSearch.ContinuationSignatures.FutureEquivalent
      (reconfiguredFutureContract
        (channel := publicAgentActionChannel)
        (certify := publicReconfigurationCertificateForState)
        (initialState := completePublicChain.forgettingInitialState))
      completePublicChain.forgottenLeft
      completePublicChain.forgottenRight :=
  completePublicChain.forgottenFutureEquivalent

end Tests.Mechanisms.NeuralConstitutiveAlignmentRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.completePublicChain
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_consumes_executed_effect
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_continuation_uses_required_requests
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_continuation_is_exact_execution
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_forgetting_starts_from_executed_state
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_forgets_origin_but_preserves_future
/- AXIOM_AUDIT_END -/
