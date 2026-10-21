import RelationalPerimeter.Agents.Neural.PublicExactForgetting

namespace Tests.Mechanisms.NeuralExactForgettingRegression
open ConstitutiveSearch.NeuralAgent ConstitutiveSearch.ContinuationSignatures

theorem historical_sources_remain_distinct :
    publicLeftHistoricalSource.origin ≠ publicRightHistoricalSource.origin :=
  public_historical_origins_distinct

theorem forgetting_starts_from_executed_action_memory :
    publicLeftHistoricalSource.currentMemory
        publicRequirementSignalPreservation publicAgentActionChannel =
      publicActionMemory :=
  public_left_historical_memory_is_action_memory

theorem future_step_uses_executed_effect
    (input : ULift.{3} PublicRequirementInput) :
    ((interactionFutureContract publicRequirementSignalPreservation
      publicAgentActionChannel).next publicLeftHistoricalSource input).currentMemory
        publicRequirementSignalPreservation publicAgentActionChannel =
      (coveredInteractionEffect publicRequirementSignalPreservation
        publicAgentActionChannel
        (publicLeftHistoricalSource.currentMemory
          publicRequirementSignalPreservation publicAgentActionChannel)
        input.down).successor :=
  interaction_future_next_memory_exact publicRequirementSignalPreservation
    publicAgentActionChannel publicLeftHistoricalSource input

theorem exact_signature_criterion :
    interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicLeftHistoricalSource =
      interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicRightHistoricalSource ↔
    FutureEquivalent
      (interactionFutureContract publicRequirementSignalPreservation
        publicAgentActionChannel)
      publicLeftHistoricalSource publicRightHistoricalSource :=
  forgotten_iff_future_indistinguishable publicRequirementSignalPreservation
    publicAgentActionChannel publicLeftHistoricalSource
    publicRightHistoricalSource

theorem every_covered_future_is_preserved
    (future : List (ULift.{3} PublicRequirementInput)) :
    (interactionFutureContract publicRequirementSignalPreservation
        publicAgentActionChannel).outcome publicLeftHistoricalSource future =
      (interactionFutureContract publicRequirementSignalPreservation
        publicAgentActionChannel).outcome publicRightHistoricalSource future :=
  public_forgotten_sources_same_future future

theorem no_signature_decoder_recovers_both_histories
    (recover : List (Outcome ConstitutiveSearch.Agent.Event
      ConstitutiveSearch.Agent.Memory) -> PublicHistoricalOrigin)
    (denyExact :
      recover (interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicLeftHistoricalSource) =
          publicLeftHistoricalSource.origin)
    (allowExact :
      recover (interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicRightHistoricalSource) =
          publicRightHistoricalSource.origin) : False :=
  public_historical_origin_not_recoverable recover denyExact allowExact

end Tests.Mechanisms.NeuralExactForgettingRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.historical_sources_remain_distinct
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.forgetting_starts_from_executed_action_memory
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.future_step_uses_executed_effect
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.exact_signature_criterion
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.every_covered_future_is_preserved
#print axioms Tests.Mechanisms.NeuralExactForgettingRegression.no_signature_decoder_recovers_both_histories
/- AXIOM_AUDIT_END -/
