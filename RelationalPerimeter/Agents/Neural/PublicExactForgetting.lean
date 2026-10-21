import RelationalPerimeter.Agents.Neural.PublicActionRealization
import RelationalPerimeter.Agents.Neural.ExactForgetting
import RelationalPerimeter.Agents.Neural.ReconfiguredExactForgetting

/-! Closed public witness of exact produced-origin forgetting. -/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures EndogenousDecomposition

def publicHistoricalMaster : UnifiedMaster.Instance 0 :=
  UnifiedMaster.publicInstance 0

def publicHistoricalRequirement : Agent.Requirement :=
  Agent.singletonRequirement 0

abbrev PublicHistoricalOrigin : Type 3 :=
  ULift.{3} (RoleOccurrenceProfile publicHistoricalMaster.roles)

def publicHistoricalInitialMemory
    (origin : PublicHistoricalOrigin) : Agent.Memory :=
  Agent.start publicHistoricalMaster publicHistoricalRequirement origin.down

abbrev PublicHistoricalInteractionSource : Type 3 :=
  HistoricalInteractionSource PublicHistoricalOrigin
    publicHistoricalInitialMemory publicRequirementFamily

def publicLeftHistoricalSource : PublicHistoricalInteractionSource :=
  .initial (ULift.up publicHistoricalMaster.distinctPair.left)

def publicRightHistoricalSource : PublicHistoricalInteractionSource :=
  .initial (ULift.up publicHistoricalMaster.distinctPair.right)

theorem public_historical_origins_distinct :
    publicLeftHistoricalSource.origin ≠ publicRightHistoricalSource.origin :=
  fun same => publicHistoricalMaster.distinctPair.distinct
    (congrArg ULift.down same)

theorem public_historical_memories_equal :
    publicLeftHistoricalSource.currentMemory
        publicRequirementSignalPreservation publicAgentActionChannel =
      publicRightHistoricalSource.currentMemory
        publicRequirementSignalPreservation publicAgentActionChannel :=
  Agent.initial_memories_equal publicHistoricalMaster
    publicHistoricalRequirement publicHistoricalMaster.distinctPair.left
    publicHistoricalMaster.distinctPair.right

theorem public_left_historical_memory_is_action_memory :
    publicLeftHistoricalSource.currentMemory
        publicRequirementSignalPreservation publicAgentActionChannel =
      publicActionMemory :=
  rfl

theorem public_forgotten_sources_same_signature :
    interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicLeftHistoricalSource =
      interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicRightHistoricalSource :=
  same_memory_same_interaction_signature publicRequirementSignalPreservation
    publicAgentActionChannel public_historical_memories_equal

theorem public_forgotten_sources_same_future :
    FutureEquivalent
      (interactionFutureContract publicRequirementSignalPreservation
        publicAgentActionChannel)
      publicLeftHistoricalSource publicRightHistoricalSource :=
  (forgotten_iff_future_indistinguishable publicRequirementSignalPreservation
    publicAgentActionChannel publicLeftHistoricalSource
    publicRightHistoricalSource).mp public_forgotten_sources_same_signature

theorem public_historical_origin_not_recoverable
    (recover : List (Outcome Agent.Event Agent.Memory) -> PublicHistoricalOrigin)
    (recoversLeft :
      recover (interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicLeftHistoricalSource) =
          publicLeftHistoricalSource.origin)
    (recoversRight :
      recover (interactionSignature publicRequirementSignalPreservation
        publicAgentActionChannel publicRightHistoricalSource) =
          publicRightHistoricalSource.origin) : False :=
  forgotten_origin_not_recoverable publicRequirementSignalPreservation
    publicAgentActionChannel publicLeftHistoricalSource
    publicRightHistoricalSource public_historical_origins_distinct
    public_historical_memories_equal recover recoversLeft recoversRight

/-- The reconfigured future starts only after the source action has executed.
The retained state therefore contains its produced successor memory together
with the exact native system and source input needed by the next
reconfiguration. -/
def publicReconfiguredInitialHistoricalStateFor
    (source : PublicRequirementInput)
    (_origin : PublicHistoricalOrigin) :
    ReconfiguredExecutionState publicRequirementFamily :=
  publicInitialReconfiguredState source

abbrev PublicReconfiguredHistoricalSourceFor
    (source : PublicRequirementInput) : Type 3 :=
  ReconfiguredHistoricalSource PublicHistoricalOrigin publicRequirementFamily
    publicReconfigurationBuilder publicAgentActionChannel
    publicReconfigurationCertificateForState
    (publicReconfiguredInitialHistoricalStateFor source)

def publicReconfiguredLeftHistoricalSourceFor
    (source : PublicRequirementInput) :
    PublicReconfiguredHistoricalSourceFor source :=
  .initial (ULift.up publicHistoricalMaster.distinctPair.left)

def publicReconfiguredRightHistoricalSourceFor
    (source : PublicRequirementInput) :
    PublicReconfiguredHistoricalSourceFor source :=
  .initial (ULift.up publicHistoricalMaster.distinctPair.right)

theorem public_reconfigured_historical_origins_distinct_for
    (source : PublicRequirementInput) :
    (publicReconfiguredLeftHistoricalSourceFor source).origin ≠
      (publicReconfiguredRightHistoricalSourceFor source).origin :=
  fun same => publicHistoricalMaster.distinctPair.distinct
    (congrArg ULift.down same)

theorem public_reconfigured_historical_states_equal_for
    (source : PublicRequirementInput) :
    (publicReconfiguredLeftHistoricalSourceFor source).currentState =
      (publicReconfiguredRightHistoricalSourceFor source).currentState :=
  rfl

theorem public_reconfigured_forgotten_sources_same_future_for
    (source : PublicRequirementInput) :
    FutureEquivalent
      (reconfiguredFutureContract
        (channel := publicAgentActionChannel)
        (certify := publicReconfigurationCertificateForState)
        (initialState := publicReconfiguredInitialHistoricalStateFor source))
      (publicReconfiguredLeftHistoricalSourceFor source)
      (publicReconfiguredRightHistoricalSourceFor source) :=
  reconfigured_same_state_same_future
    (public_reconfigured_historical_states_equal_for source)

theorem public_reconfigured_origin_not_recoverable_for
    (source : PublicRequirementInput)
    (recover : ReconfiguredExecutionState publicRequirementFamily ->
      PublicHistoricalOrigin)
    (recoversLeft :
      recover (publicReconfiguredLeftHistoricalSourceFor source).currentState =
        (publicReconfiguredLeftHistoricalSourceFor source).origin)
    (recoversRight :
      recover (publicReconfiguredRightHistoricalSourceFor source).currentState =
        (publicReconfiguredRightHistoricalSourceFor source).origin) : False :=
  reconfigured_origin_not_recoverable
    (publicReconfiguredLeftHistoricalSourceFor source)
    (publicReconfiguredRightHistoricalSourceFor source)
    (public_reconfigured_historical_origins_distinct_for source)
    (public_reconfigured_historical_states_equal_for source)
    recover recoversLeft recoversRight

def publicReconfiguredInitialHistoricalState :
    PublicHistoricalOrigin -> ReconfiguredExecutionState publicRequirementFamily :=
  publicReconfiguredInitialHistoricalStateFor ⟨.deny, ()⟩

abbrev PublicReconfiguredHistoricalSource : Type 3 :=
  PublicReconfiguredHistoricalSourceFor ⟨.deny, ()⟩

def publicReconfiguredLeftHistoricalSource :
    PublicReconfiguredHistoricalSource :=
  publicReconfiguredLeftHistoricalSourceFor ⟨.deny, ()⟩

def publicReconfiguredRightHistoricalSource :
    PublicReconfiguredHistoricalSource :=
  publicReconfiguredRightHistoricalSourceFor ⟨.deny, ()⟩

theorem public_reconfigured_historical_origins_distinct :
    publicReconfiguredLeftHistoricalSource.origin ≠
      publicReconfiguredRightHistoricalSource.origin :=
  public_reconfigured_historical_origins_distinct_for ⟨.deny, ()⟩

theorem public_reconfigured_historical_states_equal :
    publicReconfiguredLeftHistoricalSource.currentState =
      publicReconfiguredRightHistoricalSource.currentState :=
  public_reconfigured_historical_states_equal_for ⟨.deny, ()⟩

theorem public_reconfigured_forgotten_sources_same_future :
    FutureEquivalent
      (reconfiguredFutureContract
        (channel := publicAgentActionChannel)
        (certify := publicReconfigurationCertificateForState)
        (initialState := publicReconfiguredInitialHistoricalState))
      publicReconfiguredLeftHistoricalSource
      publicReconfiguredRightHistoricalSource :=
  public_reconfigured_forgotten_sources_same_future_for ⟨.deny, ()⟩

theorem public_reconfigured_origin_not_recoverable
    (recover : ReconfiguredExecutionState publicRequirementFamily ->
      PublicHistoricalOrigin)
    (recoversLeft :
      recover publicReconfiguredLeftHistoricalSource.currentState =
        publicReconfiguredLeftHistoricalSource.origin)
    (recoversRight :
      recover publicReconfiguredRightHistoricalSource.currentState =
        publicReconfiguredRightHistoricalSource.origin) : False :=
  public_reconfigured_origin_not_recoverable_for ⟨.deny, ()⟩ recover
    recoversLeft recoversRight

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalMaster
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalRequirement
#print axioms ConstitutiveSearch.NeuralAgent.publicHistoricalInitialMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicLeftHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.publicRightHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_origins_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_memories_equal
#print axioms ConstitutiveSearch.NeuralAgent.public_left_historical_memory_is_action_memory
#print axioms ConstitutiveSearch.NeuralAgent.public_forgotten_sources_same_signature
#print axioms ConstitutiveSearch.NeuralAgent.public_forgotten_sources_same_future
#print axioms ConstitutiveSearch.NeuralAgent.public_historical_origin_not_recoverable
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredInitialHistoricalState
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredInitialHistoricalStateFor
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredLeftHistoricalSourceFor
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredRightHistoricalSourceFor
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_historical_origins_distinct_for
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_historical_states_equal_for
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_forgotten_sources_same_future_for
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_origin_not_recoverable_for
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredLeftHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredRightHistoricalSource
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_historical_origins_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_historical_states_equal
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_forgotten_sources_same_future
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_origin_not_recoverable
/- AXIOM_AUDIT_END -/
