import RelationalPerimeter.Agents.Neural.InteractionHistory
import RelationalPerimeter.Constitution.Continuation.Minimality

/-!
# Exact forgetting under an explicit neural-agent future contract

A rich source is generated inductively. It starts from a constituted origin
and its actual initial memory, then grows only by covered interactions executed
by the neural-to-agent action channel. No caller can attach an arbitrary past
label to an unrelated memory.

The reduced memory retains exactly the current agent memory and no origin
archive. A one-test finite basis is complete because the contract reads that
whole memory before every future. Equality of produced signatures is therefore
equivalent to equality of all covered future outcomes.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures

inductive HistoricalInteractionSource
    (History : Type 3) (initialMemory : History -> Agent.Memory)
    {RequirementCase Context Proposal : Type}
    (family : RequirementFamily RequirementCase Context Proposal) : Type 3 where
  | initial (origin : History) :
      HistoricalInteractionSource History initialMemory family
  | step (prior : HistoricalInteractionSource History initialMemory family)
      (input : RequirementInput family) :
      HistoricalInteractionSource History initialMemory family

def HistoricalInteractionSource.origin
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal} :
    HistoricalInteractionSource History initialMemory family -> History
  | .initial origin => origin
  | .step prior _ => prior.origin

def coveredInteractionEffect
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    (memory : Agent.Memory) (input : RequirementInput family) :
    EffectRealization (realizeAction channel (transformation input) memory) :=
  realizeEffect (realizeAction channel (transformation input) memory)

def HistoricalInteractionSource.currentMemory
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    HistoricalInteractionSource History initialMemory family -> Agent.Memory
  | .initial origin => initialMemory origin
  | .step prior input =>
      (coveredInteractionEffect transformation channel
        (prior.currentMemory transformation channel) input).successor

def interactionFutureContract
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    FutureContract (HistoricalInteractionSource History initialMemory family)
      (ULift.{3} (RequirementInput family)) Agent.Event Agent.Memory where
  next := fun source input => .step source input.down
  event := fun source input =>
    (coveredInteractionEffect transformation channel
      (source.currentMemory transformation channel) input.down).event
  read := fun source => source.currentMemory transformation channel
  Allow := fun _ _ => PUnit
  decision := fun _ _ => .inl PUnit.unit

theorem interaction_future_next_memory_exact
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    (source : HistoricalInteractionSource History initialMemory family)
    (input : ULift.{3} (RequirementInput family)) :
    ((interactionFutureContract transformation channel).next source input).currentMemory
        transformation channel =
      (coveredInteractionEffect transformation channel
        (source.currentMemory transformation channel) input.down).successor :=
  rfl

theorem interaction_future_event_exact
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    (source : HistoricalInteractionSource History initialMemory family)
    (input : ULift.{3} (RequirementInput family)) :
    (interactionFutureContract transformation channel).event source input =
      (coveredInteractionEffect transformation channel
        (source.currentMemory transformation channel) input.down).event :=
  rfl

def reducedInteractionFutureContract
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    FutureContract Agent.Memory (ULift.{3} (RequirementInput family))
      Agent.Event Agent.Memory where
  next := fun memory input =>
    (coveredInteractionEffect transformation channel memory input.down).successor
  event := fun memory input =>
    (coveredInteractionEffect transformation channel memory input.down).event
  read := fun memory => memory
  Allow := fun _ _ => PUnit
  decision := fun _ _ => .inl PUnit.unit

def signatureRealization
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    ExactRealization
      (interactionFutureContract (History := History)
        (initialMemory := initialMemory) transformation channel) Agent.Memory where
  reduced := reducedInteractionFutureContract transformation channel
  project := fun source => source.currentMemory transformation channel
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := by intro _ _ witness; cases witness; rfl
  forward_backward := by intro _ _ witness; cases witness; rfl
  next_exact := fun _ _ => rfl
  event_exact := fun _ _ => rfl
  read_exact := fun _ => rfl

def interactionFutureBasis
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal) :
    FiniteFutureBasis
      (interactionFutureContract (History := History)
        (initialMemory := initialMemory) transformation channel) where
  tests := [[]]
  complete := by
    intro left right agree
    apply (signatureRealization (History := History)
      (initialMemory := initialMemory) transformation channel).equal_memory_same_futures
    exact congrArg Outcome.read (agree [] (.head _))

def interactionSignature
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    (source : HistoricalInteractionSource History initialMemory family) :
    List (Outcome Agent.Event Agent.Memory) :=
  producedSignature
    (interactionFutureBasis (History := History) (initialMemory := initialMemory)
      transformation channel) source

theorem forgotten_iff_future_indistinguishable
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    (left right : HistoricalInteractionSource History initialMemory family) :
    interactionSignature transformation channel left =
        interactionSignature transformation channel right ↔
      FutureEquivalent
        (interactionFutureContract (History := History)
          (initialMemory := initialMemory) transformation channel) left right :=
  signature_exact
    (interactionFutureBasis (History := History) (initialMemory := initialMemory)
      transformation channel) left right

theorem same_memory_same_interaction_signature
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    {left right : HistoricalInteractionSource History initialMemory family}
    (same : left.currentMemory transformation channel =
      right.currentMemory transformation channel) :
    interactionSignature transformation channel left =
      interactionSignature transformation channel right :=
  signature_complete
    (interactionFutureBasis (History := History) (initialMemory := initialMemory)
      transformation channel)
    ((signatureRealization (History := History) (initialMemory := initialMemory)
      transformation channel).equal_memory_same_futures same)

theorem future_separable_not_forgotten
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    {left right : HistoricalInteractionSource History initialMemory family}
    (separable : ¬ FutureEquivalent
      (interactionFutureContract (History := History)
        (initialMemory := initialMemory) transformation channel) left right) :
    interactionSignature transformation channel left ≠
      interactionSignature transformation channel right :=
  fun same => separable
    ((forgotten_iff_future_indistinguishable transformation channel left right).mp same)

theorem forgotten_origin_not_recoverable
    {History : Type 3} {initialMemory : History -> Agent.Memory}
    {RequirementCase Context Proposal : Type}
    {family : RequirementFamily RequirementCase Context Proposal}
    {system : NativeMechanism.NativeSystem (RequirementInput family) Proposal}
    {encoding : RequirementEncoding system}
    {decoder : SingleOutputRequirementDecoder encoding}
    {incorporation : (input : RequirementInput family) ->
      RequirementIncorporation encoding input}
    (transformation : (input : RequirementInput family) ->
      RequirementSignalTransformation decoder (incorporation input))
    (channel : AgentActionChannel Proposal)
    (left right : HistoricalInteractionSource History initialMemory family)
    (originsDistinct : left.origin ≠ right.origin)
    (sameMemory : left.currentMemory transformation channel =
      right.currentMemory transformation channel)
    (recover : List (Outcome Agent.Event Agent.Memory) -> History)
    (recoversLeft : recover (interactionSignature transformation channel left) =
      left.origin)
    (recoversRight : recover (interactionSignature transformation channel right) =
      right.origin) : False := by
  apply originsDistinct
  exact recoversLeft.symm.trans
    ((congrArg recover
      (same_memory_same_interaction_signature transformation channel sameMemory)).trans
        recoversRight)

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalInteractionSource
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalInteractionSource.origin
#print axioms ConstitutiveSearch.NeuralAgent.coveredInteractionEffect
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalInteractionSource.currentMemory
#print axioms ConstitutiveSearch.NeuralAgent.interactionFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.interaction_future_next_memory_exact
#print axioms ConstitutiveSearch.NeuralAgent.interaction_future_event_exact
#print axioms ConstitutiveSearch.NeuralAgent.reducedInteractionFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.signatureRealization
#print axioms ConstitutiveSearch.NeuralAgent.interactionFutureBasis
#print axioms ConstitutiveSearch.NeuralAgent.interactionSignature
#print axioms ConstitutiveSearch.NeuralAgent.forgotten_iff_future_indistinguishable
#print axioms ConstitutiveSearch.NeuralAgent.same_memory_same_interaction_signature
#print axioms ConstitutiveSearch.NeuralAgent.future_separable_not_forgotten
#print axioms ConstitutiveSearch.NeuralAgent.forgotten_origin_not_recoverable
/- AXIOM_AUDIT_END -/
