import RelationalPerimeter.Agents.Neural.PublicRequirementAlignment
import RelationalPerimeter.Agents.Neural.ActionRealization
import RelationalPerimeter.Agents.Neural.InteractionHistory
import RelationalPerimeter.Agents.Neural.ReconfiguredContinuation
import RelationalPerimeter.Agents.Constitutive.PublicInstance

/-! A closed public action/effect instance for the two covered requirements. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

def publicAgentActionChannel : AgentActionChannel Bool where
  command
    | false => .advance 0
    | true => .advance 1

def publicActionMemory : Agent.Memory :=
  (Agent.publicSession 0 0).memory

def publicAction (input : PublicRequirementInput) :
    ActionRealization publicAgentActionChannel
      (publicRequirementSignalPreservation input) publicActionMemory :=
  realizeAction publicAgentActionChannel
    (publicRequirementSignalPreservation input) publicActionMemory

def publicEffect (input : PublicRequirementInput) :
    EffectRealization (publicAction input) :=
  realizeEffect (publicAction input)

theorem public_action_request_exact (input : PublicRequirementInput) :
    (publicAction input).request =
      publicAgentActionChannel.command
        (publicRequirementFamily.requiredProposal input.requirement input.context) :=
  (publicAction input).request_exact

theorem public_deny_request :
    (publicAction ⟨.deny, ()⟩).request = .advance 0 :=
  public_action_request_exact ⟨.deny, ()⟩

theorem public_allow_request :
    (publicAction ⟨.allow, ()⟩).request = .advance 1 :=
  public_action_request_exact ⟨.allow, ()⟩

theorem public_action_requests_distinct :
    (publicAction ⟨.deny, ()⟩).request ≠
      (publicAction ⟨.allow, ()⟩).request := by
  rw [public_deny_request, public_allow_request]
  intro impossible
  cases impossible

theorem public_effect_exact (input : PublicRequirementInput) :
    ((publicEffect input).successor, (publicEffect input).event) =
      Agent.executeInput publicActionMemory (publicAction input).request :=
  (publicEffect input).effect_exact

theorem public_deny_effect_message :
    (publicEffect ⟨.deny, ()⟩).event.message = .advanced 0 := by
  rw [(publicEffect ⟨.deny, ()⟩).eventExact]
  change (Agent.executeInput publicActionMemory (.advance 0)).2.message = _
  rfl

theorem public_allow_effect_message :
    (publicEffect ⟨.allow, ()⟩).event.message = .advanced 1 := by
  rw [(publicEffect ⟨.allow, ()⟩).eventExact]
  change (Agent.executeInput publicActionMemory (.advance 1)).2.message = _
  rfl

theorem public_effects_distinct :
    (publicEffect ⟨.deny, ()⟩).event ≠
      (publicEffect ⟨.allow, ()⟩).event := by
  intro same
  have messages := congrArg Agent.Event.message same
  rw [public_deny_effect_message, public_allow_effect_message] at messages
  cases messages

def publicInteractionHistory (memory : Agent.Memory)
    (inputs : List PublicRequirementInput) :
    InteractionHistory publicRequirementIncorporation
      publicRequirementSignalPreservation publicAgentActionChannel memory inputs :=
  executeInteractions publicRequirementIncorporation
    publicRequirementSignalPreservation publicAgentActionChannel memory inputs

def publicFiniteInteractionHistory (inputs : List PublicRequirementInput) :
    InteractionHistory publicRequirementIncorporation
      publicRequirementSignalPreservation publicAgentActionChannel
      publicActionMemory inputs :=
  publicInteractionHistory publicActionMemory inputs

theorem public_finite_continuation_aligned
    (inputs : List PublicRequirementInput) :
    (publicFiniteInteractionHistory inputs).requests =
      requiredRequests publicAgentActionChannel inputs :=
  finite_continuation_aligned publicRequirementIncorporation
    publicRequirementSignalPreservation publicAgentActionChannel
    publicActionMemory inputs

theorem public_finite_continuation_execution_exact
    (inputs : List PublicRequirementInput) :
    ((publicFiniteInteractionHistory inputs).finalMemory,
      (publicFiniteInteractionHistory inputs).events) =
      Agent.executeRequests publicActionMemory
        (requiredRequests publicAgentActionChannel inputs) :=
  finite_continuation_execution_exact publicRequirementIncorporation
    publicRequirementSignalPreservation publicAgentActionChannel
    publicActionMemory inputs

theorem public_head_horizon_independent
    (input : PublicRequirementInput)
    (left right : List PublicRequirementInput) :
    (publicFiniteInteractionHistory (input :: left)).headRequest =
      (publicFiniteInteractionHistory (input :: right)).headRequest :=
  head_horizon_independent publicRequirementIncorporation
    publicRequirementSignalPreservation publicAgentActionChannel
    publicActionMemory input left right

/-- The head of the public continuation is the very action exposed by the
single-step public interface, rather than an independently reconstructed
request with the same specification. -/
theorem public_continuation_head_is_action
    (input : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    (publicFiniteInteractionHistory (input :: future)).headRequest =
      some (publicAction input).request :=
  rfl

def publicBoolCode : Bool -> Activation
  | false => 0
  | true => 1

def publicReconfigurationSourcePort : Fin 2 := ⟨0, by decide⟩
def publicReconfigurationRequirementPort : Fin 2 := ⟨1, by decide⟩
def publicReconfigurationProposalOutput : Fin 2 := ⟨0, by decide⟩
def publicReconfigurationOutput : Fin 2 := ⟨1, by decide⟩

def publicReconfigurationInputs (source : Bool)
    (next : PublicRequirementInput) : SizedActivations 2 :=
  (SizedActivations.snoc SizedActivations.empty (publicBoolCode source)).snoc
    (publicRequirementCode next.requirement)

def publicReconfigurationProposalNeuron : NeuronSpec 2 0 :=
  { inputs :=
      [{ source := .receivedInput publicReconfigurationRequirementPort,
          weight := 1 }]
    bias := 0
    threshold := ⟨1⟩ }

def publicReconfigurationCombinationNeuron : NeuronSpec 2 1 :=
  { inputs :=
      [{ source := .receivedInput publicReconfigurationSourcePort, weight := 1 },
       { source := .receivedInput publicReconfigurationRequirementPort, weight := 1 }]
    bias := 0
    threshold := ⟨1⟩ }

def publicReconfigurationProgram : NetworkProgram 2 2 :=
  .extend (.extend .empty publicReconfigurationProposalNeuron)
    publicReconfigurationCombinationNeuron

def publicReconfigurationOutputs : OutputPorts 2 :=
  { sources :=
      [publicReconfigurationProposalOutput, publicReconfigurationOutput]
    nonempty := by intro impossible; cases impossible }

def publicReconfigurationSystem (source : Bool)
    (next : PublicRequirementInput) :
    NativeSystem PublicRequirementInput Bool :=
  { inputCount := 2
    producedCount := 2
    encode := fun _ => publicReconfigurationInputs source next
    program := publicReconfigurationProgram
    outputs := publicReconfigurationOutputs
    decode := decodePublicRequirement }

def proposalFromRun
    (system : NativeSystem PublicRequirementInput Bool)
    (run : NativeRun system.program) : Bool :=
  system.decode (readOutputs system.outputs run.activations)

def publicReconfigurationBuilder :
    ReconfigurationBuilder publicRequirementFamily where
  permissionVariable
    | .deny => 0
    | .allow => 1
  sourceCode := publicBoolCode
  requirementCode := publicRequirementCode
  build := fun sourceSystem run next =>
    publicReconfigurationSystem (proposalFromRun sourceSystem run) next

def publicReconfigurationPermission (next : PublicRequirementInput) :
    Resources.Ref
      (publicRequirementFamily.received next.requirement).realizedScope
      (publicReconfigurationBuilder.permissionVariable next.requirement) := by
  cases next with
  | mk requirement context =>
      cases requirement <;> cases context <;> exact .here

def publicReconfigurationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Reconfiguration publicReconfigurationBuilder sourceSystem source next :=
  reconfigure publicReconfigurationBuilder source next
    (publicReconfigurationPermission next)

def publicReconfiguration (source next : PublicRequirementInput) :
    Reconfiguration publicReconfigurationBuilder publicRequirementSystem
      source next :=
  publicReconfigurationFrom publicRequirementSystem source next

def publicReconfigurationSourceEdgeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Reaches ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (.receivedInput publicReconfigurationSourcePort)
      (.neuronOutput publicReconfigurationOutput) :=
  .step (.executedEdge publicReconfigurationOutput
    { source := .receivedInput publicReconfigurationSourcePort, weight := 1 }
    (by exact List.Mem.head _)) (.refl _)

def publicReconfigurationSourceEdge (source next : PublicRequirementInput) :
    Reaches ((publicReconfiguration source next).targetSystem.run next)
      (.receivedInput publicReconfigurationSourcePort)
      (.neuronOutput publicReconfigurationOutput) :=
  publicReconfigurationSourceEdgeFrom publicRequirementSystem source next

def publicReconfigurationRequirementEdgeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Reaches ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (.receivedInput publicReconfigurationRequirementPort)
      (.neuronOutput publicReconfigurationOutput) :=
  .step (.executedEdge publicReconfigurationOutput
    { source := .receivedInput publicReconfigurationRequirementPort, weight := 1 }
    (by exact List.Mem.tail _ (List.Mem.head _))) (.refl _)

def publicReconfigurationRequirementEdge (source next : PublicRequirementInput) :
    Reaches ((publicReconfiguration source next).targetSystem.run next)
      (.receivedInput publicReconfigurationRequirementPort)
      (.neuronOutput publicReconfigurationOutput) :=
  publicReconfigurationRequirementEdgeFrom publicRequirementSystem source next

def publicRequiredMechanismTransportFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    RequiredMechanismTransport
      (publicReconfigurationFrom sourceSystem source next) where
  sourcePort := publicReconfigurationSourcePort
  requirementPort := publicReconfigurationRequirementPort
  portsDistinct := by
    intro same
    have values := congrArg Fin.val same
    cases values
  output := publicReconfigurationOutput
  sourceExact := by
    cases source with
    | mk sourceRequirement sourceContext =>
      cases sourceRequirement <;> cases sourceContext <;> rfl
  requirementExact := by
    cases source with
    | mk sourceRequirement sourceContext =>
      cases sourceRequirement <;> cases sourceContext
      · cases next with
        | mk nextRequirement nextContext =>
          cases nextRequirement <;> cases nextContext <;> rfl
      · cases next with
        | mk nextRequirement nextContext =>
          cases nextRequirement <;> cases nextContext <;> rfl
  sourcePath := publicReconfigurationSourceEdgeFrom sourceSystem source next
  requirementPath :=
    publicReconfigurationRequirementEdgeFrom sourceSystem source next
  proposalExact := by
    cases source with
    | mk sourceRequirement sourceContext =>
        cases next with
        | mk nextRequirement nextContext =>
            cases nextRequirement <;> cases nextContext <;> rfl

def publicRequiredMechanismTransport (source next : PublicRequirementInput) :
    RequiredMechanismTransport (publicReconfiguration source next) :=
  publicRequiredMechanismTransportFrom publicRequirementSystem source next

def publicCertifiedReconfigurationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    CertifiedReconfiguration (sourceSystem := sourceSystem)
      (builder := publicReconfigurationBuilder)
      (sourceInput := source) (nextInput := next) :=
  certifyReconfiguration (publicReconfigurationFrom sourceSystem source next)
    (publicRequiredMechanismTransportFrom sourceSystem source next)

def publicCertifiedReconfiguration (source next : PublicRequirementInput) :
    CertifiedReconfiguration (sourceSystem := publicRequirementSystem)
      (builder := publicReconfigurationBuilder)
      (sourceInput := source) (nextInput := next) :=
  publicCertifiedReconfigurationFrom publicRequirementSystem source next

def publicReconfigurationCertificateForState
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (next : PublicRequirementInput) :
    CertifiedReconfiguration (builder := publicReconfigurationBuilder)
      (sourceSystem := source.system) (sourceInput := source.input)
      (nextInput := next) :=
  publicCertifiedReconfigurationFrom source.system source.input next

/-- T7 is consumed here: the first state of the reconfigured continuation
contains exactly the successor produced by the executed public source action. -/
def publicInitialReconfiguredState (source : PublicRequirementInput) :
    ReconfiguredExecutionState publicRequirementFamily :=
  { system := publicRequirementSystem
    input := source
    memory := (publicEffect source).successor }

def publicReconfiguredInteractionHistory
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    ReconfiguredInteractionHistory publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      (publicInitialReconfiguredState source) future :=
  executeReconfiguredInteractions publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    (publicInitialReconfiguredState source) future

theorem public_reconfigured_requests_exact
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    (publicReconfiguredInteractionHistory source future).requests =
      requiredRequests publicAgentActionChannel future :=
  (publicReconfiguredInteractionHistory source future).requests_exact

theorem public_reconfigured_execution_exact
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    ((publicReconfiguredInteractionHistory source future).finalState.memory,
      (publicReconfiguredInteractionHistory source future).events) =
      Agent.executeRequests (publicEffect source).successor
        (requiredRequests publicAgentActionChannel future) := by
  rw [← public_reconfigured_requests_exact source future]
  exact (publicReconfiguredInteractionHistory source future).execution_exact

theorem public_reconfigured_head_horizon_independent
    (source next : PublicRequirementInput)
    (left right : List PublicRequirementInput) :
    (publicReconfiguredInteractionHistory source (next :: left)).headRequest =
      (publicReconfiguredInteractionHistory source (next :: right)).headRequest :=
  reconfigured_head_horizon_independent publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    (publicInitialReconfiguredState source) next left right

theorem public_reconfigured_head_request_exact
    (source next : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    (publicReconfiguredInteractionHistory source (next :: future)).headRequest =
      some (publicAgentActionChannel.command
        (publicRequirementFamily.requiredProposal
          next.requirement next.context)) := by
  change some _ = some _
  exact congrArg some
    (executeReconfiguredAction publicAgentActionChannel
      (publicInitialReconfiguredState source) next
      (publicReconfigurationCertificateForState
        (publicInitialReconfiguredState source) next)).request_required_exact

theorem public_reconfiguration_source_exact
    (source next : PublicRequirementInput) :
    ((publicReconfiguration source next).targetSystem.encode next).read
        publicReconfigurationSourcePort =
      publicBoolCode (publicRequirementSystem.proposal source) :=
  (publicRequiredMechanismTransport source next).sourceExact

theorem public_reconfiguration_requirement_exact
    (source next : PublicRequirementInput) :
    ((publicReconfiguration source next).targetSystem.encode next).read
        publicReconfigurationRequirementPort =
      publicRequirementCode next.requirement :=
  (publicRequiredMechanismTransport source next).requirementExact

theorem public_reconfiguration_reads_source_distinction
    (next : PublicRequirementInput) :
    ((publicReconfiguration ⟨.deny, ()⟩ next).targetSystem.encode next).read
        publicReconfigurationSourcePort ≠
      ((publicReconfiguration ⟨.allow, ()⟩ next).targetSystem.encode next).read
        publicReconfigurationSourcePort := by
  rw [public_reconfiguration_source_exact, public_reconfiguration_source_exact]
  intro impossible
  cases impossible

theorem public_reconfiguration_reads_requirement_distinction
    (source : PublicRequirementInput) :
    ((publicReconfiguration source ⟨.deny, ()⟩).targetSystem.encode
        ⟨.deny, ()⟩).read publicReconfigurationRequirementPort ≠
      ((publicReconfiguration source ⟨.allow, ()⟩).targetSystem.encode
        ⟨.allow, ()⟩).read publicReconfigurationRequirementPort := by
  rw [public_reconfiguration_requirement_exact,
    public_reconfiguration_requirement_exact]
  intro impossible
  cases impossible

/-- With the next requirement held at `deny`, changing only the proposal
produced by the source run changes the executed output of the reconfigured
mechanism.  The source port is therefore not merely stored. -/
theorem public_reconfiguration_source_changes_output :
    (publicReconfiguration ⟨.deny, ()⟩ ⟨.deny, ()⟩).targetSystem.outputValues
        ⟨.deny, ()⟩ ≠
      (publicReconfiguration ⟨.allow, ()⟩ ⟨.deny, ()⟩).targetSystem.outputValues
        ⟨.deny, ()⟩ := by
  intro impossible
  cases impossible

/-- With the source proposal held at `false`, changing only the next
requirement changes the executed output of the reconfigured mechanism.  The
requirement port is therefore not merely stored. -/
theorem public_reconfiguration_requirement_changes_output :
    (publicReconfiguration ⟨.deny, ()⟩ ⟨.deny, ()⟩).targetSystem.outputValues
        ⟨.deny, ()⟩ ≠
      (publicReconfiguration ⟨.deny, ()⟩ ⟨.allow, ()⟩).targetSystem.outputValues
        ⟨.allow, ()⟩ := by
  intro impossible
  cases impossible

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.publicAgentActionChannel
#print axioms ConstitutiveSearch.NeuralAgent.publicActionMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicAction
#print axioms ConstitutiveSearch.NeuralAgent.publicEffect
#print axioms ConstitutiveSearch.NeuralAgent.public_action_request_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_deny_request
#print axioms ConstitutiveSearch.NeuralAgent.public_allow_request
#print axioms ConstitutiveSearch.NeuralAgent.public_action_requests_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_effect_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_deny_effect_message
#print axioms ConstitutiveSearch.NeuralAgent.public_allow_effect_message
#print axioms ConstitutiveSearch.NeuralAgent.public_effects_distinct
#print axioms ConstitutiveSearch.NeuralAgent.publicInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.publicFiniteInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.public_finite_continuation_aligned
#print axioms ConstitutiveSearch.NeuralAgent.public_finite_continuation_execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_head_horizon_independent
#print axioms ConstitutiveSearch.NeuralAgent.public_continuation_head_is_action
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationBuilder
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.proposalFromRun
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.publicRequiredMechanismTransportFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicRequiredMechanismTransport
#print axioms ConstitutiveSearch.NeuralAgent.publicCertifiedReconfigurationFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicCertifiedReconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationCertificateForState
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialReconfiguredState
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_requests_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_head_horizon_independent
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_head_request_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_source_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_requirement_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_reads_source_distinction
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_reads_requirement_distinction
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_source_changes_output
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_requirement_changes_output
/- AXIOM_AUDIT_END -/
