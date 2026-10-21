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
  proposalDistinction := fun left right => left ≠ right
  collisionPermission := fun left right => left = right
  preservesDistinction := by
    intro left right distinct
    cases left <;> cases right
    · exact False.elim (distinct rfl)
    · intro same
      cases same
    · intro same
      cases same
    · exact False.elim (distinct rfl)
  collisionExact := by
    intro left right
    constructor
    · intro same
      cases same
      rfl
    · intro same
      cases left <;> cases right
      · rfl
      · cases same
      · cases same
      · rfl

theorem public_required_proposal_distinction :
    DistinctAccordingToProposalContract publicAgentActionChannel
      false true := by
  intro impossible
  cases impossible

theorem public_required_action_distinction :
    DistinctAccordingToActionContract publicAgentActionChannel
      (publicAgentActionChannel.command false)
      (publicAgentActionChannel.command true) :=
  publicAgentActionChannel.preserves_required_distinction
    public_required_proposal_distinction

theorem public_collision_permission_exact (left right : Bool) :
    CollisionPermittedByProposalContract publicAgentActionChannel left right ↔
      publicAgentActionChannel.command left =
        publicAgentActionChannel.command right :=
  publicAgentActionChannel.collision_characterized

def publicActionMemory : Agent.Memory :=
  (Agent.publicSession 0 0).memory

def publicAction (input : PublicRequirementInput) :
    ActionRealization publicAgentActionChannel
      (publicRequirementSignalTransformation input) publicActionMemory :=
  realizeAction publicAgentActionChannel
    (publicRequirementSignalTransformation input) publicActionMemory

def publicEffect (input : PublicRequirementInput) :
    EffectRealization (publicAction input) :=
  realizeEffect (publicAction input)

theorem public_action_request_exact (input : PublicRequirementInput) :
    (publicAction input).request =
      publicAgentActionChannel.command
        (publicRequirementFamily.requiredProposal input.requirement input.context) :=
  (publicAction input).request_exact

theorem public_actions_preserve_required_proposal_distinction
    (left right : PublicRequirementInput)
    (distinct : DistinctAccordingToProposalContract publicAgentActionChannel
      (publicRequirementFamily.requiredProposal
        left.requirement left.context)
      (publicRequirementFamily.requiredProposal
        right.requirement right.context)) :
    DistinctAccordingToActionContract publicAgentActionChannel
      (publicAction left).request (publicAction right).request := by
  rw [public_action_request_exact left, public_action_request_exact right]
  exact publicAgentActionChannel.preserves_required_distinction distinct

theorem public_action_collisions_are_exactly_permitted
    (left right : PublicRequirementInput) :
    CollisionPermittedByProposalContract publicAgentActionChannel
      (publicRequirementFamily.requiredProposal
        left.requirement left.context)
      (publicRequirementFamily.requiredProposal
        right.requirement right.context) ↔
      (publicAction left).request = (publicAction right).request := by
  rw [public_action_request_exact left, public_action_request_exact right]
  exact publicAgentActionChannel.collision_characterized

theorem public_scope_zero_direct_request :
    (publicAction ⟨.scopeZero, .direct⟩).request = .advance 0 :=
  public_action_request_exact ⟨.scopeZero, .direct⟩

theorem public_scope_one_direct_request :
    (publicAction ⟨.scopeOne, .direct⟩).request = .advance 1 :=
  public_action_request_exact ⟨.scopeOne, .direct⟩

theorem public_scope_zero_reversed_request :
    (publicAction ⟨.scopeZero, .reversed⟩).request = .advance 1 :=
  public_action_request_exact ⟨.scopeZero, .reversed⟩

theorem public_contextual_action_requests_distinct :
    (publicAction ⟨.scopeZero, .direct⟩).request ≠
      (publicAction ⟨.scopeZero, .reversed⟩).request := by
  rw [public_scope_zero_direct_request, public_scope_zero_reversed_request]
  intro impossible
  cases impossible

theorem public_action_requests_distinct :
    (publicAction ⟨.scopeZero, .direct⟩).request ≠
      (publicAction ⟨.scopeOne, .direct⟩).request := by
  rw [public_scope_zero_direct_request, public_scope_one_direct_request]
  intro impossible
  cases impossible

theorem public_effect_exact (input : PublicRequirementInput) :
    ((publicEffect input).successor, (publicEffect input).event) =
      Agent.executeInput publicActionMemory (publicAction input).request :=
  (publicEffect input).effect_exact

theorem public_scope_zero_direct_effect_message :
    (publicEffect ⟨.scopeZero, .direct⟩).event.message = .advanced 0 := by
  rw [(publicEffect ⟨.scopeZero, .direct⟩).eventExact]
  change (Agent.executeInput publicActionMemory (.advance 0)).2.message = _
  rfl

theorem public_scope_one_direct_effect_message :
    (publicEffect ⟨.scopeOne, .direct⟩).event.message = .advanced 1 := by
  rw [(publicEffect ⟨.scopeOne, .direct⟩).eventExact]
  change (Agent.executeInput publicActionMemory (.advance 1)).2.message = _
  rfl

theorem public_scope_zero_reversed_effect_message :
    (publicEffect ⟨.scopeZero, .reversed⟩).event.message = .advanced 1 := by
  rw [(publicEffect ⟨.scopeZero, .reversed⟩).eventExact]
  change (Agent.executeInput publicActionMemory (.advance 1)).2.message = _
  rfl

theorem public_contextual_effects_distinct :
    (publicEffect ⟨.scopeZero, .direct⟩).event ≠
      (publicEffect ⟨.scopeZero, .reversed⟩).event := by
  intro same
  have messages := congrArg Agent.Event.message same
  rw [public_scope_zero_direct_effect_message,
    public_scope_zero_reversed_effect_message] at messages
  cases messages

theorem public_effects_distinct :
    (publicEffect ⟨.scopeZero, .direct⟩).event ≠
      (publicEffect ⟨.scopeOne, .direct⟩).event := by
  intro same
  have messages := congrArg Agent.Event.message same
  rw [public_scope_zero_direct_effect_message, public_scope_one_direct_effect_message] at messages
  cases messages

def publicInteractionHistory (memory : Agent.Memory)
    (inputs : List PublicRequirementInput) :
    InteractionHistory publicRequirementIncorporation
      publicRequirementSignalTransformation publicAgentActionChannel memory inputs :=
  executeInteractions publicRequirementIncorporation
    publicRequirementSignalTransformation publicAgentActionChannel memory inputs

def publicFiniteInteractionHistory (inputs : List PublicRequirementInput) :
    InteractionHistory publicRequirementIncorporation
      publicRequirementSignalTransformation publicAgentActionChannel
      publicActionMemory inputs :=
  publicInteractionHistory publicActionMemory inputs

theorem public_finite_continuation_aligned
    (inputs : List PublicRequirementInput) :
    (publicFiniteInteractionHistory inputs).requests =
      requiredRequests publicAgentActionChannel inputs :=
  finite_continuation_aligned publicRequirementIncorporation
    publicRequirementSignalTransformation publicAgentActionChannel
    publicActionMemory inputs

theorem public_finite_continuation_execution_exact
    (inputs : List PublicRequirementInput) :
    ((publicFiniteInteractionHistory inputs).finalMemory,
      (publicFiniteInteractionHistory inputs).events) =
      Agent.executeRequests publicActionMemory
        (requiredRequests publicAgentActionChannel inputs) :=
  finite_continuation_execution_exact publicRequirementIncorporation
    publicRequirementSignalTransformation publicAgentActionChannel
    publicActionMemory inputs

theorem public_head_horizon_independent
    (input : PublicRequirementInput)
    (left right : List PublicRequirementInput) :
    (publicFiniteInteractionHistory (input :: left)).headRequest =
      (publicFiniteInteractionHistory (input :: right)).headRequest :=
  head_horizon_independent publicRequirementIncorporation
    publicRequirementSignalTransformation publicAgentActionChannel
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

def publicReconfigurationSourcePort : Fin 3 := ⟨0, by decide⟩
def publicReconfigurationRequirementPort : Fin 3 := ⟨1, by decide⟩
def publicReconfigurationAuthorizationPort : Fin 3 := ⟨2, by decide⟩
def publicReconfigurationProposalOutput : Fin 2 := ⟨0, by decide⟩
def publicReconfigurationOutput : Fin 2 := ⟨1, by decide⟩

def publicReconfigurationCodeInputs
    (sourceCode requirementCode authorizationCode : Activation) :
    SizedActivations 3 :=
  ((SizedActivations.snoc SizedActivations.empty sourceCode).snoc
    requirementCode).snoc authorizationCode

def publicReconfigurationInputs (source : Bool)
    (next : PublicRequirementInput) (authorizationCode : Activation) :
    SizedActivations 3 :=
  publicReconfigurationCodeInputs (publicBoolCode source)
    (publicRequirementCode next.requirement next.context) authorizationCode

def publicReconfigurationProposalNeuron : NeuronSpec 3 0 :=
  { inputs :=
      [{ source := .receivedInput publicReconfigurationSourcePort,
          weight := 1 },
       { source := .receivedInput publicReconfigurationRequirementPort,
          weight := 2 },
       { source := .receivedInput publicReconfigurationAuthorizationPort,
          weight := 1 }]
    bias := 0
    threshold := ⟨7⟩ }

def publicReconfigurationCombinationNeuron : NeuronSpec 3 1 :=
  { inputs :=
      [{ source := .receivedInput publicReconfigurationSourcePort, weight := 1 },
       { source := .receivedInput publicReconfigurationRequirementPort, weight := 1 },
       { source := .receivedInput publicReconfigurationAuthorizationPort,
          weight := 1 }]
    bias := 0
    threshold := ⟨4⟩ }

def publicReconfigurationProgram : NetworkProgram 3 2 :=
  .extend (.extend .empty publicReconfigurationProposalNeuron)
    publicReconfigurationCombinationNeuron

def publicReconfigurationOutputs : OutputPorts 2 :=
  { sources :=
      [publicReconfigurationProposalOutput, publicReconfigurationOutput]
    nonempty := by intro impossible; cases impossible }

def publicReconfigurationProposalOutputPort :
    Fin publicReconfigurationOutputs.sources.length :=
  ⟨0, by decide⟩

def publicReconfigurationSystem (source : Bool)
    (next : PublicRequirementInput) (authorizationCode : Activation) :
    NativeSystem PublicRequirementInput Bool :=
  { inputCount := 3
    producedCount := 2
    encode := fun _ => publicReconfigurationInputs source next authorizationCode
    program := publicReconfigurationProgram
    outputs := publicReconfigurationOutputs
    decode := decodePublicRequirement }

def proposalFromRun
    (system : NativeSystem PublicRequirementInput Bool)
    (run : NativeRun system.program) : Bool :=
  system.decode (readOutputs system.outputs run.activations)

def publicReconfigurationPermissionVariable : PublicRequirementCase -> SAT.Var
  | .scopeZero => 0
  | .scopeOne => 1

def publicReconfigurationAuthorizationCode
    (next : PublicRequirementInput)
    (permission : ReconfigurationPermission publicRequirementFamily
      publicReconfigurationPermissionVariable next) : Activation :=
  Int.ofNat (permission.position + 1)

def publicReconfigurationBuilder :
    ReconfigurationBuilder publicRequirementFamily where
  permissionVariable
    | .scopeZero => publicReconfigurationPermissionVariable .scopeZero
    | .scopeOne => publicReconfigurationPermissionVariable .scopeOne
  sourceCode := publicBoolCode
  requirementCode := publicRequirementCode
  authorizationCode := publicReconfigurationAuthorizationCode
  build := fun sourceSystem run next authorization =>
    publicReconfigurationSystem (proposalFromRun sourceSystem run) next
      (publicReconfigurationAuthorizationCode next
        authorization.admission.permission)

def publicReconfigurationPermission (next : PublicRequirementInput) :
    Resources.Ref
      (publicRequirementFamily.received next.requirement).realizedScope
      (publicReconfigurationBuilder.permissionVariable next.requirement) := by
  cases next with
  | mk requirement context =>
      cases requirement <;> cases context <;> exact .here

def publicReconfigurationAdmission (next : PublicRequirementInput) :
    AdmittedReconfigurationPermission publicRequirementFamily
      publicReconfigurationBuilder.permissionVariable next :=
  admitReconfigurationPermission (publicReconfigurationPermission next) (by
    cases next with
    | mk requirement context =>
      cases requirement <;> cases context <;> rfl)

def publicReconfigurationAuthorization (next : PublicRequirementInput) :
    IncorporatedReconfigurationPermission publicRequirementFamily
      publicReconfigurationBuilder.permissionVariable next :=
  incorporateReconfigurationPermission (publicReconfigurationAdmission next)

def publicReconfigurationAuthorizationActivation
    (next : PublicRequirementInput) : Activation :=
  publicReconfigurationBuilder.authorizationCode next
    (publicReconfigurationAuthorization next).admission.permission

def publicReconfigurationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Reconfiguration publicReconfigurationBuilder sourceSystem source next :=
  reconfigure publicReconfigurationBuilder source next
    (publicReconfigurationAuthorization next)

def publicReconfiguration (source next : PublicRequirementInput) :
    Reconfiguration publicReconfigurationBuilder publicRequirementSystem
      source next :=
  publicReconfigurationFrom publicRequirementSystem source next

def publicReconfigurationSourceEdgeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    EffectiveReadsFrom
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (.receivedInput publicReconfigurationSourcePort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .executedEdge publicReconfigurationProposalOutput
    { source := .receivedInput publicReconfigurationSourcePort, weight := 1 }
    (by exact List.Mem.head _)
    (by decide)

def publicReconfigurationSourceEdge (source next : PublicRequirementInput) :
    EffectiveReadsFrom ((publicReconfiguration source next).targetSystem.run next)
      (.receivedInput publicReconfigurationSourcePort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  publicReconfigurationSourceEdgeFrom publicRequirementSystem source next

def publicReconfigurationRequirementEdgeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    EffectiveReadsFrom
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (.receivedInput publicReconfigurationRequirementPort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .executedEdge publicReconfigurationProposalOutput
    { source := .receivedInput publicReconfigurationRequirementPort, weight := 2 }
    (by exact List.Mem.tail _ (List.Mem.head _))
    (by decide)

def publicReconfigurationRequirementEdge (source next : PublicRequirementInput) :
    EffectiveReadsFrom ((publicReconfiguration source next).targetSystem.run next)
      (.receivedInput publicReconfigurationRequirementPort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  publicReconfigurationRequirementEdgeFrom publicRequirementSystem source next

def publicReconfigurationAuthorizationEdgeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    EffectiveReadsFrom
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (.receivedInput publicReconfigurationAuthorizationPort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .executedEdge publicReconfigurationProposalOutput
    { source := .receivedInput publicReconfigurationAuthorizationPort,
      weight := 1 }
    (by
      exact List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))
    (by decide)

def publicReconfigurationAuthorizationEdge
    (source next : PublicRequirementInput) :
    EffectiveReadsFrom ((publicReconfiguration source next).targetSystem.run next)
      (.receivedInput publicReconfigurationAuthorizationPort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  publicReconfigurationAuthorizationEdgeFrom publicRequirementSystem source next

def publicReconfigurationSourceReplacement
    (next : PublicRequirementInput) : Activation :=
  match next with
  | ⟨.scopeZero, .direct⟩ => 2
  | ⟨.scopeZero, .reversed⟩ => -1
  | ⟨.scopeOne, .direct⟩ => -1
  | ⟨.scopeOne, .reversed⟩ => 2

def publicReconfigurationRequirementReplacement
    (next : PublicRequirementInput) : Activation :=
  match next with
  | ⟨.scopeZero, .direct⟩ => 3
  | ⟨.scopeZero, .reversed⟩ => 2
  | ⟨.scopeOne, .direct⟩ => 2
  | ⟨.scopeOne, .reversed⟩ => 3

def publicReconfigurationAuthorizationReplacement
    (next : PublicRequirementInput) : Activation :=
  match next with
  | ⟨.scopeZero, .direct⟩ => 3
  | ⟨.scopeZero, .reversed⟩ => -1
  | ⟨.scopeOne, .direct⟩ => -1
  | ⟨.scopeOne, .reversed⟩ => 3

def publicReconfigurationSourceInterventionAt
    (sourceProposal : Bool) (next : PublicRequirementInput) :
    Intervention ((publicReconfigurationSystem sourceProposal next
      (publicReconfigurationAuthorizationActivation next)).run next) :=
  { focus := .input publicReconfigurationSourcePort
    replacement := publicReconfigurationSourceReplacement next
    changesValue := by
      cases sourceProposal <;>
      cases next with
      | mk requirement context =>
          cases requirement <;> cases context <;> decide }

def publicReconfigurationSourceInterventionFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Intervention
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run
        next) :=
  publicReconfigurationSourceInterventionAt
    (proposalFromRun sourceSystem (sourceSystem.run source)) next

def publicReconfigurationRequirementInterventionAt
    (sourceProposal : Bool) (next : PublicRequirementInput) :
    Intervention ((publicReconfigurationSystem sourceProposal next
      (publicReconfigurationAuthorizationActivation next)).run next) :=
  { focus := .input publicReconfigurationRequirementPort
    replacement := publicReconfigurationRequirementReplacement next
    changesValue := by
      cases sourceProposal <;>
      cases next with
      | mk requirement context =>
          cases requirement <;> cases context <;> decide }

def publicReconfigurationRequirementInterventionFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Intervention
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run
        next) :=
  publicReconfigurationRequirementInterventionAt
    (proposalFromRun sourceSystem (sourceSystem.run source)) next

def publicReconfigurationAuthorizationInterventionAt
    (sourceProposal : Bool) (next : PublicRequirementInput) :
    Intervention ((publicReconfigurationSystem sourceProposal next
      (publicReconfigurationAuthorizationActivation next)).run next) :=
  { focus := .input publicReconfigurationAuthorizationPort
    replacement := publicReconfigurationAuthorizationReplacement next
    changesValue := by
      cases sourceProposal <;>
      cases next with
      | mk requirement context =>
          cases requirement <;> cases context <;> decide }

def publicReconfigurationAuthorizationInterventionFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    Intervention
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run
        next) :=
  publicReconfigurationAuthorizationInterventionAt
    (proposalFromRun sourceSystem (sourceSystem.run source)) next

theorem publicReconfigurationSourceFocusExactFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    (publicReconfigurationSourceInterventionFrom sourceSystem source next).focusOccurrence =
      (.receivedInput publicReconfigurationSourcePort :
        ActivationOccurrence
          ((publicReconfigurationFrom sourceSystem source next).targetSystem.run
            next)) :=
  rfl

theorem publicReconfigurationRequirementFocusExactFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    (publicReconfigurationRequirementInterventionFrom
      sourceSystem source next).focusOccurrence =
      (.receivedInput publicReconfigurationRequirementPort :
        ActivationOccurrence
          ((publicReconfigurationFrom sourceSystem source next).targetSystem.run
            next)) :=
  rfl

theorem publicReconfigurationAuthorizationFocusExactFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    (publicReconfigurationAuthorizationInterventionFrom
      sourceSystem source next).focusOccurrence =
      (.receivedInput publicReconfigurationAuthorizationPort :
        ActivationOccurrence
          ((publicReconfigurationFrom sourceSystem source next).targetSystem.run
            next)) :=
  rfl

theorem publicReconfigurationSourceOutputChangedFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    OccurrenceChanged
      (publicReconfigurationSourceInterventionFrom sourceSystem source next)
      (.neuronOutput publicReconfigurationProposalOutput) := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change OccurrenceChanged
    (publicReconfigurationSourceInterventionAt sourceProposal next)
    (.neuronOutput publicReconfigurationProposalOutput)
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationRequirementOutputChangedFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    OccurrenceChanged
      (publicReconfigurationRequirementInterventionFrom sourceSystem source next)
      (.neuronOutput publicReconfigurationProposalOutput) := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change OccurrenceChanged
    (publicReconfigurationRequirementInterventionAt sourceProposal next)
    (.neuronOutput publicReconfigurationProposalOutput)
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationAuthorizationOutputChangedFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    OccurrenceChanged
      (publicReconfigurationAuthorizationInterventionFrom sourceSystem source next)
      (.neuronOutput publicReconfigurationProposalOutput) := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change OccurrenceChanged
    (publicReconfigurationAuthorizationInterventionAt sourceProposal next)
    (.neuronOutput publicReconfigurationProposalOutput)
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

def publicReconfigurationSourcePropagationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    NontrivialExecutedChangePath
      (publicReconfigurationSourceInterventionFrom sourceSystem source next)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .step .origin
    (publicReconfigurationSourceEdgeFrom sourceSystem source next)
    (publicReconfigurationSourceOutputChangedFrom sourceSystem source next)

def publicReconfigurationRequirementPropagationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    NontrivialExecutedChangePath
      (publicReconfigurationRequirementInterventionFrom sourceSystem source next)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .step .origin
    (publicReconfigurationRequirementEdgeFrom sourceSystem source next)
    (publicReconfigurationRequirementOutputChangedFrom sourceSystem source next)

def publicReconfigurationAuthorizationPropagationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    NontrivialExecutedChangePath
      (publicReconfigurationAuthorizationInterventionFrom sourceSystem source next)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .step .origin
    (publicReconfigurationAuthorizationEdgeFrom sourceSystem source next)
    (publicReconfigurationAuthorizationOutputChangedFrom sourceSystem source next)

theorem publicReconfigurationSourceTargetChangeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ChangesTarget
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (publicReconfigurationSourceInterventionFrom sourceSystem source next)
      (publicReconfigurationFrom sourceSystem source next).targetSystem.outputs := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change ChangesTarget
    ((publicReconfigurationSystem sourceProposal next
      (publicReconfigurationAuthorizationActivation next)).run next)
    (publicReconfigurationSourceInterventionAt sourceProposal next)
    publicReconfigurationOutputs
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationRequirementTargetChangeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ChangesTarget
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (publicReconfigurationRequirementInterventionFrom sourceSystem source next)
      (publicReconfigurationFrom sourceSystem source next).targetSystem.outputs := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change ChangesTarget
    ((publicReconfigurationSystem sourceProposal next
      (publicReconfigurationAuthorizationActivation next)).run next)
    (publicReconfigurationRequirementInterventionAt sourceProposal next)
    publicReconfigurationOutputs
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationAuthorizationTargetChangeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ChangesTarget
      ((publicReconfigurationFrom sourceSystem source next).targetSystem.run next)
      (publicReconfigurationAuthorizationInterventionFrom sourceSystem source next)
      (publicReconfigurationFrom sourceSystem source next).targetSystem.outputs := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change ChangesTarget
    ((publicReconfigurationSystem sourceProposal next
      (publicReconfigurationAuthorizationActivation next)).run next)
    (publicReconfigurationAuthorizationInterventionAt sourceProposal next)
    publicReconfigurationOutputs
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationSourceProposalChangeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ChangesProposal
      (publicReconfigurationFrom sourceSystem source next).targetSystem next
      (publicReconfigurationSourceInterventionFrom sourceSystem source next) := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change ChangesProposal (publicReconfigurationSystem sourceProposal next
    (publicReconfigurationAuthorizationActivation next)) next
    (publicReconfigurationSourceInterventionAt sourceProposal next)
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationRequirementProposalChangeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ChangesProposal
      (publicReconfigurationFrom sourceSystem source next).targetSystem next
      (publicReconfigurationRequirementInterventionFrom sourceSystem source next) := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change ChangesProposal (publicReconfigurationSystem sourceProposal next
    (publicReconfigurationAuthorizationActivation next)) next
    (publicReconfigurationRequirementInterventionAt sourceProposal next)
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

theorem publicReconfigurationAuthorizationProposalChangeFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ChangesProposal
      (publicReconfigurationFrom sourceSystem source next).targetSystem next
      (publicReconfigurationAuthorizationInterventionFrom sourceSystem source next) := by
  let sourceProposal :=
    proposalFromRun sourceSystem (sourceSystem.run source)
  change ChangesProposal (publicReconfigurationSystem sourceProposal next
    (publicReconfigurationAuthorizationActivation next)) next
    (publicReconfigurationAuthorizationInterventionAt sourceProposal next)
  cases sourceProposal <;>
    cases next with
    | mk requirement context =>
        cases requirement <;> cases context <;>
          exact { different := by decide }

def publicReconfigurationSourceCausalRoleFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    CausalRole
      (publicReconfigurationFrom sourceSystem source next).targetSystem next
      (.receivedInput publicReconfigurationSourcePort) :=
  { intervention :=
      publicReconfigurationSourceInterventionFrom sourceSystem source next
    focusExact :=
      publicReconfigurationSourceFocusExactFrom sourceSystem source next
    output := publicReconfigurationProposalOutputPort
    propagation :=
      publicReconfigurationSourcePropagationFrom sourceSystem source next
    targetChange :=
      publicReconfigurationSourceTargetChangeFrom sourceSystem source next
    proposalChange :=
      publicReconfigurationSourceProposalChangeFrom sourceSystem source next }

def publicReconfigurationRequirementCausalRoleFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    CausalRole
      (publicReconfigurationFrom sourceSystem source next).targetSystem next
      (.receivedInput publicReconfigurationRequirementPort) :=
  { intervention :=
      publicReconfigurationRequirementInterventionFrom sourceSystem source next
    focusExact :=
      publicReconfigurationRequirementFocusExactFrom sourceSystem source next
    output := publicReconfigurationProposalOutputPort
    propagation :=
      publicReconfigurationRequirementPropagationFrom sourceSystem source next
    targetChange :=
      publicReconfigurationRequirementTargetChangeFrom sourceSystem source next
    proposalChange :=
      publicReconfigurationRequirementProposalChangeFrom sourceSystem source next }

def publicReconfigurationAuthorizationCausalRoleFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    CausalRole
      (publicReconfigurationFrom sourceSystem source next).targetSystem next
      (.receivedInput publicReconfigurationAuthorizationPort) :=
  { intervention :=
      publicReconfigurationAuthorizationInterventionFrom sourceSystem source next
    focusExact :=
      publicReconfigurationAuthorizationFocusExactFrom sourceSystem source next
    output := publicReconfigurationProposalOutputPort
    propagation :=
      publicReconfigurationAuthorizationPropagationFrom sourceSystem source next
    targetChange :=
      publicReconfigurationAuthorizationTargetChangeFrom sourceSystem source next
    proposalChange :=
      publicReconfigurationAuthorizationProposalChangeFrom sourceSystem source next }

/-- The complete output representation produced by the reconfigured program
from the three transported input values.  Its first component is the proposal
representation; its second component is the executed combination of the
source proposal, the new requirement signal, and the incorporated
authorization. -/
def publicReconfigurationCombinedOutputs
    (sourceCode requirementCode authorizationCode : Activation) :
    List Activation :=
  readOutputs publicReconfigurationOutputs
    (executeProgram publicReconfigurationProgram
      (publicReconfigurationCodeInputs sourceCode requirementCode
        authorizationCode))

theorem publicReconfigurationSourceAuthorizationPortsDistinct :
    publicReconfigurationSourcePort ≠
      publicReconfigurationAuthorizationPort := by
  decide

theorem publicReconfigurationRequirementAuthorizationPortsDistinct :
    publicReconfigurationRequirementPort ≠
      publicReconfigurationAuthorizationPort := by
  decide

theorem publicReconfigurationAuthorizationExactFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ((publicReconfigurationFrom sourceSystem source next).targetSystem.encode
      next).read publicReconfigurationAuthorizationPort =
        publicReconfigurationBuilder.authorizationCode next
          (publicReconfigurationFrom sourceSystem source next).permission := by
  cases next with
  | mk nextRequirement nextContext =>
    cases nextRequirement <;> cases nextContext <;> rfl

def publicRequiredMechanismTransportFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    RequiredMechanismTransport
      (publicReconfigurationFrom sourceSystem source next) where
  sourcePort := publicReconfigurationSourcePort
  requirementPort := publicReconfigurationRequirementPort
  authorizationPort := publicReconfigurationAuthorizationPort
  portsDistinct := by
    intro same
    have values := congrArg Fin.val same
    cases values
  sourceAuthorizationDistinct := by
    exact publicReconfigurationSourceAuthorizationPortsDistinct
  requirementAuthorizationDistinct := by
    exact publicReconfigurationRequirementAuthorizationPortsDistinct
  sourceExact := by
    cases source with
    | mk sourceRequirement sourceContext =>
      cases sourceRequirement <;> cases sourceContext <;> rfl
  requirementExact := by
    cases next with
    | mk nextRequirement nextContext =>
      cases nextRequirement <;> cases nextContext <;> rfl
  authorizationExact :=
    publicReconfigurationAuthorizationExactFrom sourceSystem source next
  sourceRole :=
    publicReconfigurationSourceCausalRoleFrom sourceSystem source next
  requirementRole :=
    publicReconfigurationRequirementCausalRoleFrom sourceSystem source next
  authorizationRole :=
    publicReconfigurationAuthorizationCausalRoleFrom sourceSystem source next

def publicReconfiguredProposalDerivationFrom
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    ReconfiguredProposalDerivation
      (publicReconfigurationFrom sourceSystem source next)
      (publicRequiredMechanismTransportFrom sourceSystem source next) where
  combine := publicReconfigurationCombinedOutputs
  combinationExecuted := by
    cases next with
    | mk nextRequirement nextContext =>
      cases nextRequirement <;> cases nextContext <;>
        cases sourceResult :
          proposalFromRun sourceSystem (sourceSystem.run source) <;> rfl
  decoderExact := by
    generalize sourceResult : sourceSystem.proposal source = sourceProposal
    cases sourceProposal <;>
    cases next with
    | mk nextRequirement nextContext =>
      cases nextRequirement <;> cases nextContext <;> rfl

/-- The proposal consumed as source material is exactly the decoder applied to
the output of the actual source run. -/
theorem public_source_proposal_is_exact_execution
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source : PublicRequirementInput) :
    sourceSystem.proposal source =
      proposalFromRun sourceSystem (sourceSystem.run source) :=
  rfl

/-- The combined representation in the derivation is the output vector of the
target program executed on the three values transported into its input ports. -/
theorem public_reconfiguration_combination_executed_from
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    (publicReconfigurationFrom sourceSystem source next).targetSystem.outputValues
        next =
      publicReconfigurationCombinedOutputs
        (((publicReconfigurationFrom sourceSystem source next).targetSystem.encode
          next).read
            (publicRequiredMechanismTransportFrom sourceSystem source next).sourcePort)
        (((publicReconfigurationFrom sourceSystem source next).targetSystem.encode
          next).read
            (publicRequiredMechanismTransportFrom sourceSystem source next).requirementPort)
        (((publicReconfigurationFrom sourceSystem source next).targetSystem.encode
          next).read
            (publicRequiredMechanismTransportFrom sourceSystem source next).authorizationPort) :=
  (publicReconfiguredProposalDerivationFrom sourceSystem source next).combinationExecuted

/-- C4: final proposal exactness is not stored in the transport or the
certificate.  It is obtained by the generic derivation theorem from the source
run code, the requirement code, their exact internal transports, the executed
combination and the target decoder equation. -/
theorem public_reconfigured_proposal_exact_from_derivation
    (sourceSystem : NativeSystem PublicRequirementInput Bool)
    (source next : PublicRequirementInput) :
    (publicReconfigurationFrom sourceSystem source next).targetSystem.proposal
        next =
      publicRequirementFamily.requiredProposal
        next.requirement next.context :=
  (publicReconfiguredProposalDerivationFrom sourceSystem source next).proposal_exact

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
    (publicReconfiguredProposalDerivationFrom sourceSystem source next)

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
      publicRequirementCode next.requirement next.context :=
  (publicRequiredMechanismTransport source next).requirementExact

theorem public_reconfiguration_reads_source_distinction
    (next : PublicRequirementInput) :
    ((publicReconfiguration ⟨.scopeZero, .direct⟩ next).targetSystem.encode next).read
        publicReconfigurationSourcePort ≠
      ((publicReconfiguration ⟨.scopeOne, .direct⟩ next).targetSystem.encode next).read
        publicReconfigurationSourcePort := by
  rw [public_reconfiguration_source_exact, public_reconfiguration_source_exact]
  intro impossible
  cases impossible

theorem public_reconfiguration_reads_requirement_distinction
    (source : PublicRequirementInput) :
    ((publicReconfiguration source ⟨.scopeZero, .direct⟩).targetSystem.encode
        ⟨.scopeZero, .direct⟩).read publicReconfigurationRequirementPort ≠
      ((publicReconfiguration source ⟨.scopeOne, .direct⟩).targetSystem.encode
        ⟨.scopeOne, .direct⟩).read publicReconfigurationRequirementPort := by
  rw [public_reconfiguration_requirement_exact,
    public_reconfiguration_requirement_exact]
  exact (by decide : (2 : Activation) ≠ 3)

theorem public_reconfiguration_reads_context_distinction
    (source : PublicRequirementInput) :
    ((publicReconfiguration source
        ⟨.scopeZero, .direct⟩).targetSystem.encode
        ⟨.scopeZero, .direct⟩).read publicReconfigurationRequirementPort ≠
      ((publicReconfiguration source
        ⟨.scopeZero, .reversed⟩).targetSystem.encode
        ⟨.scopeZero, .reversed⟩).read
          publicReconfigurationRequirementPort := by
  rw [public_reconfiguration_requirement_exact,
    public_reconfiguration_requirement_exact]
  exact public_context_codes_distinct

/-- With the next requirement held at `scopeZero`, changing only the proposal
produced by the source run changes the executed output of the reconfigured
mechanism.  The source port is therefore not merely stored. -/
theorem public_reconfiguration_source_changes_output :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeOne, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ := by
  intro impossible
  cases impossible

/-- With the source proposal held at `false`, changing only the next
requirement changes the executed output of the reconfigured mechanism.  The
requirement port is therefore not merely stored. -/
theorem public_reconfiguration_requirement_changes_output :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeOne, .direct⟩).targetSystem.outputValues
        ⟨.scopeOne, .direct⟩ := by
  intro impossible
  cases impossible

theorem public_reconfiguration_context_changes_output :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .reversed⟩).targetSystem.outputValues
        ⟨.scopeZero, .reversed⟩ := by
  intro impossible
  cases impossible

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.publicAgentActionChannel
#print axioms ConstitutiveSearch.NeuralAgent.public_required_proposal_distinction
#print axioms ConstitutiveSearch.NeuralAgent.public_required_action_distinction
#print axioms ConstitutiveSearch.NeuralAgent.public_collision_permission_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicActionMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicAction
#print axioms ConstitutiveSearch.NeuralAgent.publicEffect
#print axioms ConstitutiveSearch.NeuralAgent.public_action_request_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_actions_preserve_required_proposal_distinction
#print axioms ConstitutiveSearch.NeuralAgent.public_action_collisions_are_exactly_permitted
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_zero_direct_request
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_one_direct_request
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_zero_reversed_request
#print axioms ConstitutiveSearch.NeuralAgent.public_contextual_action_requests_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_action_requests_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_effect_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_zero_direct_effect_message
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_one_direct_effect_message
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_zero_reversed_effect_message
#print axioms ConstitutiveSearch.NeuralAgent.public_contextual_effects_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_effects_distinct
#print axioms ConstitutiveSearch.NeuralAgent.publicInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.publicFiniteInteractionHistory
#print axioms ConstitutiveSearch.NeuralAgent.public_finite_continuation_aligned
#print axioms ConstitutiveSearch.NeuralAgent.public_finite_continuation_execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_head_horizon_independent
#print axioms ConstitutiveSearch.NeuralAgent.public_continuation_head_is_action
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationBuilder
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAdmission
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorization
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationActivation
#print axioms ConstitutiveSearch.NeuralAgent.proposalFromRun
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationCodeInputs
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationProposalNeuron
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceEdgeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementEdgeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationEdgeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceInterventionAt
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceInterventionFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementInterventionAt
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementInterventionFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationInterventionFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceOutputChangedFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementOutputChangedFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationOutputChangedFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourcePropagationFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementPropagationFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationPropagationFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceTargetChangeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementTargetChangeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationTargetChangeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceProposalChangeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementProposalChangeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationProposalChangeFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceCausalRoleFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementCausalRoleFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationCausalRoleFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationCombinedOutputs
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationSourceAuthorizationPortsDistinct
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationRequirementAuthorizationPortsDistinct
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfigurationAuthorizationExactFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicRequiredMechanismTransportFrom
#print axioms ConstitutiveSearch.NeuralAgent.publicRequiredMechanismTransport
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredProposalDerivationFrom
#print axioms ConstitutiveSearch.NeuralAgent.public_source_proposal_is_exact_execution
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_combination_executed_from
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfigured_proposal_exact_from_derivation
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
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_reads_context_distinction
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_source_changes_output
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_requirement_changes_output
#print axioms ConstitutiveSearch.NeuralAgent.public_reconfiguration_context_changes_output
/- AXIOM_AUDIT_END -/
