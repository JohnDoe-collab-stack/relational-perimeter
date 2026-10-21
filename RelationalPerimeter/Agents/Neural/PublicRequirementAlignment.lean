import RelationalPerimeter.Agents.Neural.RequirementSensitivity

/-!
# A closed requirement-and-context-sensitive native instance

Two positively received requirements and two contexts are run through the same
one-neuron program.  The input signal jointly encodes the requirement and the
context.  Holding either component fixed while changing the other changes the
encoded signal and the required proposal.  Each joint signal is causally
incorporated through the executed edge.  The executed neuron transforms the
received codes `2` and `3` into the distinct terminal representations `0` and
`1`; the decoder then produces the proposal required by that exact pair.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

inductive PublicRequirementCase where
  | scopeZero
  | scopeOne

inductive PublicRequirementContext where
  | direct
  | reversed

def singletonRequirement (var : SAT.Var) : Agent.Requirement :=
  (Agent.receive [var]).get (by rfl)

def publicRequirementFamily :
    RequirementFamily PublicRequirementCase PublicRequirementContext Bool where
  received
    | .scopeZero => singletonRequirement 0
    | .scopeOne => singletonRequirement 1
  requiredProposal
    | .scopeZero, .direct => false
    | .scopeZero, .reversed => true
    | .scopeOne, .direct => true
    | .scopeOne, .reversed => false

/-- The public case names describe the exact scope of the received
requirement.  They do not claim an admission or refusal before the future
contract has executed its decision. -/
theorem public_scope_zero_received_exact :
    publicRequirementFamily.received .scopeZero = singletonRequirement 0 :=
  rfl

theorem public_scope_one_received_exact :
    publicRequirementFamily.received .scopeOne = singletonRequirement 1 :=
  rfl

theorem public_scope_zero_scope_exact :
    (publicRequirementFamily.received .scopeZero).scope = [0] :=
  rfl

theorem public_scope_one_scope_exact :
    (publicRequirementFamily.received .scopeOne).scope = [1] :=
  rfl

/-- `direct` reads the scope index as its Boolean proposal, whereas
`reversed` computes its complement.  These names therefore describe the
actual proposal table rather than suggesting an admission decision. -/
theorem public_direct_proposals_exact :
    publicRequirementFamily.requiredProposal .scopeZero .direct = false ∧
      publicRequirementFamily.requiredProposal .scopeOne .direct = true :=
  ⟨rfl, rfl⟩

theorem public_reversed_proposals_exact :
    publicRequirementFamily.requiredProposal .scopeZero .reversed = true ∧
      publicRequirementFamily.requiredProposal .scopeOne .reversed = false :=
  ⟨rfl, rfl⟩

abbrev PublicRequirementInput := RequirementInput publicRequirementFamily

def publicRequirementPort : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩
def publicRequirementOutput : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩

def publicRequirementCode :
    PublicRequirementCase -> PublicRequirementContext -> Activation
  | .scopeZero, .direct => 2
  | .scopeZero, .reversed => 3
  | .scopeOne, .direct => 3
  | .scopeOne, .reversed => 2

def encodePublicRequirement (input : PublicRequirementInput) :
    SizedActivations 1 :=
  SizedActivations.snoc SizedActivations.empty
    (publicRequirementCode input.requirement input.context)

def publicRequirementNeuron : NeuronSpec 1 0 :=
  { inputs := [{ source := .receivedInput publicRequirementPort, weight := 1 }]
    bias := 0
    threshold := ⟨3⟩ }

def publicRequirementProgram : NetworkProgram 1 1 :=
  .extend .empty publicRequirementNeuron

def publicRequirementOutputs : OutputPorts 1 :=
  { sources := [publicRequirementOutput]
    nonempty := by intro impossible; cases impossible }

def publicRequirementOutputPort :
    Fin publicRequirementOutputs.sources.length :=
  ⟨0, by decide⟩

def decodePublicRequirement : List Activation -> Bool
  | [] => false
  | value :: _ => decide (value ≠ 0)

def publicRequirementSystem : NativeSystem PublicRequirementInput Bool :=
  { inputCount := 1
    producedCount := 1
    encode := encodePublicRequirement
    program := publicRequirementProgram
    outputs := publicRequirementOutputs
    decode := decodePublicRequirement }

theorem publicRequirementInputExact (input : PublicRequirementInput) :
    (publicRequirementSystem.encode input).read publicRequirementPort =
      publicRequirementCode input.requirement input.context :=
  SizedActivations.read_snoc_last SizedActivations.empty _

theorem publicRequirementCodeReflectsCase
    (one two : PublicRequirementCase)
    (context : PublicRequirementContext)
    (same : publicRequirementCode one context =
      publicRequirementCode two context) :
    one = two := by
  cases one <;> cases two <;> cases context
  · rfl
  · rfl
  · exact False.elim ((by decide : (2 : Nat) ≠ 3) (Int.ofNat.inj same))
  · exact False.elim ((by decide : (3 : Nat) ≠ 2) (Int.ofNat.inj same))
  · exact False.elim ((by decide : (3 : Nat) ≠ 2) (Int.ofNat.inj same))
  · exact False.elim ((by decide : (2 : Nat) ≠ 3) (Int.ofNat.inj same))
  · rfl
  · rfl

theorem publicRequirementReflecting
    (one two : PublicRequirementCase)
    (context : PublicRequirementContext)
    (same : publicRequirementCode one context =
      publicRequirementCode two context) :
    publicRequirementFamily.received one =
      publicRequirementFamily.received two :=
  congrArg publicRequirementFamily.received
    (publicRequirementCodeReflectsCase one two context same)

def publicRequirementEncoding :
    RequirementEncoding publicRequirementSystem where
  port := publicRequirementPort
  code := publicRequirementCode
  inputExact := publicRequirementInputExact
  requirementReflecting := publicRequirementReflecting

def publicRequirementIntervention
    (input : PublicRequirementInput) :
    Intervention (publicRequirementSystem.run input) :=
  match input with
  | ⟨.scopeZero, .direct⟩ =>
      { focus := .input publicRequirementPort
        replacement := 3
        changesValue := by decide }
  | ⟨.scopeZero, .reversed⟩ =>
      { focus := .input publicRequirementPort
        replacement := 2
        changesValue := by decide }
  | ⟨.scopeOne, .direct⟩ =>
      { focus := .input publicRequirementPort
        replacement := 2
        changesValue := by decide }
  | ⟨.scopeOne, .reversed⟩ =>
      { focus := .input publicRequirementPort
        replacement := 3
        changesValue := by decide }

theorem publicRequirementFocusExact (input : PublicRequirementInput) :
    (publicRequirementIntervention input).focusOccurrence =
      (.receivedInput publicRequirementPort :
        ActivationOccurrence (publicRequirementSystem.run input)) := by
  cases input with
  | mk requirement context => cases requirement <;> cases context <;> rfl

def publicRequirementEdge (input : PublicRequirementInput) :
    EffectiveReadsFrom (publicRequirementSystem.run input)
      (.receivedInput publicRequirementPort)
      (.neuronOutput publicRequirementOutput) :=
  .executedEdge publicRequirementOutput
    { source := .receivedInput publicRequirementPort, weight := 1 }
    (by
      change
        ({ source := .receivedInput publicRequirementPort, weight := 1 } :
          WeightedInput 1 0) ∈
          [{ source := .receivedInput publicRequirementPort, weight := 1 }]
      exact List.Mem.head _)
    (by decide)

theorem publicRequirementOutputChanged (input : PublicRequirementInput) :
    OccurrenceChanged (publicRequirementIntervention input)
      (.neuronOutput publicRequirementOutput) := by
  cases input with
  | mk requirement context =>
      cases requirement <;> cases context <;>
        exact { different := by decide }

def publicRequirementPropagation (input : PublicRequirementInput) :
    NontrivialExecutedChangePath (publicRequirementIntervention input)
      (.neuronOutput publicRequirementOutput) :=
  let edge : EffectiveReadsFrom (publicRequirementSystem.run input)
      (publicRequirementIntervention input).focusOccurrence
      (.neuronOutput publicRequirementOutput) :=
    Eq.mp
      (congrArg
        (fun source => EffectiveReadsFrom
          (publicRequirementSystem.run input) source
          (.neuronOutput publicRequirementOutput))
        (publicRequirementFocusExact input).symm)
      (publicRequirementEdge input)
  .step .origin edge (publicRequirementOutputChanged input)

theorem publicRequirementTargetChange (input : PublicRequirementInput) :
    ChangesTarget (publicRequirementSystem.run input)
      (publicRequirementIntervention input) publicRequirementSystem.outputs := by
  cases input with
  | mk requirement context =>
      cases requirement <;> cases context <;>
        exact { different := by decide }

theorem publicRequirementProposalChange (input : PublicRequirementInput) :
    ChangesProposal publicRequirementSystem input
      (publicRequirementIntervention input) := by
  cases input with
  | mk requirement context =>
      cases requirement <;> cases context <;>
        exact { different := by decide }

def publicRequirementCausalRole (input : PublicRequirementInput) :
    CausalRole publicRequirementSystem input
      (.receivedInput publicRequirementPort) :=
  { intervention := publicRequirementIntervention input
    focusExact := publicRequirementFocusExact input
    output := publicRequirementOutputPort
    propagation := publicRequirementPropagation input
    targetChange := publicRequirementTargetChange input
    proposalChange := publicRequirementProposalChange input }

def publicRequirementIncorporation (input : PublicRequirementInput) :
    RequirementIncorporation publicRequirementEncoding input :=
  { role := publicRequirementCausalRole input }

theorem publicRequirementRoleOutputExact (input : PublicRequirementInput) :
    publicRequirementSystem.outputs.sources.get
        (publicRequirementIncorporation input).role.output =
      publicRequirementOutput := by
  cases input with
  | mk requirement context => cases requirement <;> cases context <;> rfl

def publicRequirementDecoder :
    SingleOutputRequirementDecoder publicRequirementEncoding where
  output := publicRequirementOutput
  portsExact := rfl
  terminalRepresentation
    | .scopeZero, .direct => 0
    | .scopeZero, .reversed => 1
    | .scopeOne, .direct => 1
    | .scopeOne, .reversed => 0
  decodeRepresentation := by
    intro requirement context
    cases requirement <;> cases context <;> rfl

def publicRequirementSignalTransform (value : Activation) : Activation :=
  asActivation (fires ⟨3⟩ value)

def publicRequirementExecutedTransformation (input : PublicRequirementInput) :
    ExecutedSignalTransformation (publicRequirementSystem.run input)
      (.receivedInput publicRequirementPort)
      (.neuronOutput publicRequirementOutput) where
  transform := publicRequirementSignalTransform
  edge := (publicRequirementEdge input).toReadsFrom
  outputExact := by
    cases input with
    | mk requirement context => cases requirement <;> cases context <;> rfl

def publicRequirementSignalPath (input : PublicRequirementInput) :
    RequirementSignalPath publicRequirementEncoding input
      (.neuronOutput publicRequirementOutput)
      (fun value => publicRequirementSignalTransform value) :=
  RequirementSignalPath.step
    (encoding := publicRequirementEncoding)
    (input := input)
    (source := .receivedInput publicRequirementPort)
    (target := .neuronOutput publicRequirementOutput)
    (accumulated := fun value => value)
    (RequirementSignalPath.origin
      (encoding := publicRequirementEncoding) (input := input))
    (publicRequirementExecutedTransformation input)

def publicRequirementSignalTransformation (input : PublicRequirementInput) :
    RequirementSignalTransformation publicRequirementDecoder
      (publicRequirementIncorporation input) := by
  exact
    { roleOutputExact := publicRequirementRoleOutputExact input
      transform := fun value => publicRequirementSignalTransform value
      path := publicRequirementSignalPath input
      terminalExact := by
        cases input with
        | mk requirement context => cases requirement <;> cases context <;> rfl }

/-- The positive C3 witness: the code received by the run is never the
terminal representation consumed by the decoder. -/
theorem publicRequirementTransformationNonidentity
    (input : PublicRequirementInput) :
    publicRequirementEncoding.code input.requirement input.context ≠
      publicRequirementDecoder.terminalRepresentation
        input.requirement input.context := by
  cases input with
  | mk requirement context => cases requirement <;> cases context <;> decide

theorem publicRequirementOccurrencesDiffer
    (input : PublicRequirementInput) :
    (ActivationOccurrence.receivedInput publicRequirementPort :
        ActivationOccurrence (publicRequirementSystem.run input)).value ≠
      (ActivationOccurrence.neuronOutput publicRequirementOutput :
        ActivationOccurrence (publicRequirementSystem.run input)).value := by
  cases input with
  | mk requirement context => cases requirement <;> cases context <;> decide

theorem public_proposal_aligned (input : PublicRequirementInput) :
    publicRequirementSystem.proposal input =
      publicRequirementFamily.requiredProposal
        input.requirement input.context :=
  proposal_aligned (publicRequirementSignalTransformation input)

theorem public_received_requirements_distinct :
    publicRequirementFamily.received .scopeZero ≠
      publicRequirementFamily.received .scopeOne := by
  intro same
  have scopes := congrArg (fun requirement : Agent.Requirement =>
    requirement.scope) same
  change ([0] : List Nat) = [1] at scopes
  have heads : (0 : Nat) = 1 := (List.cons.inj scopes).1
  exact Nat.noConfusion heads

theorem public_required_proposals_distinct :
    publicRequirementFamily.requiredProposal .scopeZero .direct ≠
      publicRequirementFamily.requiredProposal .scopeOne .direct := by
  decide

theorem publicSeparatingRequirements :
    SeparatingRequirements publicRequirementFamily .scopeZero .scopeOne .direct :=
  { receivedDistinct := public_received_requirements_distinct
    requiredDistinct := public_required_proposals_distinct }

theorem public_requirement_codes_distinct :
    publicRequirementEncoding.code .scopeZero .direct ≠
      publicRequirementEncoding.code .scopeOne .direct :=
  separating_requirement_codes publicRequirementEncoding
    publicSeparatingRequirements

theorem public_executed_proposals_distinct :
    publicRequirementSystem.proposal (RequirementInput.mk .scopeZero .direct) ≠
      publicRequirementSystem.proposal (RequirementInput.mk .scopeOne .direct) :=
  separating_executed_proposals publicSeparatingRequirements
    (publicRequirementSignalTransformation
      (RequirementInput.mk .scopeZero .direct))
    (publicRequirementSignalTransformation
      (RequirementInput.mk .scopeOne .direct))

theorem public_contexts_distinct :
    PublicRequirementContext.direct ≠ PublicRequirementContext.reversed := by
  intro same
  cases same

theorem public_contextual_required_proposals_distinct :
    publicRequirementFamily.requiredProposal .scopeZero .direct ≠
      publicRequirementFamily.requiredProposal .scopeZero .reversed := by
  decide

theorem publicSeparatingContexts :
    SeparatingContexts publicRequirementFamily .scopeZero .direct .reversed :=
  { contextsDistinct := public_contexts_distinct
    requiredDistinct := public_contextual_required_proposals_distinct }

theorem public_context_codes_distinct :
    publicRequirementEncoding.code .scopeZero .direct ≠
      publicRequirementEncoding.code .scopeZero .reversed :=
  by decide

theorem public_contextual_executed_inputs_distinct :
    (publicRequirementSystem.run
        (RequirementInput.mk .scopeZero .direct)).inputs.read
        publicRequirementEncoding.port ≠
      (publicRequirementSystem.run
        (RequirementInput.mk .scopeZero .reversed)).inputs.read
        publicRequirementEncoding.port := by
  change publicRequirementEncoding.code .scopeZero .direct ≠
    publicRequirementEncoding.code .scopeZero .reversed
  exact public_context_codes_distinct

theorem public_contextual_executed_proposals_distinct :
    publicRequirementSystem.proposal (RequirementInput.mk .scopeZero .direct) ≠
      publicRequirementSystem.proposal
        (RequirementInput.mk .scopeZero .reversed) :=
  separating_contextual_executed_proposals publicSeparatingContexts
    (publicRequirementSignalTransformation
      (RequirementInput.mk .scopeZero .direct))
    (publicRequirementSignalTransformation
      (RequirementInput.mk .scopeZero .reversed))

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.PublicRequirementCase
#print axioms ConstitutiveSearch.NeuralAgent.PublicRequirementContext
#print axioms ConstitutiveSearch.NeuralAgent.singletonRequirement
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementFamily
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_zero_received_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_one_received_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_zero_scope_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_scope_one_scope_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_direct_proposals_exact
#print axioms ConstitutiveSearch.NeuralAgent.public_reversed_proposals_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSystem
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementInputExact
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementCodeReflectsCase
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementReflecting
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementEncoding
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementIntervention
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementCausalRole
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementIncorporation
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementDecoder
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSignalTransform
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementExecutedTransformation
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSignalPath
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSignalTransformation
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementTransformationNonidentity
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementOccurrencesDiffer
#print axioms ConstitutiveSearch.NeuralAgent.public_proposal_aligned
#print axioms ConstitutiveSearch.NeuralAgent.public_received_requirements_distinct
#print axioms ConstitutiveSearch.NeuralAgent.publicSeparatingRequirements
#print axioms ConstitutiveSearch.NeuralAgent.public_requirement_codes_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_executed_proposals_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_contexts_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_contextual_required_proposals_distinct
#print axioms ConstitutiveSearch.NeuralAgent.publicSeparatingContexts
#print axioms ConstitutiveSearch.NeuralAgent.public_context_codes_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_contextual_executed_inputs_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_contextual_executed_proposals_distinct
/- AXIOM_AUDIT_END -/
