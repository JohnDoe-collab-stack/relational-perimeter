import RelationalPerimeter.Agents.Neural.RequirementSensitivity

/-!
# A closed requirement-sensitive native instance

Two positively received requirements are run through the same one-neuron
program and the same unit context.  Their signals are distinct, each signal is
causally incorporated through the executed edge, the output preserves it, and
the decoder produces the proposal required by that received requirement.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

inductive PublicRequirementCase where
  | deny
  | allow

def singletonRequirement (var : SAT.Var) : Agent.Requirement :=
  (Agent.receive [var]).get (by rfl)

def publicRequirementFamily :
    RequirementFamily PublicRequirementCase Unit Bool where
  received
    | .deny => singletonRequirement 0
    | .allow => singletonRequirement 1
  requiredProposal
    | .deny, _ => false
    | .allow, _ => true

abbrev PublicRequirementInput := RequirementInput publicRequirementFamily

def publicRequirementPort : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩
def publicRequirementOutput : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩

def publicRequirementCode : PublicRequirementCase -> Activation
  | .deny => 0
  | .allow => 1

def encodePublicRequirement (input : PublicRequirementInput) :
    SizedActivations 1 :=
  SizedActivations.snoc SizedActivations.empty
    (publicRequirementCode input.requirement)

def publicRequirementNeuron : NeuronSpec 1 0 :=
  { inputs := [{ source := .receivedInput publicRequirementPort, weight := 1 }]
    bias := 0
    threshold := ⟨1⟩ }

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

def publicRequirementEncoding :
    RequirementEncoding publicRequirementSystem where
  port := publicRequirementPort
  code := publicRequirementCode
  inputExact := by
    intro input
    exact SizedActivations.read_snoc_last SizedActivations.empty _
  requirementReflecting := by
    intro one two same
    cases one <;> cases two
    · rfl
    · cases same
    · cases same
    · rfl

def publicRequirementIntervention
    (input : PublicRequirementInput) :
    Intervention (publicRequirementSystem.run input) :=
  match input with
  | ⟨.deny, ()⟩ =>
      { focus := .input publicRequirementPort
        replacement := 1
        changesValue := by decide }
  | ⟨.allow, ()⟩ =>
      { focus := .input publicRequirementPort
        replacement := 0
        changesValue := by decide }

theorem publicRequirementFocusExact (input : PublicRequirementInput) :
    (publicRequirementIntervention input).focusOccurrence =
      (.receivedInput publicRequirementPort :
        ActivationOccurrence (publicRequirementSystem.run input)) := by
  cases input with
  | mk requirement context => cases requirement <;> cases context <;> rfl

def publicRequirementEdge (input : PublicRequirementInput) :
    ReadsFrom (publicRequirementSystem.run input)
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
  let edge : ReadsFrom (publicRequirementSystem.run input)
      (publicRequirementIntervention input).focusOccurrence
      (.neuronOutput publicRequirementOutput) :=
    Eq.mp
      (congrArg
        (fun source => ReadsFrom (publicRequirementSystem.run input) source
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
  decodeCode := by
    intro requirement context
    cases requirement <;> cases context <;> rfl

theorem publicRequirementSignalPreserved (input : PublicRequirementInput) :
    (ActivationOccurrence.neuronOutput publicRequirementOutput :
      ActivationOccurrence (publicRequirementSystem.run input)).value =
        (ActivationOccurrence.receivedInput publicRequirementPort :
          ActivationOccurrence (publicRequirementSystem.run input)).value := by
  cases input with
  | mk requirement context => cases requirement <;> cases context <;> rfl

def publicRequirementSignalPath (input : PublicRequirementInput) :
    RequirementSignalPath publicRequirementEncoding input
      (.neuronOutput publicRequirementOutput) :=
  .step .origin (publicRequirementEdge input)
    (publicRequirementSignalPreserved input)

def publicRequirementSignalPreservation (input : PublicRequirementInput) :
    RequirementSignalPreservation publicRequirementDecoder
      (publicRequirementIncorporation input) := by
  exact
    { roleOutputExact := publicRequirementRoleOutputExact input
      path := publicRequirementSignalPath input }

theorem public_proposal_aligned (input : PublicRequirementInput) :
    publicRequirementSystem.proposal input =
      publicRequirementFamily.requiredProposal
        input.requirement input.context :=
  proposal_aligned (publicRequirementSignalPreservation input)

theorem public_received_requirements_distinct :
    publicRequirementFamily.received .deny ≠
      publicRequirementFamily.received .allow := by
  intro same
  have scopes := congrArg (fun requirement : Agent.Requirement =>
    requirement.scope) same
  change ([0] : List Nat) = [1] at scopes
  have heads : (0 : Nat) = 1 := (List.cons.inj scopes).1
  exact Nat.noConfusion heads

theorem public_required_proposals_distinct :
    publicRequirementFamily.requiredProposal .deny () ≠
      publicRequirementFamily.requiredProposal .allow () := by
  decide

theorem publicSeparatingRequirements :
    SeparatingRequirements publicRequirementFamily .deny .allow () :=
  { receivedDistinct := public_received_requirements_distinct
    requiredDistinct := public_required_proposals_distinct }

theorem public_requirement_codes_distinct :
    publicRequirementEncoding.code .deny ≠
      publicRequirementEncoding.code .allow :=
  separating_requirement_codes publicRequirementEncoding
    publicSeparatingRequirements

theorem public_executed_proposals_distinct :
    publicRequirementSystem.proposal (RequirementInput.mk .deny ()) ≠
      publicRequirementSystem.proposal (RequirementInput.mk .allow ()) :=
  separating_executed_proposals publicSeparatingRequirements
    (publicRequirementSignalPreservation (RequirementInput.mk .deny ()))
    (publicRequirementSignalPreservation (RequirementInput.mk .allow ()))

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.PublicRequirementCase
#print axioms ConstitutiveSearch.NeuralAgent.singletonRequirement
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementFamily
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSystem
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementEncoding
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementIntervention
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementCausalRole
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementIncorporation
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementDecoder
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSignalPath
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementSignalPreservation
#print axioms ConstitutiveSearch.NeuralAgent.public_proposal_aligned
#print axioms ConstitutiveSearch.NeuralAgent.public_received_requirements_distinct
#print axioms ConstitutiveSearch.NeuralAgent.publicSeparatingRequirements
#print axioms ConstitutiveSearch.NeuralAgent.public_requirement_codes_distinct
#print axioms ConstitutiveSearch.NeuralAgent.public_executed_proposals_distinct
/- AXIOM_AUDIT_END -/
