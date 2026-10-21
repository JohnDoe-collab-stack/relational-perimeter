import RelationalPerimeter.Agents.Neural.PublicRequirementAlignment

set_option genInjectivity false
namespace Tests.Mechanisms.NativeRequirementAlignmentRegression
open ConstitutiveSearch.NativeMechanism ConstitutiveSearch.NeuralAgent

def scopeZeroDirectInput : PublicRequirementInput :=
  { requirement := .scopeZero, context := .direct }

def scopeOneDirectInput : PublicRequirementInput :=
  { requirement := .scopeOne, context := .direct }

def scopeZeroReversedInput : PublicRequirementInput :=
  { requirement := .scopeZero, context := .reversed }

theorem scope_zero_requirement_scope :
    scopeZeroDirectInput.receivedRequirement.scope = [0] := rfl

theorem scope_one_requirement_scope :
    scopeOneDirectInput.receivedRequirement.scope = [1] := rfl

theorem public_case_names_match_received_scopes :
    (publicRequirementFamily.received .scopeZero).scope = [0] ∧
      (publicRequirementFamily.received .scopeOne).scope = [1] :=
  ⟨public_scope_zero_scope_exact, public_scope_one_scope_exact⟩

theorem public_context_names_match_proposal_table :
    (publicRequirementFamily.requiredProposal .scopeZero .direct = false ∧
      publicRequirementFamily.requiredProposal .scopeOne .direct = true) ∧
    (publicRequirementFamily.requiredProposal .scopeZero .reversed = true ∧
      publicRequirementFamily.requiredProposal .scopeOne .reversed = false) :=
  ⟨public_direct_proposals_exact, public_reversed_proposals_exact⟩

theorem scope_zero_encoding_exact :
    (publicRequirementSystem.run scopeZeroDirectInput).inputs.read
      publicRequirementEncoding.port =
        publicRequirementEncoding.code .scopeZero .direct :=
  encoded_requirement_exact publicRequirementEncoding scopeZeroDirectInput

theorem scope_one_encoding_exact :
    (publicRequirementSystem.run scopeOneDirectInput).inputs.read
      publicRequirementEncoding.port =
        publicRequirementEncoding.code .scopeOne .direct :=
  encoded_requirement_exact publicRequirementEncoding scopeOneDirectInput

theorem reversed_context_encoding_exact :
    (publicRequirementSystem.run scopeZeroReversedInput).inputs.read
      publicRequirementEncoding.port =
        publicRequirementEncoding.code .scopeZero .reversed :=
  encoded_requirement_exact publicRequirementEncoding scopeZeroReversedInput

def scope_zero_executed_path :=
  incorporated_requirement_has_executed_path
    (publicRequirementIncorporation scopeZeroDirectInput)

def scope_one_executed_path :=
  incorporated_requirement_has_executed_path
    (publicRequirementIncorporation scopeOneDirectInput)

def scope_zero_causal_role :
    CausalRole publicRequirementSystem scopeZeroDirectInput
      (.receivedInput publicRequirementEncoding.port) :=
  publicRequirementCausalRole scopeZeroDirectInput

def scope_one_causal_role :
    CausalRole publicRequirementSystem scopeOneDirectInput
      (.receivedInput publicRequirementEncoding.port) :=
  publicRequirementCausalRole scopeOneDirectInput

theorem scope_zero_changes_executed_proposal :
    ChangesProposal publicRequirementSystem scopeZeroDirectInput
      (publicRequirementIntervention scopeZeroDirectInput) :=
  publicRequirementProposalChange scopeZeroDirectInput

theorem scope_one_changes_executed_proposal :
    ChangesProposal publicRequirementSystem scopeOneDirectInput
      (publicRequirementIntervention scopeOneDirectInput) :=
  publicRequirementProposalChange scopeOneDirectInput

def scope_zero_signal_path := publicRequirementSignalPath scopeZeroDirectInput
def scope_one_signal_path := publicRequirementSignalPath scopeOneDirectInput

/-- The generic C3 transition is inhabited by the effective edge consumed by
the executed neuron, not by a caller-supplied transformation function. -/
def scope_zero_effective_signal_edge :
    EffectiveReadsFrom (publicRequirementSystem.run scopeZeroDirectInput)
      (.receivedInput publicRequirementPort)
      (.neuronOutput publicRequirementOutput) :=
  (publicRequirementExecutedTransformation scopeZeroDirectInput).edge

theorem scope_zero_signal_transform_is_execution_derived :
    (ActivationOccurrence.neuronOutput publicRequirementOutput :
        ActivationOccurrence
          (publicRequirementSystem.run scopeZeroDirectInput)).value =
      (publicRequirementExecutedTransformation scopeZeroDirectInput).transform
        ((ActivationOccurrence.receivedInput publicRequirementPort :
          ActivationOccurrence
            (publicRequirementSystem.run scopeZeroDirectInput)).value) :=
  (publicRequirementExecutedTransformation scopeZeroDirectInput).outputExact

theorem scope_zero_received_code_is_not_terminal_representation :
    publicRequirementEncoding.code .scopeZero .direct ≠
      publicRequirementDecoder.terminalRepresentation .scopeZero .direct :=
  publicRequirementTransformationNonidentity scopeZeroDirectInput

theorem scope_one_received_code_is_not_terminal_representation :
    publicRequirementEncoding.code .scopeOne .direct ≠
      publicRequirementDecoder.terminalRepresentation .scopeOne .direct :=
  publicRequirementTransformationNonidentity scopeOneDirectInput

theorem scope_zero_executed_occurrences_differ :
    (ActivationOccurrence.receivedInput publicRequirementPort :
        ActivationOccurrence (publicRequirementSystem.run scopeZeroDirectInput)).value ≠
      (ActivationOccurrence.neuronOutput publicRequirementOutput :
        ActivationOccurrence (publicRequirementSystem.run scopeZeroDirectInput)).value :=
  publicRequirementOccurrencesDiffer scopeZeroDirectInput

theorem scope_zero_path_executes_nonidentity_transform :
    (ActivationOccurrence.neuronOutput publicRequirementOutput :
        ActivationOccurrence (publicRequirementSystem.run scopeZeroDirectInput)).value =
      (publicRequirementExecutedTransformation scopeZeroDirectInput).transform
        (publicRequirementEncoding.code .scopeZero .direct) :=
  (publicRequirementSignalPath scopeZeroDirectInput).signalExact

theorem scope_zero_proposal_aligned :
    publicRequirementSystem.proposal scopeZeroDirectInput = false :=
  public_proposal_aligned scopeZeroDirectInput

theorem scope_one_proposal_aligned :
    publicRequirementSystem.proposal scopeOneDirectInput = true :=
  public_proposal_aligned scopeOneDirectInput

theorem reversed_context_proposal_aligned :
    publicRequirementSystem.proposal scopeZeroReversedInput = true :=
  public_proposal_aligned scopeZeroReversedInput

theorem requirements_are_not_collapsed :
    scopeZeroDirectInput.receivedRequirement ≠ scopeOneDirectInput.receivedRequirement :=
  public_received_requirements_distinct

theorem encodings_are_not_constant :
    publicRequirementEncoding.code .scopeZero .direct ≠
      publicRequirementEncoding.code .scopeOne .direct :=
  public_requirement_codes_distinct

theorem executed_proposals_are_not_constant :
    publicRequirementSystem.proposal scopeZeroDirectInput ≠
      publicRequirementSystem.proposal scopeOneDirectInput :=
  public_executed_proposals_distinct

theorem contexts_are_distinct :
    PublicRequirementContext.direct ≠ PublicRequirementContext.reversed :=
  public_contexts_distinct

theorem contextual_inputs_keep_the_same_requirement :
    scopeZeroDirectInput.requirement = scopeZeroReversedInput.requirement :=
  rfl

theorem context_changes_required_proposal :
    publicRequirementFamily.requiredProposal scopeZeroDirectInput.requirement
        scopeZeroDirectInput.context ≠
      publicRequirementFamily.requiredProposal scopeZeroReversedInput.requirement
        scopeZeroReversedInput.context :=
  public_contextual_required_proposals_distinct

theorem context_changes_encoded_signal :
    publicRequirementEncoding.code scopeZeroDirectInput.requirement scopeZeroDirectInput.context ≠
      publicRequirementEncoding.code scopeZeroReversedInput.requirement
        scopeZeroReversedInput.context :=
  public_context_codes_distinct

theorem context_changes_executed_input :
    (publicRequirementSystem.run scopeZeroDirectInput).inputs.read
        publicRequirementEncoding.port ≠
      (publicRequirementSystem.run scopeZeroReversedInput).inputs.read
        publicRequirementEncoding.port :=
  public_contextual_executed_inputs_distinct

theorem context_changes_executed_proposal :
    publicRequirementSystem.proposal scopeZeroDirectInput ≠
      publicRequirementSystem.proposal scopeZeroReversedInput :=
  public_contextual_executed_proposals_distinct

end Tests.Mechanisms.NativeRequirementAlignmentRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_requirement_scope
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_requirement_scope
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.public_case_names_match_received_scopes
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.public_context_names_match_proposal_table
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_encoding_exact
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_encoding_exact
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.reversed_context_encoding_exact
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_executed_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_executed_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_causal_role
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_causal_role
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_changes_executed_proposal
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_changes_executed_proposal
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_signal_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_signal_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_effective_signal_edge
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_signal_transform_is_execution_derived
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_received_code_is_not_terminal_representation
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_received_code_is_not_terminal_representation
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_executed_occurrences_differ
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_path_executes_nonidentity_transform
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_zero_proposal_aligned
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.scope_one_proposal_aligned
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.reversed_context_proposal_aligned
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.requirements_are_not_collapsed
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.encodings_are_not_constant
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.executed_proposals_are_not_constant
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.contexts_are_distinct
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.contextual_inputs_keep_the_same_requirement
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.context_changes_required_proposal
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.context_changes_encoded_signal
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.context_changes_executed_input
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.context_changes_executed_proposal
/- AXIOM_AUDIT_END -/
