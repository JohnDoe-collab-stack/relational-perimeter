import RelationalPerimeter.Agents.Neural.PublicActionRealization

namespace Tests.Mechanisms.NativeActionRealizationRegression
open ConstitutiveSearch.NativeMechanism ConstitutiveSearch.NeuralAgent

def scopeZeroDirectInput : PublicRequirementInput := ⟨.scopeZero, .direct⟩
def scopeOneDirectInput : PublicRequirementInput := ⟨.scopeOne, .direct⟩
def scopeZeroReversedInput : PublicRequirementInput := ⟨.scopeZero, .reversed⟩

theorem scope_zero_command_is_produced :
    (publicAction scopeZeroDirectInput).request = .advance 0 :=
  public_scope_zero_direct_request

theorem scope_one_command_is_produced :
    (publicAction scopeOneDirectInput).request = .advance 1 :=
  public_scope_one_direct_request

theorem commands_are_not_reconstructed_as_one :
    (publicAction scopeZeroDirectInput).request ≠ (publicAction scopeOneDirectInput).request :=
  public_action_requests_distinct

theorem context_changes_produced_command :
    (publicAction scopeZeroDirectInput).request ≠
      (publicAction scopeZeroReversedInput).request :=
  public_contextual_action_requests_distinct

theorem required_proposal_distinction_is_declared :
    DistinctAccordingToProposalContract publicAgentActionChannel
      false true :=
  public_required_proposal_distinction

theorem required_proposal_distinction_reaches_action :
    DistinctAccordingToActionContract publicAgentActionChannel
      (publicAgentActionChannel.command false)
      (publicAgentActionChannel.command true) :=
  public_required_action_distinction

theorem command_collisions_are_exactly_authorized
    (left right : Bool) :
    CollisionPermittedByProposalContract publicAgentActionChannel left right ↔
      publicAgentActionChannel.command left =
        publicAgentActionChannel.command right :=
  public_collision_permission_exact left right

theorem executed_actions_preserve_required_distinction
    (left right : PublicRequirementInput)
    (distinct : DistinctAccordingToProposalContract publicAgentActionChannel
      (publicRequirementFamily.requiredProposal
        left.requirement left.context)
      (publicRequirementFamily.requiredProposal
        right.requirement right.context)) :
    DistinctAccordingToActionContract publicAgentActionChannel
      (publicAction left).request (publicAction right).request :=
  public_actions_preserve_required_proposal_distinction left right distinct

theorem executed_action_collisions_are_exactly_authorized
    (left right : PublicRequirementInput) :
    CollisionPermittedByProposalContract publicAgentActionChannel
      (publicRequirementFamily.requiredProposal
        left.requirement left.context)
      (publicRequirementFamily.requiredProposal
        right.requirement right.context) ↔
      (publicAction left).request = (publicAction right).request :=
  public_action_collisions_are_exactly_permitted left right

theorem scope_zero_effect_is_executed :
    (publicEffect scopeZeroDirectInput).event.message = .advanced 0 :=
  public_scope_zero_direct_effect_message

theorem scope_one_effect_is_executed :
    (publicEffect scopeOneDirectInput).event.message = .advanced 1 :=
  public_scope_one_direct_effect_message

theorem effects_are_not_reconstructed_as_one :
    (publicEffect scopeZeroDirectInput).event ≠ (publicEffect scopeOneDirectInput).event :=
  public_effects_distinct

theorem context_changes_executed_effect :
    (publicEffect scopeZeroDirectInput).event ≠
      (publicEffect scopeZeroReversedInput).event :=
  public_contextual_effects_distinct

def scope_zero_action_carries_execution_evidence :
    ConstitutiveSearch.Agent.RequestEvidence publicActionMemory
      (publicAction scopeZeroDirectInput).request (publicAction scopeZeroDirectInput).result :=
  (publicAction scopeZeroDirectInput).evidence

def scope_one_action_carries_execution_evidence :
    ConstitutiveSearch.Agent.RequestEvidence publicActionMemory
      (publicAction scopeOneDirectInput).request (publicAction scopeOneDirectInput).result :=
  (publicAction scopeOneDirectInput).evidence

end Tests.Mechanisms.NativeActionRealizationRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.scope_zero_command_is_produced
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.scope_one_command_is_produced
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.commands_are_not_reconstructed_as_one
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.context_changes_produced_command
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.required_proposal_distinction_is_declared
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.required_proposal_distinction_reaches_action
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.command_collisions_are_exactly_authorized
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.executed_actions_preserve_required_distinction
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.executed_action_collisions_are_exactly_authorized
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.scope_zero_effect_is_executed
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.scope_one_effect_is_executed
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.effects_are_not_reconstructed_as_one
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.context_changes_executed_effect
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.scope_zero_action_carries_execution_evidence
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.scope_one_action_carries_execution_evidence
/- AXIOM_AUDIT_END -/
