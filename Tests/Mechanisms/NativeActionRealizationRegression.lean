import RelationalPerimeter.Agents.Neural.PublicActionRealization

namespace Tests.Mechanisms.NativeActionRealizationRegression
open ConstitutiveSearch.NativeMechanism ConstitutiveSearch.NeuralAgent

def denyInput : PublicRequirementInput := ⟨.deny, ()⟩
def allowInput : PublicRequirementInput := ⟨.allow, ()⟩

theorem deny_command_is_produced :
    (publicAction denyInput).request = .advance 0 :=
  public_deny_request

theorem allow_command_is_produced :
    (publicAction allowInput).request = .advance 1 :=
  public_allow_request

theorem commands_are_not_reconstructed_as_one :
    (publicAction denyInput).request ≠ (publicAction allowInput).request :=
  public_action_requests_distinct

theorem deny_effect_is_executed :
    (publicEffect denyInput).event.message = .advanced 0 :=
  public_deny_effect_message

theorem allow_effect_is_executed :
    (publicEffect allowInput).event.message = .advanced 1 :=
  public_allow_effect_message

theorem effects_are_not_reconstructed_as_one :
    (publicEffect denyInput).event ≠ (publicEffect allowInput).event :=
  public_effects_distinct

def deny_action_carries_execution_evidence :
    ConstitutiveSearch.Agent.RequestEvidence publicActionMemory
      (publicAction denyInput).request (publicAction denyInput).result :=
  (publicAction denyInput).evidence

def allow_action_carries_execution_evidence :
    ConstitutiveSearch.Agent.RequestEvidence publicActionMemory
      (publicAction allowInput).request (publicAction allowInput).result :=
  (publicAction allowInput).evidence

end Tests.Mechanisms.NativeActionRealizationRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.deny_command_is_produced
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.allow_command_is_produced
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.commands_are_not_reconstructed_as_one
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.deny_effect_is_executed
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.allow_effect_is_executed
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.effects_are_not_reconstructed_as_one
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.deny_action_carries_execution_evidence
#print axioms Tests.Mechanisms.NativeActionRealizationRegression.allow_action_carries_execution_evidence
/- AXIOM_AUDIT_END -/
