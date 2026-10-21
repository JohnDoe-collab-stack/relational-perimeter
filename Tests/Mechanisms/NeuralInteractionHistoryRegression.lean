import RelationalPerimeter.Agents.Neural.PublicActionRealization

namespace Tests.Mechanisms.NeuralInteractionHistoryRegression
open ConstitutiveSearch.NeuralAgent

def scopeZeroDirectInput : PublicRequirementInput := ⟨.scopeZero, .direct⟩
def scopeOneDirectInput : PublicRequirementInput := ⟨.scopeOne, .direct⟩

theorem two_step_requests_are_aligned :
    (publicFiniteInteractionHistory [scopeZeroDirectInput, scopeOneDirectInput]).requests =
      [.advance 0, .advance 1] := by
  rw [public_finite_continuation_aligned]
  rfl

theorem two_step_execution_is_exact :
    ((publicFiniteInteractionHistory [scopeZeroDirectInput, scopeOneDirectInput]).finalMemory,
      (publicFiniteInteractionHistory [scopeZeroDirectInput, scopeOneDirectInput]).events) =
      ConstitutiveSearch.Agent.executeRequests publicActionMemory
        [.advance 0, .advance 1] := by
  rw [public_finite_continuation_execution_exact]
  rfl

theorem head_does_not_read_future :
    (publicFiniteInteractionHistory (scopeZeroDirectInput :: [scopeZeroDirectInput])).headRequest =
      (publicFiniteInteractionHistory (scopeZeroDirectInput :: [scopeOneDirectInput, scopeZeroDirectInput])).headRequest :=
  public_head_horizon_independent scopeZeroDirectInput [scopeZeroDirectInput] [scopeOneDirectInput, scopeZeroDirectInput]

theorem changed_head_requirement_changes_request :
    (publicFiniteInteractionHistory (scopeZeroDirectInput :: [scopeOneDirectInput])).headRequest ≠
      (publicFiniteInteractionHistory (scopeOneDirectInput :: [scopeZeroDirectInput])).headRequest := by
  change some (publicAction scopeZeroDirectInput).request ≠ some (publicAction scopeOneDirectInput).request
  intro same
  exact public_action_requests_distinct (Option.some.inj same)

end Tests.Mechanisms.NeuralInteractionHistoryRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.two_step_requests_are_aligned
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.two_step_execution_is_exact
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.head_does_not_read_future
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.changed_head_requirement_changes_request
/- AXIOM_AUDIT_END -/
