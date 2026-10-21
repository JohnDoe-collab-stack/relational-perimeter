import RelationalPerimeter.Agents.Neural.PublicActionRealization

namespace Tests.Mechanisms.NeuralInteractionHistoryRegression
open ConstitutiveSearch.NeuralAgent

def denyInput : PublicRequirementInput := ⟨.deny, ()⟩
def allowInput : PublicRequirementInput := ⟨.allow, ()⟩

theorem two_step_requests_are_aligned :
    (publicFiniteInteractionHistory [denyInput, allowInput]).requests =
      [.advance 0, .advance 1] := by
  rw [public_finite_continuation_aligned]
  rfl

theorem two_step_execution_is_exact :
    ((publicFiniteInteractionHistory [denyInput, allowInput]).finalMemory,
      (publicFiniteInteractionHistory [denyInput, allowInput]).events) =
      ConstitutiveSearch.Agent.executeRequests publicActionMemory
        [.advance 0, .advance 1] := by
  rw [public_finite_continuation_execution_exact]
  rfl

theorem head_does_not_read_future :
    (publicFiniteInteractionHistory (denyInput :: [denyInput])).headRequest =
      (publicFiniteInteractionHistory (denyInput :: [allowInput, denyInput])).headRequest :=
  public_head_horizon_independent denyInput [denyInput] [allowInput, denyInput]

theorem changed_head_requirement_changes_request :
    (publicFiniteInteractionHistory (denyInput :: [allowInput])).headRequest ≠
      (publicFiniteInteractionHistory (allowInput :: [denyInput])).headRequest := by
  change some (publicAction denyInput).request ≠ some (publicAction allowInput).request
  intro same
  exact public_action_requests_distinct (Option.some.inj same)

end Tests.Mechanisms.NeuralInteractionHistoryRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.two_step_requests_are_aligned
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.two_step_execution_is_exact
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.head_does_not_read_future
#print axioms Tests.Mechanisms.NeuralInteractionHistoryRegression.changed_head_requirement_changes_request
/- AXIOM_AUDIT_END -/
