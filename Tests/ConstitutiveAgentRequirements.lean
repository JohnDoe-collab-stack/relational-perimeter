import RelationalPerimeter
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace Tests.ConstitutiveAgentRequirements
open ConstitutiveSearch.Agent ConstitutiveSearch.EndogenousDecomposition

theorem empty_rejected (input : Nat) (code : List Bool) :
    initializeAgent input [] code = .error .emptyScope := initialize_empty input code

theorem scope_changes_rights :
    (singletonRequirement 0).permission 1 = none ∧
    (singletonRequirement 1).permission 1 = some (.here) :=
  ⟨rfl, singleton_permission 1⟩

theorem concrete_good_proposal (input : Nat) :
    let master := UnifiedMaster.publicInstance input
    let goal := singletonRequirement 0
    let profile := master.distinctPair.left
    let authorized := firstAuthorization master goal profile 0 .here
    (executeInput (start master goal profile) (.propose 0 0 authorized.1)).2.message =
      .answer 0 0 authorized.1 :=
  correct_candidate_returns (singletonRequirement 0) _ 0 0 _
    (firstAuthorization (UnifiedMaster.publicInstance input) (singletonRequirement 0)
      (UnifiedMaster.publicInstance input).distinctPair.left 0 .here).2

theorem bool_opposite (value : Bool) : (!value) ≠ value := by
  cases value <;> intro impossible <;> cases impossible

theorem concrete_bad_proposal (input : Nat) :
    let master := UnifiedMaster.publicInstance input
    let goal := singletonRequirement 0
    let profile := master.distinctPair.left
    let authorized := firstAuthorization master goal profile 0 .here
    (executeInput (start master goal profile) (.propose 0 0 (!authorized.1))).2.message =
      .refused 0 0 .incorrectValue := by
  dsimp only
  let authorized := firstAuthorization (UnifiedMaster.publicInstance input)
    (singletonRequirement 0) (UnifiedMaster.publicInstance input).distinctPair.left 0 .here
  exact incorrect_candidate_refused (singletonRequirement 0) _ 0 0 authorized.2.occurrence .here
    authorized.2.occurrenceExact (!authorized.1)
    (by rw [← authorized.2.valueExact]; exact bool_opposite _)

theorem both_source_codes_admitted (input : Nat) :
    let master := UnifiedMaster.publicInstance input
    (initializeAgent input [0] (encodeSelection master.roles master.distinctPair.left)).isOk = true ∧
      (initializeAgent input [0] (encodeSelection master.roles master.distinctPair.right)).isOk = true :=
  ⟨initialized_codes_admitted input 0 _, initialized_codes_admitted input 0 _⟩

-- Finite code-generation checks, not a confirmatory complexity experiment.
#eval (publicAgent 0 [] [false]).map (fun session => session.memory.register.length)
#eval (publicAgent 0 [0] []).map (fun session => session.memory.register.length)
#eval (publicAgent 0 [0] [false]).map (fun session => session.memory.register.length)

end Tests.ConstitutiveAgentRequirements
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ConstitutiveAgentRequirements.empty_rejected
#print axioms Tests.ConstitutiveAgentRequirements.scope_changes_rights
#print axioms Tests.ConstitutiveAgentRequirements.concrete_good_proposal
#print axioms Tests.ConstitutiveAgentRequirements.concrete_bad_proposal
#print axioms Tests.ConstitutiveAgentRequirements.both_source_codes_admitted
/- AXIOM_AUDIT_END -/
