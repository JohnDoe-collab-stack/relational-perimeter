import RelationalPerimeter
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace Tests.ConstitutiveAgentPersistence
open ConstitutiveSearch.Agent ConstitutiveSearch.EndogenousDecomposition

theorem distinct_sources_same_complete_memory (input : Nat) :
    let master := UnifiedMaster.publicInstance input
    let goal := singletonRequirement 0
    master.distinctPair.left ≠ master.distinctPair.right ∧
      start master goal master.distinctPair.left = start master goal master.distinctPair.right :=
  ⟨(UnifiedMaster.publicInstance input).distinctPair.distinct, initial_memories_equal _ _ _ _⟩

theorem entire_memory_cannot_decode (input : Nat) :
    let master := UnifiedMaster.publicInstance input
    ¬ (∃ recover : Memory → RoleOccurrenceProfile master.roles,
      ∀ profile, recover (start master (singletonRequirement 0) profile) = profile) :=
  initial_profile_not_recoverable _ _

theorem same_future_after_forgetting (input : Nat) (requests : List Request) :
    let master := UnifiedMaster.publicInstance input
    executeRequests (start master (singletonRequirement 0) master.distinctPair.left) requests =
      executeRequests (start master (singletonRequirement 0) master.distinctPair.right) requests :=
  forgotten_sources_same_future _ _ _ _ requests

def concrete_certificate (input : Nat) :
    Certificate (UnifiedMaster.publicInstance input) (singletonRequirement 0) := certify _ _

def concrete_following (input : Nat) (requests : List Request) :
    Followed (UnifiedMaster.publicInstance input)
      (sourceStart (UnifiedMaster.publicInstance input) (singletonRequirement 0)
        (UnifiedMaster.publicInstance input).distinctPair.left) requests :=
  (concrete_certificate input).followed _ requests

theorem historical_handle_square {input : Nat} (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (history : History (UnifiedMaster.publicInstance input) profile) {target : AnswerTarget}
    (ref : ConstitutiveSearch.Resources.Ref history.targets target) :
    (History.step history).realization.reference
      (extendReference [resumedTarget (LiveContinuation.sourceProduction history.cursor)] ref) =
      history.realization.advance.2.references (history.realization.reference ref) :=
  (concrete_certificate input).historicalHandles profile history ref

theorem historical_read_agreement {input : Nat}
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (history : History (UnifiedMaster.publicInstance input) profile) :
    history.realization.materialRegister = history.targets :=
  (concrete_certificate input).historicalTargets profile history

theorem historical_position_moves {input : Nat}
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (history : History (UnifiedMaster.publicInstance input) profile) {target : AnswerTarget}
    (ref : ConstitutiveSearch.Resources.Ref history.targets target) :
    ((History.step history).realization.reference
      (extendReference [resumedTarget (LiveContinuation.sourceProduction history.cursor)] ref)).position =
        (history.realization.reference ref).position + history.realization.advance.2.added :=
  (concrete_certificate input).historicalPositions profile history ref

theorem historical_occurrences_do_not_collapse {input : Nat}
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (history : History (UnifiedMaster.publicInstance input) profile) {target : AnswerTarget}
    (one two : ConstitutiveSearch.Resources.Ref history.targets target)
    (same : history.realization.reference one = history.realization.reference two) : one = two :=
  (concrete_certificate input).historicalDistinctness profile history one two same

def every_internal_head_followed {input : Nat}
    (source : Source (UnifiedMaster.publicInstance input)) (count : Nat) :
    FollowedStages (UnifiedMaster.publicInstance input) source count := followStages _ count source

end Tests.ConstitutiveAgentPersistence
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ConstitutiveAgentPersistence.distinct_sources_same_complete_memory
#print axioms Tests.ConstitutiveAgentPersistence.entire_memory_cannot_decode
#print axioms Tests.ConstitutiveAgentPersistence.same_future_after_forgetting
#print axioms Tests.ConstitutiveAgentPersistence.concrete_certificate
#print axioms Tests.ConstitutiveAgentPersistence.concrete_following
#print axioms Tests.ConstitutiveAgentPersistence.historical_handle_square
#print axioms Tests.ConstitutiveAgentPersistence.historical_read_agreement
#print axioms Tests.ConstitutiveAgentPersistence.historical_position_moves
#print axioms Tests.ConstitutiveAgentPersistence.historical_occurrences_do_not_collapse
#print axioms Tests.ConstitutiveAgentPersistence.every_internal_head_followed
/- AXIOM_AUDIT_END -/
