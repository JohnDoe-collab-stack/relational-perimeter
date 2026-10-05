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

theorem all_responses_keep_produced_criterion (input : Nat)
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles) (requests : List Request) :
    FiniteResponseCriterion (start (UnifiedMaster.publicInstance input) (singletonRequirement 0) profile) requests :=
  (concrete_certificate input).satisfaction profile requests

def every_internal_head_has_two_transports {input : Nat}
    (source : Source (UnifiedMaster.publicInstance input)) (count : Nat) : InternalStepAgreement source :=
  (every_internal_head_followed source (count + 1)).head

theorem followed_stages_are_actual_execution {input : Nat}
    (source : Source (UnifiedMaster.publicInstance input)) (count : Nat) :
    let followed := every_internal_head_followed source count
    (project followed.final, followed.events) = runSteps count (project source) :=
  (every_internal_head_followed source count).execution_exact

theorem historical_support_is_not_declared_given {input : Nat}
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (history : History (UnifiedMaster.publicInstance input) profile) {target : AnswerTarget}
    (ref : ConstitutiveSearch.Resources.Ref history.targets target) :
    history.realization.support.formation ≠ .given history.realization.support.values :=
  ((concrete_certificate input).historicalFormation profile history).not_given (history.realization.reference ref)

/-! Regression pins for guarantees whose deletion previously went unnoticed. -/
section RegressionPins
open ConstitutiveSearch.SAT ConstitutiveSearch.Resources

/-- The value an answer target restitutes is the read of its own produced
continuation, both definitionally and as a closed certificate field. -/
theorem answer_read_is_produced_value (target : AnswerTarget) (var : Var) :
    target.read var = target.continuation.1 var := rfl

theorem certified_answer_read {input : Nat} (target : AnswerTarget) (var : Var) :
    target.read var = target.continuation.1 var :=
  (concrete_certificate input).targetReads target var

/-- Normalized origins are indexed by the executed retained target of their
own license, not by an arbitrary accepted continuation. -/
def normalized_origin_index : ∀ {state : CausalConstitutiveState} {head : CausalConstitutiveStageExecution state}
    {role : RelationalConstitutiveRoleStage head} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom),
    TargetOrigin _ (causalOpeningRight state head.selected head.fresh)
      (retainedExecutedRoleOperationalTarget license) := @TargetOrigin.normalized

/-- Resumed origins are indexed by the context and output of their own live production. -/
def resumed_origin_index : ∀ {memory : LiveContinuation.Memory} (production : LiveContinuation.Production memory),
    TargetOrigin _ production.built.stage.schedule.entry.target production.built.stage.application.output :=
  @TargetOrigin.resumed

/-- Exhaustive: no third origin constructor (for example a free tag) exists. -/
def origin_producer {root : Cnf} {context : GeneratedStructuralBranchContext root}
    {continuation : GeneratedStructuralBranchContinuation context} :
    TargetOrigin root context continuation → Bool
  | .normalized _ => true
  | .resumed _ => false

theorem certified_resumed_origin {input : Nat} {memory : LiveContinuation.Memory}
    (production : LiveContinuation.Production memory) :
    (resumedTarget production).origin = TargetOrigin.resumed production :=
  (concrete_certificate input).resumedOrigin production

theorem certified_targets_accepted {input : Nat} (target : AnswerTarget) :
    GeneratedStructuralBranchAccept target.context target.continuation :=
  (concrete_certificate input).targetsAccepted target

/-- An answer criterion is an authorization together with contextual acceptance. -/
theorem answer_criterion_is_contextual_acceptance (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (value : Bool) :
    ReplyCriterion requirement register (.answer handle var value) =
      ∃ authorization : Authorization requirement register handle var value,
        GeneratedStructuralBranchAccept authorization.occurrence.1.context authorization.occurrence.1.continuation :=
  rfl

/-- Every internal stage of the head request is followed by the certificate. -/
theorem certified_internal_stages (input : Nat)
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (request : Request) (rest : List Request) :
    let master := UnifiedMaster.publicInstance input
    let source := sourceStart master (singletonRequirement 0) profile
    let stages := ((concrete_certificate input).followed profile (request :: rest)).stages
    (project stages.final, stages.events) =
      ((executeInput (project source) request).1, (executeInput (project source) request).2.productions) := by
  intro master source stages
  show (project ((concrete_certificate input).followed profile (request :: rest)).stages.final,
      ((concrete_certificate input).followed profile (request :: rest)).stages.events) = _
  rw [(concrete_certificate input).followedStages profile request rest]
  exact (concrete_certificate input).internalStages source request

theorem certified_followed_references (input : Nat)
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (request : Request) (rest : List Request) :
    ((concrete_certificate input).followed profile (request :: rest)).references =
      (sourcePerform (sourceStart (UnifiedMaster.publicInstance input) (singletonRequirement 0) profile)
        request).1.history.references :=
  (concrete_certificate input).followedReferences profile request rest

/-- Both admission return laws remain closed certificate fields. -/
theorem certified_received_return {input : Nat} {register : List AnswerTarget}
    {cursor : MasterResources.Cursor} (requirement : Requirement)
    (realization : RegisterRealization register cursor) (request : Request)
    (witness : RichAdmission requirement realization request) :
    receivedAdmission requirement realization request (realizeAdmission requirement realization request witness) =
      witness :=
  (concrete_certificate input).receivedReturn requirement realization request witness

theorem certified_realized_return {input : Nat} {register : List AnswerTarget}
    {cursor : MasterResources.Cursor} (requirement : Requirement)
    (realization : RegisterRealization register cursor) (request : Request)
    (witness : Admission requirement register request) :
    realizeAdmission requirement realization request (receivedAdmission requirement realization request witness) =
      witness :=
  (concrete_certificate input).realizedReturn requirement realization request witness

end RegressionPins

/-- The concrete missing handle requires two internal productions, not one
production merely because there is one external request. -/
theorem missing_handle_has_two_internal_stages :
    requestStageCount
      (sourceStart (UnifiedMaster.publicInstance 0) (singletonRequirement 0)
        (UnifiedMaster.publicInstance 0).distinctPair.left) (.obtain 2 0) = 2 := rfl

/-- Reading the already-produced initial handle adds no internal production. -/
theorem cached_handle_has_no_internal_stage :
    requestStageCount
      (sourceStart (UnifiedMaster.publicInstance 0) (singletonRequirement 0)
        (UnifiedMaster.publicInstance 0).distinctPair.left) (.obtain 0 0) = 0 := rfl

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
#print axioms Tests.ConstitutiveAgentPersistence.all_responses_keep_produced_criterion
#print axioms Tests.ConstitutiveAgentPersistence.every_internal_head_has_two_transports
#print axioms Tests.ConstitutiveAgentPersistence.followed_stages_are_actual_execution
#print axioms Tests.ConstitutiveAgentPersistence.historical_support_is_not_declared_given
#print axioms Tests.ConstitutiveAgentPersistence.answer_read_is_produced_value
#print axioms Tests.ConstitutiveAgentPersistence.certified_answer_read
#print axioms Tests.ConstitutiveAgentPersistence.normalized_origin_index
#print axioms Tests.ConstitutiveAgentPersistence.resumed_origin_index
#print axioms Tests.ConstitutiveAgentPersistence.origin_producer
#print axioms Tests.ConstitutiveAgentPersistence.certified_resumed_origin
#print axioms Tests.ConstitutiveAgentPersistence.certified_targets_accepted
#print axioms Tests.ConstitutiveAgentPersistence.answer_criterion_is_contextual_acceptance
#print axioms Tests.ConstitutiveAgentPersistence.certified_internal_stages
#print axioms Tests.ConstitutiveAgentPersistence.certified_followed_references
#print axioms Tests.ConstitutiveAgentPersistence.certified_received_return
#print axioms Tests.ConstitutiveAgentPersistence.certified_realized_return
#print axioms Tests.ConstitutiveAgentPersistence.missing_handle_has_two_internal_stages
#print axioms Tests.ConstitutiveAgentPersistence.cached_handle_has_no_internal_stage
/- AXIOM_AUDIT_END -/
