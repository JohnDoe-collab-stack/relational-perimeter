import RelationalPerimeter.Agents.Constitutive.Agreement

/-! Finite interaction closure and loss of the initial source distinction in
the entire runtime memory. The rich archive is not a runtime dependency. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent
open SAT Resources EndogenousDecomposition Grouping

theorem executeRequests_final (memory : Memory) (requests : List Request) :
    (executeRequests memory requests).1 =
      Continuation.run (fun state request => (executeInput state request).1) memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih => exact ih _

theorem executeRequests_events (memory : Memory) (requests : List Request) :
    (executeRequests memory requests).2 =
      Continuation.events (fun state request => (executeInput state request).1)
        (fun state request => (executeInput state request).2) memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih => exact congrArg (List.cons _) (ih _)

theorem all_future_requests_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) (requests : List Request) :
    project (Continuation.run (bridge master).sourceNext source requests) =
      (executeRequests (project source) requests).1 :=
  ((bridge master).run_exact source requests).trans (executeRequests_final _ _).symm

theorem all_future_events_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) (requests : List Request) :
    Continuation.events (bridge master).sourceNext (bridge master).sourceEvent source requests =
      (executeRequests (project source) requests).2 :=
  ((bridge master).events_exact source requests).trans (executeRequests_events _ _).symm

theorem all_future_reads_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) (requests : List Request) :
    Continuation.observations (bridge master).sourceNext (bridge master).sourceRead source requests =
      Continuation.observations (bridge master).reducedNext (bridge master).reducedRead
        (project source) requests := (bridge master).observations_exact source requests

def admissions_forward {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) (requests : List Request) :
    Continuation.Admitted (bridge master).sourceNext (bridge master).sourceAllow source requests →
      Continuation.Admitted (bridge master).reducedNext (bridge master).reducedAllow
        (project source) requests := (bridge master).admitted

def admissions_reflected {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) (requests : List Request) :
    Continuation.Admitted (bridge master).reducedNext (bridge master).reducedAllow
        (project source) requests →
      Continuation.Admitted (bridge master).sourceNext (bridge master).sourceAllow source requests :=
  (bridge master).admittedSource

theorem requirement_persists (memory : Memory) (requests : List Request) :
    (executeRequests memory requests).1.requirement = memory.requirement := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih => exact (ih _).trans (executeInput_requirement memory request)

theorem requirement_transport_exact (memory : Memory) (requests : List Request) :
    (executeRequests memory requests).1.requirement.realizedScope = memory.requirement.scope :=
  (congrArg Requirement.realizedScope (requirement_persists memory requests)).trans memory.requirement.scope_exact

theorem all_future_old_reads (memory : Memory) (requests : List Request) (handle : Nat) (var : SAT.Var)
    (within : handle < memory.register.length) :
    readRegister (executeRequests memory requests).1.register handle var = readRegister memory.register handle var := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih =>
      have continued := Nat.lt_of_lt_of_le within (executeInput_register_monotone memory request)
      exact (ih _ continued).trans (executeInput_old_read memory request handle var within)

/- A request may produce several internal heads. Follow those heads, not just
the request boundaries. Each row is pinned to the actual rich realization. -/
/-- Agreement of one actual internal head. The engine and historical-target
supports have different kinds and different extensions; neither is replaced
by the transport from the initial master or by an ordinal-only surrogate. -/
structure InternalStepAgreement {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : Type 3 where
  head : HistoricalProduction source.cursor
  headExact : head = HistoricalProduction.produce source.cursor
  productionExact : head.production = LiveContinuation.produce (project source).live
  transitionExact : (project (sourceStep source).1, (sourceStep source).2) = step (project source)
  targetExact : (sourceStep source).1.history.targets =
    source.history.targets ++ [resumedTarget head.production]
  targetAccepted : GeneratedStructuralBranchAccept (resumedTarget head.production).context
    (resumedTarget head.production).continuation
  engine : Support.Extension source.cursor.support (sourceStep source).1.cursor.support
  engineExact : engine = cursorReferences source.cursor
  historical : Support.Extension source.history.realization.support (sourceStep source).1.history.realization.support
  historicalExact : historical = source.history.realization.advance.2
  oldHandles : ∀ {target} (ref : Ref source.history.targets target),
    (sourceStep source).1.history.realization.reference
      (extendReference [resumedTarget (LiveContinuation.sourceProduction source.cursor)] ref) =
    historical.references (source.history.realization.reference ref)
  nextRequirement : (sourceStep source).1.requirement = source.requirement

def internalStepAgreement {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : InternalStepAgreement source where
  head := HistoricalProduction.produce source.cursor
  headExact := rfl
  productionExact := rfl
  transitionExact := sourceStep_exact source
  targetExact := rfl
  targetAccepted := (resumedTarget (HistoricalProduction.produce source.cursor).production).origin.accepted
  engine := cursorReferences source.cursor
  engineExact := rfl
  historical := source.history.realization.advance.2
  historicalExact := rfl
  oldHandles := source.history.handle_transport
  nextRequirement := rfl

inductive FollowedStages {input : Nat} (master : UnifiedMaster.Instance input) :
    Source master → Nat → Type 3 where
  | nil (source : Source master) : FollowedStages master source 0
  | step {source : Source master} {count : Nat}
      (head : InternalStepAgreement source)
      (tail : FollowedStages master (sourceStep source).1 count) : FollowedStages master source (count + 1)

def followStages {input : Nat} (master : UnifiedMaster.Instance input) :
    (count : Nat) → (source : Source master) → FollowedStages master source count
  | 0, source => .nil source
  | count + 1, source => .step (internalStepAgreement source) (followStages master count (sourceStep source).1)

def InternalHead {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : Nat → Type 3
  | 0 => ULift.{3} Unit
  | _ + 1 => InternalStepAgreement source

def FollowedStages.head {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} : FollowedStages master source count → InternalHead source count
  | .nil _ => ⟨()⟩
  | .step head _ => head

def FollowedStages.final {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} : FollowedStages master source count → Source master
  | .nil source => source
  | .step _ tail => tail.final

def FollowedStages.events {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} : FollowedStages master source count → List LiveContinuation.Event
  | .nil _ => []
  | .step _ tail => (sourceStep source).2 :: tail.events

/-- Compose the actual current-to-next engine extensions along this execution. -/
def FollowedStages.engineTransport {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} (followed : FollowedStages master source count) :
    Support.Extension source.cursor.support followed.final.cursor.support :=
  match followed with
  | .nil source => Support.Extension.identity source.cursor.support
  | .step head tail => head.engine.compose tail.engineTransport

/-- The target archive has its own extensions, not the engine's kind list. -/
def FollowedStages.historicalTransport {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} (followed : FollowedStages master source count) :
    Support.Extension source.history.realization.support followed.final.history.realization.support :=
  match followed with
  | .nil source => Support.Extension.identity source.history.realization.support
  | .step head tail => head.historical.compose tail.historicalTransport

theorem FollowedStages.engine_reads {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} (followed : FollowedStages master source count)
    {kind} (reference : Ref source.cursor.support.kinds kind) :
    followed.final.cursor.support.read (followed.engineTransport.references reference) =
      source.cursor.support.read reference := followed.engineTransport.reads reference

theorem FollowedStages.historical_reads {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} (followed : FollowedStages master source count)
    {kind} (reference : Ref source.history.realization.support.kinds kind) :
    followed.final.history.realization.support.read (followed.historicalTransport.references reference) =
      source.history.realization.support.read reference := followed.historicalTransport.reads reference

theorem FollowedStages.execution_exact {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {count : Nat} (followed : FollowedStages master source count) :
    (project followed.final, followed.events) = runSteps count (project source) := by
  induction followed with
  | nil source => rfl
  | @step source count head tail ih =>
      change (project tail.final, (sourceStep source).2 :: tail.events) = _
      rw [runSteps, ← head.transitionExact]
      exact congrArg (fun result : Memory × List LiveContinuation.Event =>
        (result.1, (sourceStep source).2 :: result.2)) ih

def requestStageCount {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : Request → Nat
  | .advance count => count
  | .inspect _ _ => 0
  | .propose _ _ _ => 0
  | .obtain handle var => match source.requirement.permission var with
      | none => 0
      | some _ => needed source.history.targets.length handle

def RequestStages {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) : Type 3 :=
  FollowedStages master source (requestStageCount source request)

def requestStages {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) : (request : Request) → RequestStages source request
  | request => followStages master (requestStageCount source request) source

theorem request_internal_execution {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) :
    (runSteps (requestStageCount source request) (project source)).1 =
      (executeInput (project source) request).1 ∧
    (runSteps (requestStageCount source request) (project source)).2 =
      (executeInput (project source) request).2.productions := by
  rw [executeInput_exact]
  cases request with
  | advance count => exact ⟨rfl, rfl⟩
  | inspect handle var => exact ⟨rfl, rfl⟩
  | propose handle var value => exact ⟨rfl, rfl⟩
  | obtain handle var =>
      rw [perform_obtain]
      dsimp only [requestStageCount, project]
      cases permitted : source.requirement.permission var with
      | none => exact ⟨rfl, rfl⟩
      | some permission => exact ⟨rfl, rfl⟩

/-- Each node is the actual current request, its produced response evidence,
 rich/reduced agreement and engine-reference extension from the master. -/
inductive Followed {input : Nat} (master : UnifiedMaster.Instance input) :
    Source master → List Request → Type 3 where
  | nil (source : Source master) : Followed master source []
  | cons {source : Source master} {request : Request} {rest : List Request}
      (response : RequestEvidence (project source) request (executeInput (project source) request))
      (criterion : RequestCriterion (project source) request (executeInput (project source) request))
      (rich : RichOperation source request)
      (richExact : rich = sourceProduced source request)
      (nextExact : (project (sourcePerform source request).1, (sourcePerform source request).2) =
        executeInput (project source) request)
      (requirementExact : (executeInput (project source) request).1.requirement = source.requirement)
      (references : Support.Extension master.cursor.support (sourcePerform source request).1.cursor.support)
      (referencesExact : references = (sourcePerform source request).1.history.references)
      (stages : FollowedStages master source (requestStageCount source request))
      (stageMemoryExact : project stages.final = (executeInput (project source) request).1)
      (stageEventsExact : stages.events = (executeInput (project source) request).2.productions)
      (tail : Followed master (sourcePerform source request).1 rest) :
      Followed master source (request :: rest)

def all_executed_determinations_followed {input : Nat} (master : UnifiedMaster.Instance input) :
    (source : Source master) → (requests : List Request) → Followed master source requests
  | source, [] => .nil source
  | source, request :: rest =>
      .cons (executedEvidence (project source) request) (executed_reply_criterion (project source) request)
        (sourceProduced source request) rfl (sourcePerform_exact source request)
        (executeInput_requirement (project source) request)
        (sourcePerform source request).1.history.references rfl
        (requestStages master source request)
        ((congrArg Prod.fst (requestStages master source request).execution_exact).trans
          (request_internal_execution source request).1)
        ((congrArg Prod.snd (requestStages master source request).execution_exact).trans
          (request_internal_execution source request).2)
        (all_executed_determinations_followed master (sourcePerform source request).1 rest)

/-- Independent finite response contract on the real executor. -/
def FiniteResponseCriterion : Memory → List Request → Prop
  | _, [] => True
  | memory, request :: rest =>
      RequestCriterion memory request (executeInput memory request) ∧
        FiniteResponseCriterion (executeInput memory request).1 rest

theorem Followed.satisfies {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {requests : List Request} (followed : Followed master source requests) :
    FiniteResponseCriterion (project source) requests := by
  induction followed with
  | nil source => exact True.intro
  | cons response criterion rich richExact nextExact requirementExact references referencesExact stages
      memoryExact eventsExact tail ih =>
      refine ⟨criterion, ?_⟩
      rw [← congrArg Prod.fst nextExact]
      exact ih

/-- The internal stages carried by the head node of a followed interaction. -/
def Followed.stages {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {request : Request} {rest : List Request} :
    Followed master source (request :: rest) → FollowedStages master source (requestStageCount source request)
  | .cons _ _ _ _ _ _ _ _ stages _ _ _ => stages

/-- The engine-reference extension from the master carried by the head node.
The historical-target support has a separate extension. -/
def Followed.references {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {request : Request} {rest : List Request} :
    Followed master source (request :: rest) →
      Support.Extension master.cursor.support (sourcePerform source request).1.cursor.support
  | .cons _ _ _ _ _ _ references _ _ _ _ _ => references

theorem Followed.references_exact {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {request : Request} {rest : List Request}
    (followed : Followed master source (request :: rest)) :
    followed.references = (sourcePerform source request).1.history.references := by
  cases followed with
  | cons _ _ _ _ _ _ _ referencesExact _ _ _ _ => exact referencesExact

/-- Every internal stage of one request, followed in producer order, is the
actual worker execution of that request. -/
theorem request_stages_exact {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) :
    (project (requestStages master source request).final, (requestStages master source request).events) =
      ((executeInput (project source) request).1, (executeInput (project source) request).2.productions) :=
  (requestStages master source request).execution_exact.trans
    (Prod.ext (request_internal_execution source request).1 (request_internal_execution source request).2)

theorem all_finite_responses_satisfy {input : Nat} (master : UnifiedMaster.Instance input)
    (source : Source master) (requests : List Request) : FiniteResponseCriterion (project source) requests :=
  (all_executed_determinations_followed master source requests).satisfies

theorem executeRequests_head_entire (memory : Memory) (request : Request) (rest : List Request) :
    executeRequests memory (request :: rest) =
      let head := executeProducedInput memory request
      let tail := executeRequests head.1.1 rest
      (tail.1, head.1.2 :: tail.2) := rfl

theorem initial_memories_equal {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (left right : RoleOccurrenceProfile master.roles) :
    start master requirement left = start master requirement right :=
  agent_memory_factors_through_output master requirement left right
    (master.normalization.targets_converge left right)

theorem initial_profile_not_recoverable {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) :
    ¬ (∃ recover : Memory → RoleOccurrenceProfile master.roles,
      ∀ profile, recover (start master requirement profile) = profile) := by
  intro alleged
  obtain ⟨recover, exact⟩ := alleged
  let pair := master.distinctPair
  exact pair.distinct ((exact pair.left).symm.trans
    ((congrArg recover (initial_memories_equal master requirement pair.left pair.right)).trans
      (exact pair.right)))

theorem forgotten_sources_same_future {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (left right : RoleOccurrenceProfile master.roles)
    (requests : List Request) :
    executeRequests (start master requirement left) requests =
      executeRequests (start master requirement right) requests :=
  congrArg (fun memory => executeRequests memory requests)
    (initial_memories_equal master requirement left right)

/-- Closed on the shared master and the actual executor. No memory, register
or independent responder is accepted as an extra certification parameter. -/
structure Certificate {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) : Type 3 where
  private mk ::
  initialExact : ∀ profile, project (sourceStart master requirement profile) = start master requirement profile
  headExact : ∀ memory request, executeInput memory request = perform memory request
  headResources : ∀ memory request, executeInput memory request =
    (interactionProducer.operation (memory, ULift.up request, PUnit.unit)).1
  headEntire : ∀ memory request, executeProducedInput memory request =
    interactionProducer.operation (memory, ULift.up request, PUnit.unit)
  horizon : ∀ memory request one two,
    (executeRequests memory (request :: one)).2.head? = (executeRequests memory (request :: two)).2.head?
  formedRegister : ∀ memory, (step memory).1.register =
    memory.register ++ [resumedTarget (LiveContinuation.produce memory.live)]
  progress : ∀ memory, (step memory).1.register.length = memory.register.length + 1
  oldReads : ∀ count memory handle var, handle < memory.register.length →
    readRegister (runSteps count memory).1.register handle var = readRegister memory.register handle var
  allOldReads : ∀ memory requests handle var, handle < memory.register.length →
    readRegister (executeRequests memory requests).1.register handle var = readRegister memory.register handle var
  handlesTransport : ∀ register extra handle, handle < register.length →
    resolveHandle (register ++ extra) handle = (resolveHandle register handle).map
      (fun occurrence => ⟨occurrence.1, extendReference extra occurrence.2⟩)
  historicalTargets : ∀ profile (history : History master profile),
    history.realization.materialRegister = history.targets
  historicalFormation : ∀ profile (history : History master profile), HistoricalFormation history.realization.support
  richOperations : ∀ (source : Source master) request, RichOperation source request
  richOperationsExact : ∀ source request, richOperations source request = sourceProduced source request
  richResultExact : ∀ source request, (richOperations source request).result = sourcePerform source request
  historicalHandles : ∀ profile (history : History master profile) {target}
    (ref : Ref history.targets target),
    (History.step history).realization.reference
      (extendReference [resumedTarget (LiveContinuation.sourceProduction history.cursor)] ref) =
      history.realization.advance.2.references (history.realization.reference ref)
  historicalPositions : ∀ profile (history : History master profile) {target}
    (ref : Ref history.targets target),
    ((History.step history).realization.reference
      (extendReference [resumedTarget (LiveContinuation.sourceProduction history.cursor)] ref)).position =
        (history.realization.reference ref).position + history.realization.advance.2.added
  historicalDistinctness : ∀ profile (history : History master profile) {target}
    (one two : Ref history.targets target),
    history.realization.reference one = history.realization.reference two → one = two
  retainedCriterion : ∀ {req register handle var value} (authorization : Authorization req register handle var value),
    GeneratedStructuralBranchAccept authorization.occurrence.1.context authorization.occurrence.1.continuation
  targetsAccepted : ∀ target : AnswerTarget, GeneratedStructuralBranchAccept target.context target.continuation
  targetReads : ∀ (target : AnswerTarget) var, target.read var = target.continuation.1 var
  resumedOrigin : ∀ {memory : LiveContinuation.Memory} (production : LiveContinuation.Production memory),
    (resumedTarget production).origin = TargetOrigin.resumed production
  cachedObtain : ∀ memory handle var, handle < memory.register.length →
    (executeInput memory (.obtain handle var)).2.productions = []
  replies : ∀ memory request, RequestEvidence memory request (executeInput memory request)
  candidateExact : ∀ req register handle var value,
    Nonempty (Authorization req register handle var value) ↔
      (decideReply req register handle var (some value)).message = .answer handle var value
  inspectionReturns : ∀ req register handle var value (_authorization : Authorization req register handle var value),
    (decideReply req register handle var none).message = .answer handle var value
  obtainReturns : ∀ memory handle var (permission : Ref memory.requirement.realizedScope var),
    (executeInput memory (.obtain handle var)).2.message =
      .answer handle var (obtainedAuthorization memory handle var permission).1
  obtainSize : ∀ memory handle var (_permission : Ref memory.requirement.realizedScope var),
    memory.register.length ≤ handle → (executeInput memory (.obtain handle var)).1.register.length = handle + 1
  obtainWork : ∀ memory handle var (_permission : Ref memory.requirement.realizedScope var),
    (executeInput memory (.obtain handle var)).2.productions.length = needed memory.register.length handle
  refusalsPreserveMemory : ∀ memory request handle var reason,
    (executeInput memory request).2.message = .refused handle var reason →
      (executeInput memory request).1 = memory
  followed : ∀ profile requests, Followed master (sourceStart master requirement profile) requests
  followedStages : ∀ profile request rest,
    (followed profile (request :: rest)).stages = requestStages master (sourceStart master requirement profile) request
  followedReferences : ∀ profile request rest,
    (followed profile (request :: rest)).references =
      (sourcePerform (sourceStart master requirement profile) request).1.history.references
  internalStages : ∀ (source : Source master) request,
    (project (requestStages master source request).final, (requestStages master source request).events) =
      ((executeInput (project source) request).1, (executeInput (project source) request).2.productions)
  satisfaction : ∀ profile requests, FiniteResponseCriterion (start master requirement profile) requests
  entireHead : ∀ memory request rest, executeRequests memory (request :: rest) =
    let head := executeProducedInput memory request
    let tail := executeRequests head.1.1 rest
    (tail.1, head.1.2 :: tail.2)
  futures : ∀ source requests, project (Continuation.run (bridge master).sourceNext source requests) =
    (executeRequests (project source) requests).1
  events : ∀ source requests,
    Continuation.events (bridge master).sourceNext (bridge master).sourceEvent source requests =
      (executeRequests (project source) requests).2
  reads : ∀ source requests,
    Continuation.observations (bridge master).sourceNext (bridge master).sourceRead source requests =
      Continuation.observations (bridge master).reducedNext (bridge master).reducedRead (project source) requests
  admissions : ∀ source requests,
    Continuation.Admitted (bridge master).sourceNext (bridge master).sourceAllow source requests →
      Continuation.Admitted (bridge master).reducedNext (bridge master).reducedAllow (project source) requests
  reflection : ∀ source requests,
    Continuation.Admitted (bridge master).reducedNext (bridge master).reducedAllow (project source) requests →
      Continuation.Admitted (bridge master).sourceNext (bridge master).sourceAllow source requests
  receivedReturn : ∀ req {register cursor} (realization : RegisterRealization register cursor) request
    (witness : RichAdmission req realization request),
    receivedAdmission req realization request (realizeAdmission req realization request witness) = witness
  realizedReturn : ∀ req {register cursor} (realization : RegisterRealization register cursor) request
    (witness : Admission req register request),
    realizeAdmission req realization request (receivedAdmission req realization request witness) = witness
  requirementPersistent : ∀ memory requests,
    (executeRequests memory requests).1.requirement = memory.requirement
  requirementReading : ∀ memory requests,
    (executeRequests memory requests).1.requirement.realizedScope = memory.requirement.scope
  memoryFactor : ∀ left right, master.normalization.target left = master.normalization.target right →
    start master requirement left = start master requirement right
  irrecoverable : ¬ (∃ recover : Memory → RoleOccurrenceProfile master.roles,
    ∀ profile, recover (start master requirement profile) = profile)
  futureIndistinguishable : ∀ left right requests,
    executeRequests (start master requirement left) requests = executeRequests (start master requirement right) requests

def certify {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Requirement) :
    Certificate master requirement where
  initialExact := initialize_from_master_exact master requirement
  headExact := executeInput_exact
  headResources := head_uses_current_resources
  headEntire := head_production_entire_exact
  horizon := head_horizon_independent
  formedRegister := executed_step_register_exact
  progress := register_grows_by_one
  oldReads := runSteps_old_read
  allOldReads := all_future_old_reads
  handlesTransport := resolveHandle_transport
  historicalTargets := fun _ history => history.realization.materialRegister_exact
  historicalFormation := fun _ history => history.realization.formation
  richOperations := sourceProduced
  richOperationsExact := fun _ _ => rfl
  richResultExact := fun _ _ => rfl
  historicalHandles := fun _ history => history.handle_transport
  historicalPositions := fun _ history => history.realization.advance_position
  historicalDistinctness := fun _ history => history.realization.injective
  retainedCriterion := authorized_target_accepted
  targetsAccepted := AnswerTarget.accepted
  targetReads := fun _ _ => rfl
  resumedOrigin := fun _ => rfl
  cachedObtain := cached_obtain_runs_no_stage
  replies := executedEvidence
  candidateExact := candidate_authorization_exact
  inspectionReturns := admitted_inspection_returns
  obtainReturns := obtain_produces_and_returns
  obtainSize := obtain_register_exact
  obtainWork := obtain_work_exact
  refusalsPreserveMemory := refusal_preserves_memory
  followed := fun profile => all_executed_determinations_followed master (sourceStart master requirement profile)
  followedStages := fun _ _ _ => rfl
  followedReferences := fun _ _ _ => rfl
  internalStages := request_stages_exact
  satisfaction := fun profile => all_finite_responses_satisfy master (sourceStart master requirement profile)
  entireHead := executeRequests_head_entire
  futures := all_future_requests_exact master
  events := all_future_events_exact master
  reads := all_future_reads_exact master
  admissions := admissions_forward master
  reflection := admissions_reflected master
  receivedReturn := admission_received_return
  realizedReturn := admission_realized_return
  requirementPersistent := requirement_persists
  requirementReading := requirement_transport_exact
  memoryFactor := agent_memory_factors_through_output master requirement
  irrecoverable := initial_profile_not_recoverable master requirement
  futureIndistinguishable := forgotten_sources_same_future master requirement

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.executeRequests_final
#print axioms ConstitutiveSearch.Agent.executeRequests_events
#print axioms ConstitutiveSearch.Agent.all_future_requests_exact
#print axioms ConstitutiveSearch.Agent.all_future_events_exact
#print axioms ConstitutiveSearch.Agent.all_future_reads_exact
#print axioms ConstitutiveSearch.Agent.admissions_forward
#print axioms ConstitutiveSearch.Agent.admissions_reflected
#print axioms ConstitutiveSearch.Agent.requirement_persists
#print axioms ConstitutiveSearch.Agent.requirement_transport_exact
#print axioms ConstitutiveSearch.Agent.all_future_old_reads
#print axioms ConstitutiveSearch.Agent.FollowedStages
#print axioms ConstitutiveSearch.Agent.InternalStepAgreement
#print axioms ConstitutiveSearch.Agent.InternalHead
#print axioms ConstitutiveSearch.Agent.internalStepAgreement
#print axioms ConstitutiveSearch.Agent.FollowedStages.head
#print axioms ConstitutiveSearch.Agent.FollowedStages.final
#print axioms ConstitutiveSearch.Agent.FollowedStages.events
#print axioms ConstitutiveSearch.Agent.FollowedStages.engineTransport
#print axioms ConstitutiveSearch.Agent.FollowedStages.historicalTransport
#print axioms ConstitutiveSearch.Agent.FollowedStages.engine_reads
#print axioms ConstitutiveSearch.Agent.FollowedStages.historical_reads
#print axioms ConstitutiveSearch.Agent.FollowedStages.execution_exact
#print axioms ConstitutiveSearch.Agent.requestStageCount
#print axioms ConstitutiveSearch.Agent.request_internal_execution
#print axioms ConstitutiveSearch.Agent.FiniteResponseCriterion
#print axioms ConstitutiveSearch.Agent.Followed.satisfies
#print axioms ConstitutiveSearch.Agent.all_finite_responses_satisfy
#print axioms ConstitutiveSearch.Agent.Followed.stages
#print axioms ConstitutiveSearch.Agent.Followed.references
#print axioms ConstitutiveSearch.Agent.Followed.references_exact
#print axioms ConstitutiveSearch.Agent.request_stages_exact
#print axioms ConstitutiveSearch.Agent.executeRequests_head_entire
#print axioms ConstitutiveSearch.Agent.followStages
#print axioms ConstitutiveSearch.Agent.RequestStages
#print axioms ConstitutiveSearch.Agent.requestStages
#print axioms ConstitutiveSearch.Agent.all_executed_determinations_followed
#print axioms ConstitutiveSearch.Agent.initial_memories_equal
#print axioms ConstitutiveSearch.Agent.initial_profile_not_recoverable
#print axioms ConstitutiveSearch.Agent.forgotten_sources_same_future
#print axioms ConstitutiveSearch.Agent.certify
/- AXIOM_AUDIT_END -/
