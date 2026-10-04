import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.LiveResourceContinuation
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparation

/-!
# Continuation after a produced profile normalization

The restricted interface permits real search-step requests and reads of the
produced continuation at any constituted role and any variable. It excludes
reading the original profile or its normalization trace. The historical API
remains available separately. This contract does not forget the provenance
which the next discovery still consumes.

The forgotten distinction is an actual normalization input, not a difference
between chronological canonical search prefixes. These are different domains.
The public construction below derives both its normalization and its restart
cursor from one resource execution; no second family is introduced.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation
open SAT ConstitutiveSearch.Grouping

/-- Derived ordinal of a constituted role and a variable of its continuation.
Valid role bounds are checked by the admission predicate below. -/
structure Query where
  slot : Nat
  var : Var

/-- Materialize the live readers once, from the actual produced continuations.
Only this preparation traverses the executed role chain. -/
def targetReaders : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} → (reduction : ExecutedRoleReductionHistory program) →
    ExecutedOperationalTargetProfile reduction → List Assignment
  | _, _, _, _, _, .nil, _ => []
  | _, _, _, _, _, .step _ rest, target => target.1.1 :: targetReaders rest target.2

theorem targetReaders_length : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} → (reduction : ExecutedRoleReductionHistory program) →
    (target : ExecutedOperationalTargetProfile reduction) → (targetReaders reduction target).length = count
  | _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, .step _ rest, target => congrArg Nat.succ (targetReaders_length rest target.2)

/-- Runtime inspection reads only the stored live readers. -/
def lookupReader : Nat → List Assignment → Option Assignment
  | _, [] => none
  | 0, reader :: _ => some reader
  | slot + 1, _ :: rest => lookupReader slot rest

def readTarget (query : Query) (readers : List Assignment) : Option Bool :=
  (lookupReader query.slot readers).map (fun reader => reader query.var)

theorem lookupReader_present : ∀ (readers : List Assignment) (slot : Nat),
    slot < readers.length → ∃ reader, lookupReader slot readers = some reader
  | [], _, impossible => False.elim (Nat.not_lt_zero _ impossible)
  | reader :: _, 0, _ => ⟨reader, rfl⟩
  | _ :: rest, slot + 1, within => lookupReader_present rest slot (Nat.lt_of_succ_lt_succ within)

variable {count : Nat} {state : CausalConstitutiveState}
  {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
  {program : RoleIndexedProgram roles} {reduction : ExecutedRoleReductionHistory program}

structure Memory (_normalization : ExecutedCausalNormalization reduction) : Type 3 where
  live : LiveContinuation.Memory
  output : ExecutedOperationalTargetProfile reduction
  readers : List Assignment
  readersExact : readers = targetReaders reduction output

def Memory.ofOutput (normalization : ExecutedCausalNormalization reduction)
    (live : LiveContinuation.Memory) (output : ExecutedOperationalTargetProfile reduction) : Memory normalization :=
  ⟨live, output, targetReaders reduction output, rfl⟩

/-- The historical side keeps the actual source and executed result. -/
structure Source (normalization : ExecutedCausalNormalization reduction) : Type 3 where
  private mk ::
  cursor : MasterResources.Cursor
  profile : RoleOccurrenceProfile roles
  result : ExecutedChainNormalization normalization.constitutiveChain profile
  resultExact : result = normalization.result profile
  output : ExecutedOperationalTargetProfile reduction
  outputExact : output = result.target
  readers : List Assignment
  readersExact : readers = targetReaders reduction output

def produce (normalization : ExecutedCausalNormalization reduction)
    (cursor : MasterResources.Cursor) (profile : RoleOccurrenceProfile roles) : Source normalization :=
  let result := normalization.result profile
  let output := result.target
  ⟨cursor, profile, result, rfl, output, rfl, targetReaders reduction output, rfl⟩

def project {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) : Memory normalization :=
  ⟨LiveContinuation.project source.cursor, source.output, source.readers, source.readersExact⟩

theorem output_is_executed {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) : (project source).output = normalization.target source.profile := by
  change source.output = (normalization.result source.profile).target
  rw [source.outputExact, source.resultExact]

theorem output_accepted {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) : RoleSemantics.TargetAccept reduction (project source).output := by
  have accepted := RoleSemantics.profilePreserves normalization.constitutivePreservation
    source.profile (canonicalRoleProfilePayload roles source.profile)
    (RoleSemantics.canonicalPayload_accepted roles source.profile)
  rw [RoleSemantics.canonicalAction_exact] at accepted
  rw [output_is_executed, normalization.target_exact]
  exact accepted

inductive Input (normalization : ExecutedCausalNormalization reduction) where
  | advance (steps : Nat)
  | inspect (query : Query)

inductive Event (normalization : ExecutedCausalNormalization reduction) : Type 3 where
  | execution (productions : List LiveContinuation.Event)
  | observed (query : Query) (value : Option Bool)

def next {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) : Input normalization → Memory normalization
  | .advance steps => ⟨LiveContinuation.run steps memory.live, memory.output, memory.readers, memory.readersExact⟩
  | .inspect _ => memory

def sourceNext {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) : Input normalization → Source normalization
  | .advance steps => ⟨LiveContinuation.sourceRun steps source.cursor,
      source.profile, source.result, source.resultExact, source.output, source.outputExact,
      source.readers, source.readersExact⟩
  | .inspect _ => source

def event {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) : Input normalization → Event normalization
  | .advance steps => .execution (LiveContinuation.events steps memory.live)
  | .inspect query => .observed query (readTarget query memory.readers)

/-- One runtime request produces both the next memory and its event. -/
def executeInput {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) : Input normalization → Memory normalization × Event normalization
  | .advance steps =>
      let produced := LiveContinuation.execute steps memory.live
      (⟨produced.1, memory.output, memory.readers, memory.readersExact⟩, .execution produced.2)
  | .inspect query => (memory, .observed query (readTarget query memory.readers))

theorem executeInput_next {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (input : Input normalization) :
    (executeInput memory input).1 = next memory input := by
  cases input with
  | advance steps =>
      exact congrArg (fun live => Memory.mk live memory.output memory.readers memory.readersExact)
        (LiveContinuation.execute_state steps memory.live)
  | inspect => rfl

theorem executeInput_event {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (input : Input normalization) :
    (executeInput memory input).2 = event memory input := by
  cases input with
  | advance steps => exact congrArg Event.execution (LiveContinuation.execute_events steps memory.live)
  | inspect => rfl

def executeRequests {normalization : ExecutedCausalNormalization reduction} :
    Memory normalization → List (Input normalization) → Memory normalization × List (Event normalization)
  | memory, [] => (memory, [])
  | memory, input :: rest =>
      let produced := executeInput memory input
      let future := executeRequests produced.1 rest
      (future.1, produced.2 :: future.2)

theorem executeRequests_next {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (inputs : List (Input normalization)) :
    (executeRequests memory inputs).1 = Continuation.run next memory inputs := by
  induction inputs generalizing memory with
  | nil => rfl
  | cons input rest ih =>
      exact (ih (executeInput memory input).1).trans
        (congrArg (fun nextMemory => Continuation.run next nextMemory rest) (executeInput_next memory input))

theorem executeRequests_events {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (inputs : List (Input normalization)) :
    (executeRequests memory inputs).2 = Continuation.events next event memory inputs := by
  induction inputs generalizing memory with
  | nil => rfl
  | cons input rest ih =>
      change (executeInput memory input).2 :: (executeRequests (executeInput memory input).1 rest).2 = _
      rw [ih, executeInput_event, executeInput_next]
      rfl

def sourceEvent {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) : Input normalization → Event normalization
  | .advance steps => .execution (LiveContinuation.sourceEvents steps source.cursor)
  | .inspect query => .observed query (readTarget query source.readers)

theorem next_exact {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) (input : Input normalization) :
    project (sourceNext source input) = next (project source) input := by
  cases input with
  | advance steps =>
      exact congrArg (fun live => Memory.mk live source.output source.readers source.readersExact)
        (LiveContinuation.run_exact steps source.cursor)
  | inspect => rfl

theorem event_exact {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) (input : Input normalization) :
    sourceEvent source input = event (project source) input := by
  cases input with
  | advance steps => exact congrArg Event.execution (LiveContinuation.events_exact steps source.cursor)
  | inspect => rfl

/-- These are the advertised observations, not retrospective source queries. -/
def read {normalization : ExecutedCausalNormalization reduction} (memory : Memory normalization) :=
  (LiveContinuation.read memory.live, memory.output)

def allow {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) : Input normalization → Type 3
  | .advance _ => ULift.{3} Unit
  | .inspect query => ULift.{3} (PLift (query.slot < memory.readers.length))

/-- Admission is pinned to the number of produced role continuations, not
merely to agreement between two implementations of the same predicate. -/
theorem inspect_admitted_iff {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (query : Query) :
    Nonempty (allow memory (.inspect query)) ↔ query.slot < count := by
  have size : memory.readers.length = count :=
    (congrArg List.length memory.readersExact).trans (targetReaders_length reduction memory.output)
  constructor
  · intro ⟨witness⟩
    exact size ▸ witness.down.down
  · intro within
    exact ⟨⟨⟨size.symm ▸ within⟩⟩⟩

theorem inspect_out_of_bounds {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (query : Query) (outside : count ≤ query.slot) :
    ¬ Nonempty (allow memory (.inspect query)) :=
  fun admitted => Nat.not_lt_of_ge outside ((inspect_admitted_iff memory query).mp admitted)

/-- The observable value is a read of the actual produced output. This law
is independent of the source/restart agreement law. -/
theorem inspect_event_exact {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (query : Query) :
    event memory (.inspect query) =
      .observed query (readTarget query (targetReaders reduction memory.output)) := by
  change Event.observed query (readTarget query memory.readers) = _
  rw [memory.readersExact]

theorem source_inspect_event_exact {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) (query : Query) :
    sourceEvent source (.inspect query) =
      .observed query (readTarget query (targetReaders reduction (normalization.target source.profile))) := by
  rw [event_exact, inspect_event_exact, output_is_executed]

theorem execute_inspect_exact {normalization : ExecutedCausalNormalization reduction}
    (memory : Memory normalization) (query : Query) :
    (executeInput memory (.inspect query)).2 =
      .observed query (readTarget query (targetReaders reduction memory.output)) :=
  (executeInput_event memory (.inspect query)).trans (inspect_event_exact memory query)

def contract (normalization : ExecutedCausalNormalization reduction) :
    Continuation.Exact (Source normalization) (Memory normalization)
      (Input normalization) (Event normalization)
      ((Nat × List Var × Nat) × ExecutedOperationalTargetProfile reduction) where
  project := project
  sourceNext := sourceNext
  reducedNext := next
  sourceAllow := fun source input => allow (project source) input
  reducedAllow := allow
  toReduced := fun _ _ witness => witness
  toSource := fun _ _ witness => witness
  sourceEvent := sourceEvent
  reducedEvent := event
  sourceRead := fun source => read (project source)
  reducedRead := read
  nextLaw := next_exact
  eventLaw := event_exact
  readLaw := fun _ => rfl

theorem all_future_events (normalization : ExecutedCausalNormalization reduction)
    (source : Source normalization) (inputs : List (Input normalization)) :
    Continuation.events sourceNext sourceEvent source inputs =
      Continuation.events next event (project source) inputs :=
  (contract normalization).events_exact source inputs

theorem all_future_reads (normalization : ExecutedCausalNormalization reduction)
    (source : Source normalization) (inputs : List (Input normalization)) :
    Continuation.observations sourceNext (fun source => read (project source)) source inputs =
      Continuation.observations next read (project source) inputs :=
  (contract normalization).observations_exact source inputs

def all_requests_admitted {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) {inputs : List (Input normalization)}
    (admitted : Continuation.Admitted sourceNext (fun source input => allow (project source) input) source inputs) :
    Continuation.Admitted next allow (project source) inputs :=
  (contract normalization).admitted admitted

def all_requests_reflected {normalization : ExecutedCausalNormalization reduction}
    (source : Source normalization) {inputs : List (Input normalization)}
    (admitted : Continuation.Admitted next allow (project source) inputs) :
    Continuation.Admitted sourceNext (fun source input => allow (project source) input) source inputs :=
  (contract normalization).admittedSource admitted

theorem same_memory (normalization : ExecutedCausalNormalization reduction)
    (cursor : MasterResources.Cursor) (left right : RoleOccurrenceProfile roles) :
    project (produce normalization cursor left) = project (produce normalization cursor right) :=
  congrArg (Memory.ofOutput normalization (LiveContinuation.project cursor)) (normalization.targets_converge left right)

theorem memory_fibres (normalization : ExecutedCausalNormalization reduction)
    (cursor : MasterResources.Cursor) (left right : RoleOccurrenceProfile roles) :
    project (produce normalization cursor left) = project (produce normalization cursor right) ↔
      normalization.target left = normalization.target right := by
  constructor
  · intro same
    exact congrArg Memory.output same
  · intro same
    exact congrArg (Memory.ofOutput normalization (LiveContinuation.project cursor)) same

theorem profile_not_recoverable (normalization : ExecutedCausalNormalization reduction)
    (cursor : MasterResources.Cursor) (left right : RoleOccurrenceProfile roles) (distinct : left ≠ right) :
    ¬ (∃ recover : Memory normalization → RoleOccurrenceProfile roles,
      ∀ profile, recover (project (produce normalization cursor profile)) = profile) := by
  intro ⟨recover, correct⟩
  exact distinct ((correct left).symm.trans
    ((congrArg recover (same_memory normalization cursor left right)).trans (correct right)))

theorem same_all_future_events (normalization : ExecutedCausalNormalization reduction)
    (cursor : MasterResources.Cursor) (left right : RoleOccurrenceProfile roles)
    (inputs : List (Input normalization)) :
    Continuation.events sourceNext sourceEvent (produce normalization cursor left) inputs =
      Continuation.events sourceNext sourceEvent (produce normalization cursor right) inputs := by
  rw [all_future_events, all_future_events, same_memory normalization cursor left right]

/-- One execution supplies both the constitutive chain and the restart point. -/
def publicOrigin (input : Nat) := MasterResources.initialCursor
    (initialThreadedConstitutiveStateFromInitialization (initializeConstitutiveHistory input))
    (initialOperationalPrefix input)
    (initialThreadedConstitutiveStateFromInitialization_fresh (initializeConstitutiveHistory input))

def publicExecution (input : Nat) :=
  MasterResources.execute (resolutionLength input) (publicOrigin input)

def publicNormalization (input : Nat) :=
  executedCausalNormalization (publicExecution input).1.stagewiseDecomposition.reduction

def publicRoles (input : Nat) := (publicExecution input).1.stagewiseDecomposition.roles
def publicCursor (input : Nat) := (publicExecution input).2

/-- Executable entry: share one execution, rather than preparing each projection anew. -/
def publicProduce (input : Nat) (profile : RoleOccurrenceProfile (publicRoles input)) :
    Source (publicNormalization input) :=
  let origin := publicOrigin input
  let executed := MasterResources.execute (resolutionLength input) origin
  let normalization := executedCausalNormalization executed.1.stagewiseDecomposition.reduction
  produce (state := causalStateOfThreadedState origin.state) normalization executed.2 profile

theorem publicProduce_exact (input : Nat) (profile : RoleOccurrenceProfile (publicRoles input)) :
    publicProduce input profile = produce (publicNormalization input) (publicCursor input) profile := rfl

def publicLeft (input : Nat) := (publicRoles input).headTransformedProfile
def publicRight (input : Nat) := (publicRoles input).headRetainedProfile

def publicStart (input : Nat) : Memory (publicNormalization input) :=
  let origin := publicOrigin input
  let executed := MasterResources.execute (resolutionLength input) origin
  let normalization := executedCausalNormalization executed.1.stagewiseDecomposition.reduction
  let profile := executed.1.stagewiseDecomposition.roles.headTransformedProfile
  project (produce (state := causalStateOfThreadedState origin.state) normalization executed.2 profile)

theorem publicStart_exact (input : Nat) :
    publicStart input = project (publicProduce input (publicLeft input)) := rfl

theorem public_reader_count (input : Nat) : (publicStart input).readers.length = input + 1 :=
  targetReaders_length _ _

def publicFirstQuery : Query := ⟨0, 0⟩

def publicFirstQuery_admitted (input : Nat) :
    allow (publicStart input) (.inspect publicFirstQuery) := by
  refine ⟨⟨?_⟩⟩
  change 0 < (publicStart input).readers.length
  rw [public_reader_count]
  exact Nat.zero_lt_succ input

theorem public_first_read_exists (input : Nat) :
    ∃ value, readTarget publicFirstQuery (publicStart input).readers = some value := by
  have within : 0 < (publicStart input).readers.length := by
    rw [public_reader_count]
    exact Nat.zero_lt_succ input
  rcases lookupReader_present (publicStart input).readers 0 within with ⟨reader, exactRead⟩
  exact ⟨reader 0, congrArg (Option.map (fun reader : Assignment => reader 0)) exactRead⟩

theorem public_distinct (input : Nat) : publicLeft input ≠ publicRight input :=
  (publicRoles input).headProfilesDistinct (Nat.zero_lt_succ input)

theorem public_same_memory (input : Nat) :
    project (produce (publicNormalization input) (publicCursor input) (publicLeft input)) =
      project (produce (publicNormalization input) (publicCursor input) (publicRight input)) :=
  same_memory _ _ _ _

theorem public_profile_irrecoverable (input : Nat) :
    ¬ (∃ recover : Memory (publicNormalization input) → RoleOccurrenceProfile (publicRoles input),
      ∀ profile, recover (project (produce (publicNormalization input) (publicCursor input) profile)) = profile) :=
  profile_not_recoverable _ _ _ _ (public_distinct input)

theorem public_execution_exact (input : Nat) :
    (publicExecution input).1 = publicCausalOperationalExecution input :=
  MasterResources.execute_erases _ _

theorem public_all_future_events (input : Nat) (inputs : List (Input (publicNormalization input))) :
    Continuation.events sourceNext sourceEvent
        (produce (publicNormalization input) (publicCursor input) (publicLeft input)) inputs =
      Continuation.events sourceNext sourceEvent
        (produce (publicNormalization input) (publicCursor input) (publicRight input)) inputs :=
  same_all_future_events _ _ _ _ inputs

/-- Scientific evidence is separate from the memory passed to the runtime. -/
structure PublicContractCertificate (input : Nat) : Prop where
  executionExact : (publicExecution input).1 = publicCausalOperationalExecution input
  outputExact : ∀ profile, (project (publicProduce input profile)).output =
    (publicNormalization input).target profile
  outputAccepted : ∀ profile,
    RoleSemantics.TargetAccept (publicExecution input).1.stagewiseDecomposition.reduction
      (project (publicProduce input profile)).output
  distinctSources : publicLeft input ≠ publicRight input
  commonMemory : project (publicProduce input (publicLeft input)) =
    project (publicProduce input (publicRight input))
  noSourceDecoder : ¬ (∃ recover : Memory (publicNormalization input) → RoleOccurrenceProfile (publicRoles input),
    ∀ profile, recover (project (publicProduce input profile)) = profile)
  futureEventsExact : ∀ profile inputs,
    Continuation.events sourceNext sourceEvent (publicProduce input profile) inputs =
      Continuation.events next event (project (publicProduce input profile)) inputs
  futureReadsExact : ∀ profile inputs,
    Continuation.observations sourceNext (fun source => read (project source)) (publicProduce input profile) inputs =
      Continuation.observations next read (project (publicProduce input profile)) inputs
  oldTarget : Nonempty (ExactCausalExponentialTarget input)

theorem publicContractCertificate (input : Nat) : PublicContractCertificate input where
  executionExact := public_execution_exact input
  outputExact := fun profile => output_is_executed (publicProduce input profile)
  outputAccepted := fun profile => output_accepted (publicProduce input profile)
  distinctSources := public_distinct input
  commonMemory := public_same_memory input
  noSourceDecoder := public_profile_irrecoverable input
  futureEventsExact := fun profile inputs => all_future_events _ (publicProduce input profile) inputs
  futureReadsExact := fun profile inputs => all_future_reads _ (publicProduce input profile) inputs
  oldTarget := ⟨exactCausalExponentialTarget input⟩

end ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.inspect_admitted_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.inspect_out_of_bounds
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.inspect_event_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.source_inspect_event_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.execute_inspect_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.Query
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.targetReaders
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.targetReaders_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.lookupReader
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.lookupReader_present
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.readTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.produce
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.output_is_executed
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.output_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.next_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.event_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.contract
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.all_future_events
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.all_future_reads
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.all_requests_admitted
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.all_requests_reflected
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.executeInput
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.executeInput_next
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.executeInput_event
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.executeRequests
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.executeRequests_next
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.executeRequests_events
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.same_memory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.memory_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.profile_not_recoverable
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.same_all_future_events
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.publicProduce
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.publicProduce_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.publicStart
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.publicStart_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_reader_count
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.publicFirstQuery_admitted
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_first_read_exists
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_same_memory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_profile_irrecoverable
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_execution_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.public_all_future_events
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedContinuation.publicContractCertificate
/- AXIOM_AUDIT_END -/
