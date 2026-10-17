import RelationalPerimeter.Constitution.Reals.CommonRealRuntime

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Persistent heterogeneous precision services

An authoritative state is an execution archive, never minimal live memory.
Each rich transition executes once from its current archive. The live kernel
is a separate specification, connected transition by transition; the rich
runner does not execute that specification beside the authoritative producer.
The executed Runtime carries only its compact read/step/answer environment and
live memory. Exact memory claims concern that live contract at one fixed
environment only, never the provenance-bearing rich contract.
-/

namespace RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime
open StrongPerimetralTurning
open RuntimeCorrespondence
open ConstitutiveSearch.ContinuationSignatures

variable {P : CircularPresentation} {baseDepth : Nat}

structure LiveStep (Memory Event : Type) where
  next : Memory
  event : Event

/-- Exactly the fixed executable data read by the live runtime. -/
structure LiveEnvironment where
  Memory : Type
  Event : Type
  Read : Type
  read : Memory → Read
  step : Memory → Nat → LiveStep Memory Event
  answer : Event → SignedDyadicCode
  separates : (first second : Memory) → (p : Nat) →
    read first = read second →
    (step first p).event = (step second p).event → first = second

/--
The rich service owns archives, resources and provenance.  Its live fields are
kept separately so that a live Runtime never carries the rich producer.
-/
structure Service (P : CircularPresentation) (baseDepth : Nat) where
  Archive : Type
  Memory : Type
  Event : Type
  RichEvent : Type
  Read : Type
  Resource : Archive → Nat → Type
  initialArchive : Archive
  execute : (archive : Archive) → (precision : Nat) → Resource archive precision
  next : {archive : Archive} → {precision : Nat} → Resource archive precision → Archive
  richEvent : {archive : Archive} → {precision : Nat} → Resource archive precision → RichEvent
  code : {archive : Archive} → {precision : Nat} → Resource archive precision → SignedDyadicCode
  readArchive : Archive → Read
  project : Archive → Memory
  projectEvent : RichEvent → Event
  readLive : Memory → Read
  liveStep : Memory → Nat → LiveStep Memory Event
  answer : Event → SignedDyadicCode
  nextExact : (archive : Archive) → (p : Nat) →
    project (next (execute archive p)) = (liveStep (project archive) p).next
  eventExact : (archive : Archive) → (p : Nat) →
    projectEvent (richEvent (execute archive p)) = (liveStep (project archive) p).event
  readExact : (archive : Archive) → readArchive archive = readLive (project archive)
  answerExact : {archive : Archive} → {p : Nat} → (resource : Resource archive p) →
    answer (projectEvent (richEvent resource)) = code resource
  separates : (first second : Memory) → (p : Nat) →
    readLive first = readLive second →
    (liveStep first p).event = (liveStep second p).event → first = second

/-- The compact executable environment, with no archive or rich-resource field. -/
def Service.liveEnvironment (service : Service P baseDepth) : LiveEnvironment where
  Memory := service.Memory
  Event := service.Event
  Read := service.Read
  read := service.readLive
  step := service.liveStep
  answer := service.answer
  separates := service.separates

/-- This packet owns the one actual produced resource. -/
structure Step (service : Service P baseDepth) (archive : service.Archive) (precision : Nat) where
  private mk ::
  resource : service.Resource archive precision
  produced : resource = service.execute archive precision

namespace Step
def next {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) : s.Archive :=
  s.next step.resource
def event {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) : s.RichEvent :=
  s.richEvent step.resource
def liveEvent {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) : s.Event :=
  s.projectEvent step.event
def code {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) : SignedDyadicCode :=
  s.code step.resource
theorem nextProjection {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) :
    s.project step.next = (s.liveStep (s.project a) p).next := by
  change s.project (s.next step.resource) = _
  rw [step.produced]
  exact s.nextExact a p
theorem eventProjection {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) :
    step.liveEvent = (s.liveStep (s.project a) p).event := by
  change s.projectEvent (s.richEvent step.resource) = _
  rw [step.produced]
  exact s.eventExact a p
theorem answerProjection {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) :
    s.answer step.liveEvent = step.code := s.answerExact step.resource
end Step

def perform (service : Service P baseDepth) (archive : service.Archive) (precision : Nat) :
    Step service archive precision :=
  let resource := service.execute archive precision
  ⟨resource, rfl⟩

def LiveEnvironment.contract (environment : LiveEnvironment) :
    FutureContract environment.Memory Nat environment.Event environment.Read where
  next memory p := (environment.step memory p).next
  event memory p := (environment.step memory p).event
  read := environment.read
  Allow _ _ := Unit
  decision _ _ := .inl ()

def liveContract (service : Service P baseDepth) := service.liveEnvironment.contract

/-- The provenance-bearing contract.  Its events are not live projections. -/
def richContract (service : Service P baseDepth) :
    FutureContract service.Archive Nat service.RichEvent service.Read where
  next archive p := (perform service archive p).next
  event archive p := (perform service archive p).event
  read := service.readArchive
  Allow _ _ := Unit
  decision _ _ := .inl ()

/-- Archive-indexed contract after the explicitly declared event projection. -/
def projectedArchiveContract (service : Service P baseDepth) :
    FutureContract service.Archive Nat service.Event service.Read where
  next archive p := (perform service archive p).next
  event archive p := (perform service archive p).liveEvent
  read := service.readArchive
  Allow _ _ := Unit
  decision _ _ := .inl ()

def realization (service : Service P baseDepth) :
    ExactRealization (projectedArchiveContract service) service.Memory where
  reduced := liveContract service
  project := service.project
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := fun _ _ _ => rfl
  forward_backward := fun _ _ _ => rfl
  next_exact archive p := (perform service archive p).nextProjection
  event_exact archive p := (perform service archive p).eventProjection
  read_exact := service.readExact

def outcomeRead {Event Read : Type} : Outcome Event Read → Read
  | .stop read => read
  | .step read _ _ _ => read

def outcomeEvent {Event Read : Type} : Outcome Event Read → Option Event
  | .stop _ => none
  | .step _ _ event _ => some event

/-- Project only events; reads and the complete finite shape are retained. -/
def projectOutcome (service : Service P baseDepth) : Outcome service.RichEvent service.Read →
    Outcome service.Event service.Read
  | .stop read => .stop read
  | .step read enabled event later =>
      .step read enabled (service.projectEvent event) (projectOutcome service later)

/-- Projection of a rich future is exactly the separately declared archive projection contract. -/
theorem projectOutcome_richContract (service : Service P baseDepth)
    (archive : service.Archive) (requests : List Nat) :
    projectOutcome service ((richContract service).outcome archive requests) =
      (projectedArchiveContract service).outcome archive requests := by
  induction requests generalizing archive with
  | nil => rfl
  | cons p remaining ih =>
      change Outcome.step (service.readArchive archive) true
          (service.projectEvent (perform service archive p).event)
          (projectOutcome service ((richContract service).outcome
            (perform service archive p).next remaining)) =
        Outcome.step (service.readArchive archive) true
          (perform service archive p).liveEvent
          ((projectedArchiveContract service).outcome
          (perform service archive p).next remaining)
      rw [ih]
      rfl

/-- The actual rich one-request future of an operand, with both genuine reads. -/
def sourceFuture {service : Service P baseDepth} {archive : service.Archive} {p : Nat}
    (step : Step service archive p) : Outcome service.RichEvent service.Read :=
  .step (service.readArchive archive) true step.event (.stop (service.readArchive step.next))

def liveFuture (environment : LiveEnvironment) (memory : environment.Memory) (p : Nat)
    (step : LiveStep environment.Memory environment.Event) : Outcome environment.Event environment.Read :=
  .step (environment.read memory) true step.event (.stop (environment.read step.next))

theorem sourceFuture_projects {service : Service P baseDepth} {archive : service.Archive} {p : Nat}
    (step : Step service archive p) :
    projectOutcome service (sourceFuture step) =
      liveFuture service.liveEnvironment (service.project archive) p
        (service.liveStep (service.project archive) p) := by
  change Outcome.step (service.readArchive archive) true (service.projectEvent step.event)
      (.stop (service.readArchive step.next)) =
    Outcome.step (service.readLive (service.project archive)) true
      (service.liveStep (service.project archive) p).event
      (.stop (service.readLive (service.liveStep (service.project archive) p).next))
  rw [service.readExact archive]
  have eventExact : service.projectEvent step.event =
      (service.liveStep (service.project archive) p).event := step.eventProjection
  rw [eventExact, service.readExact step.next]
  have nextExact : service.project step.next =
      (service.liveStep (service.project archive) p).next := step.nextProjection
  rw [nextExact]

/-- Product memory keeps the views read by the two real operand futures and the installed target. -/
structure CompositeMemory (left right : LiveEnvironment) where
  left : left.Memory
  right : right.Memory
  last : Option SignedDyadicCode

theorem CompositeMemory.extensionality {left right : LiveEnvironment}
    {first second : CompositeMemory left right}
    (leftExact : first.left = second.left) (rightExact : first.right = second.right)
    (lastExact : first.last = second.last) : first = second := by
  cases first; cases second; cases leftExact; cases rightExact; cases lastExact; rfl

/-- The live event contains only the declared projections of the two rich futures. -/
structure CompositeLiveEvent (left right : LiveEnvironment) where
  left : Outcome left.Event left.Read
  right : Outcome right.Event right.Read
  code : SignedDyadicCode

theorem CompositeLiveEvent.extensionality {left right : LiveEnvironment}
    {first second : CompositeLiveEvent left right}
    (leftExact : first.left = second.left) (rightExact : first.right = second.right)
    (codeExact : first.code = second.code) : first = second := by
  cases first; cases second; cases leftExact; cases rightExact; cases codeExact; rfl

theorem compositeMemorySeparates {left right : LiveEnvironment}
    {first second : CompositeMemory left right} (p : Nat)
    (lastExact : first.last = second.last)
    (leftFuture : liveFuture left first.left (Nat.succ p) (left.step first.left (Nat.succ p)) =
      liveFuture left second.left (Nat.succ p) (left.step second.left (Nat.succ p)))
    (rightFuture : liveFuture right first.right (Nat.succ p) (right.step first.right (Nat.succ p)) =
      liveFuture right second.right (Nat.succ p) (right.step second.right (Nat.succ p))) :
    first = second := by
  apply CompositeMemory.extensionality
  · exact left.separates first.left second.left (Nat.succ p)
      (congrArg outcomeRead leftFuture) (Option.some.inj (congrArg outcomeEvent leftFuture))
  · exact right.separates first.right second.right (Nat.succ p)
      (congrArg outcomeRead rightFuture) (Option.some.inj (congrArg outcomeEvent rightFuture))
  · exact lastExact

theorem LiveEnvironment.minimality (environment : LiveEnvironment)
    {first second : environment.Memory} :
    first = second ↔ FutureEquivalent environment.contract first second := by
  constructor
  · intro same requests
    exact congrArg (fun memory => environment.contract.outcome memory requests) same
  · intro same
    apply environment.separates first second 0 same.read
    exact Option.some.inj (congrArg outcomeEvent (same [0]))

theorem liveMinimality (service : Service P baseDepth) {first second : service.Memory} :
    first = second ↔ FutureEquivalent (liveContract service) first second :=
  service.liveEnvironment.minimality

theorem archiveMemoryMinimality (service : Service P baseDepth) {first second : service.Archive} :
    service.project first = service.project second ↔
      FutureEquivalent (projectedArchiveContract service) first second := by
  constructor
  · exact (realization service).equal_memory_same_futures
  · intro same
    apply (liveMinimality service).2
    intro requests
    exact ((realization service).outcome_exact first requests).symm.trans
      ((same requests).trans ((realization service).outcome_exact second requests))

inductive Reachable (service : Service P baseDepth) : service.Archive → Type
  | initial : Reachable service service.initialArchive
  | step {archive : service.Archive} {p : Nat} (prior : Reachable service archive)
      (step : Step service archive p) : Reachable service step.next

inductive RunTrace (service : Service P baseDepth) : service.Archive → List Nat → service.Archive → Type
  | done (archive : service.Archive) : RunTrace service archive [] archive
  | step {archive final : service.Archive} {p : Nat} {remaining : List Nat}
      (step : Step service archive p) (later : RunTrace service step.next remaining final) :
      RunTrace service archive (p :: remaining) final

namespace RunTrace
def outcome {service : Service P baseDepth} : {archive final : service.Archive} → {requests : List Nat} →
    RunTrace service archive requests final → Outcome service.RichEvent service.Read
  | archive, _, [], .done _ => .stop (service.readArchive archive)
  | archive, _, _ :: _, .step executed later => .step (service.readArchive archive) true executed.event later.outcome

def length {service : Service P baseDepth} : {archive final : service.Archive} → {requests : List Nat} →
    RunTrace service archive requests final → Nat
  | _, _, [], .done _ => 0
  | _, _, _ :: _, .step _ later => Nat.succ later.length

def reachable {service : Service P baseDepth} : {archive final : service.Archive} → {requests : List Nat} →
    RunTrace service archive requests final → Reachable service archive → Reachable service final
  | _, _, [], .done _, prior => prior
  | _, _, _ :: _, .step executed later, prior => later.reachable (.step prior executed)
end RunTrace

structure RunResult (service : Service P baseDepth) (archive : service.Archive) (requests : List Nat) where
  private mk ::
  final : service.Archive
  trace : RunTrace service archive requests final

def run (service : Service P baseDepth) : (archive : service.Archive) → (requests : List Nat) →
    RunResult service archive requests
  | archive, [] => ⟨archive, .done archive⟩
  | archive, p :: remaining =>
      let step := perform service archive p
      let later := run service step.next remaining
      ⟨later.final, .step step later.trace⟩

theorem run_contract (service : Service P baseDepth) (archive : service.Archive) (requests : List Nat) :
    (run service archive requests).trace.outcome = (richContract service).outcome archive requests := by
  induction requests generalizing archive with
  | nil => rfl
  | cons p remaining ih =>
      change Outcome.step _ _ _ (run service (perform service archive p).next remaining).trace.outcome =
        Outcome.step _ _ _ ((richContract service).outcome _ remaining)
      rw [ih]
      rfl

theorem run_length (service : Service P baseDepth) (archive : service.Archive) (requests : List Nat) :
    (run service archive requests).trace.length = requests.length := by
  induction requests generalizing archive with
  | nil => rfl
  | cons p remaining ih =>
      change Nat.succ (run service (perform service archive p).next remaining).trace.length = Nat.succ remaining.length
      exact congrArg Nat.succ (ih _)

theorem run_two_final (service : Service P baseDepth) (archive : service.Archive) (p q : Nat) :
    (run service archive [p, q]).final = (perform service (perform service archive p).next q).next := rfl

structure ArchivedExecution (P : CircularPresentation) (baseDepth : Nat) where
  environment : Service P baseDepth
  archive : environment.Archive

structure Runtime (P : CircularPresentation) (baseDepth : Nat) where
  environment : LiveEnvironment
  memory : environment.Memory

def ArchivedExecution.live (state : ArchivedExecution P baseDepth) : Runtime P baseDepth :=
  ⟨state.environment.liveEnvironment, state.environment.project state.archive⟩

def initialArchiveExecution (service : Service P baseDepth) : ArchivedExecution P baseDepth :=
  ⟨service, service.initialArchive⟩

def runArchived (state : ArchivedExecution P baseDepth) (requests : List Nat) :
    ArchivedExecution P baseDepth × RunResult state.environment state.archive requests :=
  let result := run state.environment state.archive requests
  ⟨⟨state.environment, result.final⟩, result⟩

/-- A live transition owns one liveStep result and no source archive. -/
structure RuntimeTransition (state : Runtime P baseDepth) (precision : Nat) where
  private mk ::
  step : LiveStep state.environment.Memory state.environment.Event
  produced : step = state.environment.step state.memory precision

namespace RuntimeTransition
def next {state : Runtime P baseDepth} {p : Nat} (transition : RuntimeTransition state p) : Runtime P baseDepth :=
  ⟨state.environment, transition.step.next⟩
def event {state : Runtime P baseDepth} {p : Nat} (transition : RuntimeTransition state p) : state.environment.Event :=
  transition.step.event
def code {state : Runtime P baseDepth} {p : Nat} (transition : RuntimeTransition state p) : SignedDyadicCode :=
  state.environment.answer transition.event
end RuntimeTransition

def performRuntime (state : Runtime P baseDepth) (p : Nat) : RuntimeTransition state p :=
  let step := state.environment.step state.memory p
  ⟨step, rfl⟩

structure LiveRunResult (environment : LiveEnvironment) where
  final : environment.Memory
  outcome : Outcome environment.Event environment.Read

def runLive (environment : LiveEnvironment) : environment.Memory → List Nat → LiveRunResult environment
  | memory, [] => ⟨memory, .stop (environment.read memory)⟩
  | memory, p :: remaining =>
      let step := environment.step memory p
      let later := runLive environment step.next remaining
      ⟨later.final, .step (environment.read memory) true step.event later.outcome⟩

def runRuntime (state : Runtime P baseDepth) (requests : List Nat) : Runtime P baseDepth × LiveRunResult state.environment :=
  let result := runLive state.environment state.memory requests
  ⟨⟨state.environment, result.final⟩, result⟩

theorem runLive_contract (environment : LiveEnvironment) (memory : environment.Memory) (requests : List Nat) :
    (runLive environment memory requests).outcome = environment.contract.outcome memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons p remaining ih =>
      change Outcome.step _ _ _ (runLive environment (environment.step memory p).next remaining).outcome =
        Outcome.step _ _ _ (environment.contract.outcome _ remaining)
      rw [ih]
      rfl

theorem archivedNext_runtime (service : Service P baseDepth) (archive : service.Archive) (p : Nat) :
    (ArchivedExecution.mk service (perform service archive p).next).live =
      (performRuntime (ArchivedExecution.mk service archive).live p).next :=
  congrArg (fun memory => Runtime.mk service.liveEnvironment memory) (perform service archive p).nextProjection

theorem archivedEvent_runtime (service : Service P baseDepth) (archive : service.Archive) (p : Nat) :
    (perform service archive p).liveEvent = (performRuntime (ArchivedExecution.mk service archive).live p).event :=
  (perform service archive p).eventProjection

theorem archivedCode_runtime (service : Service P baseDepth) (archive : service.Archive) (p : Nat) :
    (perform service archive p).code = (performRuntime (ArchivedExecution.mk service archive).live p).code :=
  (perform service archive p).answerProjection.symm.trans
    (congrArg service.answer (archivedEvent_runtime service archive p))

theorem run_final_projects (service : Service P baseDepth) (archive : service.Archive) (requests : List Nat) :
    service.project (run service archive requests).final =
      (runLive service.liveEnvironment (service.project archive) requests).final := by
  induction requests generalizing archive with
  | nil => rfl
  | cons p remaining ih =>
      change service.project (run service (perform service archive p).next remaining).final = _
      rw [ih, (perform service archive p).nextProjection]
      rfl

theorem run_outcome_projects (service : Service P baseDepth) (archive : service.Archive) (requests : List Nat) :
    projectOutcome service (run service archive requests).trace.outcome =
      (runLive service.liveEnvironment (service.project archive) requests).outcome := by
  have traceToRich :
      projectOutcome service (run service archive requests).trace.outcome =
        projectOutcome service ((richContract service).outcome archive requests) :=
    congrArg (projectOutcome service) (run_contract service archive requests)
  have richToArchive :
      projectOutcome service ((richContract service).outcome archive requests) =
        (projectedArchiveContract service).outcome archive requests :=
    projectOutcome_richContract service archive requests
  have archiveToLive :
      (projectedArchiveContract service).outcome archive requests =
        (liveContract service).outcome (service.project archive) requests :=
    (realization service).outcome_exact archive requests
  have liveToRun :
      (liveContract service).outcome (service.project archive) requests =
        (runLive service.liveEnvironment (service.project archive) requests).outcome :=
    (runLive_contract service.liveEnvironment (service.project archive) requests).symm
  exact traceToRich.trans (richToArchive.trans (archiveToLive.trans liveToRun))

theorem runArchived_runtime (state : ArchivedExecution P baseDepth) (requests : List Nat) :
    (runArchived state requests).1.live = (runRuntime state.live requests).1 :=
  congrArg (fun memory => Runtime.mk state.environment.liveEnvironment memory)
    (run_final_projects state.environment state.archive requests)

/-- Canonical readout uses this same service, from its initial archive. -/
def canonicalStep (service : Service P baseDepth) (p : Nat) : Step service service.initialArchive p :=
  perform service service.initialArchive p

def canonicalReadout (service : Service P baseDepth) (p : Nat) : SignedDyadicCode :=
  (canonicalStep service p).code

/-- The authoritative source state and its accessibility remain in the archive. -/
structure LeafArchive (real : RuntimeReal P baseDepth) where
  state : AuthoritativeRuntime.Runtime real.family
  reachable : AuthoritativeRuntime.Reachable real.family state

/-- The leaf event owns the exact archive and authoritative executed resource. -/
structure LeafRichEvent (real : RuntimeReal P baseDepth) where
  archive : LeafArchive real
  precision : Nat
  resource : AuthoritativeRuntime.ExecutedStep real.family archive.state (.limit precision)

def LeafRichEvent.project {real : RuntimeReal P baseDepth} (event : LeafRichEvent real) :
    AuthoritativeRuntime.CommonEvent := .executed event.resource.event

def leafLiveStep (environment : CommonRealRuntime.Environment)
    (memory : AuthoritativeRuntime.ReducedState) (p : Nat) :
    LiveStep AuthoritativeRuntime.ReducedState AuthoritativeRuntime.CommonEvent :=
  let step := CommonRealRuntime.performReal
    { environment := environment, memory := memory } (.limit p)
  ⟨step.next.memory, step.event⟩

def leafAnswer : AuthoritativeRuntime.CommonEvent → SignedDyadicCode
  | .executed event => event.readout
  | .refused _ _ => ⟨0, 0, 0⟩

def leafEventStart : AuthoritativeRuntime.CommonEvent → Nat
  | .executed event => event.startDepth
  | .refused depth _ => depth

theorem leafNextProjection (real : RuntimeReal P baseDepth) (archive : LeafArchive real) (p : Nat) :
    AuthoritativeRuntime.project
      (real.produced.produce archive.state archive.reachable p).next =
      (leafLiveStep (CommonRealRuntime.environmentOfFamily real.family)
        (AuthoritativeRuntime.project archive.state) p).next := by
  rw [real.produced.produceCanonical]
  exact congrArg CommonRealRuntime.Runtime.memory
    (CommonRealRuntime.typedNextProjection real.family archive.state (.limit p))

theorem leafEventProjection (real : RuntimeReal P baseDepth) (archive : LeafArchive real) (p : Nat) :
    AuthoritativeRuntime.CommonEvent.executed
      (real.produced.produce archive.state archive.reachable p).event =
      (leafLiveStep (CommonRealRuntime.environmentOfFamily real.family)
        (AuthoritativeRuntime.project archive.state) p).event := by
  rw [real.produced.produceCanonical]
  exact CommonRealRuntime.typedEventProjection real.family archive.state (.limit p)

theorem leafMemorySeparates (environment : CommonRealRuntime.Environment)
    (first second : AuthoritativeRuntime.ReducedState) (p : Nat)
    (readExact : first.last = second.last)
    (eventExact : (leafLiveStep environment first p).event =
      (leafLiveStep environment second p).event) : first = second :=
  AuthoritativeRuntime.ReducedState.extensionality first second
    (congrArg leafEventStart eventExact) readExact

/-- Concrete authoritative realization: no hypotheses about execution are left open. -/
def leaf (real : RuntimeReal P baseDepth) : Service P baseDepth where
  Archive := LeafArchive real
  Memory := AuthoritativeRuntime.ReducedState
  Event := AuthoritativeRuntime.CommonEvent
  RichEvent := LeafRichEvent real
  Read := Option AuthoritativeRuntime.Observation
  Resource archive p := AuthoritativeRuntime.ExecutedStep real.family archive.state (.limit p)
  initialArchive := ⟨real.initial, real.initialReachable⟩
  execute archive p := real.produced.produce archive.state archive.reachable p
  next {archive} {precision} step := ⟨step.next, .performed archive.reachable step⟩
  richEvent {archive} {precision} step := ⟨archive, precision, step⟩
  code {archive} {precision} step := step.response.readout
  readArchive archive := AuthoritativeRuntime.read archive.state
  project archive := AuthoritativeRuntime.project archive.state
  projectEvent := LeafRichEvent.project
  readLive := AuthoritativeRuntime.readLive
  liveStep := leafLiveStep (CommonRealRuntime.environmentOfFamily real.family)
  answer := leafAnswer
  nextExact := leafNextProjection real
  eventExact := leafEventProjection real
  readExact _ := rfl
  answerExact _ := rfl
  separates := leafMemorySeparates (CommonRealRuntime.environmentOfFamily real.family)

theorem leafCanonicalIsAuthoritative (real : RuntimeReal P baseDepth) (p : Nat) :
    (canonicalStep (leaf real) p).resource = real.stepAt p := rfl

theorem leafCurrentReadout (real : RuntimeReal P baseDepth) (archive : LeafArchive real) (p : Nat)
    (step : Step (leaf real) archive p) : step.code = real.readout p :=
  real.limitStep_readout_eq step.resource

end RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LiveStep
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LiveEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LiveEnvironment.contract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LiveEnvironment.minimality
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Service
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Service.liveEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.next
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.event
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.liveEvent
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.code
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.nextProjection
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.eventProjection
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Step.answerProjection
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.perform
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.liveContract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.richContract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.projectedArchiveContract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.realization
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.outcomeRead
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.outcomeEvent
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.projectOutcome
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.projectOutcome_richContract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.sourceFuture
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.liveFuture
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.sourceFuture_projects
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.CompositeMemory
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.CompositeMemory.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.CompositeLiveEvent
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.CompositeLiveEvent.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.compositeMemorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.liveMinimality
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.archiveMemoryMinimality
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Reachable
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RunTrace
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RunTrace.outcome
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RunTrace.length
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RunTrace.reachable
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RunResult
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.run
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.run_contract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.run_length
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.run_two_final
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.ArchivedExecution
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.Runtime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.ArchivedExecution.live
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.initialArchiveExecution
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.runArchived
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RuntimeTransition
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RuntimeTransition.next
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RuntimeTransition.event
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.RuntimeTransition.code
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.performRuntime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LiveRunResult
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.runLive
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.runRuntime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.runLive_contract
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.archivedNext_runtime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.archivedEvent_runtime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.archivedCode_runtime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.run_final_projects
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.run_outcome_projects
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.runArchived_runtime
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.canonicalStep
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.canonicalReadout
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LeafArchive
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LeafRichEvent
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.LeafRichEvent.project
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafLiveStep
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafAnswer
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafEventStart
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafMemorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leaf
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafCanonicalIsAuthoritative
#print axioms RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime.leafCurrentReadout
/- AXIOM_AUDIT_END -/
