import RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# A common directly executed real runtime

The executable environment is DATA of Runtime, not a family index or an
external interpreter argument. Exact memory minimality is relative to one
fixed environment. Numerical equivalence between environments is a separate
positive relation; it never identifies programs, encodings or occurrences.
-/

namespace RelationalPerimeter.Constitution.Reals.CommonRealRuntime
open StrongPerimetralTurning
open ConstitutiveRuntime
open ProducedCompleteness
open AuthoritativeRuntime
open ConstitutiveSearch.ContinuationSignatures

/-- All causally relevant producer functions are explicit executable data. -/
structure Environment where
  producer : SourceProducer
  modulus : Nat -> Nat

def environmentOfFamily {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) : Environment :=
  { producer := family.producer, modulus := family.modulus }

abbrev Memory := ReducedState

/-- A common type, not indexed by its producer or by a real family. -/
structure Runtime where
  environment : Environment
  memory : Memory

def initialState (environment : Environment) (baseDepth : Nat) : Runtime :=
  { environment := environment, memory := { depth := baseDepth, last := none } }

inductive Request where
  | source (request : SourceRequest)
  | limit (precision : Nat)
  | group (precision : Nat) (sources : List SourceRequest)
  | continueInstalled (extraScale : Nat)
  | unsupported (stamp : RequestStamp)

/-- Only the current installed target survives a following source request. -/
def readInstalled (memory : Memory) : Option Observation :=
  match memory.last with
  | none => none
  | some observed =>
      match observed.stamp with
      | .source _ _ => none
      | .limit _ | .finiteGrouping _ _ => some observed

def groupAllowed (environment : Environment) (precision : Nat) :
    List SourceRequest -> Bool
  | [] => true
  | request :: rest =>
      decide (environment.modulus precision ≤ request.term) &&
        decide (precision ≤ request.precision) &&
        groupAllowed environment precision rest

def enabled (state : Runtime) : Request -> Bool
  | .source _ | .limit _ => true
  | .group precision sources => groupAllowed state.environment precision sources
  | .continueInstalled _ =>
      match readInstalled state.memory with | none => false | some _ => true
  | .unsupported _ => false

def Admission : Bool -> Type
  | true => Unit
  | false => Empty

def admissionDecision (allowed : Bool) :
    PSum (Admission allowed) (Admission allowed -> False) :=
  match allowed with
  | true => .inl ()
  | false => .inr (fun impossible => nomatch impossible)

theorem admissionEnabled (allowed : Bool) :
    (match admissionDecision allowed with | .inl _ => true | .inr _ => false) = allowed := by
  cases allowed <;> rfl

/-- This is the value view of a normalization, not an occurrence identity. -/
structure ValueNormalization where
  private mk ::
  consumed : List SignedDyadicCode
  code : SignedDyadicCode

/-- Every input code is consumed once, oldest first; the anchor is a source. -/
def normalizeValues (anchor : SignedDyadicCode) :
    List SignedDyadicCode -> ValueNormalization
  | [] => { consumed := [], code := anchor }
  | source :: remaining =>
      let later := normalizeValues anchor remaining
      { consumed := source :: later.consumed, code := later.code }

theorem normalizeValues_code (anchor : SignedDyadicCode) (sources : List SignedDyadicCode) :
    (normalizeValues anchor sources).code = anchor := by
  induction sources with
  | nil => rfl
  | cons source remaining ih => exact ih

theorem normalizeValues_consumed (anchor : SignedDyadicCode) (sources : List SignedDyadicCode) :
    (normalizeValues anchor sources).consumed = sources := by
  induction sources with
  | nil => rfl
  | cons source remaining ih => exact congrArg (List.cons source) ih

/-- One transition owns the one result used for next/event/observation. -/
structure Transition where
  private mk ::
  next : Runtime
  event : CommonEvent
  produced : Option Observation
  normalization : Option ValueNormalization

private def finish (state : Runtime) (stamp : RequestStamp)
    (cost : Nat) (code : SignedDyadicCode) : Transition :=
  let observation : Observation := { stamp := stamp, code := code }
  let event : RuntimeEvent :=
    { startDepth := state.memory.depth, endDepth := state.memory.depth + cost,
      stamp := stamp, readout := observation.code }
  { next :=
      { environment := state.environment,
        memory := { depth := event.endDepth, last := some observation } }
    event := .executed event
    produced := some observation
    normalization := none }

private def refuse (state : Runtime) (stamp : RequestStamp) : Transition :=
  { next := state, event := .refused state.memory.depth stamp, produced := none,
    normalization := none }

/-- Source + anchor/grouping phases, with no physical-cost claim. -/
def groupCost : Nat -> Nat
  | 0 => 12
  | Nat.succ size => groupCost size + 6

/--
The only public interpreter reads the environment in its input state.
Grouping executes its source plan once before normalizing its value view.
The rich realization below retains the corresponding exact resources/traces.
-/
def performReal (state : Runtime) : Request -> Transition
  | .source request =>
      finish state (.source request.term request.precision) 6
        (state.environment.producer.calculate request)
  | .limit precision =>
      let anchor := state.environment.producer.calculate
        { term := state.environment.modulus precision, precision := precision }
      let target := normalizeValues anchor []
      let transition := finish state (.limit precision) 12 target.code
      { transition with normalization := some target }
  | .group precision sources =>
      if groupAllowed state.environment precision sources then
        let codes := sources.map state.environment.producer.calculate
        let anchor := state.environment.producer.calculate
          { term := state.environment.modulus precision, precision := precision }
        let target := normalizeValues anchor codes
        let transition := finish state (.finiteGrouping precision sources.length)
          (groupCost sources.length) target.code
        { transition with normalization := some target }
      else refuse state (.finiteGrouping precision sources.length)
  | .continueInstalled extra =>
      match readInstalled state.memory with
      | none => refuse state (.limit 0)
      | some installed =>
          -- This changes the encoding scale, not its certified accuracy.
          finish state installed.stamp 6 (installed.code.raise extra)
  | .unsupported stamp => refuse state stamp

def read (state : Runtime) : Option Observation := state.memory.last

def contract : FutureContract Runtime Request CommonEvent (Option Observation) where
  next state request := (performReal state request).next
  event state request := (performReal state request).event
  read := read
  Allow state request := Admission (enabled state request)
  decision state request := admissionDecision (enabled state request)

def runReal : Runtime -> List Request -> Outcome CommonEvent (Option Observation)
  | state, [] => .stop (read state)
  | state, request :: remaining =>
      let transition := performReal state request
      .step (read state) (contract.enabled state request) transition.event
        (runReal transition.next remaining)

theorem runReal_contract (state : Runtime) (requests : List Request) :
    runReal state requests = contract.outcome state requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request remaining ih =>
      change Outcome.step _ _ _ (runReal _ remaining) =
        Outcome.step _ _ _ (contract.outcome _ remaining)
      rw [ih]
      rfl

theorem performReal_environment (state : Runtime) (request : Request) :
    (performReal state request).next.environment = state.environment := by
  cases request with
  | source request => rfl
  | limit precision => rfl
  | group precision sources =>
      simp only [performReal]
      split <;> rfl
  | continueInstalled extra =>
      simp only [performReal]
      cases readInstalled state.memory <;> rfl
  | unsupported stamp => rfl

/-- Exact fixed-environment memory contract. No producer is hidden from Runtime. -/
def memoryContract (environment : Environment) :
    FutureContract Memory Request CommonEvent (Option Observation) where
  next memory request :=
    (performReal { environment := environment, memory := memory } request).next.memory
  event memory request :=
    (performReal { environment := environment, memory := memory } request).event
  read := fun memory => memory.last
  Allow memory request :=
    Admission (enabled { environment := environment, memory := memory } request)
  decision memory request :=
    admissionDecision (enabled { environment := environment, memory := memory } request)

private def startDepth : Outcome CommonEvent (Option Observation) -> Nat
  | .stop _ => 0
  | .step _ _ (.executed event) _ => event.startDepth
  | .step _ _ (.refused depth _) _ => depth

/-- SAT-style exact identity, ONLY while this executable environment is fixed. -/
theorem fixedEnvironmentMinimality (environment : Environment) {first second : Memory} :
    first = second ↔ FutureEquivalent (memoryContract environment) first second := by
  constructor
  · intro same requests
    exact congrArg (fun memory => (memoryContract environment).outcome memory requests) same
  · intro same
    apply ReducedState.extensionality
    · exact congrArg startDepth (same [.limit 0])
    · exact same.read

theorem anyFixedEnvironmentRealization (environment : Environment)
    {Other : Type} (other : ExactRealization (memoryContract environment) Other)
    {first second : Memory} (same : other.project first = other.project second) :
    first = second :=
  (fixedEnvironmentMinimality environment).2 (other.equal_memory_same_futures same)


theorem Runtime.extensionality (first second : Runtime)
    (environmentExact : first.environment = second.environment)
    (memoryExact : first.memory = second.memory) : first = second := by
  cases first
  cases second
  cases environmentExact
  cases memoryExact
  rfl

/-- Directed projection, preserving the executable environment as data. -/
def projectArchive {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (state : AuthoritativeRuntime.Runtime family) : Runtime :=
  { environment := environmentOfFamily family, memory := AuthoritativeRuntime.project state }

def typedRequest {P : CircularPresentation} {baseDepth : Nat}
    {family : ExecutedCauchyFamily P baseDepth} : RuntimeRequest family -> Request
  | .source _ source => .source source.request
  | .limit precision => .limit precision

theorem typedNextProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (state : AuthoritativeRuntime.Runtime family) (request : RuntimeRequest family) :
    projectArchive family (AuthoritativeRuntime.perform family state request).next =
      (performReal (projectArchive family state) (typedRequest request)).next := by
  apply Runtime.extensionality
  · exact (performReal_environment (projectArchive family state) (typedRequest request)).symm
  · cases request with
    | source precision source =>
        exact AuthoritativeRuntime.perform_projects family state (.source precision source)
    | limit precision =>
        exact AuthoritativeRuntime.perform_projects family state (.limit precision)

theorem typedEventProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (state : AuthoritativeRuntime.Runtime family) (request : RuntimeRequest family) :
    CommonEvent.executed (AuthoritativeRuntime.perform family state request).event =
      (performReal (projectArchive family state) (typedRequest request)).event := by
  cases request with
  | source precision source =>
      exact congrArg CommonEvent.executed
        (AuthoritativeRuntime.perform_event_projects family state (.source precision source))
  | limit precision =>
      exact congrArg CommonEvent.executed
        (AuthoritativeRuntime.perform_event_projects family state (.limit precision))

/-- Exact admissions, next states, events and reads for ALL typed source requests. -/
def typedArchiveBridge {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) :
    ConstitutiveSearch.Grouping.Continuation.Exact
      (AuthoritativeRuntime.Runtime family) Runtime (RuntimeRequest family)
      CommonEvent (Option Observation) where
  project := projectArchive family
  sourceNext state request := (AuthoritativeRuntime.perform family state request).next
  reducedNext state request := (performReal state (typedRequest request)).next
  sourceAllow _state _request := Unit
  reducedAllow state request := Admission (enabled state (typedRequest request))
  toReduced := by intro state request witness; cases request <;> exact witness
  toSource := by intro state request witness; cases request <;> exact witness
  sourceEvent state request := .executed (AuthoritativeRuntime.perform family state request).event
  reducedEvent state request := (performReal state (typedRequest request)).event
  sourceRead := AuthoritativeRuntime.read
  reducedRead := read
  nextLaw := typedNextProjection family
  eventLaw := typedEventProjection family
  readLaw := fun _ => rfl

theorem typedArchiveEvents {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (state : AuthoritativeRuntime.Runtime family)
    (requests : List (RuntimeRequest family)) :
    ConstitutiveSearch.Grouping.Continuation.events
        (typedArchiveBridge family).sourceNext (typedArchiveBridge family).sourceEvent state requests =
      ConstitutiveSearch.Grouping.Continuation.events
        (typedArchiveBridge family).reducedNext (typedArchiveBridge family).reducedEvent
        (projectArchive family state) requests :=
  (typedArchiveBridge family).events_exact state requests

theorem typedArchiveObservations {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (state : AuthoritativeRuntime.Runtime family)
    (requests : List (RuntimeRequest family)) :
    ConstitutiveSearch.Grouping.Continuation.observations
        (typedArchiveBridge family).sourceNext (typedArchiveBridge family).sourceRead state requests =
      ConstitutiveSearch.Grouping.Continuation.observations
        (typedArchiveBridge family).reducedNext (typedArchiveBridge family).reducedRead
        (projectArchive family state) requests :=
  (typedArchiveBridge family).observations_exact state requests



structure CertifiedSources {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (precision : Nat)
    (requests : List SourceRequest) where
  sources : List (family.SourceAt precision)
  requestsExact : sources.map (fun source => source.request) = requests
  lengthExact : sources.length = requests.length

def extensionFromBound : (coarse fine : Nat) -> coarse ≤ fine -> PrecisionExtension coarse fine
  | 0, fine, _ => { extra := fine, exact := Nat.zero_add fine }
  | Nat.succ coarse, 0, impossible => False.elim (Nat.not_succ_le_zero coarse impossible)
  | Nat.succ coarse, Nat.succ fine, bound =>
      let prior := extensionFromBound coarse fine (Nat.le_of_succ_le_succ bound)
      { extra := prior.extra,
        exact := (Nat.succ_add coarse prior.extra).trans (congrArg Nat.succ prior.exact) }

def extensionOfLe {coarse fine : Nat} (bound : coarse ≤ fine) :
    PrecisionExtension coarse fine := extensionFromBound coarse fine bound

theorem andTrueParts (left right : Bool) (allowed : (left && right) = true) :
    left = true ∧ right = true := by
  cases left <;> cases right <;> cases allowed
  exact ⟨rfl, rfl⟩

/-- Admission constructs all certificates without choice or an output payload. -/
def certifySources {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (precision : Nat) :
    (requests : List SourceRequest) ->
      groupAllowed (environmentOfFamily family) precision requests = true ->
        CertifiedSources family precision requests
  | [], _ => { sources := [], requestsExact := rfl, lengthExact := rfl }
  | request :: remaining, allowed => by
      have parts := andTrueParts _ _ allowed
      have firstPart := andTrueParts _ _ parts.1
      have indexBound : family.modulus precision ≤ request.term :=
        of_decide_eq_true firstPart.1
      have precisionBound : precision ≤ request.precision :=
        of_decide_eq_true firstPart.2
      let source : family.SourceAt precision :=
        { request := request, indexBeyondModulus := extensionOfLe indexBound,
          readoutRefines := extensionOfLe precisionBound }
      let later := certifySources family precision remaining parts.2
      exact
      { sources := source :: later.sources
        requestsExact := congrArg (List.cons request) later.requestsExact
        lengthExact := congrArg Nat.succ later.lengthExact }

inductive ArchiveResource {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) where
  | raw {state : AuthoritativeRuntime.Runtime family} {request : SourceRequest}
      (step : RawSourceStep family state request)
  | limit {state : AuthoritativeRuntime.Runtime family} {precision : Nat}
      (step : ExecutedStep family state (.limit precision))
  | batch {state : AuthoritativeRuntime.Runtime family} {precision : Nat}
      (step : GroupingStep family state precision)
  | continued {state : AuthoritativeRuntime.Runtime family} {extra : Nat}
      (step : ContinuedStep family state extra)
  | refused

structure ArchiveTransition {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) where
  private mk ::
  next : AuthoritativeRuntime.Runtime family
  event : CommonEvent
  produced : Option Observation
  resource : ArchiveResource family

/-- Execute the rich resources once; all projections retain this same step. -/
def performArchive {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (state : AuthoritativeRuntime.Runtime family) : Request -> ArchiveTransition family
  | .source request =>
      let step := performRawSource family state request
      { next := step.next, event := .executed step.event,
        produced := step.next.last, resource := .raw step }
  | .limit precision =>
      let step := AuthoritativeRuntime.perform family state (.limit precision)
      { next := step.next, event := .executed step.event,
        produced := step.next.last, resource := .limit step }
  | .group precision requests =>
      if allowed : groupAllowed (environmentOfFamily family) precision requests = true then
        let certified := certifySources family precision requests allowed
        let step := performSourceListGrouping family state certified.sources
        { next := step.next, event := .executed step.event,
          produced := step.next.last, resource := .batch step }
      else
        { next := state,
          event := .refused state.journal.absoluteDepth (.finiteGrouping precision requests.length),
          produced := none, resource := .refused }
  | .continueInstalled extra =>
      match AuthoritativeRuntime.continueInstalled family state extra with
      | none =>
          { next := state, event := .refused state.journal.absoluteDepth (.limit 0),
            produced := none, resource := .refused }
      | some step =>
          { next := step.next, event := .executed step.event,
            produced := step.next.last, resource := .continued step }
  | .unsupported stamp =>
      { next := state, event := .refused state.journal.absoluteDepth stamp,
        produced := none, resource := .refused }



theorem groupCost_exact (size : Nat) :
    groupCost size = ExecutedCauchyFamily.ExecutedSourceChain.operationCount size + 12 := by
  induction size with
  | zero => rfl
  | succ size ih =>
      change groupCost size + 6 =
        (ExecutedCauchyFamily.ExecutedSourceChain.operationCount size + 6) + 12
      rw [ih]

theorem rawNextProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {request : SourceRequest} (step : RawSourceStep family state request) :
    projectArchive family step.next =
      (finish (projectArchive family state) (.source request.term request.precision) 6
        (family.producer.calculate request)).next := by
  apply Runtime.extensionality
  · rfl
  · apply ReducedState.extensionality
    · exact step.execution.completed_absoluteDepth
    · apply congrArg some
      apply Observation.extensionality
      · rfl
      · exact step.readoutExact

theorem rawEventProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {request : SourceRequest} (step : RawSourceStep family state request) :
    CommonEvent.executed step.event =
      (finish (projectArchive family state) (.source request.term request.precision) 6
        (family.producer.calculate request)).event := by
  apply congrArg CommonEvent.executed
  apply RuntimeEvent.extensionality
  · rfl
  · exact step.execution.completed_absoluteDepth
  · rfl
  · exact step.readoutExact

theorem groupingReadoutExact {P : CircularPresentation} {baseDepth : Nat}
    {family : ExecutedCauchyFamily P baseDepth} {state : AuthoritativeRuntime.Runtime family}
    {precision : Nat} (step : GroupingStep family state precision) :
    step.grouped.readout =
      family.producer.calculate { term := family.modulus precision, precision := precision } :=
  (ExecutedCauchyFamily.readout_is_anchor step.grouped).trans
    step.grouped.anchor.source.readout_is_calculated

theorem groupingDepthExact {P : CircularPresentation} {baseDepth : Nat}
    {family : ExecutedCauchyFamily P baseDepth} {state : AuthoritativeRuntime.Runtime family}
    {precision : Nat} (step : GroupingStep family state precision) :
    step.grouped.execution.completedJournal.absoluteDepth =
      state.journal.absoluteDepth + groupCost step.size := by
  rw [ExecutedCauchyFamily.completedDepth step.grouped, step.chain.finalDepth_exact, groupCost_exact]
  exact Nat.add_assoc _ _ _

theorem groupingNextProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {precision : Nat} (step : GroupingStep family state precision) :
    projectArchive family step.next =
      (finish (projectArchive family state) (.finiteGrouping precision step.size)
        (groupCost step.size)
        (family.producer.calculate { term := family.modulus precision, precision := precision })).next := by
  apply Runtime.extensionality
  · rfl
  · apply ReducedState.extensionality
    · exact groupingDepthExact step
    · apply congrArg some
      apply Observation.extensionality
      · rfl
      · exact groupingReadoutExact step

theorem groupingEventProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {precision : Nat} (step : GroupingStep family state precision) :
    CommonEvent.executed step.event =
      (finish (projectArchive family state) (.finiteGrouping precision step.size)
        (groupCost step.size)
        (family.producer.calculate { term := family.modulus precision, precision := precision })).event := by
  apply congrArg CommonEvent.executed
  apply RuntimeEvent.extensionality
  · rfl
  · exact groupingDepthExact step
  · rfl
  · exact groupingReadoutExact step

theorem installedProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (state : AuthoritativeRuntime.Runtime family) :
    state.target.map OwnedTarget.observation = readInstalled (projectArchive family state).memory :=
  state.targetReadExact

theorem continuedReadProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {extra : Nat} (step : ContinuedStep family state extra) :
    readInstalled (projectArchive family state).memory = some step.target.observation :=
  (installedProjection family state).symm.trans
    (congrArg (fun target => target.map OwnedTarget.observation) step.installedExact)

theorem continuedNextProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {extra : Nat} (step : ContinuedStep family state extra) :
    projectArchive family step.next =
      (finish (projectArchive family state) step.target.stamp 6
        (step.target.readout.raise extra)).next := by
  apply Runtime.extensionality
  · rfl
  · apply ReducedState.extensionality
    · exact step.execution.completed_absoluteDepth
    · apply congrArg some
      apply Observation.extensionality
      · rfl
      · exact targetContinuation_readout step.target extra step.execution

theorem continuedEventProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {state : AuthoritativeRuntime.Runtime family}
    {extra : Nat} (step : ContinuedStep family state extra) :
    CommonEvent.executed step.event =
      (finish (projectArchive family state) step.target.stamp 6
        (step.target.readout.raise extra)).event := by
  apply congrArg CommonEvent.executed
  apply RuntimeEvent.extensionality
  · rfl
  · exact step.execution.completed_absoluteDepth
  · rfl
  · exact targetContinuation_readout step.target extra step.execution



theorem noContinuationRead {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (state : AuthoritativeRuntime.Runtime family)
    (extra : Nat) (empty : AuthoritativeRuntime.continueInstalled family state extra = none) :
    readInstalled (projectArchive family state).memory = none := by
  have noTarget : state.target = none :=
    AuthoritativeRuntime.continueInstalled_none family state extra empty
  exact (installedProjection family state).symm.trans
    (congrArg (fun target => target.map OwnedTarget.observation) noTarget)

/-- Every common transition has exact rich next/event projections. -/
theorem archiveProjection {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (state : AuthoritativeRuntime.Runtime family)
    (request : Request) :
    projectArchive family (performArchive family state request).next =
        (performReal (projectArchive family state) request).next ∧
      (performArchive family state request).event =
        (performReal (projectArchive family state) request).event := by
  cases request with
  | source request =>
      exact ⟨rawNextProjection family (performRawSource family state request),
        rawEventProjection family (performRawSource family state request)⟩
  | limit precision =>
      exact ⟨typedNextProjection family state (.limit precision),
        typedEventProjection family state (.limit precision)⟩
  | group precision requests =>
      by_cases allowed : groupAllowed (environmentOfFamily family) precision requests = true
      · let certified := certifySources family precision requests allowed
        let step := performSourceListGrouping family state certified.sources
        have sizeExact : step.size = requests.length :=
          (executeSourceList family state.journal certified.sources).sizeExact.trans certified.lengthExact
        have nextExact := groupingNextProjection family step
        have eventExact := groupingEventProjection family step
        rw [sizeExact] at nextExact eventExact
        constructor
        · dsimp only [performArchive, performReal, projectArchive]
          rw [dif_pos allowed, if_pos allowed, normalizeValues_code]
          exact nextExact
        · dsimp only [performArchive, performReal, projectArchive]
          rw [dif_pos allowed, if_pos allowed, normalizeValues_code]
          exact eventExact
      · constructor <;>
          dsimp only [performArchive, performReal, projectArchive]
        · rw [dif_neg allowed, if_neg allowed]
          rfl
        · rw [dif_neg allowed, if_neg allowed]
          rfl
  | continueInstalled extra =>
      cases computed : AuthoritativeRuntime.continueInstalled family state extra with
      | none =>
          have noRead := noContinuationRead family state extra computed
          constructor <;>
            simp only [performArchive, computed, performReal, noRead]
          · rfl
          · rfl
      | some step =>
          have sameRead := continuedReadProjection family step
          constructor
          · simpa only [performArchive, computed, performReal, sameRead, OwnedTarget.observation] using
              continuedNextProjection family step
          · simpa only [performArchive, computed, performReal, sameRead, OwnedTarget.observation] using
              continuedEventProjection family step
  | unsupported stamp => exact ⟨rfl, rfl⟩

def archiveContract {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) :
    FutureContract (AuthoritativeRuntime.Runtime family) Request CommonEvent
      (Option Observation) where
  next state request := (performArchive family state request).next
  event state request := (performArchive family state request).event
  read := AuthoritativeRuntime.read
  Allow state request := Admission (enabled (projectArchive family state) request)
  decision state request := admissionDecision (enabled (projectArchive family state) request)

/-- Complete exact realization: raw sources, limits, groups, reads and refusals. -/
def archiveRealization {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) :
    ExactRealization (archiveContract family) Runtime where
  reduced := contract
  project := projectArchive family
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := fun _ _ _ => rfl
  forward_backward := fun _ _ _ => rfl
  next_exact state request := (archiveProjection family state request).1
  event_exact state request := (archiveProjection family state request).2
  read_exact := fun _ => rfl

theorem archiveFutures_exact {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) (state : AuthoritativeRuntime.Runtime family)
    (requests : List Request) :
    (archiveContract family).outcome state requests =
      runReal (projectArchive family state) requests :=
  ((archiveRealization family).outcome_exact state requests).trans
    (runReal_contract _ _).symm




/-- Bilateral exact memory theorem for the WHOLE rich common-request archive. -/
theorem archiveMemoryMinimality {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    {first second : AuthoritativeRuntime.Runtime family} :
    projectArchive family first = projectArchive family second ↔
      FutureEquivalent (archiveContract family) first second := by
  constructor
  · exact (archiveRealization family).equal_memory_same_futures
  · intro same
    apply Runtime.extensionality
    · rfl
    · apply ReducedState.extensionality
      · exact congrArg startDepth (same [.limit 0])
      · exact same.read

theorem everyArchiveRealizationNeedsMemory {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) {Other : Type}
    (other : ExactRealization (archiveContract family) Other)
    {first second : AuthoritativeRuntime.Runtime family}
    (same : other.project first = other.project second) :
    projectArchive family first = projectArchive family second :=
  (archiveMemoryMinimality family).2 (other.equal_memory_same_futures same)


/-- Group ONE already executed source; do not execute or reconstruct it again. -/
def groupSource {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (state : AuthoritativeRuntime.Runtime family) {precision : Nat}
    (sourceAt : family.SourceAt precision)
    (produced : family.ProducedSourceAt state.journal sourceAt) :
    GroupingStep family state precision :=
  AuthoritativeRuntime.performGrouping family state
    (.snoc (.empty state.journal) sourceAt produced)

/--
Parallel source identities may share the common target future at equal start
depth. This is fixed-family behavioral equivalence, NOT occurrence identity.
-/
theorem groupedSources_project_eq {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    {first second : AuthoritativeRuntime.Runtime family} {precision : Nat}
    (firstAt secondAt : family.SourceAt precision)
    (firstSource : family.ProducedSourceAt first.journal firstAt)
    (secondSource : family.ProducedSourceAt second.journal secondAt)
    (sameDepth : first.journal.absoluteDepth = second.journal.absoluteDepth) :
    projectArchive family (groupSource family first firstAt firstSource).next =
      projectArchive family (groupSource family second secondAt secondSource).next := by
  rw [groupingNextProjection family (groupSource family first firstAt firstSource),
    groupingNextProjection family (groupSource family second secondAt secondSource)]
  apply Runtime.extensionality
  · rfl
  · apply ReducedState.extensionality
    · exact congrArg (fun depth => depth + groupCost 1) sameDepth
    · rfl

theorem groupedSourcesSameFuture {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    {first second : AuthoritativeRuntime.Runtime family} {precision : Nat}
    (firstAt secondAt : family.SourceAt precision)
    (firstSource : family.ProducedSourceAt first.journal firstAt)
    (secondSource : family.ProducedSourceAt second.journal secondAt)
    (sameDepth : first.journal.absoluteDepth = second.journal.absoluteDepth) :
    FutureEquivalent (archiveContract family)
      (groupSource family first firstAt firstSource).next
      (groupSource family second secondAt secondSource).next :=
  (archiveMemoryMinimality family).1
    (groupedSources_project_eq family firstAt secondAt firstSource secondSource sameDepth)

/-! ## Numerical comparison across executable environments -/

/-- Refusal has no numerical output; the default is never used by a limit step. -/
def eventCode : CommonEvent -> SignedDyadicCode
  | .executed event => event.readout
  | .refused _ _ => { positive := 0, negative := 0, scale := 0 }

theorem limitEventCode (state : Runtime) (precision : Nat) :
    eventCode (performReal state (.limit precision)).event =
      state.environment.producer.calculate
        { term := state.environment.modulus precision, precision := precision } := rfl

/--
A positive pairing of ACTUAL interpreter transitions. It compares only their
numerical readouts, never stamps, depth encodings, resources or occurrences.
The continuation is the next state returned by that same transition.
-/
inductive NumericalTrace (threshold : Nat -> Nat) :
    Runtime -> Runtime -> List (RuntimeCorrespondence.LimitQuery threshold) -> Type
  | done (first second : Runtime) : NumericalTrace threshold first second []
  | step {first second : Runtime}
      {query : RuntimeCorrespondence.LimitQuery threshold}
      {remaining : List (RuntimeCorrespondence.LimitQuery threshold)}
      (near : Near query.accuracy
        (eventCode (performReal first (.limit query.leftResponse)).event)
        (eventCode (performReal second (.limit query.rightResponse)).event))
      (later : NumericalTrace threshold
        (performReal first (.limit query.leftResponse)).next
        (performReal second (.limit query.rightResponse)).next remaining) :
      NumericalTrace threshold first second (query :: remaining)

/--
All finite numerical limit futures, from any memories in the two environments.
This is NOT exact FutureEquivalent and does not identify executable environments.
-/
structure NumericalFutureEquivalent (first second : Environment) where
  responseThreshold : Nat -> Nat
  traces : (firstMemory secondMemory : Memory) ->
    (queries : List (RuntimeCorrespondence.LimitQuery responseThreshold)) ->
      NumericalTrace responseThreshold
        { environment := first, memory := firstMemory }
        { environment := second, memory := secondMemory } queries

def pairNumericalTraces {firstEnvironment secondEnvironment : Environment}
    (threshold : Nat -> Nat)
    (near : (precision leftResponse rightResponse : Nat) ->
      PrecisionExtension (threshold precision) leftResponse ->
      PrecisionExtension (threshold precision) rightResponse ->
      Near precision
        (firstEnvironment.producer.calculate
          { term := firstEnvironment.modulus leftResponse, precision := leftResponse })
        (secondEnvironment.producer.calculate
          { term := secondEnvironment.modulus rightResponse, precision := rightResponse })) :
    (first second : Runtime) -> first.environment = firstEnvironment ->
      second.environment = secondEnvironment ->
      (queries : List (RuntimeCorrespondence.LimitQuery threshold)) ->
        NumericalTrace threshold first second queries
  | first, second, _, _, [] => .done first second
  | first, second, firstExact, secondExact, query :: remaining =>
      .step
        (by
          rw [limitEventCode, limitEventCode, firstExact, secondExact]
          exact near query.accuracy query.leftResponse query.rightResponse
            query.leftBeyond query.rightBeyond)
        (pairNumericalTraces threshold near _ _
          ((performReal_environment first (.limit query.leftResponse)).trans firstExact)
          ((performReal_environment second (.limit query.rightResponse)).trans secondExact)
          remaining)

theorem familyLimitReadout {P : CircularPresentation} {baseDepth : Nat}
    (real : RuntimeCorrespondence.RuntimeReal P baseDepth) (precision : Nat) :
    real.readout precision = real.family.producer.calculate
      { term := real.family.modulus precision, precision := precision } := by
  unfold RuntimeCorrespondence.RuntimeReal.readout
  rw [real.stepAt_is_perform]
  exact (AuthoritativeRuntime.perform real.family real.initial
    (.limit precision)).response.limit_readout_is_calculated

def numericalFuturesOfReadouts {P : CircularPresentation} {baseDepth : Nat}
    {first second : RuntimeCorrespondence.RuntimeReal P baseDepth}
    (equivalent : RuntimeCorrespondence.RuntimeReadoutEquivalent first second) :
    NumericalFutureEquivalent (environmentOfFamily first.family)
      (environmentOfFamily second.family) where
  responseThreshold := equivalent.responseThreshold
  traces firstMemory secondMemory queries :=
    pairNumericalTraces equivalent.responseThreshold
      (fun precision leftResponse rightResponse leftBeyond rightBeyond => by
        have near := equivalent.near precision leftResponse rightResponse leftBeyond rightBeyond
        rw [familyLimitReadout, familyLimitReadout] at near
        exact near)
      { environment := environmentOfFamily first.family, memory := firstMemory }
      { environment := environmentOfFamily second.family, memory := secondMemory }
      rfl rfl queries

def readoutsOfNumericalFutures {P : CircularPresentation} {baseDepth : Nat}
    {first second : RuntimeCorrespondence.RuntimeReal P baseDepth}
    (equivalent : NumericalFutureEquivalent (environmentOfFamily first.family)
      (environmentOfFamily second.family)) :
    RuntimeCorrespondence.RuntimeReadoutEquivalent first second where
  responseThreshold := equivalent.responseThreshold
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    let query : RuntimeCorrespondence.LimitQuery equivalent.responseThreshold :=
      { accuracy := precision, leftResponse := leftResponse, rightResponse := rightResponse
        leftBeyond := leftBeyond, rightBeyond := rightBeyond }
    have paired := equivalent.traces
      { depth := 0, last := none } { depth := 0, last := none } [query]
    cases paired with
    | step near later =>
        rw [limitEventCode, limitEventCode] at near
        rw [familyLimitReadout, familyLimitReadout]
        exact near

/-- Exact numerical correspondence, without any identity of occurrences. -/
def numericalFutureCorrespondence {P : CircularPresentation} {baseDepth : Nat}
    (first second : RuntimeCorrespondence.RuntimeReal P baseDepth) :
    (RuntimeCorrespondence.RuntimeReadoutEquivalent first second ->
      NumericalFutureEquivalent (environmentOfFamily first.family)
        (environmentOfFamily second.family)) ×
    (NumericalFutureEquivalent (environmentOfFamily first.family)
        (environmentOfFamily second.family) ->
      RuntimeCorrespondence.RuntimeReadoutEquivalent first second) :=
  ⟨numericalFuturesOfReadouts, readoutsOfNumericalFutures⟩


/-! ## One generic master, then the Gödel-specific raccord -/

/--
The one generic master retains the generic executed real and every term, the
whole common-future realization, and the causal grouping/installed continuation
services. No independent limit producer is substituted in its consumers.
-/
structure Completeness {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) where
  rich : GenericCompleteness family
  richExact : rich = completeGeneric family
  live : Runtime
  liveExact : live = projectArchive family (AuthoritativeRuntime.initialState family)
  realization : ExactRealization (archiveContract family) Runtime
  realizationExact : realization = archiveRealization family
  group : (state : AuthoritativeRuntime.Runtime family) -> {precision : Nat} ->
    List (family.SourceAt precision) -> GroupingStep family state precision
  groupExact : (state : AuthoritativeRuntime.Runtime family) -> {precision : Nat} ->
    (sources : List (family.SourceAt precision)) ->
      group state sources = performSourceListGrouping family state sources
  resumeInstalled : (state : AuthoritativeRuntime.Runtime family) -> (extra : Nat) ->
    Option (ContinuedStep family state extra)
  continueExact : (state : AuthoritativeRuntime.Runtime family) -> (extra : Nat) ->
    resumeInstalled state extra = AuthoritativeRuntime.continueInstalled family state extra

def complete {P : CircularPresentation} {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) : Completeness family where
  rich := completeGeneric family
  richExact := rfl
  live := projectArchive family (AuthoritativeRuntime.initialState family)
  liveExact := rfl
  realization := archiveRealization family
  realizationExact := rfl
  group := performSourceListGrouping family
  groupExact := fun _ _ _ => rfl
  resumeInstalled := AuthoritativeRuntime.continueInstalled family
  continueExact := fun _ _ => rfl

end RelationalPerimeter.Constitution.Reals.CommonRealRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Environment
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.environmentOfFamily
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Runtime
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.initialState
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Request
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.readInstalled
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupAllowed
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.enabled
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Admission
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.admissionDecision
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.ValueNormalization
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.normalizeValues
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.normalizeValues_code
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.normalizeValues_consumed
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Transition
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupCost
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.performReal
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.read
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.contract
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.runReal
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.runReal_contract
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.performReal_environment
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.memoryContract
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.fixedEnvironmentMinimality
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.anyFixedEnvironmentRealization
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.admissionEnabled
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Runtime.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.projectArchive
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.typedRequest
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.typedNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.typedEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.typedArchiveBridge
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.typedArchiveEvents
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.typedArchiveObservations
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.CertifiedSources
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.extensionOfLe
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.certifySources
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.ArchiveResource
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.ArchiveTransition
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.performArchive
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.extensionFromBound
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.andTrueParts
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupCost_exact
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.rawNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.rawEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupingReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupingDepthExact
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupingNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupingEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.installedProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.continuedReadProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.continuedNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.continuedEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.noContinuationRead
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveProjection
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveRealization
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveFutures_exact
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.eventCode
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.limitEventCode
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.NumericalTrace
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.NumericalFutureEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.pairNumericalTraces
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.familyLimitReadout
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.numericalFuturesOfReadouts
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.readoutsOfNumericalFutures
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.numericalFutureCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Completeness
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.complete
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveMemoryMinimality
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.everyArchiveRealizationNeedsMemory
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupSource
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupedSources_project_eq
#print axioms RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupedSourcesSameFuture
/- AXIOM_AUDIT_END -/
