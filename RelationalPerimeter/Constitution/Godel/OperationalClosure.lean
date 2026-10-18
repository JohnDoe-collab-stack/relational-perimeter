import RelationalPerimeter.Constitution.Godel.OperationalH1
import RelationalPerimeter.Constitution.Continuation.CommonMemoryGrouping
import RelationalPerimeter.Constitution.Continuation.ReadoutCorrespondence

/-! Close creates a terminal phase and a computed common operational memory.
Readout preservation remains a separate, conditional specification. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.defProp false
namespace StrongPerimetralTurning
open ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures
inductive ClosurePole where
  | left
  | right
  deriving DecidableEq
inductive GodelRuntimePhase where
  | active
  | terminal
  deriving DecidableEq
universe uA uB uC uP uV u
variable {coding : GodelDiagonalSyntax.{uC,uA,uB,uP,uV}}
  {unprovabilityFormula : coding.UnaryFormula}
  {interpretation : GodelProvabilityInterpretation coding unprovabilityFormula}
structure GodelClosureSource
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  core : GodelPositiveExecutionCore execution
  h1 : GodelOperationalH1 core
  pole : ClosurePole
  operationalHistory : GodelOperationalHistory h1
  phase : GodelRuntimePhase
/-- A nondependent readout packages the actual H1 and continuation together. -/
structure GodelRuntimeHistory
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  core : GodelPositiveExecutionCore execution
  h1 : GodelOperationalH1 core
  post : GodelOperationalHistory h1
namespace GodelRuntimeHistory
variable {execution : ExecutedGodelProduction coding unprovabilityFormula interpretation}
def additionalDepth (history : GodelRuntimeHistory execution) := history.post.additionalDepth
def depth (history : GodelRuntimeHistory execution) := history.post.depth
def extend (history : GodelRuntimeHistory execution) : GodelRuntimeHistory execution :=
  { history with post := history.post.extend }
end GodelRuntimeHistory
namespace GodelClosureSource
variable {execution : ExecutedGodelProduction coding unprovabilityFormula interpretation}
def history (source : GodelClosureSource execution) : GodelRuntimeHistory execution :=
  ⟨source.core, source.h1, source.operationalHistory⟩
def depth (source : GodelClosureSource execution) := source.history.depth
def provenance (source : GodelClosureSource execution) :
    Sigma (fun core : GodelPositiveExecutionCore execution => GodelOperationalH1 core) :=
  ⟨source.core, source.h1⟩
abbrev occurrences (source : GodelClosureSource execution) := History.Occurrence source.operationalHistory.continuation
end GodelClosureSource
variable (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
def godelEndpointAt : ClosurePole → Type uP
  | .left => interpretation.Truth execution.witness.production.sentence
  | .right => coding.Proof execution.witness.production.sentence
abbrev GodelRuntimeState := GodelClosureSource execution
def initializeAt (core : GodelPositiveExecutionCore execution)
    (h1 : GodelOperationalH1 core) (pole : ClosurePole) : GodelRuntimeState execution :=
  ⟨core, h1, pole, GodelOperationalHistory.root h1, .active⟩
def «initialize» (pole : ClosurePole) : GodelRuntimeState execution :=
  let core := godelPositiveExecutionCore execution
  let h1 := godelOperationalH1 core
  initializeAt execution core h1 pole
def semanticSource := «initialize» execution .left
def syntacticSource := «initialize» execution .right
theorem semanticSource_ne_syntacticSource : semanticSource execution ≠ syntacticSource execution := by
  intro same
  have roles := congrArg GodelClosureSource.pole same
  cases roles
inductive GodelRuntimeRequest : Type u where
  | continue
  | close
  deriving DecidableEq
def godelContinueRequest (_execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelRuntimeRequest.{max uA uC uP uV} := .continue
def godelCloseRequest (_execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelRuntimeRequest.{max uA uC uP uV} := .close
structure GodelRuntimeEvent where
  beforePhase : GodelRuntimePhase
  beforeDepth : Nat
  request : GodelRuntimeRequest.{0}
  afterPhase : GodelRuntimePhase
  afterDepth : Nat
def GodelRuntimeRequest.eraseUniverse : GodelRuntimeRequest.{u} → GodelRuntimeRequest.{0}
  | .continue => .continue
  | .close => .close
/-- The very same positive family is shared by both contracts. -/
inductive GodelOperationalAllow : Nat → GodelRuntimePhase → GodelRuntimeRequest.{u} → Type u
  | continue (depth : Nat) : GodelOperationalAllow depth .active .continue
  | close : GodelOperationalAllow 0 .active .close
def godelOperationalPermission (depth : Nat) (phase : GodelRuntimePhase)
    (request : GodelRuntimeRequest.{u}) : Prop :=
  match phase with
  | .active => match request with
    | .continue => True
    | .close => match depth with
      | 0 => True
      | _ + 1 => False
  | .terminal => False
def GodelOperationalAllow.permission {depth : Nat} {phase : GodelRuntimePhase}
    {request : GodelRuntimeRequest.{u}} (witness : GodelOperationalAllow depth phase request) :
    godelOperationalPermission depth phase request :=
  match witness with
  | .continue _ => True.intro
  | .close => True.intro
def godelOperationalDecision (depth : Nat) (phase : GodelRuntimePhase) (request : GodelRuntimeRequest.{u}) :
    PSum (GodelOperationalAllow depth phase request) (GodelOperationalAllow depth phase request → False) :=
  match phase, request, depth with
  | .active, .continue, depth => .inl (.continue depth)
  | .active, .close, 0 => .inl .close
  | .active, .close, _ + 1 => .inr (fun witness => witness.permission)
  | .terminal, _, _ => .inr (fun witness => witness.permission)
def GodelRuntimeAllow (source : GodelClosureSource execution)
    (request : GodelRuntimeRequest.{max uA uC uP uV}) :=
  GodelOperationalAllow source.operationalHistory.additionalDepth source.phase request
def godelRuntimeDecision (source : GodelClosureSource execution)
    (request : GodelRuntimeRequest.{max uA uC uP uV}) :
    PSum (GodelRuntimeAllow execution source request) (GodelRuntimeAllow execution source request → False) :=
  godelOperationalDecision source.operationalHistory.additionalDepth source.phase request
def godelNextPhase (phase : GodelRuntimePhase) (depth : Nat)
    (request : GodelRuntimeRequest.{u}) : GodelRuntimePhase :=
  match phase with
  | .active => match request with
    | .continue => .active
    | .close => match depth with
      | 0 => .terminal
      | _ + 1 => .active
  | .terminal => .terminal
def godelNextHistory {core : GodelPositiveExecutionCore execution} {h1 : GodelOperationalH1 core}
    (history : GodelOperationalHistory h1) (phase : GodelRuntimePhase)
    (request : GodelRuntimeRequest.{u}) : GodelOperationalHistory h1 :=
  match phase with
  | .active => match request with
    | .continue => history.extend
    | .close => history
  | .terminal => history
def godelRuntimeNext (source : GodelClosureSource execution)
    (request : GodelRuntimeRequest.{max uA uC uP uV}) : GodelClosureSource execution :=
  { source with
    operationalHistory := godelNextHistory execution source.operationalHistory source.phase request
    phase := godelNextPhase source.phase source.operationalHistory.additionalDepth request }
def godelRuntimeEvent (source : GodelClosureSource execution)
    (request : GodelRuntimeRequest.{max uA uC uP uV}) : GodelRuntimeEvent :=
  let target := godelRuntimeNext execution source request
  ⟨source.phase, source.depth, request.eraseUniverse, target.phase, target.depth⟩
def godelClosureContract :
    FutureContract (GodelClosureSource execution) GodelRuntimeRequest
      (ULift.{uP+1} GodelRuntimeEvent) (Type uP) where
  next := godelRuntimeNext execution
  event := fun source request => ⟨godelRuntimeEvent execution source request⟩
  read := fun source => godelEndpointAt execution source.pole
  Allow := GodelRuntimeAllow execution
  decision := godelRuntimeDecision execution
def godelRuntimePerform (source : GodelRuntimeState execution) (request : GodelRuntimeRequest)
    (authorized : (godelClosureContract execution).Allow source request) :=
  perform (godelClosureContract execution) source request authorized
abbrev godelRuntimeRun := Grouping.Continuation.run (godelClosureContract execution).next
abbrev GodelReachableRuntime (pole : ClosurePole) :=
  ReachableRuntime (godelClosureContract execution) («initialize» execution pole)
def godelIdentityRealization := identityRealization (godelClosureContract execution)
inductive GodelOperationalMemory
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
  | active (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core)
      (pole : ClosurePole) (history : GodelOperationalHistory h1)
  | grouped (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core)
      (history : GodelOperationalHistory h1)
def godelOperationalProject (source : GodelClosureSource execution) : GodelOperationalMemory execution :=
  match source.phase with
  | .active => .active source.core source.h1 source.pole source.operationalHistory
  | .terminal => .grouped source.core source.h1 source.operationalHistory
namespace GodelOperationalMemory
variable {execution}
def phase : GodelOperationalMemory execution → GodelRuntimePhase
  | .active _ _ _ _ => .active
  | .grouped _ _ _ => .terminal
def additionalDepth : GodelOperationalMemory execution → Nat
  | .active _ _ _ history => history.additionalDepth
  | .grouped _ _ history => history.additionalDepth
def depth (memory : GodelOperationalMemory execution) := memory.additionalDepth + 1
def activePole? : GodelOperationalMemory execution → Option ClosurePole
  | .active _ _ pole _ => some pole
  | .grouped _ _ _ => none
end GodelOperationalMemory
def godelOperationalNext : GodelOperationalMemory execution → GodelRuntimeRequest → GodelOperationalMemory execution
  | .active core h1 pole history, .continue => .active core h1 pole history.extend
  | memory@(.active core h1 _ history), .close => match history.additionalDepth with
    | 0 => .grouped core h1 history
    | _ + 1 => memory
  | memory@(.grouped _ _ _), _ => memory
def godelOperationalEvent (memory : GodelOperationalMemory execution) (request : GodelRuntimeRequest) :
    GodelRuntimeEvent :=
  let target := godelOperationalNext execution memory request
  ⟨memory.phase, memory.depth, request.eraseUniverse, target.phase, target.depth⟩
def godelOperationalReducedContract :
    FutureContract (GodelOperationalMemory execution) GodelRuntimeRequest
      (ULift.{uP+1} GodelRuntimeEvent) (Type uP) where
  next := godelOperationalNext execution
  event := fun memory request => ⟨godelOperationalEvent execution memory request⟩
  read := fun _ => PUnit
  Allow := fun memory request => GodelOperationalAllow memory.additionalDepth memory.phase request
  decision := fun memory request => godelOperationalDecision memory.additionalDepth memory.phase request
structure GodelOperationalRealizationWithoutRead where
  reduced : FutureContract (GodelOperationalMemory execution) GodelRuntimeRequest
    (ULift.{uP+1} GodelRuntimeEvent) (Type uP)
  project : GodelClosureSource execution → GodelOperationalMemory execution
  forward : ∀ source request,
    (godelClosureContract execution).Allow source request → reduced.Allow (project source) request
  backward : ∀ source request,
    reduced.Allow (project source) request → (godelClosureContract execution).Allow source request
  backward_forward : ∀ source request witness,
    backward source request (forward source request witness) = witness
  forward_backward : ∀ source request witness,
    forward source request (backward source request witness) = witness
  next_exact : ∀ source request,
    project ((godelClosureContract execution).next source request) = reduced.next (project source) request
  event_exact : ∀ source request,
    (godelClosureContract execution).event source request = reduced.event (project source) request
def godelOperationalRealizationWithoutRead : GodelOperationalRealizationWithoutRead execution where
  reduced := godelOperationalReducedContract execution
  project := godelOperationalProject execution
  forward := by
    intro source request witness
    cases source with
    | mk core h1 pole history phase => cases phase <;> exact witness
  backward := by
    intro source request witness
    cases source with
    | mk core h1 pole history phase => cases phase <;> exact witness
  backward_forward := by
    intro source request witness
    cases source with
    | mk core h1 pole history phase => cases phase <;> rfl
  forward_backward := by
    intro source request witness
    cases source with
    | mk core h1 pole history phase => cases phase <;> rfl
  next_exact := by
    intro source request
    cases source with
    | mk core h1 pole history phase =>
      cases history with
      | mk depth continuation => cases phase <;> cases request <;> cases depth <;> rfl
  event_exact := by
    intro source request
    cases source with
    | mk core h1 pole history phase =>
      cases history with
      | mk depth continuation => cases phase <;> cases request <;> cases depth <;> rfl
theorem godelOperational_initial_memories_distinct :
    godelOperationalProject execution (semanticSource execution) ≠
      godelOperationalProject execution (syntacticSource execution) := by
  intro same
  have roles := congrArg GodelOperationalMemory.activePole? same
  cases roles
theorem godelRuntimeNext_pole (source : GodelClosureSource execution) (request : GodelRuntimeRequest) :
    (godelRuntimeNext execution source request).pole = source.pole := by
  cases source with
  | mk core h1 pole history phase =>
    cases phase <;> cases request <;> cases depthEq : history.additionalDepth <;>
      rfl
theorem pole_run (source : GodelClosureSource execution) (requests : List GodelRuntimeRequest) :
    (godelRuntimeRun execution source requests).pole = source.pole := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih => exact (ih _).trans (godelRuntimeNext_pole execution source request)
theorem read_run (source : GodelClosureSource execution) (requests : List GodelRuntimeRequest) :
    (godelClosureContract execution).read (godelRuntimeRun execution source requests) =
      (godelClosureContract execution).read source :=
  congrArg (godelEndpointAt execution) (pole_run execution source requests)
theorem godel_read_semantic : (godelClosureContract execution).read (semanticSource execution) =
    interpretation.Truth execution.witness.production.sentence := rfl
theorem godel_read_syntactic : (godelClosureContract execution).read (syntacticSource execution) =
    coding.Proof execution.witness.production.sentence := rfl
namespace GodelClosureSource
variable {execution}
theorem history_continue (source : GodelClosureSource execution) (active : source.phase = .active) :
    (godelRuntimeNext execution source .continue).history = source.history.extend := by
  cases source with
  | mk core h1 pole history phase => cases active; rfl
theorem history_close (source : GodelClosureSource execution) :
    (godelRuntimeNext execution source .close).history = source.history := by
  cases source with
  | mk core h1 pole history phase =>
    cases phase <;> cases depthEq : history.additionalDepth <;>
      cases history.additionalDepth <;> rfl
theorem provenance_continue (source : GodelClosureSource execution) :
    (godelRuntimeNext execution source .continue).provenance = source.provenance := by
  cases source with
  | mk core h1 pole history phase => cases phase <;> rfl
theorem provenance_close (source : GodelClosureSource execution) :
    (godelRuntimeNext execution source .close).provenance = source.provenance := by
  rfl
def continueOccurrenceSplit (source : GodelClosureSource execution) (active : source.phase = .active) :
    ExactTypeTransport (source.occurrences ⊕ Unit)
      (godelRuntimeNext execution source .continue).occurrences := by
  cases source with
  | mk core h1 pole history phase =>
    cases active
    exact history.extendOccurrenceTransport
end GodelClosureSource
theorem initialize_history (pole : ClosurePole) :
    («initialize» execution pole).history =
      ⟨godelPositiveExecutionCore execution, godelOperationalH1 (godelPositiveExecutionCore execution),
        GodelOperationalHistory.root (godelOperationalH1 (godelPositiveExecutionCore execution))⟩ := rfl
def godelCloseAuthorized (pole : ClosurePole) :
    (godelClosureContract execution).Allow («initialize» execution pole) (godelCloseRequest execution) := .close
def godelOpenCloseRun (pole : ClosurePole) :
    ExecutedRun (godelClosureContract execution) («initialize» execution pole)
      [godelCloseRequest execution] (godelRuntimeNext execution («initialize» execution pole) .close)
      [(godelClosureContract execution).event («initialize» execution pole) (godelCloseRequest execution)] :=
  .cons (godelRuntimePerform execution _ _ (godelCloseAuthorized execution pole)) (.nil _)
theorem godelClose_changes_phase (pole : ClosurePole) :
    (godelRuntimeNext execution («initialize» execution pole) .close).phase = .terminal := rfl
theorem godelClose_not_identity (pole : ClosurePole) :
    godelRuntimeNext execution («initialize» execution pole) .close ≠ «initialize» execution pole := by
  intro same
  have phases := congrArg GodelClosureSource.phase same
  cases phases
theorem godelTerminalNextStable (source : GodelClosureSource execution)
    (terminal : source.phase = .terminal) (request : GodelRuntimeRequest) :
    godelRuntimeNext execution source request = source := by
  cases source with
  | mk core h1 pole history phase => cases terminal; rfl
def godelTerminalNoAuthorization (source : GodelClosureSource execution)
    (terminal : source.phase = .terminal) (request : GodelRuntimeRequest) :
    GodelRuntimeAllow execution source request → False := by
  cases source with
  | mk core h1 pole history phase =>
    cases terminal
    exact fun witness => witness.permission
theorem godelClosePreservesRead (source : GodelClosureSource execution) :
    (godelClosureContract execution).read (godelRuntimeNext execution source .close) =
      (godelClosureContract execution).read source := rfl
structure GodelOperationalGroupingWithoutRead where
  trace : NonemptyRequestTrace GodelRuntimeRequest
  leftTerminal : GodelClosureSource execution
  leftEvents : List (ULift.{uP+1} GodelRuntimeEvent)
  leftRun : ExecutedRun (godelClosureContract execution) (semanticSource execution)
    trace.toList leftTerminal leftEvents
  rightTerminal : GodelClosureSource execution
  rightEvents : List (ULift.{uP+1} GodelRuntimeEvent)
  rightRun : ExecutedRun (godelClosureContract execution) (syntacticSource execution)
    trace.toList rightTerminal rightEvents
  terminalCollision :
    Grouping.Continuation.run (godelOperationalRealizationWithoutRead execution).reduced.next
        ((godelOperationalRealizationWithoutRead execution).project (semanticSource execution)) trace.toList =
      Grouping.Continuation.run (godelOperationalRealizationWithoutRead execution).reduced.next
        ((godelOperationalRealizationWithoutRead execution).project (syntacticSource execution)) trace.toList
def GodelOperationalGroupingWithoutRead.requests
    (grouping : GodelOperationalGroupingWithoutRead execution) := grouping.trace.toList
theorem GodelOperationalGroupingWithoutRead.nonempty
    (grouping : GodelOperationalGroupingWithoutRead execution) : grouping.requests ≠ [] := by
  intro impossible
  cases impossible
def godelOpenContinueRun (pole : ClosurePole) :
    ExecutedRun (godelClosureContract execution) («initialize» execution pole)
      [godelContinueRequest execution] (godelRuntimeNext execution («initialize» execution pole) .continue)
      [(godelClosureContract execution).event («initialize» execution pole) .continue] :=
  .cons (godelRuntimePerform execution («initialize» execution pole) .continue (.continue 0)) (.nil _)
def godelOpenRuntime (pole : ClosurePole) : GodelReachableRuntime execution pole :=
  ⟨[godelContinueRequest execution], _, _, godelOpenContinueRun execution pole⟩
theorem godelIdentity_close_outputs_distinct :
    Grouping.Continuation.run (godelIdentityRealization execution).reduced.next
        ((godelIdentityRealization execution).project (semanticSource execution)) [godelCloseRequest execution] ≠
      Grouping.Continuation.run (godelIdentityRealization execution).reduced.next
        ((godelIdentityRealization execution).project (syntacticSource execution)) [godelCloseRequest execution] := by
  intro same
  have roles := congrArg GodelClosureSource.pole same
  cases roles
theorem godelExactRunExact {Memory : Type (max uA uC uP uV)}
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (source : GodelClosureSource execution) (requests : List GodelRuntimeRequest) :
    realization.project (Grouping.Continuation.run (godelClosureContract execution).next source requests) =
      Grouping.Continuation.run realization.reduced.next (realization.project source) requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    exact (ih _).trans (congrArg
      (fun memory => Grouping.Continuation.run realization.reduced.next memory rest)
      (realization.next_exact source request))
def godelExecutedGroupingProjectedTerminalsEqual {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (grouping : ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution)) :
    realization.project grouping.leftTerminal = realization.project grouping.rightTerminal :=
  let leftExact := (congrArg realization.project grouping.leftRun.terminal_eq_run).trans
    (godelExactRunExact execution realization _ grouping.requests)
  let rightExact := (congrArg realization.project grouping.rightRun.terminal_eq_run).trans
    (godelExactRunExact execution realization _ grouping.requests)
  leftExact.trans (grouping.terminalCollision.trans rightExact.symm)
def godelExecutedGroupingToEndpointEquality {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (grouping : ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution)) :
    interpretation.Truth execution.witness.production.sentence = coding.Proof execution.witness.production.sentence :=
  let leftRead := (congrArg (godelClosureContract execution).read
    grouping.leftRun.terminal_eq_run).trans (read_run execution _ grouping.requests)
  let rightRead := (congrArg (godelClosureContract execution).read
    grouping.rightRun.terminal_eq_run).trans (read_run execution _ grouping.requests)
  let projectedEqual := godelExecutedGroupingProjectedTerminalsEqual execution grouping
  let terminalReadEqual := (realization.read_exact grouping.leftTerminal).trans
    ((congrArg realization.reduced.read projectedEqual).trans (realization.read_exact grouping.rightTerminal).symm)
  leftRead.symm.trans (terminalReadEqual.trans rightRead)
def godelExecutedOperationalGroupingToProducedCompleteness
    {Memory : Type (max uA uC uP uV)}
    (realization : OperationalRealization (godelClosureContract execution) Memory)
    {leftTerminal rightTerminal : GodelClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (semanticSource execution) (syntacticSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization leftTerminal rightTerminal) :
    ExecutedGodelProducedCompleteness execution.witness := by
  have leftRead := (congrArg (godelClosureContract execution).read
    grouping.leftRun.terminal_eq_run).trans (read_run execution _ grouping.requests)
  have rightRead := (congrArg (godelClosureContract execution).read
    grouping.rightRun.terminal_eq_run).trans (read_run execution _ grouping.requests)
  exact fun truthWitness =>
    Eq.mp rightRead
      (grouping.directedReadout preservation (Eq.mp leftRead.symm truthWitness))
def rejectGodelExecutedOperationalGroupingToEmpty
    {Memory : Type (max uA uC uP uV)}
    (realization : OperationalRealization (godelClosureContract execution) Memory)
    {leftTerminal rightTerminal : GodelClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (semanticSource execution) (syntacticSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization leftTerminal rightTerminal) : Empty :=
  execution.witness.unprovable
    (godelExecutedOperationalGroupingToProducedCompleteness execution realization
      grouping preservation execution.witness.trueWitness)
theorem godelOperationalRunExact
    (source : GodelClosureSource execution) (requests : List GodelRuntimeRequest) :
    godelOperationalProject execution (godelRuntimeRun execution source requests) =
      Grouping.Continuation.run (godelOperationalReducedContract execution).next
        (godelOperationalProject execution source) requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    exact (ih _).trans (congrArg
      (fun memory => Grouping.Continuation.run (godelOperationalReducedContract execution).next memory rest)
      ((godelOperationalRealizationWithoutRead execution).next_exact source request))

inductive GodelInitializedAt (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    ClosurePole → Type (max uA uC uP uV)
  | fromContinuation (pole : ClosurePole) : GodelInitializedAt core h1 pole
namespace GodelInitializedAt
variable {execution} {core : GodelPositiveExecutionCore execution} {h1 : GodelOperationalH1 core} {pole : ClosurePole}
def source (_initialized : GodelInitializedAt execution core h1 pole) : GodelClosureSource execution :=
  initializeAt execution core h1 pole
theorem source_exact (initialized : GodelInitializedAt execution core h1 pole) :
    initialized.source = initializeAt execution core h1 pole := by cases initialized; rfl
theorem source_history (initialized : GodelInitializedAt execution core h1 pole) :
    initialized.source.history = (⟨core, h1, GodelOperationalHistory.root h1⟩ : GodelRuntimeHistory execution) := by cases initialized; rfl
end GodelInitializedAt
structure GodelClosureContextAt (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) where
  semantic : GodelInitializedAt execution core h1 .left
  syntactic : GodelInitializedAt execution core h1 .right
namespace GodelClosureContextAt
variable {execution} {core : GodelPositiveExecutionCore execution} {h1 : GodelOperationalH1 core}
def leftSource (context : GodelClosureContextAt execution core h1) := context.semantic.source
def rightSource (context : GodelClosureContextAt execution core h1) := context.syntactic.source
def request (_context : GodelClosureContextAt execution core h1) := godelCloseRequest execution
theorem leftSource_exact (context : GodelClosureContextAt execution core h1) :
    context.leftSource = initializeAt execution core h1 .left := context.semantic.source_exact
theorem rightSource_exact (context : GodelClosureContextAt execution core h1) :
    context.rightSource = initializeAt execution core h1 .right := context.syntactic.source_exact
theorem sources_distinct (context : GodelClosureContextAt execution core h1) :
    context.leftSource ≠ context.rightSource := by
  intro same
  have roles := congrArg GodelClosureSource.pole
    (context.leftSource_exact.symm.trans (same.trans context.rightSource_exact))
  cases roles
theorem h1_shared (context : GodelClosureContextAt execution core h1) :
    context.leftSource.provenance = context.rightSource.provenance := by
  rw [context.leftSource_exact, context.rightSource_exact]
  rfl
end GodelClosureContextAt
def godelReceivedClosureContext :
    GodelClosureContextAt execution (godelPositiveExecutionCore execution)
      (godelOperationalH1 (godelPositiveExecutionCore execution)) :=
  let core := godelPositiveExecutionCore execution
  let h1 := godelOperationalH1 core
  let context : GodelClosureContextAt execution core h1 := ⟨.fromContinuation .left, .fromContinuation .right⟩
  context
variable {execution} {core : GodelPositiveExecutionCore execution} {h1 : GodelOperationalH1 core}
structure GodelSearchedCloseAction (context : GodelClosureContextAt execution core h1) where
  request : GodelRuntimeRequest.{max uA uC uP uV}
  selected : request = context.request
def godelSearchCloseAction (context : GodelClosureContextAt execution core h1) :
    GodelSearchedCloseAction context := ⟨context.request, rfl⟩
theorem godelSearchedCloseAction_preservesHistory {context : GodelClosureContextAt execution core h1}
    (action : GodelSearchedCloseAction context) :
    (godelRuntimeNext execution context.leftSource action.request).history = (⟨core, h1, GodelOperationalHistory.root h1⟩ : GodelRuntimeHistory execution) ∧
      (godelRuntimeNext execution context.rightSource action.request).history = (⟨core, h1, GodelOperationalHistory.root h1⟩ : GodelRuntimeHistory execution) := by
  rw [action.selected, context.leftSource_exact, context.rightSource_exact]
  exact ⟨rfl, rfl⟩
theorem godelSearchedCloseAction_preservesProvenance {context : GodelClosureContextAt execution core h1}
    (action : GodelSearchedCloseAction context) :
    (godelRuntimeNext execution context.leftSource action.request).provenance = context.leftSource.provenance ∧
      (godelRuntimeNext execution context.rightSource action.request).provenance = context.rightSource.provenance := by
  rw [action.selected]
  exact ⟨GodelClosureSource.provenance_close _, GodelClosureSource.provenance_close _⟩
structure GodelAuthorizedCloseAction {context : GodelClosureContextAt execution core h1}
    (action : GodelSearchedCloseAction context) where
  left : (godelClosureContract execution).Allow context.leftSource action.request
  right : (godelClosureContract execution).Allow context.rightSource action.request
def godelAuthorizeCloseAction {context : GodelClosureContextAt execution core h1}
    (action : GodelSearchedCloseAction context) : GodelAuthorizedCloseAction action := by
  constructor
  · rw [action.selected, context.leftSource_exact]
    exact .close
  · rw [action.selected, context.rightSource_exact]
    exact .close
structure GodelDecomposedCloseAction {context : GodelClosureContextAt execution core h1}
    {action : GodelSearchedCloseAction context} (authorization : GodelAuthorizedCloseAction action) where
  leftStep : ExecutedStep (godelClosureContract execution) context.leftSource action.request
  rightStep : ExecutedStep (godelClosureContract execution) context.rightSource action.request
  leftAuthorizationExact : leftStep.authorized = authorization.left
  rightAuthorizationExact : rightStep.authorized = authorization.right
def godelDecomposeCloseAction {context : GodelClosureContextAt execution core h1}
    {action : GodelSearchedCloseAction context} (authorization : GodelAuthorizedCloseAction action) :
    GodelDecomposedCloseAction authorization :=
  ⟨godelRuntimePerform execution _ _ authorization.left,
    godelRuntimePerform execution _ _ authorization.right, rfl, rfl⟩
inductive GodelExecutedCloseAction {context : GodelClosureContextAt execution core h1}
    {action : GodelSearchedCloseAction context} {authorization : GodelAuthorizedCloseAction action}
    (decomposition : GodelDecomposedCloseAction authorization) : Type
  | execute
namespace GodelExecutedCloseAction
variable {context : GodelClosureContextAt execution core h1}
  {action : GodelSearchedCloseAction context} {authorization : GodelAuthorizedCloseAction action}
  {decomposition : GodelDecomposedCloseAction authorization}
def leftRun (_executed : GodelExecutedCloseAction decomposition) :
    ExecutedRun (godelClosureContract execution) context.leftSource [action.request]
      decomposition.leftStep.target [decomposition.leftStep.producedEvent] := .cons decomposition.leftStep (.nil _)
def rightRun (_executed : GodelExecutedCloseAction decomposition) :
    ExecutedRun (godelClosureContract execution) context.rightSource [action.request]
      decomposition.rightStep.target [decomposition.rightStep.producedEvent] := .cons decomposition.rightStep (.nil _)
def leftReducedTerminal {Memory : Type (max uA uC uP uV)}
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (_executed : GodelExecutedCloseAction decomposition) :=
  Grouping.Continuation.run realization.reduced.next (realization.project context.leftSource) [action.request]
def rightReducedTerminal {Memory : Type (max uA uC uP uV)}
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (_executed : GodelExecutedCloseAction decomposition) :=
  Grouping.Continuation.run realization.reduced.next (realization.project context.rightSource) [action.request]
theorem requests_exact (_executed : GodelExecutedCloseAction decomposition) :
    [action.request] = [godelCloseRequest execution] := congrArg (fun request => [request]) action.selected
def grouping {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (executed : GodelExecutedCloseAction decomposition)
    (collision : executed.leftReducedTerminal realization = executed.rightReducedTerminal realization) :
    ExecutedCommonMemoryGrouping realization context.leftSource context.rightSource where
  trace := ⟨action.request, []⟩
  leftTerminal := decomposition.leftStep.target
  leftEvents := [decomposition.leftStep.producedEvent]
  leftRun := executed.leftRun
  rightTerminal := decomposition.rightStep.target
  rightEvents := [decomposition.rightStep.producedEvent]
  rightRun := executed.rightRun
  terminalCollision := collision
end GodelExecutedCloseAction
variable (execution)
def godelOperationalGroupingWithoutRead : GodelOperationalGroupingWithoutRead execution :=
  let context := godelReceivedClosureContext execution
  let action := godelSearchCloseAction context
  let authorization := godelAuthorizeCloseAction action
  let decomposition := godelDecomposeCloseAction authorization
  let executed : GodelExecutedCloseAction decomposition := .execute
  { trace := ⟨action.request, []⟩
    leftTerminal := decomposition.leftStep.target
    leftEvents := [decomposition.leftStep.producedEvent]
    leftRun := executed.leftRun
    rightTerminal := decomposition.rightStep.target
    rightEvents := [decomposition.rightStep.producedEvent]
    rightRun := executed.rightRun
    terminalCollision := rfl }
theorem godelOperationalGroupingWithoutRead_events_equal :
    (godelOperationalGroupingWithoutRead execution).leftEvents =
      (godelOperationalGroupingWithoutRead execution).rightEvents := rfl
/-- This direct bridge consumes the executed close runs and calculated
collision. Its proof does not project any event-preservation law. -/
def godelTerminalReadExactToEndpointEquality
    (reducedRead : GodelOperationalMemory execution → Type uP)
    (readExact : ∀ source, (godelClosureContract execution).read source =
      reducedRead (godelOperationalProject execution source)) :
    interpretation.Truth execution.witness.production.sentence = coding.Proof execution.witness.production.sentence :=
  let positive := godelOperationalGroupingWithoutRead execution
  let leftRead := (congrArg (godelClosureContract execution).read
    positive.leftRun.terminal_eq_run).trans (read_run execution _ positive.requests)
  let rightRead := (congrArg (godelClosureContract execution).read
    positive.rightRun.terminal_eq_run).trans (read_run execution _ positive.requests)
  let leftExact := (congrArg (godelOperationalProject execution) positive.leftRun.terminal_eq_run).trans
    (godelOperationalRunExact execution _ positive.requests)
  let rightExact := (congrArg (godelOperationalProject execution) positive.rightRun.terminal_eq_run).trans
    (godelOperationalRunExact execution _ positive.requests)
  let terminalEquality := leftExact.trans (positive.terminalCollision.trans rightExact.symm)
  let terminalReadEquality := (readExact positive.leftTerminal).trans
    ((congrArg reducedRead terminalEquality).trans (readExact positive.rightTerminal).symm)
  leftRead.symm.trans (terminalReadEquality.trans rightRead)
def rejectGodelTerminalReadExactToEmpty
    (reducedRead : GodelOperationalMemory execution → Type uP)
    (readExact : ∀ source, (godelClosureContract execution).read source =
      reducedRead (godelOperationalProject execution source)) : Empty :=
  execution.witness.unprovable (Eq.mp
    (godelTerminalReadExactToEndpointEquality execution reducedRead readExact) execution.witness.trueWitness)
variable {execution}
structure OperationalSameRegimeClosureAt
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {Memory : Type (max uA uC uP uV)} (realization : ExactRealization (godelClosureContract execution) Memory) where
  context : GodelClosureContextAt execution (godelPositiveExecutionCore execution)
    (godelOperationalH1 (godelPositiveExecutionCore execution))
  action : GodelSearchedCloseAction context
  authorization : GodelAuthorizedCloseAction action
  decomposition : GodelDecomposedCloseAction authorization
  executed : GodelExecutedCloseAction decomposition
  terminalCollision : executed.leftReducedTerminal realization = executed.rightReducedTerminal realization
namespace OperationalSameRegimeClosureAt
variable {Memory : Type (max uA uC uP uV)} {realization : ExactRealization (godelClosureContract execution) Memory}
def executedGrouping (closure : OperationalSameRegimeClosureAt execution realization) :
    ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution) := by
  change ExecutedCommonMemoryGrouping realization
    (initializeAt execution (godelPositiveExecutionCore execution) (godelOperationalH1 (godelPositiveExecutionCore execution)) .left)
    (initializeAt execution (godelPositiveExecutionCore execution) (godelOperationalH1 (godelPositiveExecutionCore execution)) .right)
  rw [← closure.context.leftSource_exact, ← closure.context.rightSource_exact]
  exact closure.executed.grouping closure.terminalCollision
theorem requests_exact (closure : OperationalSameRegimeClosureAt execution realization) :
    closure.executedGrouping.requests = [godelCloseRequest execution] := by
  rcases closure with ⟨⟨semantic, syntactic⟩, action, authorization, decomposition, executed, collision⟩
  cases semantic
  cases syntactic
  exact congrArg (fun request => [request]) action.selected
def producedMemory (closure : OperationalSameRegimeClosureAt execution realization) : Memory :=
  closure.executed.leftReducedTerminal realization
theorem rightProducesMemory (closure : OperationalSameRegimeClosureAt execution realization) :
    closure.executed.rightReducedTerminal realization = closure.producedMemory := closure.terminalCollision.symm
end OperationalSameRegimeClosureAt
def godelOperationalClosureOfTerminalCollision {Memory : Type (max uA uC uP uV)}
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (collision : Grouping.Continuation.run realization.reduced.next (realization.project (semanticSource execution))
          [godelCloseRequest execution] =
        Grouping.Continuation.run realization.reduced.next (realization.project (syntacticSource execution))
          [godelCloseRequest execution]) : OperationalSameRegimeClosureAt execution realization :=
  let context := godelReceivedClosureContext execution
  let action := godelSearchCloseAction context
  let authorization := godelAuthorizeCloseAction action
  let decomposition := godelDecomposeCloseAction authorization
  { context := context
    action := action
    authorization := authorization
    decomposition := decomposition
    executed := .execute
    terminalCollision := collision }
def godelOperationalClosureToEndpointEquality {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) :
    interpretation.Truth execution.witness.production.sentence = coding.Proof execution.witness.production.sentence :=
  godelExecutedGroupingToEndpointEquality execution closure.executedGrouping
def godelOperationalClosureToProducedCompleteness {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) :
    ExecutedGodelProducedCompleteness execution.witness :=
  fun truthWitness => Eq.mp (godelOperationalClosureToEndpointEquality closure) truthWitness
def rejectGodelOperationalClosureToEmpty {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) : Empty :=
  execution.witness.unprovable
    (godelOperationalClosureToProducedCompleteness closure execution.witness.trueWitness)
theorem rejectGodelOperationalClosure {Memory : Type (max uA uC uP uV)}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) : False :=
  Empty.elim (rejectGodelOperationalClosureToEmpty closure)
theorem godelExactRuntimeRejectsCommonTerminalMemory {Memory : Type (max uA uC uP uV)}
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (realization : ExactRealization (godelClosureContract execution) Memory) :
    Grouping.Continuation.run realization.reduced.next (realization.project (semanticSource execution))
        [godelCloseRequest execution] ≠
      Grouping.Continuation.run realization.reduced.next (realization.project (syntacticSource execution))
        [godelCloseRequest execution] := by
  intro collision
  exact Empty.elim (rejectGodelOperationalClosureToEmpty
    (godelOperationalClosureOfTerminalCollision execution realization collision))
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.godelOperationalRunExact
#print axioms StrongPerimetralTurning.GodelClosureSource.continueOccurrenceSplit
#print axioms StrongPerimetralTurning.GodelRuntimeHistory
#print axioms StrongPerimetralTurning.GodelRuntimeHistory.additionalDepth
#print axioms StrongPerimetralTurning.GodelRuntimeHistory.depth
#print axioms StrongPerimetralTurning.GodelRuntimeHistory.extend
#print axioms StrongPerimetralTurning.godelNextPhase
#print axioms StrongPerimetralTurning.godelNextHistory
#print axioms StrongPerimetralTurning.ClosurePole
#print axioms StrongPerimetralTurning.GodelRuntimePhase
#print axioms StrongPerimetralTurning.GodelClosureSource
#print axioms StrongPerimetralTurning.GodelClosureSource.history
#print axioms StrongPerimetralTurning.GodelClosureSource.depth
#print axioms StrongPerimetralTurning.GodelClosureSource.provenance
#print axioms StrongPerimetralTurning.GodelClosureSource.occurrences
#print axioms StrongPerimetralTurning.godelEndpointAt
#print axioms StrongPerimetralTurning.GodelRuntimeState
#print axioms StrongPerimetralTurning.initializeAt
#print axioms StrongPerimetralTurning.«initialize»
#print axioms StrongPerimetralTurning.semanticSource
#print axioms StrongPerimetralTurning.syntacticSource
#print axioms StrongPerimetralTurning.semanticSource_ne_syntacticSource
#print axioms StrongPerimetralTurning.GodelRuntimeRequest
#print axioms StrongPerimetralTurning.godelContinueRequest
#print axioms StrongPerimetralTurning.godelCloseRequest
#print axioms StrongPerimetralTurning.GodelRuntimeEvent
#print axioms StrongPerimetralTurning.GodelRuntimeRequest.eraseUniverse
#print axioms StrongPerimetralTurning.GodelOperationalAllow
#print axioms StrongPerimetralTurning.godelOperationalPermission
#print axioms StrongPerimetralTurning.GodelOperationalAllow.permission
#print axioms StrongPerimetralTurning.godelOperationalDecision
#print axioms StrongPerimetralTurning.GodelRuntimeAllow
#print axioms StrongPerimetralTurning.godelRuntimeDecision
#print axioms StrongPerimetralTurning.godelRuntimeNext
#print axioms StrongPerimetralTurning.godelRuntimeEvent
#print axioms StrongPerimetralTurning.godelClosureContract
#print axioms StrongPerimetralTurning.godelRuntimePerform
#print axioms StrongPerimetralTurning.godelRuntimeRun
#print axioms StrongPerimetralTurning.GodelReachableRuntime
#print axioms StrongPerimetralTurning.godelIdentityRealization
#print axioms StrongPerimetralTurning.GodelOperationalMemory
#print axioms StrongPerimetralTurning.godelOperationalProject
#print axioms StrongPerimetralTurning.GodelOperationalMemory.phase
#print axioms StrongPerimetralTurning.GodelOperationalMemory.additionalDepth
#print axioms StrongPerimetralTurning.GodelOperationalMemory.depth
#print axioms StrongPerimetralTurning.GodelOperationalMemory.activePole?
#print axioms StrongPerimetralTurning.godelOperationalNext
#print axioms StrongPerimetralTurning.godelOperationalEvent
#print axioms StrongPerimetralTurning.godelOperationalReducedContract
#print axioms StrongPerimetralTurning.GodelOperationalRealizationWithoutRead
#print axioms StrongPerimetralTurning.godelOperationalRealizationWithoutRead
#print axioms StrongPerimetralTurning.godelOperational_initial_memories_distinct
#print axioms StrongPerimetralTurning.godelRuntimeNext_pole
#print axioms StrongPerimetralTurning.pole_run
#print axioms StrongPerimetralTurning.read_run
#print axioms StrongPerimetralTurning.godel_read_semantic
#print axioms StrongPerimetralTurning.godel_read_syntactic
#print axioms StrongPerimetralTurning.GodelClosureSource.history_continue
#print axioms StrongPerimetralTurning.GodelClosureSource.history_close
#print axioms StrongPerimetralTurning.GodelClosureSource.provenance_continue
#print axioms StrongPerimetralTurning.GodelClosureSource.provenance_close
#print axioms StrongPerimetralTurning.initialize_history
#print axioms StrongPerimetralTurning.godelCloseAuthorized
#print axioms StrongPerimetralTurning.godelOpenCloseRun
#print axioms StrongPerimetralTurning.godelClose_changes_phase
#print axioms StrongPerimetralTurning.godelClose_not_identity
#print axioms StrongPerimetralTurning.godelTerminalNextStable
#print axioms StrongPerimetralTurning.godelTerminalNoAuthorization
#print axioms StrongPerimetralTurning.godelClosePreservesRead
#print axioms StrongPerimetralTurning.GodelOperationalGroupingWithoutRead
#print axioms StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.requests
#print axioms StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.nonempty
#print axioms StrongPerimetralTurning.godelOperationalGroupingWithoutRead
#print axioms StrongPerimetralTurning.godelOperationalGroupingWithoutRead_events_equal
#print axioms StrongPerimetralTurning.godelOpenContinueRun
#print axioms StrongPerimetralTurning.godelOpenRuntime
#print axioms StrongPerimetralTurning.godelIdentity_close_outputs_distinct
#print axioms StrongPerimetralTurning.godelExactRunExact
#print axioms StrongPerimetralTurning.godelExecutedGroupingProjectedTerminalsEqual
#print axioms StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality
#print axioms StrongPerimetralTurning.godelExecutedOperationalGroupingToProducedCompleteness
#print axioms StrongPerimetralTurning.rejectGodelExecutedOperationalGroupingToEmpty
#print axioms StrongPerimetralTurning.godelTerminalReadExactToEndpointEquality
#print axioms StrongPerimetralTurning.rejectGodelTerminalReadExactToEmpty
#print axioms StrongPerimetralTurning.GodelInitializedAt
#print axioms StrongPerimetralTurning.GodelInitializedAt.source
#print axioms StrongPerimetralTurning.GodelInitializedAt.source_exact
#print axioms StrongPerimetralTurning.GodelInitializedAt.source_history
#print axioms StrongPerimetralTurning.GodelClosureContextAt
#print axioms StrongPerimetralTurning.GodelClosureContextAt.leftSource
#print axioms StrongPerimetralTurning.GodelClosureContextAt.rightSource
#print axioms StrongPerimetralTurning.GodelClosureContextAt.request
#print axioms StrongPerimetralTurning.GodelClosureContextAt.leftSource_exact
#print axioms StrongPerimetralTurning.GodelClosureContextAt.rightSource_exact
#print axioms StrongPerimetralTurning.GodelClosureContextAt.sources_distinct
#print axioms StrongPerimetralTurning.GodelClosureContextAt.h1_shared
#print axioms StrongPerimetralTurning.godelReceivedClosureContext
#print axioms StrongPerimetralTurning.GodelSearchedCloseAction
#print axioms StrongPerimetralTurning.godelSearchCloseAction
#print axioms StrongPerimetralTurning.godelSearchedCloseAction_preservesHistory
#print axioms StrongPerimetralTurning.godelSearchedCloseAction_preservesProvenance
#print axioms StrongPerimetralTurning.GodelAuthorizedCloseAction
#print axioms StrongPerimetralTurning.godelAuthorizeCloseAction
#print axioms StrongPerimetralTurning.GodelDecomposedCloseAction
#print axioms StrongPerimetralTurning.godelDecomposeCloseAction
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction.leftRun
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction.rightRun
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction.leftReducedTerminal
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction.rightReducedTerminal
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction.requests_exact
#print axioms StrongPerimetralTurning.GodelExecutedCloseAction.grouping
#print axioms StrongPerimetralTurning.OperationalSameRegimeClosureAt
#print axioms StrongPerimetralTurning.OperationalSameRegimeClosureAt.executedGrouping
#print axioms StrongPerimetralTurning.OperationalSameRegimeClosureAt.requests_exact
#print axioms StrongPerimetralTurning.OperationalSameRegimeClosureAt.producedMemory
#print axioms StrongPerimetralTurning.OperationalSameRegimeClosureAt.rightProducesMemory
#print axioms StrongPerimetralTurning.godelOperationalClosureOfTerminalCollision
#print axioms StrongPerimetralTurning.godelOperationalClosureToEndpointEquality
#print axioms StrongPerimetralTurning.godelOperationalClosureToProducedCompleteness
#print axioms StrongPerimetralTurning.rejectGodelOperationalClosureToEmpty
#print axioms StrongPerimetralTurning.rejectGodelOperationalClosure
#print axioms StrongPerimetralTurning.godelExactRuntimeRejectsCommonTerminalMemory
/- AXIOM_AUDIT_END -/
