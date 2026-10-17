import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence
import RelationalPerimeter.Computation.ConstitutiveGeneration
import RelationalPerimeter.Constitution.Continuation.CommonMemoryGrouping

/-! A fixed positive runtime and a conditional obstruction to collision of its
two computed memory outputs. Historical certificates are kept outside the
direct readout kernel. No collision is produced by diagonalization itself. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.defProp false
namespace StrongPerimetralTurning
open ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures

inductive ClosurePole where
  | left
  | right
  deriving DecidableEq

def endpointAt (presentation : CircularPresentation) : ClosurePole → presentation.Endpoint
  | .left => presentation.leftEndpoint
  | .right => presentation.rightEndpoint

universe uA uB uC uP uV
variable {coding : GodelDiagonalSyntax.{uC,uA,uB,uP,uV}}
  {unprovabilityFormula : coding.UnaryFormula}
  {interpretation : GodelProvabilityInterpretation coding unprovabilityFormula}

structure GodelClosureSource
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) : Type where
  pole : ClosurePole
  depth : Nat

variable (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)

def godelEndpointAt : ClosurePole → Type uP
  | .left => interpretation.Truth execution.witness.production.sentence
  | .right => coding.Proof execution.witness.production.sentence

abbrev GodelRuntimeState := GodelClosureSource execution

def «initialize» (pole : ClosurePole) : GodelRuntimeState execution := ⟨pole, 1⟩
def semanticSource : GodelClosureSource execution := «initialize» execution .left
def syntacticSource : GodelClosureSource execution := «initialize» execution .right

theorem semanticSource_ne_syntacticSource : semanticSource execution ≠ syntacticSource execution := by
  intro same
  have roles := congrArg GodelClosureSource.pole same
  cases roles

inductive GodelRuntimeRequest where
  | continue
  | close
  deriving DecidableEq

def godelContinueRequest (_execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelRuntimeRequest := .continue
def godelCloseRequest (_execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelRuntimeRequest := .close

structure GodelRuntimeEvent where
  pole : ClosurePole
  beforeDepth : Nat
  request : GodelRuntimeRequest
  afterDepth : Nat

def godelRuntimeNext (source : GodelClosureSource execution) :
    GodelRuntimeRequest → GodelClosureSource execution
  | .continue => ⟨source.pole, source.depth + 1⟩
  | .close => source

def godelRuntimeEvent (source : GodelClosureSource execution) (request : GodelRuntimeRequest) :
    GodelRuntimeEvent :=
  ⟨source.pole, source.depth, request, (godelRuntimeNext execution source request).depth⟩

def GodelRuntimeAllow (source : GodelClosureSource execution) : GodelRuntimeRequest → Type
  | .continue => Unit
  | .close => PLift (source.depth = 1)

def godelRuntimeDecision (source : GodelClosureSource execution) (request : GodelRuntimeRequest) :
    PSum (GodelRuntimeAllow execution source request)
      (GodelRuntimeAllow execution source request → False) :=
  match request with
  | .continue => .inl ()
  | .close =>
      match decEq source.depth 1 with
      | .isTrue yes => .inl ⟨yes⟩
      | .isFalse no => .inr (fun witness => no witness.down)

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

theorem godelRuntimeNext_pole (source : GodelClosureSource execution) (request : GodelRuntimeRequest) :
    (godelRuntimeNext execution source request).pole = source.pole := by cases request <;> rfl

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

def godelCloseAuthorized (pole : ClosurePole) :
    (godelClosureContract execution).Allow («initialize» execution pole) (godelCloseRequest execution) :=
  ⟨rfl⟩

def godelOpenCloseRun (pole : ClosurePole) :
    ExecutedRun (godelClosureContract execution) («initialize» execution pole)
      [godelCloseRequest execution] («initialize» execution pole)
      [(godelClosureContract execution).event («initialize» execution pole) (godelCloseRequest execution)] :=
  .cons (godelRuntimePerform execution _ _ (godelCloseAuthorized execution pole)) (.nil _)

def godelOpenContinueRun (pole : ClosurePole) :
    ExecutedRun (godelClosureContract execution) («initialize» execution pole)
      [godelContinueRequest execution] (godelRuntimeNext execution («initialize» execution pole) .continue)
      [(godelClosureContract execution).event («initialize» execution pole) .continue] :=
  .cons (godelRuntimePerform execution («initialize» execution pole) .continue ()) (.nil _)

def godelOpenRuntime (pole : ClosurePole) : GodelReachableRuntime execution pole :=
  ⟨[godelContinueRequest execution], _, _, godelOpenContinueRun execution pole⟩

theorem godelIdentity_close_outputs_distinct :
    Grouping.Continuation.run (godelIdentityRealization execution).reduced.next
        ((godelIdentityRealization execution).project (semanticSource execution)) [godelCloseRequest execution] ≠
      Grouping.Continuation.run (godelIdentityRealization execution).reduced.next
        ((godelIdentityRealization execution).project (syntacticSource execution)) [godelCloseRequest execution] :=
  semanticSource_ne_syntacticSource execution

/-- The critical kernel uses executed terminals, run exactness, two read laws,
and independently proved role stability. It does not inspect historical data. -/
def godelExecutedGroupingToEndpointEquality {Memory : Type}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (grouping : ExecutedCommonMemoryGrouping realization
      (semanticSource execution) (syntacticSource execution)) :
    interpretation.Truth execution.witness.production.sentence =
      coding.Proof execution.witness.production.sentence :=
  let leftRead := (congrArg (godelClosureContract execution).read
    grouping.leftRun.terminal_eq_run).trans (read_run execution _ grouping.requests)
  let rightRead := (congrArg (godelClosureContract execution).read
    grouping.rightRun.terminal_eq_run).trans (read_run execution _ grouping.requests)
  leftRead.symm.trans (grouping.terminalReadEqual.trans rightRead)

/- The following accessors and policy layers carry the historical certificate.
They are deliberately not dependencies of the preceding kernel. -/
namespace GodelClosureSource
variable {execution}

def history (source : GodelClosureSource execution) :=
  ConstitutiveGeneration.iteratedHistory (godelPerimetralPresentation execution) source.depth
def endpoint (source : GodelClosureSource execution) := source.history.endpoint
def difference (source : GodelClosureSource execution) := boundaryDifferenceReadout source.endpoint.2.2
def provenance (source : GodelClosureSource execution) := source.history.terminalClosureObstruction.provenance
abbrev occurrences (source : GodelClosureSource execution) := History.Occurrence source.history.history

theorem provenance_is_initial (source : GodelClosureSource execution) :
    source.provenance = (godelPerimetralPresentation execution).initialNode.provenance :=
  congrArg PositiveClosureObstruction.provenance source.history.terminalClosureObstruction_is_initial

theorem history_continue (source : GodelClosureSource execution) :
    (godelRuntimeNext execution source .continue).history =
      appendGenerated source.history (generate source.history.endpoint) := rfl

theorem history_close (source : GodelClosureSource execution) :
    (godelRuntimeNext execution source .close).history = source.history := rfl

theorem provenance_continue (source : GodelClosureSource execution) :
    (godelRuntimeNext execution source .continue).provenance = source.provenance :=
  congrArg PositiveClosureObstruction.provenance
    ((godelRuntimeNext execution source .continue).history.terminalClosureObstruction_is_initial.trans
      source.history.terminalClosureObstruction_is_initial.symm)

def continueOccurrenceSplit (source : GodelClosureSource execution) :
    ExactTypeTransport (source.occurrences ⊕ Unit)
      (godelRuntimeNext execution source .continue).occurrences :=
  ConstitutiveGeneration.successorOccurrenceSplit _ source.depth
end GodelClosureSource

theorem initialize_history (pole : ClosurePole) :
    («initialize» execution pole).history = godelPerimetralContinuation execution :=
  ConstitutiveGeneration.iteratedHistory_one _

theorem godelEndpointAt_matches_perimeter (pole : ClosurePole) :
    godelEndpointAt execution pole = endpointAt (godelPerimetralPresentation execution) pole := by
  cases pole <;> rfl

/-- Initialization is available at the produced continuation, not at an
arbitrary history. Every downstream layer is indexed by these received data. -/
inductive GodelInitializedAt :
    RootedGeneratedHistory (godelPerimetralPresentation execution) → ClosurePole → Type _ where
  | fromContinuation (affirmative : GodelAffirmativeConstitution execution) (pole : ClosurePole) :
      GodelInitializedAt (godelPerimetralContinuation execution) pole

namespace GodelInitializedAt
variable {execution} {history : RootedGeneratedHistory (godelPerimetralPresentation execution)}
  {pole : ClosurePole}
def source (initialized : GodelInitializedAt execution history pole) : GodelClosureSource execution :=
  match initialized with
  | .fromContinuation _ pole => «initialize» execution pole
theorem source_exact (initialized : GodelInitializedAt execution history pole) :
    initialized.source = «initialize» execution pole := by cases initialized; rfl
theorem source_history (initialized : GodelInitializedAt execution history pole) :
    initialized.source.history = history := by
  cases initialized
  exact initialize_history execution _
end GodelInitializedAt

structure GodelClosureContextAt
    (history : RootedGeneratedHistory (godelPerimetralPresentation execution)) where
  semantic : GodelInitializedAt execution history .left
  syntactic : GodelInitializedAt execution history .right

namespace GodelClosureContextAt
variable {execution} {history : RootedGeneratedHistory (godelPerimetralPresentation execution)}
def leftSource (context : GodelClosureContextAt execution history) := context.semantic.source
def rightSource (context : GodelClosureContextAt execution history) := context.syntactic.source
def request (_context : GodelClosureContextAt execution history) := godelCloseRequest execution
theorem leftSource_exact (context : GodelClosureContextAt execution history) :
    context.leftSource = semanticSource execution := context.semantic.source_exact
theorem rightSource_exact (context : GodelClosureContextAt execution history) :
    context.rightSource = syntacticSource execution := context.syntactic.source_exact
theorem sources_distinct (context : GodelClosureContextAt execution history) :
    context.leftSource ≠ context.rightSource := by
  rw [context.leftSource_exact, context.rightSource_exact]
  exact semanticSource_ne_syntacticSource execution
end GodelClosureContextAt

def godelReceivedClosureContext :
    GodelClosureContextAt execution (godelPerimetralContinuation execution) :=
  let affirmative := godelAffirmativeConstitution execution
  ⟨.fromContinuation affirmative .left, .fromContinuation affirmative .right⟩

variable {execution}
variable {history : RootedGeneratedHistory (godelPerimetralPresentation execution)}

structure GodelSearchedCloseAction (context : GodelClosureContextAt execution history) where
  request : GodelRuntimeRequest
  selected : request = context.request

def godelSearchCloseAction (context : GodelClosureContextAt execution history) :
    GodelSearchedCloseAction context := ⟨context.request, rfl⟩

/-- Preservation is a law of the selected action, separate from its data. -/
theorem godelSearchedCloseAction_preservesHistory {context : GodelClosureContextAt execution history}
    (action : GodelSearchedCloseAction context) :
    (godelRuntimeNext execution context.leftSource action.request).history = history ∧
      (godelRuntimeNext execution context.rightSource action.request).history = history := by
  rw [action.selected]
  exact ⟨context.semantic.source_history, context.syntactic.source_history⟩

theorem godelSearchedCloseAction_preservesProvenance {context : GodelClosureContextAt execution history}
    (action : GodelSearchedCloseAction context) :
    (godelRuntimeNext execution context.leftSource action.request).provenance = context.leftSource.provenance ∧
      (godelRuntimeNext execution context.rightSource action.request).provenance = context.rightSource.provenance := by
  rw [action.selected]
  exact ⟨rfl, rfl⟩

structure GodelAuthorizedCloseAction {context : GodelClosureContextAt execution history}
    (action : GodelSearchedCloseAction context) where
  left : (godelClosureContract execution).Allow context.leftSource action.request
  right : (godelClosureContract execution).Allow context.rightSource action.request

def godelAuthorizeCloseAction {context : GodelClosureContextAt execution history}
    (action : GodelSearchedCloseAction context) : GodelAuthorizedCloseAction action := by
  constructor
  · rw [action.selected, context.leftSource_exact]
    exact godelCloseAuthorized execution .left
  · rw [action.selected, context.rightSource_exact]
    exact godelCloseAuthorized execution .right

structure GodelDecomposedCloseAction {context : GodelClosureContextAt execution history}
    {action : GodelSearchedCloseAction context} (authorization : GodelAuthorizedCloseAction action) where
  leftStep : ExecutedStep (godelClosureContract execution) context.leftSource action.request
  rightStep : ExecutedStep (godelClosureContract execution) context.rightSource action.request
  leftAuthorizationExact : leftStep.authorized = authorization.left
  rightAuthorizationExact : rightStep.authorized = authorization.right

def godelDecomposeCloseAction {context : GodelClosureContextAt execution history}
    {action : GodelSearchedCloseAction context} (authorization : GodelAuthorizedCloseAction action) :
    GodelDecomposedCloseAction authorization :=
  ⟨godelRuntimePerform execution _ _ authorization.left,
    godelRuntimePerform execution _ _ authorization.right, rfl, rfl⟩

/-- This constructor executes the decomposition; no terminal or run is an
input. Its two runs below are built by the authorized cons constructor. -/
inductive GodelExecutedCloseAction {context : GodelClosureContextAt execution history}
    {action : GodelSearchedCloseAction context} {authorization : GodelAuthorizedCloseAction action}
    (decomposition : GodelDecomposedCloseAction authorization) : Type where
  | execute

namespace GodelExecutedCloseAction
variable {context : GodelClosureContextAt execution history}
  {action : GodelSearchedCloseAction context} {authorization : GodelAuthorizedCloseAction action}
  {decomposition : GodelDecomposedCloseAction authorization}

def leftRun (_executed : GodelExecutedCloseAction decomposition) :
    ExecutedRun (godelClosureContract execution) context.leftSource [action.request]
      decomposition.leftStep.target [decomposition.leftStep.producedEvent] :=
  .cons decomposition.leftStep (.nil _)
def rightRun (_executed : GodelExecutedCloseAction decomposition) :
    ExecutedRun (godelClosureContract execution) context.rightSource [action.request]
      decomposition.rightStep.target [decomposition.rightStep.producedEvent] :=
  .cons decomposition.rightStep (.nil _)

def leftReducedTerminal {Memory : Type}
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (_executed : GodelExecutedCloseAction decomposition) :=
  Grouping.Continuation.run realization.reduced.next (realization.project context.leftSource) [action.request]
def rightReducedTerminal {Memory : Type}
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (_executed : GodelExecutedCloseAction decomposition) :=
  Grouping.Continuation.run realization.reduced.next (realization.project context.rightSource) [action.request]

theorem requests_exact (_executed : GodelExecutedCloseAction decomposition) :
    [action.request] = [godelCloseRequest execution] := congrArg (fun request => [request]) action.selected

def grouping {Memory : Type} {realization : ExactRealization (godelClosureContract execution) Memory}
    (executed : GodelExecutedCloseAction decomposition)
    (collision : executed.leftReducedTerminal realization = executed.rightReducedTerminal realization) :
    ExecutedCommonMemoryGrouping realization context.leftSource context.rightSource where
  requests := [action.request]
  nonempty := by intro impossible; cases impossible
  leftTerminal := decomposition.leftStep.target
  leftEvents := [decomposition.leftStep.producedEvent]
  leftRun := executed.leftRun
  rightTerminal := decomposition.rightStep.target
  rightEvents := [decomposition.rightStep.producedEvent]
  rightRun := executed.rightRun
  terminalCollision := collision
end GodelExecutedCloseAction

/-- The fixed execution, contract, realization, and H1 are parameters. Only
the collision adds a closure specification to the already executable action. -/
structure OperationalSameRegimeClosureAt
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {Memory : Type} (realization : ExactRealization (godelClosureContract execution) Memory) where
  context : GodelClosureContextAt execution (godelPerimetralContinuation execution)
  action : GodelSearchedCloseAction context
  authorization : GodelAuthorizedCloseAction action
  decomposition : GodelDecomposedCloseAction authorization
  executed : GodelExecutedCloseAction decomposition
  terminalCollision : executed.leftReducedTerminal realization = executed.rightReducedTerminal realization

namespace OperationalSameRegimeClosureAt
variable {Memory : Type} {realization : ExactRealization (godelClosureContract execution) Memory}

def executedGrouping (closure : OperationalSameRegimeClosureAt execution realization) :
    ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution) := by
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

/-- All policy layers are positively constructed. Terminal collision is the
only additional premise required to turn this action into the rejected closure. -/
def godelOperationalClosureOfTerminalCollision {Memory : Type}
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (realization : ExactRealization (godelClosureContract execution) Memory)
    (collision :
      Grouping.Continuation.run realization.reduced.next (realization.project (semanticSource execution))
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

def godelOperationalClosureToEndpointEquality {Memory : Type}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) :
    interpretation.Truth execution.witness.production.sentence = coding.Proof execution.witness.production.sentence :=
  godelExecutedGroupingToEndpointEquality execution closure.executedGrouping

def godelOperationalClosureToProducedCompleteness {Memory : Type}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) :
    ExecutedGodelProducedCompleteness execution.witness :=
  fun truthWitness => Eq.mp (godelOperationalClosureToEndpointEquality closure) truthWitness

def rejectGodelOperationalClosureToEmpty {Memory : Type}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) : Empty :=
  execution.witness.unprovable
    (godelOperationalClosureToProducedCompleteness closure execution.witness.trueWitness)

theorem rejectGodelOperationalClosure {Memory : Type}
    {realization : ExactRealization (godelClosureContract execution) Memory}
    (closure : OperationalSameRegimeClosureAt execution realization) : False :=
  Empty.elim (rejectGodelOperationalClosureToEmpty closure)

/-- Universal separation for the fixed contract and its nonempty close run. -/
theorem godelExactRuntimeRejectsCommonTerminalMemory {Memory : Type}
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (realization : ExactRealization (godelClosureContract execution) Memory) :
    Grouping.Continuation.run realization.reduced.next (realization.project (semanticSource execution))
        [godelCloseRequest execution] ≠
      Grouping.Continuation.run realization.reduced.next (realization.project (syntacticSource execution))
        [godelCloseRequest execution] := by
  intro collision
  let grouping : ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution) :=
    ⟨[godelCloseRequest execution], (by intro impossible; cases impossible), _, _, godelOpenCloseRun execution .left,
      _, _, godelOpenCloseRun execution .right, collision⟩
  let equality := godelExecutedGroupingToEndpointEquality execution grouping
  exact Empty.elim (execution.witness.unprovable (Eq.mp equality execution.witness.trueWitness))

end StrongPerimetralTurning
/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.ClosurePole
#print axioms StrongPerimetralTurning.endpointAt
#print axioms StrongPerimetralTurning.GodelClosureSource
#print axioms StrongPerimetralTurning.godelEndpointAt
#print axioms StrongPerimetralTurning.GodelRuntimeState
#print axioms StrongPerimetralTurning.«initialize»
#print axioms StrongPerimetralTurning.semanticSource
#print axioms StrongPerimetralTurning.syntacticSource
#print axioms StrongPerimetralTurning.semanticSource_ne_syntacticSource
#print axioms StrongPerimetralTurning.GodelRuntimeRequest
#print axioms StrongPerimetralTurning.godelContinueRequest
#print axioms StrongPerimetralTurning.godelCloseRequest
#print axioms StrongPerimetralTurning.GodelRuntimeEvent
#print axioms StrongPerimetralTurning.godelRuntimeNext
#print axioms StrongPerimetralTurning.godelRuntimeEvent
#print axioms StrongPerimetralTurning.GodelRuntimeAllow
#print axioms StrongPerimetralTurning.godelRuntimeDecision
#print axioms StrongPerimetralTurning.godelClosureContract
#print axioms StrongPerimetralTurning.godelRuntimePerform
#print axioms StrongPerimetralTurning.godelRuntimeRun
#print axioms StrongPerimetralTurning.GodelReachableRuntime
#print axioms StrongPerimetralTurning.godelIdentityRealization
#print axioms StrongPerimetralTurning.godelRuntimeNext_pole
#print axioms StrongPerimetralTurning.pole_run
#print axioms StrongPerimetralTurning.read_run
#print axioms StrongPerimetralTurning.godel_read_semantic
#print axioms StrongPerimetralTurning.godel_read_syntactic
#print axioms StrongPerimetralTurning.godelCloseAuthorized
#print axioms StrongPerimetralTurning.godelOpenCloseRun
#print axioms StrongPerimetralTurning.godelOpenContinueRun
#print axioms StrongPerimetralTurning.godelOpenRuntime
#print axioms StrongPerimetralTurning.godelIdentity_close_outputs_distinct
#print axioms StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality
#print axioms StrongPerimetralTurning.GodelClosureSource.history
#print axioms StrongPerimetralTurning.GodelClosureSource.endpoint
#print axioms StrongPerimetralTurning.GodelClosureSource.difference
#print axioms StrongPerimetralTurning.GodelClosureSource.provenance
#print axioms StrongPerimetralTurning.GodelClosureSource.occurrences
#print axioms StrongPerimetralTurning.GodelClosureSource.provenance_is_initial
#print axioms StrongPerimetralTurning.GodelClosureSource.history_continue
#print axioms StrongPerimetralTurning.GodelClosureSource.history_close
#print axioms StrongPerimetralTurning.GodelClosureSource.provenance_continue
#print axioms StrongPerimetralTurning.GodelClosureSource.continueOccurrenceSplit
#print axioms StrongPerimetralTurning.initialize_history
#print axioms StrongPerimetralTurning.godelEndpointAt_matches_perimeter
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
