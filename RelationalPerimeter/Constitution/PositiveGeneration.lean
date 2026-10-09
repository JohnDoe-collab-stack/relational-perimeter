import RelationalPerimeter.Constitution.ClosingBoundary

set_option linter.checkUnivs false

/-!
# Positive formation and deployment

The formation receives primitive sorts, states, witnessed nodes and admissible
steps with their compatibility readout. It need not provide a step at every state,
or determine a unique successor. Finite histories retain the full step data;
their spines retain the nodes and selected compatibility readouts, not an inverse
of arbitrary step payloads. Closing a positive history requires a separate witness.
-/

namespace StrongPerimetralTurning

universe uE uI uK uD uP

structure SuccessiveLink
    (Explicit : Type uE) (Implicit : Type uI)
    (Compatible : Implicit → Explicit → Type uK)
    (Difference : Type uD) (Provenance : Difference → Type uP) where
  source : LocalNode Explicit Implicit Compatible Difference Provenance
  target : LocalNode Explicit Implicit Compatible Difference Provenance
  compatibility : Compatible source.implicit target.explicit

namespace PerimeterSpine

variable {Explicit : Type uE} {Implicit : Type uI}
  {Compatible : Implicit → Explicit → Type uK}
  {Difference : Type uD} {Provenance : Difference → Type uP}

def append {node : LocalNode Explicit Implicit Compatible Difference Provenance} :
    (first : PerimeterSpine Compatible node) →
    PerimeterSpine Compatible first.finalNode → PerimeterSpine Compatible node
  | .boundary _, second => second
  | .advance witness tail, second => .advance witness (append tail second)

def appendAlong
    {node endpoint : LocalNode Explicit Implicit Compatible Difference Provenance}
    (first : PerimeterSpine Compatible node) (terminalExact : first.finalNode = endpoint)
    (second : PerimeterSpine Compatible endpoint) : PerimeterSpine Compatible node :=
  first.append (terminalExact.symm ▸ second)

theorem append_finalNode
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    (first : PerimeterSpine Compatible node)
    (second : PerimeterSpine Compatible first.finalNode) :
    (first.append second).finalNode = second.finalNode := by
  induction first with
  | boundary => rfl
  | advance witness tail inductionHypothesis => exact inductionHypothesis second

def linkAt {node : LocalNode Explicit Implicit Compatible Difference Provenance} :
    (spine : PerimeterSpine Compatible node) → NonClosingPosition spine →
      SuccessiveLink Explicit Implicit Compatible Difference Provenance
  | .boundary _, position => nomatch position
  | .advance witness tail, .here => ⟨node, tail.startNode, witness⟩
  | .advance _ tail, .later position => tail.linkAt position

end PerimeterSpine
end StrongPerimetralTurning

namespace RelationalPerimeter.Constitution

open StrongPerimetralTurning

universe uE uI uK uD uP uS uStep

structure PositiveFormation where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP
  State : Type uS
  node : State → LocalNode Explicit Implicit Compatible Difference Provenance
  Step : State → State → Type uStep
  compatibility : {source target : State} → Step source target →
    Compatible (node source).implicit (node target).explicit

namespace PositiveFormation

def link (F : PositiveFormation) {source target : F.State} (step : F.Step source target) :
    SuccessiveLink F.Explicit F.Implicit F.Compatible F.Difference F.Provenance :=
  ⟨F.node source, F.node target, F.compatibility step⟩

end PositiveFormation

inductive PositiveHistory (F : PositiveFormation) : F.State → F.State → Type _
  | nil {state : F.State} : PositiveHistory F state state
  | cons {source middle target : F.State} (step : F.Step source middle)
      (tail : PositiveHistory F middle target) : PositiveHistory F source target

namespace PositiveHistory

variable {F : PositiveFormation}

def append {source middle target : F.State} :
    PositiveHistory F source middle → PositiveHistory F middle target →
      PositiveHistory F source target
  | .nil, second => second
  | .cons step tail, second => .cons step (tail.append second)

theorem nil_append {source target : F.State} (history : PositiveHistory F source target) :
    (PositiveHistory.nil : PositiveHistory F source source).append history = history := rfl

theorem append_nil {source target : F.State} (history : PositiveHistory F source target) :
    history.append .nil = history := by
  induction history with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons step) inductionHypothesis

theorem append_associative {a b c d : F.State} (first : PositiveHistory F a b)
    (second : PositiveHistory F b c) (third : PositiveHistory F c d) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons step) (inductionHypothesis second)

def deploy {source target : F.State} :
    PositiveHistory F source target → PerimeterSpine F.Compatible (F.node source)
  | .nil => .boundary (F.node source)
  | .cons step tail => .advance (F.compatibility step) tail.deploy

theorem deploy_start {source target : F.State} (history : PositiveHistory F source target) :
    history.deploy.startNode = F.node source := rfl

theorem deploy_final {source target : F.State} (history : PositiveHistory F source target) :
    history.deploy.finalNode = F.node target := by
  induction history with
  | nil => rfl
  | cons step tail inductionHypothesis => exact inductionHypothesis

theorem deploy_append {a b c : F.State} (first : PositiveHistory F a b)
    (second : PositiveHistory F b c) :
    (first.append second).deploy =
      first.deploy.appendAlong first.deploy_final second.deploy := by
  induction first with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PerimeterSpine.advance (F.compatibility step)) (inductionHypothesis second)

inductive Occurrence : {source target : F.State} → PositiveHistory F source target → Type _
  | here {source middle target : F.State} {step : F.Step source middle}
      {tail : PositiveHistory F middle target} : Occurrence (.cons step tail)
  | later {source middle target : F.State} {step : F.Step source middle}
      {tail : PositiveHistory F middle target} : Occurrence tail → Occurrence (.cons step tail)

theorem nil_noOccurrence (state : F.State) :
    Occurrence (.nil : PositiveHistory F state state) → False := fun occurrence => nomatch occurrence

theorem here_ne_later {a b c : F.State} {step : F.Step a b}
    {tail : PositiveHistory F b c} (occurrence : Occurrence tail) :
    (Occurrence.here : Occurrence (.cons step tail)) ≠ .later occurrence := by
  intro equality
  cases equality

def toPosition {source target : F.State} : (history : PositiveHistory F source target) →
    Occurrence history → NonClosingPosition history.deploy
  | .nil, occurrence => nomatch occurrence
  | .cons _ _, .here => .here
  | .cons _ tail, .later occurrence => .later (tail.toPosition occurrence)

def fromPosition {source target : F.State} : (history : PositiveHistory F source target) →
    NonClosingPosition history.deploy → Occurrence history
  | .nil => fun position => nomatch position
  | .cons step tail => fun position =>
      match position with
      | .here => Occurrence.here (step := step) (tail := tail)
      | .later position => Occurrence.later (step := step) (tail.fromPosition position)

theorem position_occurrence_return {source target : F.State}
    (history : PositiveHistory F source target) (occurrence : Occurrence history) :
    history.fromPosition (history.toPosition occurrence) = occurrence := by
  induction occurrence with
  | here => rfl
  | later occurrence inductionHypothesis =>
      exact congrArg Occurrence.later inductionHypothesis

theorem occurrence_position_return {source target : F.State}
    (history : PositiveHistory F source target) (position : NonClosingPosition history.deploy) :
    history.toPosition (history.fromPosition position) = position := by
  induction history with
  | nil => cases position
  | cons step tail inductionHypothesis =>
      cases position with
      | here => rfl
      | later position =>
          exact congrArg NonClosingPosition.later (inductionHypothesis position)

def positionTransport {source target : F.State} (history : PositiveHistory F source target) :
    ExactTypeTransport (Occurrence history) (NonClosingPosition history.deploy) :=
  { forward := history.toPosition
    backward := history.fromPosition
    forwardBackward := history.position_occurrence_return
    backwardForward := history.occurrence_position_return }

def linkAt {source target : F.State} : (history : PositiveHistory F source target) →
    Occurrence history → SuccessiveLink F.Explicit F.Implicit F.Compatible F.Difference F.Provenance
  | .nil, occurrence => nomatch occurrence
  | .cons step _, .here => F.link step
  | .cons _ tail, .later occurrence => tail.linkAt occurrence

theorem deploy_link_exact {source target : F.State} (history : PositiveHistory F source target)
    (occurrence : Occurrence history) :
    history.deploy.linkAt (history.toPosition occurrence) = history.linkAt occurrence := by
  induction occurrence with
  | here => rfl
  | later occurrence inductionHypothesis => exact inductionHypothesis

def boundaryShape {source target : F.State} (history : PositiveHistory F source target) :
    ClosingBoundaryShape :=
  { Explicit := F.Explicit
    Implicit := F.Implicit
    Compatible := F.Compatible
    source := history.deploy.finalNode.implicit
    target := (F.node source).explicit
    Difference := F.Difference
    Provenance := F.Provenance
    difference := (F.node source).difference
    provenance := (F.node source).provenance }

theorem boundary_source_exact {source target : F.State}
    (history : PositiveHistory F source target) :
    history.boundaryShape.source = (F.node target).implicit :=
  congrArg LocalNode.implicit history.deploy_final

def toCircular {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    PositiveCircularPresentation :=
  { Explicit := F.Explicit
    Implicit := F.Implicit
    Compatible := F.Compatible
    Difference := F.Difference
    Provenance := F.Provenance
    initialNode := F.node source
    perimeter := history.deploy
    perimeterPositive := history.toPosition positive
    finalJunction := junction }

theorem toCircular_initial {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.toCircular positive junction).initialNode = F.node source := rfl

theorem toCircular_deployment {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.toCircular positive junction).perimeter = history.deploy := rfl

theorem toCircular_junction {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.toCircular positive junction).finalJunction = junction := rfl

theorem toCircular_boundary {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    closingBoundary (history.toCircular positive junction) =
      (history.boundaryShape.point junction).toConstitutiveBoundary := rfl

end PositiveHistory

/- A globally chosen continuation is additional data. Not every formation has one. -/
structure ChosenPositiveContinuation (F : PositiveFormation) where
  successor : F.State → F.State
  step : (state : F.State) → F.Step state (successor state)

namespace ChosenPositiveContinuation

def walk {F : PositiveFormation} (choice : ChosenPositiveContinuation F)
    (source : F.State) : Nat → Σ target : F.State, PositiveHistory F source target
  | 0 => ⟨source, .nil⟩
  | count + 1 =>
      let tail := choice.walk (choice.successor source) count
      ⟨tail.1, .cons (choice.step source) tail.2⟩

def walk_successor_positive {F : PositiveFormation} (choice : ChosenPositiveContinuation F)
    (source : F.State) (count : Nat) :
    PositiveHistory.Occurrence (choice.walk source (count + 1)).2 := .here

end ChosenPositiveContinuation
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.SuccessiveLink
#print axioms StrongPerimetralTurning.PerimeterSpine.append
#print axioms StrongPerimetralTurning.PerimeterSpine.appendAlong
#print axioms StrongPerimetralTurning.PerimeterSpine.append_finalNode
#print axioms StrongPerimetralTurning.PerimeterSpine.linkAt
#print axioms RelationalPerimeter.Constitution.PositiveFormation
#print axioms RelationalPerimeter.Constitution.PositiveFormation.link
#print axioms RelationalPerimeter.Constitution.PositiveHistory
#print axioms RelationalPerimeter.Constitution.PositiveHistory.append
#print axioms RelationalPerimeter.Constitution.PositiveHistory.nil_append
#print axioms RelationalPerimeter.Constitution.PositiveHistory.append_nil
#print axioms RelationalPerimeter.Constitution.PositiveHistory.append_associative
#print axioms RelationalPerimeter.Constitution.PositiveHistory.deploy
#print axioms RelationalPerimeter.Constitution.PositiveHistory.deploy_start
#print axioms RelationalPerimeter.Constitution.PositiveHistory.deploy_final
#print axioms RelationalPerimeter.Constitution.PositiveHistory.deploy_append
#print axioms RelationalPerimeter.Constitution.PositiveHistory.Occurrence
#print axioms RelationalPerimeter.Constitution.PositiveHistory.nil_noOccurrence
#print axioms RelationalPerimeter.Constitution.PositiveHistory.here_ne_later
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toPosition
#print axioms RelationalPerimeter.Constitution.PositiveHistory.fromPosition
#print axioms RelationalPerimeter.Constitution.PositiveHistory.position_occurrence_return
#print axioms RelationalPerimeter.Constitution.PositiveHistory.occurrence_position_return
#print axioms RelationalPerimeter.Constitution.PositiveHistory.positionTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.linkAt
#print axioms RelationalPerimeter.Constitution.PositiveHistory.deploy_link_exact
#print axioms RelationalPerimeter.Constitution.PositiveHistory.boundaryShape
#print axioms RelationalPerimeter.Constitution.PositiveHistory.boundary_source_exact
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toCircular
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toCircular_initial
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toCircular_deployment
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toCircular_junction
#print axioms RelationalPerimeter.Constitution.PositiveHistory.toCircular_boundary
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk_successor_positive
/- AXIOM_AUDIT_END -/
