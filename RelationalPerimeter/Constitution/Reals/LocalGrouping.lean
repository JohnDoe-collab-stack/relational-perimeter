import RelationalPerimeter.Constitution.Grouping.ExactImage
import RelationalPerimeter.Constitution.Grouping.ContinuationContract
import RelationalPerimeter.Constitution.Reals.Precision

set_option autoImplicit false
set_option genInjectivity false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.defProp false
set_option linter.constructorNameAsVariable false

/-!
# Local grouping of executed approximation resources

A local grouping specification retains every source identity and its dyadic
code, supplies one target code, and carries the positive proximity witness for
each source.  Its rules have one effective step from each source state to the
common target state.  Thus normal forms share a finite image while distinct
source states are never identified.

The associated acceptance action consumes the source charge and returns the
exact target code.  The action and the proof that it preserves the accepted
code contract are separate fields, as required by the generic grouping
interface.  The proximity witness remains positive data of the specification.
-/

namespace RelationalPerimeter.Constitution.Reals
namespace LocalGrouping

open ConstitutiveSearch.Grouping

universe uSource

/-- Positive data for grouping source resources around one finite target. -/
structure Specification where
  Source : Type uSource
  precision : Nat
  sourceCode : Source -> SignedDyadicCode
  targetCode : SignedDyadicCode
  sourceNearTarget : (source : Source) ->
    Near precision (sourceCode source) targetCode

/-- Source states retain their identities; the target is a separate state. -/
inductive State (specification : Specification.{uSource}) : Type uSource
  | source (identity : specification.Source)
  | target

/-- The only local operation groups one retained source into the target. -/
inductive Step (specification : Specification.{uSource}) :
    State specification -> State specification -> Type uSource
  | group (identity : specification.Source) :
      Step specification (.source identity) .target

def rank
    {specification : Specification.{uSource}} :
    State specification -> Nat
  | .source _ => 1
  | .target => 0

def choices
    {specification : Specification.{uSource}} :
    (state : State specification) ->
      List ((target : State specification) ×
        Step specification state target)
  | .source identity => [⟨.target, .group identity⟩]
  | .target => []

def locate
    {specification : Specification.{uSource}}
    {source target : State specification}
    (step : Step specification source target) :
    {entry : (next : State specification) ×
        Step specification source next //
      entry ∈ choices source ∧
        HEq entry
          (⟨target, step⟩ :
            (next : State specification) ×
              Step specification source next)} := by
  cases step with
  | group identity =>
      exact ⟨⟨.target, .group identity⟩, List.Mem.head _, HEq.rfl⟩

theorem decreases
    {specification : Specification.{uSource}}
    {source target : State specification}
    (step : Step specification source target) :
    rank target < rank source := by
  cases step
  exact Nat.zero_lt_succ 0

def diamond
    {specification : Specification.{uSource}}
    {source left right : State specification}
    (first : Step specification source left)
    (second : Step specification source right) :
    Join (Step specification) left right := by
  cases first with
  | group identity =>
      cases second
      exact ⟨.target, .nil _, .nil _⟩

/-- Effective, terminating and confluent local grouping rules. -/
def rules (specification : Specification.{uSource}) : Rules.{uSource} :=
  { State := State specification
    Step := Step specification
    rank := rank
    choices := choices
    locate := locate
    decreases := decreases
    diamond := diamond }

theorem target_terminal
    (specification : Specification.{uSource}) :
    (rules specification).Terminal State.target :=
  (rules specification).zero_terminal State.target rfl

theorem normal_target
    (specification : Specification.{uSource}) :
    (rules specification).normal State.target = State.target :=
  (rules specification).normal_terminal _
    (target_terminal specification)

theorem normal_source
    (specification : Specification.{uSource})
    (identity : specification.Source) :
    (rules specification).normal (State.source identity) = State.target :=
  ((rules specification).normal_trace
    (Trace.one (Step.group identity))).trans
      (normal_target specification)

/-- Every source is carried to the exact same finite-image target. -/
theorem carry_source_eq_target
    (specification : Specification.{uSource})
    (identity : specification.Source) :
    FiniteImage.carry (rules specification) (State.source identity) =
      FiniteImage.carry (rules specification) State.target := by
  apply Subtype.ext
  exact (normal_source specification identity).trans
    (normal_target specification).symm

/-- Distinct sources remain distinct before grouping. -/
theorem source_ne_source
    (specification : Specification.{uSource})
    {first second : specification.Source}
    (distinct : first ≠ second) :
    State.source first ≠ State.source second := by
  intro equality
  cases equality
  exact distinct rfl

/--
Different retained sources may have the same exact finite-image target without
becoming equal source states.
-/
structure SharedTargetWithoutSourceIdentification
    (specification : Specification.{uSource})
    (first second : specification.Source) where
  sourceDistinct : State.source first ≠ State.source second
  carriedTogether :
    FiniteImage.carry (rules specification) (State.source first) =
      FiniteImage.carry (rules specification) (State.source second)

def sharedTargetWithoutSourceIdentification
    (specification : Specification.{uSource})
    {first second : specification.Source}
    (distinct : first ≠ second) :
    SharedTargetWithoutSourceIdentification specification first second :=
  { sourceDistinct := source_ne_source specification distinct
    carriedTogether :=
      (carry_source_eq_target specification first).trans
        (carry_source_eq_target specification second).symm }

/-! ## Action and preservation remain separate -/

/--
The charge presented at a source state owns the actually received code, its
exact relation to that source, and the positive proximity witness consumed by
grouping.
-/
structure SourceCharge
    (specification : Specification.{uSource})
    (identity : specification.Source) where
  receivedCode : SignedDyadicCode
  receivedCodeExact :
    SameValue receivedCode (specification.sourceCode identity)
  receivedNearTarget :
    Near specification.precision receivedCode specification.targetCode

/--
The target charge retains the source code and proximity that were consumed.
Its output code is certified separately against the common target.
-/
structure GroupedCharge
    (precision : Nat)
    (targetCode : SignedDyadicCode) where
  consumedCode : SignedDyadicCode
  consumedNearTarget : Near precision consumedCode targetCode
  outputCode : SignedDyadicCode
  outputCodeExact : SameValue outputCode targetCode

/-- The payload family distinguishes received and already-grouped resources. -/
def ActionPayload
    {specification : Specification.{uSource}} :
    State specification -> Type
  | .source identity => SourceCharge specification identity
  | .target => GroupedCharge specification.precision specification.targetCode

/-- Build the source charge from the exact data retained by the specification. -/
def sourceCharge
    (specification : Specification.{uSource})
    (identity : specification.Source) :
    SourceCharge specification identity :=
  { receivedCode := specification.sourceCode identity
    receivedCodeExact := SameValue.refl _
    receivedNearTarget := specification.sourceNearTarget identity }

/-- Acceptance is checked separately from the action that moves the charge. -/
def AcceptedCharge
    {specification : Specification.{uSource}} :
    (state : State specification) -> ActionPayload state -> Prop
  | .source identity, charge =>
      Nonempty
        (SameValue charge.receivedCode
          (specification.sourceCode identity))
  | .target, charge =>
      Nonempty (SameValue charge.outputCode specification.targetCode)

/-- Public code carried by either a received or a grouped resource. -/
def ActionPayload.code
    {specification : Specification.{uSource}}
    {state : State specification} :
    ActionPayload state -> SignedDyadicCode := by
  cases state with
  | source identity => exact SourceCharge.receivedCode
  | target => exact GroupedCharge.outputCode

/-- The proof-relevant action consumes the whole received source charge. -/
def groupingAct
    (specification : Specification.{uSource})
    {source target : State specification} :
    Step specification source target ->
      ActionPayload source -> ActionPayload target
  | .group identity, charge =>
      { consumedCode := charge.receivedCode
        consumedNearTarget := charge.receivedNearTarget
        outputCode := specification.targetCode
        outputCodeExact := SameValue.refl specification.targetCode }

/-- Preservation is a separate proof consuming source acceptance. -/
theorem groupingAct_preserves
    (specification : Specification.{uSource})
    {source target : State specification}
    (step : Step specification source target)
    (charge : ActionPayload source) :
    AcceptedCharge source charge ->
      AcceptedCharge target (groupingAct specification step charge) := by
  cases step with
  | group identity =>
      intro accepted
      cases accepted
      exact Nonempty.intro (SameValue.refl specification.targetCode)

/--
The relational action consumes a source charge and produces the exact target
code that is subsequently exposed by the limit readout.
-/
def acceptanceAction
    (specification : Specification.{uSource}) :
    AcceptanceAction (rules specification) where
  Payload := ActionPayload
  Accept := AcceptedCharge
  act := groupingAct specification
  preserves := groupingAct_preserves specification

theorem sourceAccepted
    (specification : Specification.{uSource})
    (identity : specification.Source) :
    (acceptanceAction specification).Accept
      (State.source identity) (sourceCharge specification identity) :=
  Nonempty.intro (sourceCharge specification identity).receivedCodeExact

theorem action_exact
    (specification : Specification.{uSource})
    {source target : State specification}
    (step : Step specification source target)
    (charge : (acceptanceAction specification).Payload source) :
    ActionPayload.code ((acceptanceAction specification).act step charge) =
      specification.targetCode := by
  cases step
  rfl

theorem sourceTransport_exact
    (specification : Specification.{uSource})
    (identity : specification.Source)
    (charge : SourceCharge specification identity) :
    ((acceptanceAction specification).transport
        (Trace.one (Step.group identity)) charge).outputCode =
      specification.targetCode :=
  rfl

/-- The action output retains exactly the source code it consumed. -/
theorem sourceTransport_consumedCode
    (specification : Specification.{uSource})
    (identity : specification.Source)
    (charge : SourceCharge specification identity) :
    ((acceptanceAction specification).transport
        (Trace.one (Step.group identity)) charge).consumedCode =
      charge.receivedCode :=
  rfl

/-- The action output retains exactly the positive proximity witness consumed. -/
theorem sourceTransport_consumedNear
    (specification : Specification.{uSource})
    (identity : specification.Source)
    (charge : SourceCharge specification identity) :
    ((acceptanceAction specification).transport
        (Trace.one (Step.group identity)) charge).consumedNearTarget =
      charge.receivedNearTarget :=
  rfl

theorem action_coherent
    (specification : Specification.{uSource}) :
    (acceptanceAction specification).Coherent := by
  intro source target first second charge
  cases first with
  | nil =>
      cases second with
      | nil => rfl
      | cons step tail =>
          cases step with
          | group identity =>
              cases tail with
              | cons impossible rest => nomatch impossible
  | cons firstStep firstTail =>
      cases firstStep with
      | group identity =>
          cases firstTail with
          | nil =>
              cases second with
              | cons secondStep secondTail =>
                  cases secondStep
                  cases secondTail with
                  | nil => rfl
                  | cons impossible rest => nomatch impossible
          | cons impossible rest => nomatch impossible

/-- The preserved criterion is consumed along the actual grouping step. -/
theorem groupedSourceAccepted
    (specification : Specification.{uSource})
    (identity : specification.Source) :
    (acceptanceAction specification).Accept State.target
      ((acceptanceAction specification).transport
        (Trace.one (Step.group identity))
        (sourceCharge specification identity)) :=
  (acceptanceAction specification).transport_preserves
    (Trace.one (Step.group identity))
    (sourceCharge specification identity)
    (sourceAccepted specification identity)

end LocalGrouping
end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.Specification
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.State
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.Step
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.rank
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.choices
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.locate
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.decreases
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.diamond
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.rules
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.target_terminal
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.normal_target
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.normal_source
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.carry_source_eq_target
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.source_ne_source
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.SharedTargetWithoutSourceIdentification
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.sharedTargetWithoutSourceIdentification
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.SourceCharge
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.GroupedCharge
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.ActionPayload
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.sourceCharge
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.AcceptedCharge
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.ActionPayload.code
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.groupingAct
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.groupingAct_preserves
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.acceptanceAction
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.sourceAccepted
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.action_exact
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.sourceTransport_exact
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.sourceTransport_consumedCode
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.sourceTransport_consumedNear
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.action_coherent
#print axioms RelationalPerimeter.Constitution.Reals.LocalGrouping.groupedSourceAccepted
/- AXIOM_AUDIT_END -/
