import RelationalPerimeter.Constitution.Godel.PositiveExecutionCore

set_option genInjectivity false
set_option autoImplicit false
set_option linter.defProp false

/-! A three-step positive H1, with an origin readout into the execution received
through the shared core. Further continuations retain their actual histories. -/
namespace StrongPerimetralTurning

universe uA uB uC uP uV
variable {coding : GodelDiagonalSyntax.{uC,uA,uB,uP,uV}}
  {unprovabilityFormula : coding.UnaryFormula}
  {interpretation : GodelProvabilityInterpretation coding unprovabilityFormula}
  {execution : ExecutedGodelProduction coding unprovabilityFormula interpretation}

inductive GodelOperationalH1State (core : GodelPositiveExecutionCore execution) where
  | received
  | produced
  | certified
  | continued

inductive GodelOperationalH1Step (core : GodelPositiveExecutionCore execution) :
    GodelOperationalH1State core → GodelOperationalH1State core → Type
  | production : GodelOperationalH1Step core .received .produced
  | certification : GodelOperationalH1Step core .produced .certified
  | continuation : GodelOperationalH1Step core .certified .continued

def godelOperationalH1History (core : GodelPositiveExecutionCore execution) :
    History (GodelOperationalH1Step core) .received .continued :=
  .extend (.extend (.extend .root .production) .certification) .continuation

structure GodelOperationalH1 (core : GodelPositiveExecutionCore execution) where
  history : History (GodelOperationalH1Step core) .received .continued
  historyIsCanonical : history = godelOperationalH1History core
  executedProductionNextCertification :
    History.OccurrenceNext core.occurrences.selfApplyOccurrence
      core.occurrences.certifyOccurrence

def godelOperationalH1 (core : GodelPositiveExecutionCore execution) :
    GodelOperationalH1 core :=
  { history := godelOperationalH1History core
    historyIsCanonical := rfl
    executedProductionNextCertification := core.occurrences.selfApplyNextCertify }

inductive GodelOperationalOccurrenceOrigin (core : GodelPositiveExecutionCore execution)
  | executed (occurrence : History.Occurrence execution.history)
  | generatedContinuation

inductive GodelOperationalOriginNext (core : GodelPositiveExecutionCore execution) :
    GodelOperationalOccurrenceOrigin core → GodelOperationalOccurrenceOrigin core → Prop
  | executed {first second : History.Occurrence execution.history}
      (order : History.OccurrenceNext first second) :
      GodelOperationalOriginNext core (.executed first) (.executed second)

def godelOperationalStepOrigin (core : GodelPositiveExecutionCore execution)
    {source target : GodelOperationalH1State core}
    (step : GodelOperationalH1Step core source target) :
    GodelOperationalOccurrenceOrigin core :=
  match step with
  | .production => .executed core.occurrences.selfApplyOccurrence
  | .certification => .executed core.occurrences.certifyOccurrence
  | .continuation => .generatedContinuation

namespace GodelOperationalH1
variable {core : GodelPositiveExecutionCore execution} (h1 : GodelOperationalH1 core)

def productionOccurrence : History.Occurrence h1.history :=
  transportOccurrence h1.historyIsCanonical.symm (.earlier (.earlier .last))

def certificationOccurrence : History.Occurrence h1.history :=
  transportOccurrence h1.historyIsCanonical.symm (.earlier .last)

def continuationOccurrence : History.Occurrence h1.history :=
  transportOccurrence h1.historyIsCanonical.symm .last

theorem productionNextCertification :
    History.OccurrenceNext h1.productionOccurrence h1.certificationOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      exact .earlier_earlier .previous_last

theorem certificationNextContinuation :
    History.OccurrenceNext h1.certificationOccurrence h1.continuationOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      exact .previous_last

theorem productionCertificationDistinct : h1.productionOccurrence ≠ h1.certificationOccurrence :=
  h1.productionNextCertification.toPrecedes.ne

theorem certificationContinuationDistinct : h1.certificationOccurrence ≠ h1.continuationOccurrence :=
  h1.certificationNextContinuation.toPrecedes.ne

theorem productionContinuationDistinct : h1.productionOccurrence ≠ h1.continuationOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      exact (History.OccurrencePrecedes.earlier_last (.earlier .last)).ne

def occurrenceOrigin (occurrence : History.Occurrence h1.history) :
    GodelOperationalOccurrenceOrigin core :=
  godelOperationalStepOrigin core occurrence.locatedStep.step

theorem productionOrigin : h1.occurrenceOrigin h1.productionOccurrence =
    .executed core.occurrences.selfApplyOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder => cases exactHistory; rfl

theorem certificationOrigin : h1.occurrenceOrigin h1.certificationOccurrence =
    .executed core.occurrences.certifyOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder => cases exactHistory; rfl

theorem continuationOrigin : h1.occurrenceOrigin h1.continuationOccurrence =
    .generatedContinuation := by
  cases h1 with
  | mk history exactHistory executedOrder => cases exactHistory; rfl

theorem executedOriginOrder : GodelOperationalOriginNext core
    (h1.occurrenceOrigin h1.productionOccurrence)
    (h1.occurrenceOrigin h1.certificationOccurrence) := by
  rw [h1.productionOrigin, h1.certificationOrigin]
  exact .executed h1.executedProductionNextCertification

theorem occurrenceExhaustive (occurrence : History.Occurrence h1.history) :
    occurrence = h1.productionOccurrence ∨ occurrence = h1.certificationOccurrence ∨
      occurrence = h1.continuationOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      cases occurrence with
      | last => exact .inr (.inr rfl)
      | earlier occurrence =>
          cases occurrence with
          | last => exact .inr (.inl rfl)
          | earlier occurrence =>
              cases occurrence with
              | last => exact .inl rfl
              | earlier impossible => exact nomatch impossible

end GodelOperationalH1

inductive GodelPostH1State where
  | atDepth (additionalDepth : Nat)

inductive GodelPostH1Step : GodelPostH1State → GodelPostH1State → Type
  | continue (depth : Nat) : GodelPostH1Step (.atDepth depth) (.atDepth (depth + 1))

structure GodelOperationalHistory {core : GodelPositiveExecutionCore execution}
    (h1 : GodelOperationalH1 core) where
  additionalDepth : Nat
  continuation : History GodelPostH1Step (.atDepth 0) (.atDepth additionalDepth)

namespace GodelOperationalHistory
variable {core : GodelPositiveExecutionCore execution} {h1 : GodelOperationalH1 core}

def root (h1 : GodelOperationalH1 core) : GodelOperationalHistory h1 :=
  { additionalDepth := 0, continuation := .root }

def extend (history : GodelOperationalHistory h1) : GodelOperationalHistory h1 :=
  { additionalDepth := history.additionalDepth + 1
    continuation := .extend history.continuation (.continue history.additionalDepth) }

def depth (history : GodelOperationalHistory h1) : Nat := history.additionalDepth + 1

theorem depth_root (h1 : GodelOperationalH1 core) : (root h1).depth = 1 := rfl

theorem depth_extend (history : GodelOperationalHistory h1) :
    history.extend.depth = history.depth + 1 := rfl

theorem continuation_extend (history : GodelOperationalHistory h1) :
    history.extend.continuation =
      History.extend history.continuation (.continue history.additionalDepth) := rfl

def extendOccurrenceTransport (history : GodelOperationalHistory h1) :
    ExactTypeTransport (History.Occurrence history.continuation ⊕ Unit)
      (History.Occurrence history.extend.continuation) :=
  { forward := fun
      | .inl old => .earlier old
      | .inr _ => .last
    backward := fun
      | .last => .inr ()
      | .earlier old => .inl old
    forwardBackward := by
      intro occurrence
      cases occurrence with
      | inl old => rfl
      | inr witness => cases witness; rfl
    backwardForward := by
      intro occurrence
      cases occurrence with
      | last => rfl
      | earlier old => rfl }

end GodelOperationalHistory
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelOperationalH1State
#print axioms StrongPerimetralTurning.GodelOperationalH1Step
#print axioms StrongPerimetralTurning.godelOperationalH1History
#print axioms StrongPerimetralTurning.GodelOperationalH1
#print axioms StrongPerimetralTurning.godelOperationalH1
#print axioms StrongPerimetralTurning.GodelOperationalOccurrenceOrigin
#print axioms StrongPerimetralTurning.GodelOperationalOriginNext
#print axioms StrongPerimetralTurning.godelOperationalStepOrigin
#print axioms StrongPerimetralTurning.GodelOperationalH1.productionOccurrence
#print axioms StrongPerimetralTurning.GodelOperationalH1.certificationOccurrence
#print axioms StrongPerimetralTurning.GodelOperationalH1.continuationOccurrence
#print axioms StrongPerimetralTurning.GodelOperationalH1.productionNextCertification
#print axioms StrongPerimetralTurning.GodelOperationalH1.certificationNextContinuation
#print axioms StrongPerimetralTurning.GodelOperationalH1.productionCertificationDistinct
#print axioms StrongPerimetralTurning.GodelOperationalH1.certificationContinuationDistinct
#print axioms StrongPerimetralTurning.GodelOperationalH1.productionContinuationDistinct
#print axioms StrongPerimetralTurning.GodelOperationalH1.occurrenceOrigin
#print axioms StrongPerimetralTurning.GodelOperationalH1.productionOrigin
#print axioms StrongPerimetralTurning.GodelOperationalH1.certificationOrigin
#print axioms StrongPerimetralTurning.GodelOperationalH1.continuationOrigin
#print axioms StrongPerimetralTurning.GodelOperationalH1.executedOriginOrder
#print axioms StrongPerimetralTurning.GodelOperationalH1.occurrenceExhaustive
#print axioms StrongPerimetralTurning.GodelPostH1State
#print axioms StrongPerimetralTurning.GodelPostH1Step
#print axioms StrongPerimetralTurning.GodelOperationalHistory
#print axioms StrongPerimetralTurning.GodelOperationalHistory.root
#print axioms StrongPerimetralTurning.GodelOperationalHistory.extend
#print axioms StrongPerimetralTurning.GodelOperationalHistory.depth
#print axioms StrongPerimetralTurning.GodelOperationalHistory.depth_root
#print axioms StrongPerimetralTurning.GodelOperationalHistory.depth_extend
#print axioms StrongPerimetralTurning.GodelOperationalHistory.continuation_extend
#print axioms StrongPerimetralTurning.GodelOperationalHistory.extendOccurrenceTransport
/- AXIOM_AUDIT_END -/
