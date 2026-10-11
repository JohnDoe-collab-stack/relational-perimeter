import RelationalPerimeter.Computation.ConstitutiveGeneration
import RelationalPerimeter.Constitution.OccurrencePersistence

set_option genInjectivity false
set_option linter.checkUnivs false

namespace ConstitutiveSearch.PerimeterPersistence.OneStep
open StrongPerimetralTurning
open ConstitutiveSearch.OccurrencePersistence

abbrev InitialFreeOccurrence (P : CircularPresentation) :=
  History.Occurrence (perimeterHistory P)

abbrev ExtendedFreeOccurrence (P : CircularPresentation) :=
  History.Occurrence (oneStepAfterPerimeter P).history

abbrev InitialConcreteOccurrence (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :=
  History.Occurrence (A.realizeHistory (perimeterHistory P))

abbrev ExtendedConcreteOccurrence (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :=
  History.Occurrence (A.realizeHistory (oneStepAfterPerimeter P).history)

/-- Reuse the existing generated successor, including its old/fresh split. -/
def freeOccurrenceSplit (P : CircularPresentation) :
    ExactTypeTransport (InitialFreeOccurrence P ⊕ Unit) (ExtendedFreeOccurrence P) :=
  ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit P 0

/-- The two occurrence maps are projected from an already exact interpretation.
Its structural occurrence agreement remains in the supplied interpretation. -/
def interpretationTransport
    {P : CircularPresentation} {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory : History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation : ExactHistoryInterpretation A freeHistory concreteHistory) :
    ExactTypeTransport (History.Occurrence freeHistory)
      (History.Occurrence concreteHistory) :=
  { forward := interpretation.forwardOccurrence
    backward := interpretation.backwardOccurrence
    forwardBackward := interpretation.forwardBackward
    backwardForward := interpretation.backwardForward }

def canonicalOneStepAlignment (P : CircularPresentation) :
    ExactOneStepConstitutiveAlignment :=
  { Initial := InitialFreeOccurrence P
    Extended := ExtendedFreeOccurrence P
    extension := freeOccurrenceSplit P }

def canonicalOneStepAlignmentRealization (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : (canonicalOneStepAlignment P).Realization :=
  { InitialConcrete := InitialConcreteOccurrence P A
    ExtendedConcrete := ExtendedConcreteOccurrence P A
    initialSpoke := interpretationTransport (exactlyInterpretHistory A (perimeterHistory P))
    extendedSpoke := interpretationTransport
      (exactlyInterpretHistory A (oneStepAfterPerimeter P).history) }

def oneStepResidualFreeOccurrence (P : CircularPresentation) : ExtendedFreeOccurrence P :=
  (oneStepFaithfullyLabelledExtension P).newOccurrence
    (oneStepCoreResidualOccurrence P).occurrence

theorem canonicalAlignment_fresh_eq_residualFreeOccurrence (P : CircularPresentation) :
    (canonicalOneStepAlignment P).fresh = oneStepResidualFreeOccurrence P := rfl

theorem residualFreeOccurrence_agrees_with_consumedTurning (P : CircularPresentation) :
    oneStepResidualFreeOccurrence P =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  congrArg (oneStepFaithfullyLabelledExtension P).newOccurrence
    (oneStepCoreResidualOccurrence_agrees_with_consumedTurning P)

def oneStepResidualConcreteOccurrence (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : ExtendedConcreteOccurrence P A :=
  (exactlyInterpretHistory A (oneStepAfterPerimeter P).history).forwardOccurrence
    (oneStepResidualFreeOccurrence P)

theorem canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence
    (P : CircularPresentation) (A : ConcreteContinuationAlgebra P) :
    (canonicalOneStepAlignmentRealization P A).fresh =
      oneStepResidualConcreteOccurrence P A :=
  congrArg (exactlyInterpretHistory A (oneStepAfterPerimeter P).history).forwardOccurrence
    (canonicalAlignment_fresh_eq_residualFreeOccurrence P)

end ConstitutiveSearch.PerimeterPersistence.OneStep

namespace ConstitutiveSearch.PerimeterPersistence.Iterated
open StrongPerimetralTurning
open ConstitutiveSearch.OccurrencePersistence

/-- The same history that is consumed by the existing computation. -/
abbrev iteratedHistory := ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory
abbrev successorContinuationExactlyOne :=
  ConstitutiveSearch.ConstitutiveGeneration.successorContinuationExactlyOne
abbrev successorOccurrenceSplit :=
  ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit

/-! ## Exact indexing of every iterated history -/

/--
The canonical finite index is identified with the free occurrences of the
actual circular instance history at every depth.
-/
def iteratedOccurrenceSpoke
    (P : CircularPresentation) :
    (n : Nat) →
      ExactTypeTransport
        (IteratedCarrier (OneStep.InitialFreeOccurrence P) n)
        (History.Occurrence (iteratedHistory P n).history)
  | 0 => ExactTypeTransport.reflexive _
  | n + 1 =>
      (IteratedCarrier.oneStepTransport
        (OneStep.InitialFreeOccurrence P) n).reverse
        |>.compose ((iteratedOccurrenceSpoke P n).sumUnit)
        |>.compose (successorOccurrenceSplit P n)

@[simp] theorem iteratedOccurrenceSpoke_zero_forward
    (P : CircularPresentation)
    (occurrence : OneStep.InitialFreeOccurrence P) :
    (iteratedOccurrenceSpoke P 0).forward occurrence = occurrence :=
  rfl

@[simp] theorem iteratedOccurrenceSpoke_previous
    (P : CircularPresentation)
    (n : Nat)
    (identity :
      IteratedCarrier
        (OneStep.InitialFreeOccurrence P) n) :
    (iteratedOccurrenceSpoke P (n + 1)).forward
        (IteratedCarrier.embedPrevious identity) =
      History.Occurrence.earlier
        ((iteratedOccurrenceSpoke P n).forward identity) :=
  rfl

@[simp] theorem iteratedOccurrenceSpoke_fresh
    (P : CircularPresentation)
    (n : Nat) :
    (iteratedOccurrenceSpoke P (n + 1)).forward
        (IteratedCarrier.freshAtStep n) =
      History.Occurrence.last :=
  rfl

/-- The real free occurrence carrier at one finite circular depth. -/
def iteratedAlignment
    (P : CircularPresentation)
    (n : Nat) :
    FiniteConstitutiveAlignment
      (OneStep.InitialFreeOccurrence P) n :=
  { Carrier := History.Occurrence (iteratedHistory P n).history
    carrierSpoke := iteratedOccurrenceSpoke P n }

/-- The finite construction at depth one is the established canonical split. -/
theorem iteratedAlignment_one_forward
    (P : CircularPresentation)
    (identity :
      OneStep.InitialFreeOccurrence P ⊕ Unit) :
    (iteratedAlignment P 1).carrierSpoke.forward identity =
      (OneStep.freeOccurrenceSplit P).forward identity :=
  by
    cases identity with
    | inl occurrence => rfl
    | inr witness => cases witness; rfl

/-- The depth-one finite spoke also agrees backwards with the one-step split. -/
theorem iteratedAlignment_one_backward
    (P : CircularPresentation)
    (occurrence : OneStep.ExtendedFreeOccurrence P) :
    (iteratedAlignment P 1).carrierSpoke.backward occurrence =
      (OneStep.freeOccurrenceSplit P).backward occurrence :=
  ExactTypeTransport.backward_eq_of_forward_eq
    (iteratedAlignment P 1).carrierSpoke
    (OneStep.freeOccurrenceSplit P)
    (iteratedAlignment_one_forward P)
    occurrence

/-! ## Exact concrete realizations of the iterated histories -/

/-- Every supplied concrete algebra realizes the actual history at depth `n`. -/
def iteratedRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (iteratedAlignment P n).Realization :=
  { Concrete :=
      History.Occurrence (A.realizeHistory (iteratedHistory P n).history)
    spoke := OneStep.interpretationTransport
      (exactlyInterpretHistory A (iteratedHistory P n).history) }

@[simp] theorem iteratedRealization_atIndex
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat)
    (identity :
      IteratedCarrier
        (OneStep.InitialFreeOccurrence P) n) :
    (iteratedRealization P A n).indexedSpoke.forward identity =
      (exactlyInterpretHistory A (iteratedHistory P n).history).forwardOccurrence
        ((iteratedOccurrenceSpoke P n).forward identity) :=
  rfl

@[simp] theorem iteratedRealization_previous_isEarlier
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat)
    (identity :
      IteratedCarrier
        (OneStep.InitialFreeOccurrence P) n) :
    (iteratedRealization P A (n + 1)).indexedSpoke.forward
        (IteratedCarrier.embedPrevious identity) =
      History.Occurrence.earlier
        ((iteratedRealization P A n).indexedSpoke.forward identity) :=
  rfl

@[simp] theorem iteratedRealization_fresh_isLast
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (iteratedRealization P A (n + 1)).indexedSpoke.forward
        (IteratedCarrier.freshAtStep n) =
      History.Occurrence.last :=
  rfl

/-! ## Two-axis coherence on the actual circular producer -/

/--
Changing concrete realization commutes with finite constitutive extension for
the histories generated by the circular instance.  The identity may originate at any earlier
depth, not only at the perimeter.
-/
theorem iterated_extend_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence : (iteratedRealization P A sourceDepth).Concrete) :
    (((iteratedRealization P A targetDepth).transport
        (iteratedRealization P B targetDepth)).forward
      ((iteratedRealization P A sourceDepth).extend
        (iteratedRealization P A targetDepth) depth occurrence)) =
      (iteratedRealization P B sourceDepth).extend
        (iteratedRealization P B targetDepth) depth
        (((iteratedRealization P A sourceDepth).transport
          (iteratedRealization P B sourceDepth)).forward occurrence) :=
  FiniteConstitutiveAlignment.Realization.extend_transport_natural
    (iteratedRealization P A sourceDepth)
    (iteratedRealization P B sourceDepth)
    (iteratedRealization P A targetDepth)
    (iteratedRealization P B targetDepth)
    depth occurrence

/--
Natural-depth extension between two supplied concrete realizations depends only on
its source and target depths, not on the `DepthExtension` witness.
-/
theorem iteratedExtension_witness_independent
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (first second : DepthExtension sourceDepth targetDepth)
    (occurrence : (iteratedRealization P A sourceDepth).Concrete) :
    (iteratedRealization P A sourceDepth).extend
        (iteratedRealization P B targetDepth) first occurrence =
      (iteratedRealization P A sourceDepth).extend
        (iteratedRealization P B targetDepth) second occurrence :=
  FiniteConstitutiveAlignment.Realization.extend_witness_independent
    (iteratedRealization P A sourceDepth)
    (iteratedRealization P B targetDepth)
    first second occurrence

/--
At depth one, finite horizontal transport is pointwise the established
one-step transport.  Thus the iterated construction conservatively extends the
earlier interface in both directions, not only at the level of carrier types.
-/
theorem iteratedTransport_one_eq_oneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : (iteratedRealization P A 1).Concrete) :
    ((iteratedRealization P A 1).transport
        (iteratedRealization P B 1)).forward occurrence =
      ((OneStep.canonicalOneStepAlignmentRealization P A).extendedTransport
        (OneStep.canonicalOneStepAlignmentRealization P B)).forward
          occurrence := by
  have roundTrip :=
    (iteratedAlignment P 1).carrierSpoke.backwardForward
      ((OneStep.canonicalOneStepAlignmentRealization P A).extendedSpoke.backward
        occurrence)
  exact congrArg
    (OneStep.canonicalOneStepAlignmentRealization P B).extendedSpoke.forward
    roundTrip

/--
At depth one, the backward finite horizontal transport is pointwise the
backward map of the established one-step transport.
-/
theorem iteratedTransport_one_backward_eq_oneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : (iteratedRealization P B 1).Concrete) :
    ((iteratedRealization P A 1).transport
        (iteratedRealization P B 1)).backward occurrence =
      ((OneStep.canonicalOneStepAlignmentRealization P A).extendedTransport
        (OneStep.canonicalOneStepAlignmentRealization P B)).backward
          occurrence :=
  ExactTypeTransport.backward_eq_of_forward_eq
    ((iteratedRealization P A 1).transport (iteratedRealization P B 1))
    ((OneStep.canonicalOneStepAlignmentRealization P A).extendedTransport
      (OneStep.canonicalOneStepAlignmentRealization P B))
    (iteratedTransport_one_eq_oneStep P A B)
    occurrence

/-- The finite fresh identity at depth one is the established one-step fresh identity. -/
theorem iteratedRealization_one_fresh_eq_oneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (iteratedRealization P A 1).indexedSpoke.forward
        (IteratedCarrier.freshAtStep 0) =
      (OneStep.canonicalOneStepAlignmentRealization P A).fresh :=
  rfl

/-! ## Persistence of the operational residual identity -/

/--
At depth one, the fresh identity of the finite circular realization is exactly
the concrete operational residual occurrence.
-/
theorem iteratedRealization_one_fresh_eq_residual
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (iteratedRealization P A 1).indexedSpoke.forward
        (IteratedCarrier.freshAtStep 0) =
      OneStep.oneStepResidualConcreteOccurrence P A :=
  (iteratedRealization_one_fresh_eq_oneStep P A).trans
    (OneStep.canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence P A)

/--
The concrete operational residual identity is preserved by change of exact
realization at depth one.
-/
theorem iteratedResidualOccurrence_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    ((iteratedRealization P A 1).transport
        (iteratedRealization P B 1)).forward
        (OneStep.oneStepResidualConcreteOccurrence P A) =
      OneStep.oneStepResidualConcreteOccurrence P B := by
  rw [← iteratedRealization_one_fresh_eq_residual P A]
  exact
    (FiniteConstitutiveAlignment.Realization.transport_atIndex
      (iteratedRealization P A 1)
      (iteratedRealization P B 1)
      (IteratedCarrier.freshAtStep 0)).trans
      (iteratedRealization_one_fresh_eq_residual P B)

/--
Once the first operational residual occurrence has been constituted, that
identity persists through every later finite circular depth.
-/
theorem iteratedResidualOccurrence_persists
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    (iteratedRealization P A 1).extend
        (iteratedRealization P A targetDepth)
        depth
        (OneStep.oneStepResidualConcreteOccurrence P A) =
      (iteratedRealization P A targetDepth).indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (IteratedCarrier.freshAtStep 0)) := by
  calc
    (iteratedRealization P A 1).extend
        (iteratedRealization P A targetDepth)
        depth
        (OneStep.oneStepResidualConcreteOccurrence P A) =
      (iteratedRealization P A 1).extend
        (iteratedRealization P A targetDepth)
        depth
        ((iteratedRealization P A 1).indexedSpoke.forward
          (IteratedCarrier.freshAtStep 0)) :=
      congrArg
        ((iteratedRealization P A 1).extend
          (iteratedRealization P A targetDepth) depth)
        (iteratedRealization_one_fresh_eq_residual P A).symm
    _ =
      (iteratedRealization P A targetDepth).indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (IteratedCarrier.freshAtStep 0)) :=
      FiniteConstitutiveAlignment.Realization.extend_atIndex
        (iteratedRealization P A 1)
        (iteratedRealization P A targetDepth)
        depth
        (IteratedCarrier.freshAtStep 0)

/--
Persistence of the operational residual identity commutes with change of exact
concrete realization.
-/
theorem iteratedResidualOccurrence_extension_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    ((iteratedRealization P A targetDepth).transport
        (iteratedRealization P B targetDepth)).forward
        ((iteratedRealization P A 1).extend
          (iteratedRealization P A targetDepth)
          depth
          (OneStep.oneStepResidualConcreteOccurrence P A)) =
      (iteratedRealization P B 1).extend
        (iteratedRealization P B targetDepth)
        depth
        (OneStep.oneStepResidualConcreteOccurrence P B) := by
  calc
    ((iteratedRealization P A targetDepth).transport
        (iteratedRealization P B targetDepth)).forward
        ((iteratedRealization P A 1).extend
          (iteratedRealization P A targetDepth)
          depth
          (OneStep.oneStepResidualConcreteOccurrence P A)) =
      (iteratedRealization P B 1).extend
        (iteratedRealization P B targetDepth)
        depth
        (((iteratedRealization P A 1).transport
          (iteratedRealization P B 1)).forward
          (OneStep.oneStepResidualConcreteOccurrence P A)) :=
      iterated_extend_transport_natural
        P A B depth
        (OneStep.oneStepResidualConcreteOccurrence P A)
    _ =
      (iteratedRealization P B 1).extend
        (iteratedRealization P B targetDepth)
        depth
        (OneStep.oneStepResidualConcreteOccurrence P B) :=
      congrArg
        ((iteratedRealization P B 1).extend
          (iteratedRealization P B targetDepth) depth)
        (iteratedResidualOccurrence_transport_natural P A B)

/-- Depth `0 → 1` extension is pointwise the established one-step old map. -/
theorem iteratedExtension_zero_one_eq_oneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : (iteratedRealization P A 0).Concrete) :
    (iteratedRealization P A 0).extend
        (iteratedRealization P A 1) (.step (.refl 0)) occurrence =
      (OneStep.canonicalOneStepAlignmentRealization P A).old
        occurrence :=
  rfl

end ConstitutiveSearch.PerimeterPersistence.Iterated


open ConstitutiveSearch.OccurrencePersistence

/-!
# Structural entry point

The theoretical unit of this project is neither a particular layer nor a final
result, but the demonstrated continuity of a single determination across
several distinct and interdependent layers.  Roles are established before their
representations, transported without merging the layers, and only then made
available to independent readouts.  This organization requires a global
interpretation of local results.

The same constitutive determination is followed through the facade as follows:

```text
constitutive positions/requirements of the perimeter
        ↓ exact agreement
local occurrences in an arbitrary history
        ↓ local-to-global reconstruction
canonical perimeter as an initial factor
        ├──────────────────────────────────┐
        ↓                                  ↓
one-occurrence continuation            perimeter positions
        ↓                                  ↕
perimeter preserved as a prefix        free occurrences
        ↓                                  ↕
exact realization of the               concrete occurrences in
extended history                       each realization
        ↓                                  ↓
exit from the regime and               coordination through
from the specification                 the same index
                                           ↓
                                       readouts attached only afterward
```

The facade preserves differences of status while demonstrating the exact
transports that allow a single constitutive determination to pass through
them. Here, identity means the persistence of that determination across
distinct layers through those transports.

This file is therefore a human-scale facade over the structural foundation.  It
exposes the following articulated results and introduces no new assumption:

* exact local realization in any rooted generated history reconstructs the
  canonical perimeter as an initial factor of that history;
* the canonical perimeter is exactly realized and satisfies both the
  operational regime and the independent specification, while one generated
  step beyond it is a strict one-occurrence continuation which remains exactly
  realizable in every supplied concrete continuation algebra but lies outside
  both the regime and the specification;
* that one-step continuation has an exact old/fresh occurrence split whose
  realizations commute with change of concrete representation and whose
  induced transports are pointwise independent of intermediate realizations;
* the same constitution extends to every finite number of real circular generation steps:
  earlier identities persist, each step contributes one fresh identity, and
  natural-depth extension is independent of its proof-relevant depth witness and
  commutes with change of exact concrete realization; this independence also
  holds when source and target use different supplied realizations; at depth
  one both directions of horizontal transport, the fresh identity, and the
  vertical old map agree pointwise with the established one-step interface;
* the canonical facade construction supplies mutually inverse correspondences
  between perimeter positions, free occurrences, and concrete occurrences
  before any readout or value type is chosen; two supplied concrete
  realizations are then coordinated through those same positions, so their
  occurrence readouts can be reindexed without adding an independent pairwise
  matching.

The short constructions below do not replace the underlying proofs.  They make
the local-to-global reconstruction, the canonical exit, its exact one-step
constitutive alignment, and the structural readout bus available in one
human-scale file.
-/

namespace ConstitutiveSearch.PerimeterPersistence

open StrongPerimetralTurning

/--
The central local-to-global reconstruction theorem of the circular instance, exposed at the
human-scale entry point.

The input is an arbitrary exact local realization inside a genuine
`RootedGeneratedHistory`; it is not assumed to be the canonical deployment.
Its primitive data are a realization map and exact source-cursor agreement for
each non-closing perimeter requirement.  Injectivity is reconstructed from that
agreement rather than postulated.

The output constructively exhibits the canonical perimeter history as an exact
initial factor of the supplied history.  It may leave a positive continuation,
so this result does not claim that the perimeter exhausts the history.  This
facade is a definitional alias of the foundational construction.  It preserves
the witness layer and adds no hypothesis.  The compiler emits IR for it, and it
reduces to a value when the presentation and realization are supplied as closed
data.
-/
def localExactnessReconstructsPerimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    PerimeterExtension P history :=
  realization.toPerimeterExtension

/--
The canonical human-scale certificate: exact reconstruction of the perimeter
does not close construction.  The canonical one-step continuation contains
exactly one occurrence, and the resulting history, like every rooted generated
history, admits an `ExactConcreteRealization` in every supplied concrete
continuation algebra.  This realization field records a positive preservation
witness; once the algebra is supplied, it is not a condition selecting
histories.  In the circular instance, the regime and the independently defined
norm each hold exactly of the canonical perimeter, although their witness types
and proof routes remain distinct.  The continued history exits both.  Both
refutations are relative to the supplied `CircularPresentation`, in particular
its explicit `rejectInitialContraction` field.
-/
structure ExactPerimeterAndFaithfulExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : Type _ where
  perimeterExact :
    ExactPerimeterRealization P (perimeterDeployment P)
  perimeterInRegime :
    CircularRefinement P (perimeterDeployment P)
  perimeterSatisfiesSpecification :
    CircularSpecificationSatisfaction P (perimeterDeployment P)
  continuationStrict :
    StrictConstitutivePrefix
      (perimeterDeployment P) (oneStepAfterPerimeter P)
  continuationHasExactlyOneOccurrence :
    History.ExactlyOne
      (oneStepFaithfullyLabelledExtension P).continuation
  /-- Positive exact-transport witness, not a history-selection condition. -/
  continuationFaithful :
    ExactConcreteRealization A (oneStepAfterPerimeter P)
  continuationOutsideRegime :
    CircularRefinement P (oneStepAfterPerimeter P) → False
  continuationOutsideSpecification :
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False

/--
The certificate is constructed entirely from the canonical witnesses already
proved by the structural foundation. Since `A` is arbitrary, this declaration
provides the repository's `ExactConcreteRealization` witness for the resulting
history in every supplied implementation; no implementation is postulated by
the facade.
-/
def exactPerimeterAndFaithfulExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactPerimeterAndFaithfulExit P A :=
  { perimeterExact := perimeterRealization P
    perimeterInRegime := identityCircularRefinement P
    perimeterSatisfiesSpecification :=
      perimeterDeployment_specificationSatisfaction P
    continuationStrict := oneStepAfterPerimeterStrict P
    continuationHasExactlyOneOccurrence :=
      positiveContinuation_exactlyOne
        (oneStepFaithfullyLabelledExtension P)
        (oneStepAfterPerimeter_positiveContinuation P)
    continuationFaithful :=
      exactlyInterpretHistory A (oneStepAfterPerimeter P).history
    continuationOutsideRegime :=
      oneStepAfterPerimeter_notCircularRefinement P
    continuationOutsideSpecification :=
      oneStepAfterPerimeter_notSpecificationSatisfaction P }

/-!
The transition exposed above also instantiates a content-independent notion of
exact one-step constitutive alignment.  The abstract interface contains only
an exact old/fresh split.  Each concrete algebra supplies a separate exact
carrier realization of that split.  At this content-independent level,
`Realization` asserts no preservation of labels, order, or step semantics.
Naturality, path coherence, and relative pointwise uniqueness are then derived
by `ExactOneStepConstitutiveAlignment.Realization`; they are not additional
matching data.  In the canonical instance, the induced old and fresh elements
are proved to be the native concrete occurrences `.earlier` and `.last`.

This layer contains no admission, specification, or readout value.  Those
remain distinct before being articulated by the surrounding facade.
-/

/-- The canonical one-step transition as a content-independent alignment. -/
def canonicalConstitutiveAlignment
    (P : CircularPresentation) :
    ExactOneStepConstitutiveAlignment :=
  OneStep.canonicalOneStepAlignment P

/-- One supplied concrete algebra as an exact carrier realization. -/
def canonicalConstitutiveAlignmentRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (canonicalConstitutiveAlignment P).Realization :=
  OneStep.canonicalOneStepAlignmentRealization P A

/-!
The one-step alignment above extends constructively to every finite number of
actual circular generations.  Each stage is produced by `generate` and
`appendGenerated`; it is not an abstract chain postulated by the facade.

Every determination, once constituted, persists through every later stage of
any finite prefix of this generated chain, and that persistence commutes with
change of exact realization.  A readout assembled afterward by extension to an arbitrary natural-number depth
therefore preserves every distinction it already makes on those determinations.
This does not yet instantiate a transformer and does not identify independently
supplied readouts.
-/

/-- The exact free occurrence carrier after `n` actual circular generations. -/
def finiteConstitutivePersistence
    (P : CircularPresentation)
    (n : Nat) :
    FiniteConstitutiveAlignment
      (OneStep.InitialFreeOccurrence P) n :=
  Iterated.iteratedAlignment P n

/-- One supplied algebra realizes the actual circular carrier at depth `n`. -/
def finiteConstitutivePersistenceRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (finiteConstitutivePersistence P n).Realization :=
  Iterated.iteratedRealization P A n

/--
Natural-depth extension and change of realization commute on the actual circular instance
occurrences, including identities first constituted after the perimeter.
-/
theorem finiteExtensionRealizationNaturality
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete) :
    (((finiteConstitutivePersistenceRealization P A targetDepth).transport
        (finiteConstitutivePersistenceRealization P B targetDepth)).forward
      ((finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        depth occurrence)) =
      (finiteConstitutivePersistenceRealization P B sourceDepth).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        depth
        (((finiteConstitutivePersistenceRealization P A sourceDepth).transport
          (finiteConstitutivePersistenceRealization P B sourceDepth)).forward
          occurrence) :=
  Iterated.iterated_extend_transport_natural
    P A B depth occurrence

/--
Natural-depth extension on actual circular realizations depends only on its source and
target depths, not on the proof-relevant `DepthExtension` witness supplied.
-/
theorem finiteExtensionWitnessIndependent
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (first second : DepthExtension sourceDepth targetDepth)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete) :
    (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        first occurrence =
      (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        second occurrence :=
  FiniteConstitutiveAlignment.Realization.extend_witness_independent
    (finiteConstitutivePersistenceRealization P A sourceDepth)
    (finiteConstitutivePersistenceRealization P A targetDepth)
    first second occurrence

/--
Natural-depth extension remains witness-independent when its source and target are
two different supplied concrete realizations.
-/
theorem finiteExtensionWitnessIndependentAcrossRealizations
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (first second : DepthExtension sourceDepth targetDepth)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete) :
    (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        first occurrence =
      (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        second occurrence :=
  Iterated.iteratedExtension_witness_independent
    P A B first second occurrence

/--
The finite horizontal transport at depth one is pointwise the previously
established one-step transport, so iteration adds no competing correspondence
at its base case.
-/
theorem finiteDepthOneTransportMatchesOneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A 1).Concrete) :
    (((finiteConstitutivePersistenceRealization P A 1).transport
        (finiteConstitutivePersistenceRealization P B 1)).forward occurrence) =
      (((canonicalConstitutiveAlignmentRealization P A).extendedTransport
        (canonicalConstitutiveAlignmentRealization P B)).forward occurrence) :=
  Iterated.iteratedTransport_one_eq_oneStep
    P A B occurrence

/--
The backward finite horizontal transport at depth one is pointwise the
backward map of the previously established one-step transport.
-/
theorem finiteDepthOneBackwardTransportMatchesOneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence :
      (finiteConstitutivePersistenceRealization P B 1).Concrete) :
    (((finiteConstitutivePersistenceRealization P A 1).transport
        (finiteConstitutivePersistenceRealization P B 1)).backward occurrence) =
      (((canonicalConstitutiveAlignmentRealization P A).extendedTransport
        (canonicalConstitutiveAlignmentRealization P B)).backward occurrence) :=
  Iterated.iteratedTransport_one_backward_eq_oneStep
    P A B occurrence

/-- The finite fresh identity at depth one is the one-step fresh identity. -/
theorem finiteDepthOneFreshMatchesOneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (finiteConstitutivePersistenceRealization P A 1).indexedSpoke.forward
        (IteratedCarrier.freshAtStep 0) =
      (canonicalConstitutiveAlignmentRealization P A).fresh :=
  Iterated.iteratedRealization_one_fresh_eq_oneStep P A

/-! ## Operational meaning of aligned persistence -/

/--
The fresh identity of the canonical one-step alignment is exactly the
full-history residual occurrence consumed by the operational turning theorem.
-/
theorem oneStepAlignmentFreshIsConsumedResidual
    (P : CircularPresentation) :
    (canonicalConstitutiveAlignment P).fresh =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence) := by
  change
    (OneStep.canonicalOneStepAlignment P).fresh =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence)
  exact
    (OneStep.canonicalAlignment_fresh_eq_residualFreeOccurrence P).trans
      (OneStep.residualFreeOccurrence_agrees_with_consumedTurning P)

/--
The operational residual occurrence constituted at the first exit persists as
the same constitutive identity through every later finite circular depth.
-/
theorem finiteOperationalResidualPersists
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    (finiteConstitutivePersistenceRealization P A 1).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        depth
        (OneStep.oneStepResidualConcreteOccurrence P A) =
      (finiteConstitutivePersistenceRealization P A targetDepth).indexedSpoke.forward
          (IteratedCarrier.embedFrom depth
            (IteratedCarrier.freshAtStep 0)) := by
  simpa [finiteConstitutivePersistenceRealization, finiteConstitutivePersistence] using
    (Iterated.iteratedResidualOccurrence_persists P A depth)

/--
Persistence of the operational residual occurrence is natural across supplied
exact concrete realizations.
-/
theorem finiteOperationalResidualNaturality
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    ((finiteConstitutivePersistenceRealization P A targetDepth).transport
        (finiteConstitutivePersistenceRealization P B targetDepth)).forward
        ((finiteConstitutivePersistenceRealization P A 1).extend
          (finiteConstitutivePersistenceRealization P A targetDepth)
          depth
          (OneStep.oneStepResidualConcreteOccurrence P A)) =
      (finiteConstitutivePersistenceRealization P B 1).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        depth
        (OneStep.oneStepResidualConcreteOccurrence P B) := by
  simpa [finiteConstitutivePersistenceRealization, finiteConstitutivePersistence] using
    (Iterated.iteratedResidualOccurrence_extension_transport_natural
      P A B depth)

/-- The depth `0 → 1` extension is pointwise the one-step old map. -/
theorem finiteDepthZeroOneExtensionMatchesOneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A 0).Concrete) :
    (finiteConstitutivePersistenceRealization P A 0).extend
        (finiteConstitutivePersistenceRealization P A 1)
        (.step (.refl 0)) occurrence =
      (canonicalConstitutiveAlignmentRealization P A).old occurrence :=
  Iterated.iteratedExtension_zero_one_eq_oneStep
    P A occurrence

/-- Change of realization is pointwise independent of an intermediate algebra. -/
theorem finiteTransportPathCoherence
    (P : CircularPresentation)
    (A B C : ConcreteContinuationAlgebra P)
    (depth : Nat)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A depth).Concrete) :
    (((finiteConstitutivePersistenceRealization P B depth).transport
        (finiteConstitutivePersistenceRealization P C depth)).forward
      (((finiteConstitutivePersistenceRealization P A depth).transport
        (finiteConstitutivePersistenceRealization P B depth)).forward
        occurrence)) =
      (((finiteConstitutivePersistenceRealization P A depth).transport
        (finiteConstitutivePersistenceRealization P C depth)).forward
        occurrence) :=
  FiniteConstitutiveAlignment.Realization.transport_comp
    (finiteConstitutivePersistenceRealization P A depth)
    (finiteConstitutivePersistenceRealization P B depth)
    (finiteConstitutivePersistenceRealization P C depth)
    occurrence

/--
Any distinction made by a finitely assembled readout persists on the exact
concrete occurrences through every later circular stage.
-/
theorem finiteReadoutDistinctionPersists
    {Value : Type}
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (initialReadout :
      OneStep.InitialFreeOccurrence P → Value)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (targetValues : FiniteFreshValues Value targetDepth)
    (first second :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete)
    (distinguished :
      (finiteConstitutivePersistenceRealization P A sourceDepth).realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) first ≠
        (finiteConstitutivePersistenceRealization P A sourceDepth).realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) second) :
    (finiteConstitutivePersistenceRealization P A targetDepth).realizeReadout
          (iteratedReadout initialReadout targetValues)
          ((finiteConstitutivePersistenceRealization P A sourceDepth).extend
            (finiteConstitutivePersistenceRealization P A targetDepth)
            depth first) ≠
      (finiteConstitutivePersistenceRealization P A targetDepth).realizeReadout
          (iteratedReadout initialReadout targetValues)
          ((finiteConstitutivePersistenceRealization P A sourceDepth).extend
            (finiteConstitutivePersistenceRealization P A targetDepth)
            depth second) :=
  FiniteConstitutiveAlignment.Realization.realizeIteratedReadout_distinction
    initialReadout
    (finiteConstitutivePersistenceRealization P A sourceDepth)
    (finiteConstitutivePersistenceRealization P A targetDepth)
    depth targetValues first second distinguished

/--
Structural bus from perimeter positions to free occurrences and then to
occurrences in any supplied concrete realization.

No readout value is part of this structure. The identities and their exact
correspondences are established before any evaluation is attached to them.
Here, `exact` means that the two maps of each correspondence are mutually
inverse.  The interface does not assert that an inhabitant is canonical or
unique, nor that an arbitrary inhabitant preserves order, adjacency, or labels.

Conceptually, occurrences and their exact correspondences form a structural
bus onto which independent readouts can be attached after constitution.
-/
structure ExactReadoutBus
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : Type _ where
  perimeterOccurrences :
    ExactTypeTransport
      (NonClosingPosition P.perimeter)
      (History.Occurrence (perimeterHistory P))
  concreteInterpretation :
    ExactHistoryInterpretation
      A
      (perimeterHistory P)
      (A.realizeHistory (perimeterHistory P))

/--
The canonical structural bus used by the repository is obtained entirely from
already proved exact correspondences.  No evaluation and no value type is
required.  This definition supplies the canonical inhabitant; the
`ExactReadoutBus` interface itself does not assert uniqueness.
-/
def exactReadoutBus
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactReadoutBus P A :=
  { perimeterOccurrences :=
      { forward := requirementToOccurrence P
        backward := occurrenceToRequirement P
        forwardBackward := requirementToOccurrence_toRequirement P
        backwardForward := occurrenceToRequirement_toOccurrence P }
    concreteInterpretation :=
      exactlyInterpretHistory A (perimeterHistory P) }

namespace ExactReadoutBus

universe uValue

/--
One exact spoke of the star-shaped bus, from perimeter identities directly to
the concrete occurrences of one supplied realization.

The spoke composes the already established position/free-occurrence and
free/concrete-occurrence correspondences.  It introduces no pairwise matching
with any other realization.
-/
def concreteOccurrenceSpoke
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A) :
    ExactTypeTransport
      (NonClosingPosition P.perimeter)
      (History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :=
  { forward := fun position =>
      bus.concreteInterpretation.forwardOccurrence
        (bus.perimeterOccurrences.forward position)
    backward := fun occurrence =>
      bus.perimeterOccurrences.backward
        (bus.concreteInterpretation.backwardOccurrence occurrence)
    forwardBackward := by
      intro position
      change
        bus.perimeterOccurrences.backward
            (bus.concreteInterpretation.backwardOccurrence
              (bus.concreteInterpretation.forwardOccurrence
                (bus.perimeterOccurrences.forward position))) =
          position
      rw [bus.concreteInterpretation.forwardBackward]
      rw [bus.perimeterOccurrences.forwardBackward]
    backwardForward := by
      intro occurrence
      change
        bus.concreteInterpretation.forwardOccurrence
            (bus.perimeterOccurrences.forward
              (bus.perimeterOccurrences.backward
                (bus.concreteInterpretation.backwardOccurrence occurrence))) =
          occurrence
      rw [bus.perimeterOccurrences.backwardForward]
      rw [bus.concreteInterpretation.backwardForward] }

/--
The concrete occurrence selected by one spoke at a perimeter position.

This is one spoke of the structural bus: the position is first sent to its free
occurrence and then to the corresponding occurrence in the supplied concrete
realization.  No readout value is involved.
-/
def concreteOccurrenceAt
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence
      (A.realizeHistory (perimeterHistory P)) :=
  bus.concreteOccurrenceSpoke.forward position

/--
Coordinate the concrete occurrences of two supplied realizations through their
shared perimeter identities.

The forward map follows the exact route

```text
source concrete occurrence
  -> free occurrence
  -> perimeter position
  -> free occurrence
  -> target concrete occurrence
```

and the backward map follows the reverse route.  Thus no independent pairwise
matching between the two concrete realizations is added.  The result is exact
for the two buses supplied here; it does not assert that every possible exact
coordination is equal to this one, nor does it impose a semantic relation on
values later attached to the coordinated occurrences.
-/
def concreteOccurrenceTransport
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B) :
    ExactTypeTransport
      (History.Occurrence
        (A.realizeHistory (perimeterHistory P)))
      (History.Occurrence
        (B.realizeHistory (perimeterHistory P))) :=
  { forward := fun occurrence =>
      targetBus.concreteOccurrenceSpoke.forward
        (sourceBus.concreteOccurrenceSpoke.backward occurrence)
    backward := fun occurrence =>
      sourceBus.concreteOccurrenceSpoke.forward
        (targetBus.concreteOccurrenceSpoke.backward occurrence)
    forwardBackward := by
      intro occurrence
      change
        sourceBus.concreteOccurrenceSpoke.forward
            (targetBus.concreteOccurrenceSpoke.backward
              (targetBus.concreteOccurrenceSpoke.forward
                (sourceBus.concreteOccurrenceSpoke.backward occurrence))) =
          occurrence
      rw [targetBus.concreteOccurrenceSpoke.forwardBackward]
      rw [sourceBus.concreteOccurrenceSpoke.backwardForward]
    backwardForward := by
      intro occurrence
      change
        targetBus.concreteOccurrenceSpoke.forward
            (sourceBus.concreteOccurrenceSpoke.backward
              (sourceBus.concreteOccurrenceSpoke.forward
                (targetBus.concreteOccurrenceSpoke.backward occurrence))) =
          occurrence
      rw [sourceBus.concreteOccurrenceSpoke.forwardBackward]
      rw [targetBus.concreteOccurrenceSpoke.backwardForward] }

/--
The concrete-to-concrete transport preserves the common perimeter index
pointwise.  This is the precise synchronization supplied by the structural bus:
the two concrete occurrences are coordinated because both realize the same
position, not because their values were compared after construction.
-/
theorem concreteOccurrenceTransport_atPosition
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    (position : NonClosingPosition P.perimeter) :
    (sourceBus.concreteOccurrenceTransport targetBus).forward
        (sourceBus.concreteOccurrenceAt position) =
      targetBus.concreteOccurrenceAt position := by
  change
    targetBus.concreteOccurrenceSpoke.forward
        (sourceBus.concreteOccurrenceSpoke.backward
          (sourceBus.concreteOccurrenceSpoke.forward position)) =
      targetBus.concreteOccurrenceSpoke.forward position
  rw [sourceBus.concreteOccurrenceSpoke.forwardBackward]

/--
Concrete occurrence transport is pointwise independent of an intermediate bus.
All three transports are induced by the same perimeter identities; no function
extensionality or additional pairwise coherence datum is required.
-/
theorem concreteOccurrenceTransport_forward_comp
    {P : CircularPresentation}
    {A B C : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (middleBus : ExactReadoutBus P B)
    (targetBus : ExactReadoutBus P C)
    (occurrence :
      History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :
    (middleBus.concreteOccurrenceTransport targetBus).forward
        ((sourceBus.concreteOccurrenceTransport middleBus).forward
          occurrence) =
      (sourceBus.concreteOccurrenceTransport targetBus).forward occurrence := by
  change
    targetBus.concreteOccurrenceSpoke.forward
        (middleBus.concreteOccurrenceSpoke.backward
          (middleBus.concreteOccurrenceSpoke.forward
            (sourceBus.concreteOccurrenceSpoke.backward occurrence))) =
      targetBus.concreteOccurrenceSpoke.forward
        (sourceBus.concreteOccurrenceSpoke.backward occurrence)
  rw [middleBus.concreteOccurrenceSpoke.forwardBackward]

/--
The repository's canonical concrete-to-concrete coordination.  Each spoke is
the canonical `exactReadoutBus`; canonicity here names this chosen construction,
not a uniqueness theorem for all inhabitants of `ExactReadoutBus`.
-/
def exactConcreteOccurrenceTransport
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    ExactTypeTransport
      (History.Occurrence
        (A.realizeHistory (perimeterHistory P)))
      (History.Occurrence
        (B.realizeHistory (perimeterHistory P))) :=
  (exactReadoutBus P A).concreteOccurrenceTransport (exactReadoutBus P B)

/--
Attach an arbitrary readout to perimeter identities and read it on the
corresponding concrete occurrences. The value type is completely independent
of the structural bus.
-/
def toConcreteReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout : NonClosingPosition P.perimeter → Value) :
    History.Occurrence
        (A.realizeHistory (perimeterHistory P)) →
      Value :=
  fun occurrence =>
    readout (bus.concreteOccurrenceSpoke.backward occurrence)

/--
Read a concrete occurrence-indexed evaluation back on the canonical perimeter
identities.
-/
def toPerimeterReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value) :
    NonClosingPosition P.perimeter → Value :=
  fun position =>
    readout (bus.concreteOccurrenceSpoke.forward position)

/--
Reindex a supplied concrete readout from one realization to another through the
shared structural bus.  This transports the indexing of the values only; it
does not assert any semantic compatibility between independently supplied
readouts.
-/
def transportConcreteReadout
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value) :
    History.Occurrence
        (B.realizeHistory (perimeterHistory P)) →
      Value :=
  fun occurrence =>
    readout
      ((sourceBus.concreteOccurrenceTransport targetBus).backward occurrence)

/--
A readout transported between two concrete realizations assigns the same value
to the occurrences selected by the same perimeter position.
-/
theorem transportConcreteReadout_atPosition
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (position : NonClosingPosition P.perimeter) :
    sourceBus.transportConcreteReadout targetBus readout
        (targetBus.concreteOccurrenceAt position) =
      readout (sourceBus.concreteOccurrenceAt position) := by
  change
    readout
        (sourceBus.concreteOccurrenceSpoke.forward
          (targetBus.concreteOccurrenceSpoke.backward
            (targetBus.concreteOccurrenceSpoke.forward position))) =
      readout (sourceBus.concreteOccurrenceSpoke.forward position)
  rw [targetBus.concreteOccurrenceSpoke.forwardBackward]

/-- Reindexing a concrete readout to another bus and back recovers it pointwise. -/
theorem transportConcreteReadout_roundTrip
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (occurrence :
      History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :
    targetBus.transportConcreteReadout sourceBus
        (sourceBus.transportConcreteReadout targetBus readout) occurrence =
      readout occurrence := by
  change
    readout
        ((sourceBus.concreteOccurrenceTransport targetBus).backward
          ((targetBus.concreteOccurrenceTransport sourceBus).backward
            occurrence)) =
      readout occurrence
  change
    readout
        ((sourceBus.concreteOccurrenceTransport targetBus).backward
          ((sourceBus.concreteOccurrenceTransport targetBus).forward
            occurrence)) =
      readout occurrence
  rw [(sourceBus.concreteOccurrenceTransport targetBus).forwardBackward]

/--
Concrete readout reindexing is pointwise independent of an intermediate bus.
This is the readout consequence of concrete occurrence transport coherence; it
adds no semantic relation between independently supplied values.
-/
theorem transportConcreteReadout_comp
    {P : CircularPresentation}
    {A B C : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (middleBus : ExactReadoutBus P B)
    (targetBus : ExactReadoutBus P C)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (occurrence :
      History.Occurrence
        (C.realizeHistory (perimeterHistory P))) :
    middleBus.transportConcreteReadout targetBus
        (sourceBus.transportConcreteReadout middleBus readout) occurrence =
      sourceBus.transportConcreteReadout targetBus readout occurrence := by
  change
    readout
        ((sourceBus.concreteOccurrenceTransport middleBus).backward
          ((middleBus.concreteOccurrenceTransport targetBus).backward
            occurrence)) =
      readout
        ((sourceBus.concreteOccurrenceTransport targetBus).backward occurrence)
  exact congrArg readout
    (concreteOccurrenceTransport_forward_comp
      targetBus middleBus sourceBus occurrence)

/-- Perimeter readouts are recovered pointwise after transport to the realization. -/
theorem toPerimeterReadout_toConcreteReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout : NonClosingPosition P.perimeter → Value)
    (position : NonClosingPosition P.perimeter) :
    bus.toPerimeterReadout (bus.toConcreteReadout readout) position =
      readout position := by
  change
    readout
      (bus.concreteOccurrenceSpoke.backward
        (bus.concreteOccurrenceSpoke.forward position)) =
      readout position
  rw [bus.concreteOccurrenceSpoke.forwardBackward]

/-- Concrete occurrence readouts are recovered pointwise after transport back. -/
theorem toConcreteReadout_toPerimeterReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (occurrence :
      History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :
    bus.toConcreteReadout (bus.toPerimeterReadout readout) occurrence =
      readout occurrence := by
  change
    readout
      (bus.concreteOccurrenceSpoke.forward
        (bus.concreteOccurrenceSpoke.backward occurrence)) =
      readout occurrence
  rw [bus.concreteOccurrenceSpoke.backwardForward]

end ExactReadoutBus

end ConstitutiveSearch.PerimeterPersistence

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.InitialFreeOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.ExtendedFreeOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.InitialConcreteOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.ExtendedConcreteOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.freeOccurrenceSplit
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.interpretationTransport
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.canonicalOneStepAlignment
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.canonicalOneStepAlignmentRealization
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.oneStepResidualFreeOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.canonicalAlignment_fresh_eq_residualFreeOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.residualFreeOccurrence_agrees_with_consumedTurning
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.oneStepResidualConcreteOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.OneStep.canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedHistory
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.successorOccurrenceSplit
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedOccurrenceSpoke
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedAlignment_one_forward
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedAlignment_one_backward
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedRealization
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iterated_extend_transport_natural
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedExtension_witness_independent
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedTransport_one_eq_oneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedTransport_one_backward_eq_oneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedRealization_one_fresh_eq_oneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedRealization_one_fresh_eq_residual
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedResidualOccurrence_transport_natural
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedResidualOccurrence_persists
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedResidualOccurrence_extension_transport_natural
#print axioms ConstitutiveSearch.PerimeterPersistence.Iterated.iteratedExtension_zero_one_eq_oneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.localExactnessReconstructsPerimeter
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactPerimeterAndFaithfulExit
#print axioms ConstitutiveSearch.PerimeterPersistence.exactPerimeterAndFaithfulExit
#print axioms ConstitutiveSearch.PerimeterPersistence.canonicalConstitutiveAlignment
#print axioms ConstitutiveSearch.PerimeterPersistence.canonicalConstitutiveAlignmentRealization
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteConstitutivePersistence
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteConstitutivePersistenceRealization
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteExtensionRealizationNaturality
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteExtensionWitnessIndependent
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteExtensionWitnessIndependentAcrossRealizations
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteDepthOneTransportMatchesOneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteDepthOneBackwardTransportMatchesOneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteDepthOneFreshMatchesOneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.oneStepAlignmentFreshIsConsumedResidual
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteOperationalResidualPersists
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteOperationalResidualNaturality
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteDepthZeroOneExtensionMatchesOneStep
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteTransportPathCoherence
#print axioms ConstitutiveSearch.PerimeterPersistence.finiteReadoutDistinctionPersists
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus
#print axioms ConstitutiveSearch.PerimeterPersistence.exactReadoutBus
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.concreteOccurrenceSpoke
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.concreteOccurrenceAt
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.concreteOccurrenceTransport
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.concreteOccurrenceTransport_atPosition
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.concreteOccurrenceTransport_forward_comp
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.exactConcreteOccurrenceTransport
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.toConcreteReadout
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.toPerimeterReadout
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.transportConcreteReadout
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.transportConcreteReadout_atPosition
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.transportConcreteReadout_roundTrip
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.transportConcreteReadout_comp
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.toPerimeterReadout_toConcreteReadout
#print axioms ConstitutiveSearch.PerimeterPersistence.ExactReadoutBus.toConcreteReadout_toPerimeterReadout
/- AXIOM_AUDIT_END -/
