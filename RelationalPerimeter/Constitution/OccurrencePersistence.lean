import ExactTypeTransport

set_option genInjectivity false

/- Independent carrier universes are intentional in the exact correspondences. -/
set_option linter.checkUnivs false

/-!
# Exact one-step constitutive alignment

This module isolates the content-independent structure extracted from the
canonical one-step persistence proof.  A constitutive transition and its
realizations remain distinct: the transition first separates prior identities
from one fresh identity, and each realization then supplies exact spokes from
those identities to its own carriers.

Admission, norms, specifications, and readout values are intentionally absent.
-/

namespace ConstitutiveSearch.OccurrencePersistence

universe uInitial uExtended

/--
An exact one-step constitutive transition.  The extended carrier consists of
all prior identities together with one distinguished fresh identity.
-/
structure ExactOneStepConstitutiveAlignment where
  Initial : Type uInitial
  Extended : Type uExtended
  extension : ExactTypeTransport (Initial ⊕ Unit) Extended

namespace ExactOneStepConstitutiveAlignment

/-- The image of a prior identity in the extended carrier. -/
def old
    (alignment : ExactOneStepConstitutiveAlignment) :
    alignment.Initial → alignment.Extended :=
  fun identity => alignment.extension.forward (.inl identity)

/-- The distinguished fresh identity of the extended carrier. -/
def fresh
    (alignment : ExactOneStepConstitutiveAlignment) :
    alignment.Extended :=
  alignment.extension.forward (.inr ())

theorem old_injective
    (alignment : ExactOneStepConstitutiveAlignment) :
    Function.Injective alignment.old := by
  intro first second equality
  have classified := congrArg alignment.extension.backward equality
  unfold old at classified
  rw [alignment.extension.forwardBackward,
    alignment.extension.forwardBackward] at classified
  exact Sum.inl.inj classified

theorem old_ne_fresh
    (alignment : ExactOneStepConstitutiveAlignment)
    (identity : alignment.Initial) :
    alignment.old identity ≠ alignment.fresh := by
  intro equality
  have classified := congrArg alignment.extension.backward equality
  unfold old fresh at classified
  rw [alignment.extension.forwardBackward,
    alignment.extension.forwardBackward] at classified
  cases classified

universe uInitialConcrete uExtendedConcrete

/--
One exact carrier realization of a constitutive transition.  The two spokes
preserve the distinction between the transition and its realization.  This
content-independent structure transports identities only; it does not by
itself assert preservation of labels, order, or step semantics.
-/
structure Realization
    (alignment : ExactOneStepConstitutiveAlignment) where
  InitialConcrete : Type uInitialConcrete
  ExtendedConcrete : Type uExtendedConcrete
  initialSpoke :
    ExactTypeTransport alignment.Initial InitialConcrete
  extendedSpoke :
    ExactTypeTransport alignment.Extended ExtendedConcrete

namespace Realization

/-- The realized image of a prior concrete identity. -/
def old
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization) :
    realization.InitialConcrete → realization.ExtendedConcrete :=
  fun concreteIdentity =>
    realization.extendedSpoke.forward
      (alignment.old
        (realization.initialSpoke.backward concreteIdentity))

/-- The realized fresh identity. -/
def fresh
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization) :
    realization.ExtendedConcrete :=
  realization.extendedSpoke.forward alignment.fresh

/-- Every exact realization inherits the exact old/fresh split. -/
def concreteSplit
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization) :
    ExactTypeTransport
      (realization.InitialConcrete ⊕ Unit)
      realization.ExtendedConcrete :=
  (realization.initialSpoke.reverse.sumUnit)
    |>.compose alignment.extension
    |>.compose realization.extendedSpoke

/-- Transport initial concrete identities through their common index. -/
def initialTransport
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization) :
    ExactTypeTransport
      source.InitialConcrete target.InitialConcrete :=
  source.initialSpoke.reverse.compose target.initialSpoke

/-- Transport extended concrete identities through their common index. -/
def extendedTransport
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization) :
    ExactTypeTransport
      source.ExtendedConcrete target.ExtendedConcrete :=
  source.extendedSpoke.reverse.compose target.extendedSpoke

/-- Prior identities commute with change of exact realization. -/
theorem old_natural
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization)
    (identity : source.InitialConcrete) :
    (source.extendedTransport target).forward (source.old identity) =
      target.old ((source.initialTransport target).forward identity) := by
  change
    target.extendedSpoke.forward
        (source.extendedSpoke.backward
          (source.extendedSpoke.forward
            (alignment.old (source.initialSpoke.backward identity)))) =
      target.extendedSpoke.forward
        (alignment.old
          (target.initialSpoke.backward
            (target.initialSpoke.forward
              (source.initialSpoke.backward identity))))
  rw [source.extendedSpoke.forwardBackward]
  rw [target.initialSpoke.forwardBackward]

/-- The fresh identity commutes with change of exact realization. -/
theorem fresh_natural
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization) :
    (source.extendedTransport target).forward source.fresh = target.fresh := by
  change
    target.extendedSpoke.forward
        (source.extendedSpoke.backward
          (source.extendedSpoke.forward alignment.fresh)) =
      target.extendedSpoke.forward alignment.fresh
  rw [source.extendedSpoke.forwardBackward]

theorem initialTransport_refl
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization)
    (identity : realization.InitialConcrete) :
    (realization.initialTransport realization).forward identity = identity :=
  realization.initialSpoke.backwardForward identity

theorem extendedTransport_refl
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization)
    (identity : realization.ExtendedConcrete) :
    (realization.extendedTransport realization).forward identity = identity :=
  realization.extendedSpoke.backwardForward identity

theorem initialTransport_forward_comp
    {alignment : ExactOneStepConstitutiveAlignment}
    (source middle target : alignment.Realization)
    (identity : source.InitialConcrete) :
    (middle.initialTransport target).forward
        ((source.initialTransport middle).forward identity) =
      (source.initialTransport target).forward identity := by
  change
    target.initialSpoke.forward
        (middle.initialSpoke.backward
          (middle.initialSpoke.forward
            (source.initialSpoke.backward identity))) =
      target.initialSpoke.forward (source.initialSpoke.backward identity)
  rw [middle.initialSpoke.forwardBackward]

theorem extendedTransport_forward_comp
    {alignment : ExactOneStepConstitutiveAlignment}
    (source middle target : alignment.Realization)
    (identity : source.ExtendedConcrete) :
    (middle.extendedTransport target).forward
        ((source.extendedTransport middle).forward identity) =
      (source.extendedTransport target).forward identity := by
  change
    target.extendedSpoke.forward
        (middle.extendedSpoke.backward
          (middle.extendedSpoke.forward
            (source.extendedSpoke.backward identity))) =
      target.extendedSpoke.forward (source.extendedSpoke.backward identity)
  rw [middle.extendedSpoke.forwardBackward]

/--
Pointwise uniqueness relative to agreement on every old identity and on the
fresh identity.
-/
theorem extendedTransport_unique_at
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization)
    (candidate : source.ExtendedConcrete → target.ExtendedConcrete)
    (onOld :
      (identity : source.InitialConcrete) →
        candidate (source.old identity) =
          target.old ((source.initialTransport target).forward identity))
    (onFresh : candidate source.fresh = target.fresh)
    (identity : source.ExtendedConcrete) :
    candidate identity =
      (source.extendedTransport target).forward identity := by
  have reconstruction := source.concreteSplit.backwardForward identity
  generalize classificationEquality :
      source.concreteSplit.backward identity = classification
  at reconstruction
  cases classification with
  | inl oldIdentity =>
      change source.old oldIdentity = identity at reconstruction
      calc
        candidate identity = candidate (source.old oldIdentity) :=
          congrArg candidate reconstruction.symm
        _ = target.old
              ((source.initialTransport target).forward oldIdentity) :=
          onOld oldIdentity
        _ = (source.extendedTransport target).forward
              (source.old oldIdentity) :=
          (source.old_natural target oldIdentity).symm
        _ = (source.extendedTransport target).forward identity :=
          congrArg (source.extendedTransport target).forward reconstruction
  | inr residual =>
      cases residual
      change source.fresh = identity at reconstruction
      calc
        candidate identity = candidate source.fresh :=
          congrArg candidate reconstruction.symm
        _ = target.fresh := onFresh
        _ = (source.extendedTransport target).forward source.fresh :=
          (source.fresh_natural target).symm
        _ = (source.extendedTransport target).forward identity :=
          congrArg (source.extendedTransport target).forward reconstruction

end Realization
end ExactOneStepConstitutiveAlignment
end ConstitutiveSearch.OccurrencePersistence


/-!
# Constitutive persistence at arbitrary natural depth

This module derives alignment at an arbitrary natural-number depth from a common constitutive index.
Every depth retains the initial identities and adds one fresh identity.  Exact
realizations are connected horizontally through that index, while prior
identities are embedded vertically into later depths.  The two directions are
proved to commute; the commuting law is not stored as additional matching data.

No admission, specification, norm, or readout value occurs in this layer.
-/

namespace ConstitutiveSearch.OccurrencePersistence

universe uInitial uCarrier uConcrete

/-- A positively constructed extension between two natural-number depths. -/
inductive DepthExtension : Nat → Nat → Type
  | refl (n : Nat) : DepthExtension n n
  | step {source target : Nat} :
      DepthExtension source target → DepthExtension source (target + 1)

namespace DepthExtension

/-- Construct the extension from depth zero to any supplied natural-number depth. -/
def zeroTo : (n : Nat) → DepthExtension 0 n
  | 0 => .refl 0
  | n + 1 => .step (zeroTo n)

/-- Compose two extensions between natural-number depths. -/
def trans
    {first middle last : Nat} :
    DepthExtension first middle →
      DepthExtension middle last →
      DepthExtension first last
  | firstToMiddle, .refl _ => firstToMiddle
  | firstToMiddle, .step middleToLast =>
      .step (trans firstToMiddle middleToLast)

/-- Forget the proof-relevant extension while retaining its arithmetic order. -/
theorem toLE
    {source target : Nat} :
    DepthExtension source target → source ≤ target
  | .refl _ => Nat.le_refl source
  | .step depth => Nat.le_succ_of_le depth.toLE

end DepthExtension

/--
The constitutive carrier at arbitrary depth `n : Nat`: initial identities together with
the `n` identities introduced by the successive extensions.
-/
def IteratedCarrier (Initial : Type uInitial) : Nat → Type uInitial
  | 0 => Initial
  | n + 1 => IteratedCarrier Initial n ⊕ Unit

namespace IteratedCarrier

/-- Preserve every existing identity in the next natural-depth carrier. -/
def embedPrevious
    {Initial : Type uInitial}
    {n : Nat} :
    IteratedCarrier Initial n → IteratedCarrier Initial (n + 1) :=
  fun identity => .inl identity

/-- The identity introduced at the transition from depth `n` to `n + 1`. -/
def freshAtStep
    {Initial : Type uInitial}
    (n : Nat) :
    IteratedCarrier Initial (n + 1) :=
  .inr ()

/-- Embed every identity from one depth into a later depth. -/
def embedFrom
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target) :
    IteratedCarrier Initial source → IteratedCarrier Initial target :=
  match depth with
  | .refl _ => fun identity => identity
  | .step prior => fun identity => .inl (embedFrom prior identity)

/-- Embed an initial identity into any natural-number constitutive depth. -/
def embedInitial
    {Initial : Type uInitial}
    (n : Nat) :
    Initial → IteratedCarrier Initial n :=
  embedFrom (DepthExtension.zeroTo n)

/--
A depth-independent structural code for identities at arbitrary natural depth.  Initial identities
retain their identity; every fresh identity retains the depth at which it was
introduced.  The code deliberately forgets the later carrier in which the
identity is observed.
-/
def identityCode
    {Initial : Type uInitial} :
    {depth : Nat} → IteratedCarrier Initial depth → Initial ⊕ Nat
  | 0, identity => .inl identity
  | _ + 1, .inl identity => identityCode identity
  | n + 1, .inr () => .inr n

theorem identityCode_fresh_lt
    {Initial : Type uInitial}
    {depth freshDepth : Nat}
    (identity : IteratedCarrier Initial depth)
    (equality : identityCode identity = Sum.inr freshDepth) :
    freshDepth < depth := by
  induction depth with
  | zero =>
      cases equality
  | succ depth inductionHypothesis =>
      cases identity with
      | inl prior =>
          exact Nat.le.step (inductionHypothesis prior equality)
      | inr fresh =>
          cases fresh
          have depthEqual : depth = freshDepth := Sum.inr.inj equality
          cases depthEqual
          exact Nat.le_refl (freshDepth + 1)

/-- The structural code loses no identity information at a fixed depth. -/
theorem identityCode_injective
    {Initial : Type uInitial}
    {depth : Nat} :
    Function.Injective (@identityCode Initial depth) := by
  induction depth with
  | zero =>
      intro first second equality
      exact Sum.inl.inj equality
  | succ depth inductionHypothesis =>
      intro first second equality
      cases first with
      | inl firstPrior =>
          cases second with
          | inl secondPrior =>
              exact congrArg Sum.inl (inductionHypothesis equality)
          | inr secondFresh =>
              cases secondFresh
              exact False.elim
                (Nat.not_succ_le_self depth
                  (identityCode_fresh_lt firstPrior equality))
      | inr firstFresh =>
          cases firstFresh
          cases second with
          | inl secondPrior =>
              exact False.elim
                (Nat.not_succ_le_self depth
                  (identityCode_fresh_lt secondPrior equality.symm))
          | inr secondFresh =>
              cases secondFresh
              rfl

/-- Every extension between natural-number depths preserves the same structural identity code. -/
theorem identityCode_embedFrom
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target)
    (identity : IteratedCarrier Initial source) :
    identityCode (embedFrom depth identity) = identityCode identity := by
  induction depth with
  | refl => rfl
  | step prior inductionHypothesis =>
      exact inductionHypothesis

/--
Fresh identities introduced at distinct depths remain distinct after embedding
into any common later carrier.
-/
theorem fresh_ne_fresh_of_depth_ne
    {Initial : Type uInitial}
    {m n target : Nat}
    (first : DepthExtension (m + 1) target)
    (second : DepthExtension (n + 1) target)
    (distinct : m ≠ n) :
    embedFrom (Initial := Initial) first (freshAtStep m) ≠
      embedFrom (Initial := Initial) second (freshAtStep n) := by
  intro equality
  have codes := congrArg identityCode equality
  rw [identityCode_embedFrom, identityCode_embedFrom] at codes
  exact distinct (Sum.inr.inj codes)

/--
The embedded identity depends only on the two depths, not on the supplied
proof-relevant path between them.  This compares the observable construction,
not the `DepthExtension` witnesses themselves.
-/
theorem embedFrom_witness_independent
    {Initial : Type uInitial}
    {source target : Nat}
    (first second : DepthExtension source target)
    (identity : IteratedCarrier Initial source) :
    embedFrom first identity = embedFrom second identity := by
  apply identityCode_injective
  exact
    (identityCode_embedFrom first identity).trans
      (identityCode_embedFrom second identity).symm

theorem embedFrom_refl
    {Initial : Type uInitial}
    {n : Nat}
    (identity : IteratedCarrier Initial n) :
    embedFrom (.refl n) identity = identity := by
  rfl

theorem embedFrom_trans
    {Initial : Type uInitial}
    {first middle last : Nat}
    (firstToMiddle : DepthExtension first middle)
    (middleToLast : DepthExtension middle last)
    (identity : IteratedCarrier Initial first) :
    embedFrom middleToLast (embedFrom firstToMiddle identity) =
      embedFrom (firstToMiddle.trans middleToLast) identity := by
  induction middleToLast with
  | refl => rfl
  | step depth inductionHypothesis =>
      exact congrArg Sum.inl inductionHypothesis

theorem embedFrom_injective
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target) :
    Function.Injective (@embedFrom Initial source target depth) := by
  induction depth with
  | refl =>
      intro first second equality
      exact equality
  | step depth inductionHypothesis =>
      intro first second equality
      exact inductionHypothesis (Sum.inl.inj equality)

theorem embedFrom_ne
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target)
    {first second : IteratedCarrier Initial source}
    (distinct : first ≠ second) :
    embedFrom depth first ≠ embedFrom depth second := by
  intro equality
  exact distinct (embedFrom_injective depth equality)

theorem embedInitial_injective
    {Initial : Type uInitial}
    (n : Nat) :
    Function.Injective (@embedInitial Initial n) :=
  embedFrom_injective (DepthExtension.zeroTo n)

/-- The exact old/fresh split between adjacent canonical carriers. -/
def oneStepTransport
    (Initial : Type uInitial)
    (n : Nat) :
    ExactTypeTransport
      (IteratedCarrier Initial n ⊕ Unit)
      (IteratedCarrier Initial (n + 1)) :=
  ExactTypeTransport.reflexive (IteratedCarrier Initial n ⊕ Unit)

/-- The adjacent transition as the existing exact one-step interface. -/
def oneStepAlignment
    (Initial : Type uInitial)
    (n : Nat) :
    ExactOneStepConstitutiveAlignment :=
  { Initial := IteratedCarrier Initial n
    Extended := IteratedCarrier Initial (n + 1)
    extension := oneStepTransport Initial n }

theorem embedPrevious_injective
    {Initial : Type uInitial}
    {n : Nat} :
    Function.Injective (@embedPrevious Initial n) :=
  (oneStepAlignment Initial n).old_injective

theorem embedPrevious_ne_fresh
    {Initial : Type uInitial}
    {n : Nat}
    (identity : IteratedCarrier Initial n) :
    embedPrevious identity ≠ freshAtStep n :=
  (oneStepAlignment Initial n).old_ne_fresh identity

/-- The old/fresh distinction survives every supplied later extension. -/
theorem embedPrevious_ne_fresh_later
    {Initial : Type uInitial}
    {n target : Nat}
    (depth : DepthExtension (n + 1) target)
    (identity : IteratedCarrier Initial n) :
    embedFrom depth (embedPrevious identity) ≠
      embedFrom depth (freshAtStep n) :=
  embedFrom_ne depth (embedPrevious_ne_fresh identity)

theorem embedPrevious_eq_embedFrom
    {Initial : Type uInitial}
    {n : Nat}
    (identity : IteratedCarrier Initial n) :
    embedPrevious identity =
      embedFrom (.step (.refl n)) identity := by
  rfl

end IteratedCarrier

/--
One carrier at an arbitrary natural-number constitutive depth, exactly indexed by the canonical
carrier at that depth.  Intermediate depths remain separate instances of this
structure rather than being collapsed into the final carrier.
-/
structure FiniteConstitutiveAlignment
    (Initial : Type uInitial)
    (depth : Nat) where
  Carrier : Type uCarrier
  carrierSpoke : ExactTypeTransport (IteratedCarrier Initial depth) Carrier

namespace FiniteConstitutiveAlignment

/-- One exact concrete realization of a constitutive carrier at an arbitrary natural-number depth. -/
structure Realization
    {Initial : Type uInitial}
    {depth : Nat}
    (alignment : FiniteConstitutiveAlignment Initial depth) where
  Concrete : Type uConcrete
  spoke : ExactTypeTransport alignment.Carrier Concrete

namespace Realization

/-- The derived spoke from the common natural-depth index to one concrete carrier. -/
def indexedSpoke
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization) :
    ExactTypeTransport (IteratedCarrier Initial depth) realization.Concrete :=
  alignment.carrierSpoke.compose realization.spoke

/-- The backward map of every exact indexed spoke is injective. -/
theorem indexedSpoke_backward_injective
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization) :
    Function.Injective realization.indexedSpoke.backward := by
  intro first second equality
  calc
    first =
        realization.indexedSpoke.forward
          (realization.indexedSpoke.backward first) :=
      (realization.indexedSpoke.backwardForward first).symm
    _ =
        realization.indexedSpoke.forward
          (realization.indexedSpoke.backward second) :=
      congrArg realization.indexedSpoke.forward equality
    _ = second :=
      realization.indexedSpoke.backwardForward second

/-- Change concrete realization at one fixed constitutive depth. -/
def transport
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization) :
    ExactTypeTransport source.Concrete target.Concrete :=
  source.indexedSpoke.reverse.compose target.indexedSpoke

/-- Extend a concrete identity from one depth to a later depth. -/
def extend
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth) :
    source.Concrete → target.Concrete :=
  fun identity =>
    target.indexedSpoke.forward
      (IteratedCarrier.embedFrom depth
        (source.indexedSpoke.backward identity))

theorem transport_atIndex
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (identity : IteratedCarrier Initial depth) :
    (source.transport target).forward (source.indexedSpoke.forward identity) =
      target.indexedSpoke.forward identity := by
  change
    target.indexedSpoke.forward
        (source.indexedSpoke.backward
          (source.indexedSpoke.forward identity)) =
      target.indexedSpoke.forward identity
  rw [source.indexedSpoke.forwardBackward]

theorem transport_roundTrip
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (identity : source.Concrete) :
    (target.transport source).forward
        ((source.transport target).forward identity) = identity := by
  exact (source.transport target).forwardBackward identity

theorem transport_comp
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source middle target : alignment.Realization)
    (identity : source.Concrete) :
    (middle.transport target).forward
        ((source.transport middle).forward identity) =
      (source.transport target).forward identity := by
  change
    target.indexedSpoke.forward
        (middle.indexedSpoke.backward
          (middle.indexedSpoke.forward
            (source.indexedSpoke.backward identity))) =
      target.indexedSpoke.forward (source.indexedSpoke.backward identity)
  rw [middle.indexedSpoke.forwardBackward]

theorem extend_atIndex
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : IteratedCarrier Initial sourceDepth) :
    source.extend target depth (source.indexedSpoke.forward identity) =
      target.indexedSpoke.forward (IteratedCarrier.embedFrom depth identity) := by
  change
    target.indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (source.indexedSpoke.backward
            (source.indexedSpoke.forward identity))) =
      target.indexedSpoke.forward (IteratedCarrier.embedFrom depth identity)
  rw [source.indexedSpoke.forwardBackward]

/-- Concrete natural-depth extension is independent of its depth witness. -/
theorem extend_witness_independent
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (first second : DepthExtension sourceDepth targetDepth)
    (identity : source.Concrete) :
    source.extend target first identity =
      source.extend target second identity := by
  exact congrArg target.indexedSpoke.forward
    (IteratedCarrier.embedFrom_witness_independent first second
      (source.indexedSpoke.backward identity))

theorem extend_refl
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization)
    (identity : realization.Concrete) :
    realization.extend realization (.refl depth) identity = identity := by
  change
    realization.indexedSpoke.forward
        (IteratedCarrier.embedFrom (.refl depth)
          (realization.indexedSpoke.backward identity)) = identity
  rw [IteratedCarrier.embedFrom_refl]
  exact realization.indexedSpoke.backwardForward identity

theorem extend_comp
    {Initial : Type uInitial}
    {firstDepth middleDepth lastDepth : Nat}
    {firstAlignment : FiniteConstitutiveAlignment Initial firstDepth}
    {middleAlignment : FiniteConstitutiveAlignment Initial middleDepth}
    {lastAlignment : FiniteConstitutiveAlignment Initial lastDepth}
    (first : firstAlignment.Realization)
    (middle : middleAlignment.Realization)
    (last : lastAlignment.Realization)
    (firstToMiddle : DepthExtension firstDepth middleDepth)
    (middleToLast : DepthExtension middleDepth lastDepth)
    (identity : first.Concrete) :
    middle.extend last middleToLast
        (first.extend middle firstToMiddle identity) =
      first.extend last (firstToMiddle.trans middleToLast) identity := by
  change
    last.indexedSpoke.forward
        (IteratedCarrier.embedFrom middleToLast
          (middle.indexedSpoke.backward
            (middle.indexedSpoke.forward
              (IteratedCarrier.embedFrom firstToMiddle
                (first.indexedSpoke.backward identity))))) =
      last.indexedSpoke.forward
        (IteratedCarrier.embedFrom (firstToMiddle.trans middleToLast)
          (first.indexedSpoke.backward identity))
  rw [middle.indexedSpoke.forwardBackward]
  rw [IteratedCarrier.embedFrom_trans]

/--
Natural-depth extension commutes with change of exact realization.  This is the
two-axis coherence law: extending then changing realization gives the same
concrete identity as changing realization then extending.
-/
theorem extend_transport_natural
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : sourceA.Concrete) :
    (targetA.transport targetB).forward
        (sourceA.extend targetA depth identity) =
      sourceB.extend targetB depth
        ((sourceA.transport sourceB).forward identity) := by
  change
    targetB.indexedSpoke.forward
        (targetA.indexedSpoke.backward
          (targetA.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceA.indexedSpoke.backward identity)))) =
      targetB.indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (sourceB.indexedSpoke.backward
            (sourceB.indexedSpoke.forward
              (sourceA.indexedSpoke.backward identity))))
  rw [targetA.indexedSpoke.forwardBackward]
  rw [sourceB.indexedSpoke.forwardBackward]

end Realization
end FiniteConstitutiveAlignment
end ConstitutiveSearch.OccurrencePersistence


/-!
# Readouts on finitely persistent constitutive carriers

Readout values are attached only after the finite constitutive carriers and
their exact realizations have been built.  The results below show that a
readout constructed by extension to an arbitrary natural-number depth retains its earlier values.  They do
not require arbitrary readouts to be injective and do not identify readouts
that were supplied independently.
-/

namespace ConstitutiveSearch.OccurrencePersistence

universe uInitial uOld uValue

/-- Extend an existing readout by one independently supplied fresh value. -/
def extendReadout
    {Old : Type uOld}
    {Value : Type uValue}
    (oldReadout : Old → Value)
    (freshValue : Value) :
    Old ⊕ Unit → Value
  | .inl old => oldReadout old
  | .inr _ => freshValue

@[simp] theorem extendReadout_old
    {Old : Type uOld}
    {Value : Type uValue}
    (oldReadout : Old → Value)
    (freshValue : Value)
    (old : Old) :
    extendReadout oldReadout freshValue (.inl old) = oldReadout old :=
  rfl

@[simp] theorem extendReadout_fresh
    {Old : Type uOld}
    {Value : Type uValue}
    (oldReadout : Old → Value)
    (freshValue : Value) :
    extendReadout oldReadout freshValue (.inr ()) = freshValue :=
  rfl

/-- Exactly the finite values introduced during `n` extensions. -/
def FiniteFreshValues (Value : Type uValue) : Nat → Type uValue
  | 0 => PUnit
  | n + 1 => FiniteFreshValues Value n × Value

namespace FiniteFreshValues

/-- Keep the prefix of values belonging to an earlier constitutive depth. -/
def take
    {Value : Type uValue}
    {source target : Nat} :
    DepthExtension source target →
      FiniteFreshValues Value target →
      FiniteFreshValues Value source
  | .refl _, values => values
  | .step depth, (prior, _) => take depth prior

theorem take_refl
    {Value : Type uValue}
    {n : Nat}
    (values : FiniteFreshValues Value n) :
    take (.refl n) values = values :=
  rfl

theorem take_trans
    {Value : Type uValue}
    {first middle last : Nat}
    (firstToMiddle : DepthExtension first middle)
    (middleToLast : DepthExtension middle last)
    (values : FiniteFreshValues Value last) :
    take firstToMiddle (take middleToLast values) =
      take (firstToMiddle.trans middleToLast) values := by
  induction middleToLast with
  | refl => rfl
  | step depth inductionHypothesis =>
      cases values with
      | mk prior fresh => exact inductionHypothesis prior

end FiniteFreshValues

/-- A readout assembled from initial values and one value per natural-depth extension. -/
def iteratedReadout
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value) :
    {n : Nat} →
      FiniteFreshValues Value n →
      IteratedCarrier Initial n →
      Value
  | 0, _, identity => initialReadout identity
  | _ + 1, (priorValues, _freshValue), .inl priorIdentity =>
      iteratedReadout initialReadout priorValues priorIdentity
  | _ + 1, (_, freshValue), .inr _ => freshValue

@[simp] theorem iteratedReadout_previous
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {n : Nat}
    (priorValues : FiniteFreshValues Value n)
    (freshValue : Value)
    (identity : IteratedCarrier Initial n) :
    iteratedReadout initialReadout (n := n + 1) (priorValues, freshValue)
        (IteratedCarrier.embedPrevious identity) =
      iteratedReadout initialReadout priorValues identity :=
  rfl

@[simp] theorem iteratedReadout_fresh
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {n : Nat}
    (priorValues : FiniteFreshValues Value n)
    (freshValue : Value) :
    iteratedReadout initialReadout (n := n + 1) (priorValues, freshValue)
        (IteratedCarrier.freshAtStep n) = freshValue :=
  rfl

/-- Values on every previously constituted identity persist to a later depth. -/
theorem iteratedReadout_embedFrom
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {source target : Nat}
    (depth : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target)
    (identity : IteratedCarrier Initial source) :
    iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom depth identity) =
      iteratedReadout initialReadout
        (FiniteFreshValues.take depth targetValues) identity := by
  induction depth with
  | refl => rfl
  | step depth inductionHypothesis =>
      cases targetValues with
      | mk priorValues freshValue =>
          exact inductionHypothesis priorValues

/--
At every earlier identity, the retained readout value depends only on the
source and target depths, not on the supplied extension witness.
-/
theorem iteratedReadout_take_witness_independent
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {source target : Nat}
    (first second : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target)
    (identity : IteratedCarrier Initial source) :
    iteratedReadout initialReadout
        (FiniteFreshValues.take first targetValues) identity =
      iteratedReadout initialReadout
        (FiniteFreshValues.take second targetValues) identity := by
  calc
    iteratedReadout initialReadout
        (FiniteFreshValues.take first targetValues) identity =
      iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom first identity) :=
          (iteratedReadout_embedFrom initialReadout first targetValues identity).symm
    _ = iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom second identity) :=
          congrArg (iteratedReadout initialReadout targetValues)
            (IteratedCarrier.embedFrom_witness_independent first second identity)
    _ = iteratedReadout initialReadout
        (FiniteFreshValues.take second targetValues) identity :=
          iteratedReadout_embedFrom initialReadout second targetValues identity

namespace FiniteFreshValues

/--
A finite value package is determined by its readout on the fresh identities.
`PEmpty` removes any unrelated initial value from this characterization.
-/
theorem eq_of_iteratedReadout_eq
    {Value : Type uValue}
    {depth : Nat}
    (first second : FiniteFreshValues Value depth)
    (agreement :
      (identity : IteratedCarrier (PEmpty : Type) depth) →
        iteratedReadout (Initial := PEmpty) PEmpty.elim first identity =
          iteratedReadout (Initial := PEmpty) PEmpty.elim second identity) :
    first = second := by
  induction depth with
  | zero =>
      cases first
      cases second
      rfl
  | succ depth inductionHypothesis =>
      cases first with
      | mk firstPrior firstFresh =>
          cases second with
          | mk secondPrior secondFresh =>
              have priorEqual : firstPrior = secondPrior :=
                inductionHypothesis firstPrior secondPrior
                  (fun identity => agreement (.inl identity))
              have freshEqual : firstFresh = secondFresh :=
                agreement (.inr ())
              cases priorEqual
              cases freshEqual
              rfl

/-- The retained finite value package is independent of the depth witness. -/
theorem take_witness_independent
    {Value : Type uValue}
    {source target : Nat}
    (first second : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target) :
    take first targetValues = take second targetValues := by
  apply eq_of_iteratedReadout_eq
  intro identity
  exact iteratedReadout_take_witness_independent
    (Initial := PEmpty) PEmpty.elim first second targetValues identity

end FiniteFreshValues

/-- A distinction already made by a readout persists through extension to an arbitrary natural-number depth. -/
theorem iteratedReadout_distinction
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {source target : Nat}
    (depth : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target)
    (first second : IteratedCarrier Initial source)
    (distinguished :
      iteratedReadout initialReadout
          (FiniteFreshValues.take depth targetValues) first ≠
        iteratedReadout initialReadout
          (FiniteFreshValues.take depth targetValues) second) :
    iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom depth first) ≠
      iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom depth second) := by
  intro collapsed
  apply distinguished
  rw [← iteratedReadout_embedFrom initialReadout depth targetValues first]
  rw [← iteratedReadout_embedFrom initialReadout depth targetValues second]
  exact collapsed

namespace FiniteConstitutiveAlignment.Realization

/-- Read a canonical finite value assignment on one exact realization. -/
def realizeReadout
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization)
    (readout : IteratedCarrier Initial depth → Value) :
    realization.Concrete → Value :=
  fun identity => readout (realization.indexedSpoke.backward identity)

theorem realizeReadout_atIndex
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization)
    (readout : IteratedCarrier Initial depth → Value)
    (identity : IteratedCarrier Initial depth) :
    realization.realizeReadout readout
        (realization.indexedSpoke.forward identity) = readout identity := by
  change
    readout
        (realization.indexedSpoke.backward
          (realization.indexedSpoke.forward identity)) = readout identity
  rw [realization.indexedSpoke.forwardBackward]

/-- Reindex a concrete readout through the shared finite constitutive carrier. -/
def transportReadout
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (readout : source.Concrete → Value) :
    target.Concrete → Value :=
  fun identity => readout ((source.transport target).backward identity)

theorem transportReadout_atIndex
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (readout : source.Concrete → Value)
    (identity : IteratedCarrier Initial depth) :
    source.transportReadout target readout
        (target.indexedSpoke.forward identity) =
      readout (source.indexedSpoke.forward identity) := by
  change
    readout
        (source.indexedSpoke.forward
          (target.indexedSpoke.backward
            (target.indexedSpoke.forward identity))) =
      readout (source.indexedSpoke.forward identity)
  rw [target.indexedSpoke.forwardBackward]

theorem transportReadout_roundTrip
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (readout : source.Concrete → Value)
    (identity : source.Concrete) :
    target.transportReadout source
        (source.transportReadout target readout) identity = readout identity := by
  change
    readout
        ((source.transport target).backward
          ((target.transport source).backward identity)) = readout identity
  change
    readout
        ((source.transport target).backward
          ((source.transport target).forward identity)) = readout identity
  rw [(source.transport target).forwardBackward]

theorem transportReadout_comp
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source middle target : alignment.Realization)
    (readout : source.Concrete → Value)
    (identity : target.Concrete) :
    middle.transportReadout target
        (source.transportReadout middle readout) identity =
      source.transportReadout target readout identity := by
  change
    readout
        (source.indexedSpoke.forward
          (middle.indexedSpoke.backward
            (middle.indexedSpoke.forward
              (target.indexedSpoke.backward identity)))) =
      readout
        (source.indexedSpoke.forward
          (target.indexedSpoke.backward identity))
  rw [middle.indexedSpoke.forwardBackward]

/--
A finitely assembled readout persists on concrete identities extended from any
earlier depth.
-/
theorem realizeIteratedReadout_extend
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (targetValues : FiniteFreshValues Value targetDepth)
    (identity : source.Concrete) :
    target.realizeReadout (iteratedReadout initialReadout targetValues)
        (source.extend target depth identity) =
      source.realizeReadout
        (iteratedReadout initialReadout
          (FiniteFreshValues.take depth targetValues)) identity := by
  change
    iteratedReadout initialReadout targetValues
        (target.indexedSpoke.backward
          (target.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (source.indexedSpoke.backward identity)))) =
      iteratedReadout initialReadout
        (FiniteFreshValues.take depth targetValues)
        (source.indexedSpoke.backward identity)
  rw [target.indexedSpoke.forwardBackward]
  exact iteratedReadout_embedFrom initialReadout depth targetValues
    (source.indexedSpoke.backward identity)

theorem realizeIteratedReadout_distinction
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (targetValues : FiniteFreshValues Value targetDepth)
    (first second : source.Concrete)
    (distinguished :
      source.realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) first ≠
        source.realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) second) :
    target.realizeReadout (iteratedReadout initialReadout targetValues)
        (source.extend target depth first) ≠
      target.realizeReadout (iteratedReadout initialReadout targetValues)
        (source.extend target depth second) := by
  intro collapsed
  apply distinguished
  rw [← realizeIteratedReadout_extend initialReadout source target depth
    targetValues first]
  rw [← realizeIteratedReadout_extend initialReadout source target depth
    targetValues second]
  exact collapsed

end FiniteConstitutiveAlignment.Realization
end ConstitutiveSearch.OccurrencePersistence

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.old_injective
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.old_ne_fresh
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization.concreteSplit
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization.old_natural
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization.fresh_natural
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization.initialTransport_forward_comp
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization.extendedTransport_forward_comp
#print axioms ConstitutiveSearch.OccurrencePersistence.ExactOneStepConstitutiveAlignment.Realization.extendedTransport_unique_at
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.oneStepTransport
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.identityCode_injective
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.identityCode_embedFrom
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.fresh_ne_fresh_of_depth_ne
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.embedFrom_witness_independent
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.embedFrom_injective
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.embedInitial_injective
#print axioms ConstitutiveSearch.OccurrencePersistence.IteratedCarrier.embedPrevious_ne_fresh_later
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.indexedSpoke_backward_injective
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.extend_witness_independent
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.extend_comp
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.extend_transport_natural
#print axioms ConstitutiveSearch.OccurrencePersistence.iteratedReadout_embedFrom
#print axioms ConstitutiveSearch.OccurrencePersistence.iteratedReadout_take_witness_independent
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteFreshValues.eq_of_iteratedReadout_eq
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteFreshValues.take_witness_independent
#print axioms ConstitutiveSearch.OccurrencePersistence.iteratedReadout_distinction
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.transportReadout_comp
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.realizeIteratedReadout_extend
#print axioms ConstitutiveSearch.OccurrencePersistence.FiniteConstitutiveAlignment.Realization.realizeIteratedReadout_distinction
/- AXIOM_AUDIT_END -/
