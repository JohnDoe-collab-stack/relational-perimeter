import RelationalPerimeter.Relativity.Production.ConstitutedReadingConstraints

/-!
# Executable finite covers of constituted numerical readings

The only branching rule uses positively ordered overlapping rational windows.
Its chooser reads the certified value, then refines that same certificate.
Finite composition records the selected leaf; restriction returns the original
reading. This covers readings of an actual attached port, not physical places.
Overlap is neither an equality of sources nor a memory-erasure authorization.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production

theorem rational_not_strict {one two : Rational} (notBelow : ¬ RationalStrictLess one two) :
    Rational.Le two one := by
  cases Rational.le_total one two with
  | inr below => exact below
  | inl below =>
    by_cases same : one = two
    · exact same ▸ Rational.le_refl one
    · exact False.elim (notBelow ⟨below, same⟩)

/-- The three strict comparisons are the rule's justification, not an
arbitrary covering relation. They include a genuine overlap and strict shrink. -/
structure OverlappingWindowSplit (window : ReadingWindow) where
  lowerCut : Rational
  upperCut : Rational
  lowerInside : RationalStrictLess window.lower lowerCut
  overlap : RationalStrictLess lowerCut upperCut
  upperInside : RationalStrictLess upperCut window.upper

def OverlappingWindowSplit.left {window} (split : OverlappingWindowSplit window) : ReadingWindow :=
  ⟨window.lower, split.upperCut⟩

def OverlappingWindowSplit.right {window} (split : OverlappingWindowSplit window) : ReadingWindow :=
  ⟨split.lowerCut, window.upper⟩

theorem OverlappingWindowSplit.leftRefinement {window} (split : OverlappingWindowSplit window) :
    WindowRefinement window split.left := ⟨Rational.le_refl _, split.upperInside.1⟩

theorem OverlappingWindowSplit.rightRefinement {window} (split : OverlappingWindowSplit window) :
    WindowRefinement window split.right := ⟨split.lowerInside.1, Rational.le_refl _⟩

theorem split_windows_strictly_shrink {window} (split : OverlappingWindowSplit window) :
    RationalStrictLess split.left.span window.span ∧ RationalStrictLess split.right.span window.span := by
  constructor
  · refine ⟨split.leftRefinement.span_le, ?_⟩
    intro same
    have cancelled := congrArg (fun value => Rational.add value window.lower) same
    change Rational.add (Rational.sub split.upperCut window.lower) window.lower =
      Rational.add (Rational.sub window.upper window.lower) window.lower at cancelled
    rw [Rational.sub, Rational.sub, Rational.add_assoc, Rational.add_assoc,
      Rational.neg_add_cancel, Rational.add_zero, Rational.add_zero] at cancelled
    exact split.upperInside.2 cancelled
  · refine ⟨split.rightRefinement.span_le, ?_⟩
    intro same
    have cancelled := congrArg (fun value => Rational.add (Rational.neg window.upper) value) same
    change Rational.add (Rational.neg window.upper) (Rational.sub window.upper split.lowerCut) =
      Rational.add (Rational.neg window.upper) (Rational.sub window.upper window.lower) at cancelled
    rw [Rational.sub, Rational.sub, ← Rational.add_assoc, ← Rational.add_assoc,
      Rational.neg_add_cancel, Rational.zero_add, Rational.zero_add] at cancelled
    have cuts := congrArg Rational.neg cancelled
    rw [Rational.neg_neg, Rational.neg_neg] at cuts
    exact split.lowerInside.2 cuts.symm

theorem split_contains_overlap {window} (split : OverlappingWindowSplit window) {value}
    (inside : (ReadingWindow.mk split.lowerCut split.upperCut).Contains value) :
    split.left.Contains value ∧ split.right.Contains value :=
  ⟨⟨rational_le_strict split.lowerInside.1 inside.1, inside.2⟩,
    ⟨inside.1, rational_strict_le inside.2 split.upperInside.1⟩⟩

theorem split_cover_exact {window} (split : OverlappingWindowSplit window) (value : Rational) :
    window.Contains value ↔ split.left.Contains value ∨ split.right.Contains value := by
  constructor
  · intro inside
    by_cases below : RationalStrictLess value split.upperCut
    · exact .inl ⟨inside.1, below⟩
    · exact .inr ⟨rational_strict_le split.overlap (rational_not_strict below), inside.2⟩
  · intro inside
    cases inside with
    | inl left => exact split.leftRefinement.contains left
    | inr right => exact split.rightRefinement.contains right

/-- In the overlap the left branch is chosen. At its excluded upper boundary
the right branch is chosen. No branch is supplied by the caller. -/
def OverlappingWindowSplit.choose {source pair head current attached port window}
    (split : OverlappingWindowSplit window)
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    PSum (CertifiedNumericReading attached port split.left) (CertifiedNumericReading attached port split.right) :=
  if below : RationalStrictLess reading.value split.upperCut then
    .inl ⟨reading.value, reading.valueExact, reading.inside.1, below⟩
  else
    .inr ⟨reading.value, reading.valueExact,
      rational_strict_le split.overlap (rational_not_strict below), reading.inside.2⟩

inductive InstrumentalReadingCover : ReadingWindow → Type where
  | identity (window : ReadingWindow) : InstrumentalReadingCover window
  | split {window} (division : OverlappingWindowSplit window)
      (first : InstrumentalReadingCover division.left) (second : InstrumentalReadingCover division.right) :
      InstrumentalReadingCover window

/-- A positive derivation of membership in the finite cover, not a free window. -/
inductive InstrumentalReadingCover.Leaf : {window : ReadingWindow} →
    InstrumentalReadingCover window → ReadingWindow → Type where
  | here {window} : Leaf (.identity window) window
  | left {window division first second fine} (past : @Leaf division.left first fine) :
      Leaf (@InstrumentalReadingCover.split window division first second) fine
  | right {window division first second fine} (past : @Leaf division.right second fine) :
      Leaf (@InstrumentalReadingCover.split window division first second) fine

theorem InstrumentalReadingCover.Leaf.refinement {window cover fine}
    (leaf : @InstrumentalReadingCover.Leaf window cover fine) : WindowRefinement window fine :=
  match leaf with
  | .here => .identity window
  | .left (division := division) past => division.leftRefinement.compose past.refinement
  | .right (division := division) past => division.rightRefinement.compose past.refinement

def InstrumentalReadingCover.Leaf.branches {window cover fine}
    (leaf : @InstrumentalReadingCover.Leaf window cover fine) : List Bool :=
  match leaf with
  | .here => []
  | .left past => true :: past.branches
  | .right past => false :: past.branches

structure CoveredNumericReading {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    {window : ReadingWindow} (cover : InstrumentalReadingCover window) where
  window : ReadingWindow
  leaf : cover.Leaf window
  reading : CertifiedNumericReading attached port window

def InstrumentalReadingCover.select {source pair head current attached port window}
    (cover : InstrumentalReadingCover window)
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    CoveredNumericReading attached port cover :=
  match cover with
  | .identity _ => ⟨window, .here, reading⟩
  | .split division first second =>
    match division.choose reading with
    | .inl narrowed =>
      let chosen := first.select narrowed
      ⟨chosen.window, .left chosen.leaf, chosen.reading⟩
    | .inr narrowed =>
      let chosen := second.select narrowed
      ⟨chosen.window, .right chosen.leaf, chosen.reading⟩
termination_by structural cover

theorem selected_cover_value {source pair head current attached port window}
    (cover : InstrumentalReadingCover window)
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    (cover.select reading).reading.value = reading.value :=
  (cover.select reading).reading.valueExact.trans reading.valueExact.symm

theorem certified_numeric_reading_ext {source pair head current attached port window}
    (one two : @CertifiedNumericReading source pair head current attached port window)
    (same : one.value = two.value) : one = two := by
  cases one; cases two; cases same; rfl

def CoveredNumericReading.restrict {source pair head current attached port window cover}
    (chosen : @CoveredNumericReading source pair head current attached port window cover) :
    CertifiedNumericReading attached port window := chosen.reading.restrict chosen.leaf.refinement

theorem selected_cover_restricts_to_source {source pair head current attached port window}
    (cover : InstrumentalReadingCover window)
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    (cover.select reading).restrict = reading :=
  certified_numeric_reading_ext _ _ (selected_cover_value cover reading)

def CoveredNumericReading.prolong {source pair head current target attached port window cover}
    (chosen : @CoveredNumericReading source pair head current attached port window cover)
    (history : RecurringHistory current target) : CoveredNumericReading (attached.prolong history) port cover :=
  ⟨chosen.window, chosen.leaf, chosen.reading.prolong history⟩

def CoveredNumericReading.transport {source pair head current target one two port}
    {window : ReadingWindow} {cover : InstrumentalReadingCover window}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (chosen : CoveredNumericReading one port cover) : CoveredNumericReading two port cover :=
  ⟨chosen.window, chosen.leaf, chosen.reading.transport agreement⟩

theorem cover_selection_prolong_square {source pair head current target attached port window}
    (cover : InstrumentalReadingCover window)
    (reading : @CertifiedNumericReading source pair head current attached port window)
    (history : RecurringHistory current target) :
    (cover.select reading).prolong history = cover.select (reading.prolong history) := by
  induction cover with
  | identity => rfl
  | split division first second ihFirst ihSecond =>
    rw [InstrumentalReadingCover.select, InstrumentalReadingCover.select]
    dsimp only [OverlappingWindowSplit.choose, CertifiedNumericReading.prolong,
      OverlappingWindowSplit.left, OverlappingWindowSplit.right, ReadingWindow.Contains]
    by_cases below : RationalStrictLess reading.value division.upperCut
    · simp only [dif_pos below]
      exact congrArg (fun chosen => CoveredNumericReading.mk chosen.window (.left chosen.leaf) chosen.reading) (ihFirst _)
    · simp only [dif_neg below]
      exact congrArg (fun chosen => CoveredNumericReading.mk chosen.window (.right chosen.leaf) chosen.reading) (ihSecond _)

theorem cover_selection_transport_square {source pair head current target one two port window}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (cover : InstrumentalReadingCover window) (reading : CertifiedNumericReading one port window) :
    (cover.select reading).transport agreement = cover.select (reading.transport agreement) := by
  induction cover with
  | identity => rfl
  | split division first second ihFirst ihSecond =>
    rw [InstrumentalReadingCover.select, InstrumentalReadingCover.select]
    dsimp only [OverlappingWindowSplit.choose, CertifiedNumericReading.transport,
      OverlappingWindowSplit.left, OverlappingWindowSplit.right, ReadingWindow.Contains]
    by_cases below : RationalStrictLess reading.value division.upperCut
    · simp only [dif_pos below]
      exact congrArg (fun chosen => CoveredNumericReading.mk chosen.window (.left chosen.leaf) chosen.reading) (ihFirst _)
    · simp only [dif_neg below]
      exact congrArg (fun chosen => CoveredNumericReading.mk chosen.window (.right chosen.leaf) chosen.reading) (ihSecond _)

theorem covered_continuation_square {source pair head current target one two port}
    {window : ReadingWindow} {cover : InstrumentalReadingCover window}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord)
    (chosen : CoveredNumericReading one port cover) :
    (chosen.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (chosen.transport agreement).prolong extension.execution.second.history := by
  cases chosen; rfl

theorem covered_prolong_restriction_square {source pair head current target attached port window cover}
    (chosen : @CoveredNumericReading source pair head current attached port window cover)
    (history : RecurringHistory current target) :
    (chosen.prolong history).restrict = chosen.restrict.prolong history := rfl

theorem covered_transport_restriction_square {source pair head current target one two port}
    {window : ReadingWindow} {cover : InstrumentalReadingCover window}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (chosen : CoveredNumericReading one port cover) :
    (chosen.transport agreement).restrict = chosen.restrict.transport agreement := rfl

/-- Replacing every leaf by another justified finite cover. This is composition
of descriptions; the family argument is not a future input to any producer. -/
def InstrumentalReadingCover.refine (cover : InstrumentalReadingCover window)
    (next : (fine : ReadingWindow) → InstrumentalReadingCover fine) : InstrumentalReadingCover window :=
  match cover with
  | .identity fine => next fine
  | .split division first second => .split division (first.refine next) (second.refine next)
termination_by structural cover

theorem cover_refine_identity (cover : InstrumentalReadingCover window) :
    cover.refine InstrumentalReadingCover.identity = cover := by
  induction cover with
  | identity => rfl
  | split division first second ihFirst ihSecond =>
    change InstrumentalReadingCover.split division _ _ = _
    rw [ihFirst, ihSecond]

theorem cover_refine_associates (cover : InstrumentalReadingCover window)
    (first second : (fine : ReadingWindow) → InstrumentalReadingCover fine) :
    (cover.refine first).refine second = cover.refine (fun fine => (first fine).refine second) := by
  induction cover with
  | identity => rfl
  | split division one two ihOne ihTwo =>
    change InstrumentalReadingCover.split division _ _ = _
    rw [ihOne, ihTwo]
    rfl

/-- Refining one clause retains the jointly certified suffix on the same
attachment; a cover is not a license to forget the other constraints. -/
structure CoveredConstraintHead {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    {window : ReadingWindow} (cover : InstrumentalReadingCover window) (rest : List AttachedReadingConstraint) where
  chosen : CoveredNumericReading attached port cover
  tail : CertifiedReadingConstraints attached rest

def coverConstraintHead {source pair head current attached port window rest}
    (cover : InstrumentalReadingCover window)
    (readings : @CertifiedReadingConstraints source pair head current attached (⟨port, window⟩ :: rest)) :
    CoveredConstraintHead attached port cover rest :=
  match readings with
  | .cons reading tail => ⟨cover.select reading, tail⟩

def CoveredConstraintHead.refined {source pair head current attached port window cover rest}
    (covered : @CoveredConstraintHead source pair head current attached port window cover rest) :
    CertifiedReadingConstraints attached (⟨port, covered.chosen.window⟩ :: rest) :=
  .cons covered.chosen.reading covered.tail

def CoveredConstraintHead.restrict {source pair head current attached port window cover rest}
    (covered : @CoveredConstraintHead source pair head current attached port window cover rest) :
    CertifiedReadingConstraints attached (⟨port, window⟩ :: rest) :=
  .cons covered.chosen.restrict covered.tail

theorem constraint_cover_restricts_to_source {source pair head current attached port window rest}
    (cover : InstrumentalReadingCover window)
    (readings : @CertifiedReadingConstraints source pair head current attached (⟨port, window⟩ :: rest)) :
    (coverConstraintHead cover readings).restrict = readings := by
  cases readings with
  | cons reading tail =>
    exact congrArg (fun actual => CertifiedReadingConstraints.cons actual tail)
      (selected_cover_restricts_to_source cover reading)

theorem constraint_cover_preserves_all_values {source pair head current attached port window rest}
    (cover : InstrumentalReadingCover window)
    (readings : @CertifiedReadingConstraints source pair head current attached (⟨port, window⟩ :: rest)) :
    (coverConstraintHead cover readings).refined.values = readings.values := by
  cases readings with
  | cons reading tail => exact congrArg (fun value => value :: tail.values) (selected_cover_value cover reading)

/-- Pulling the choice back to an already certified fine window constructs
its actual intersection, not a presumed compatibility of free constraints. -/
def coveredWindowIntersection {source pair head current attached port coarse fine}
    (cover : InstrumentalReadingCover coarse) (refinement : WindowRefinement coarse fine)
    (reading : @CertifiedNumericReading source pair head current attached port fine) :
    CertifiedNumericReading attached port ((cover.select (reading.restrict refinement)).window.intersection fine) :=
  (cover.select (reading.restrict refinement)).reading.common reading

theorem covered_intersection_restrictions {source pair head current attached port coarse fine}
    (cover : InstrumentalReadingCover coarse) (refinement : WindowRefinement coarse fine)
    (reading : @CertifiedNumericReading source pair head current attached port fine) :
    (coveredWindowIntersection cover refinement reading).restrict
        (window_intersection_left _ _) = (cover.select (reading.restrict refinement)).reading ∧
      (coveredWindowIntersection cover refinement reading).restrict (window_intersection_right _ _) = reading :=
  numeric_common_restrictions (cover.select (reading.restrict refinement)).reading reading

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.rational_not_strict
#print axioms RelationalPerimeter.Relativity.Production.OverlappingWindowSplit
#print axioms RelationalPerimeter.Relativity.Production.split_windows_strictly_shrink
#print axioms RelationalPerimeter.Relativity.Production.split_contains_overlap
#print axioms RelationalPerimeter.Relativity.Production.split_cover_exact
#print axioms RelationalPerimeter.Relativity.Production.OverlappingWindowSplit.choose
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.Leaf
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.Leaf.refinement
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.Leaf.branches
#print axioms RelationalPerimeter.Relativity.Production.CoveredNumericReading
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.select
#print axioms RelationalPerimeter.Relativity.Production.selected_cover_value
#print axioms RelationalPerimeter.Relativity.Production.certified_numeric_reading_ext
#print axioms RelationalPerimeter.Relativity.Production.CoveredNumericReading.restrict
#print axioms RelationalPerimeter.Relativity.Production.selected_cover_restricts_to_source
#print axioms RelationalPerimeter.Relativity.Production.CoveredNumericReading.prolong
#print axioms RelationalPerimeter.Relativity.Production.CoveredNumericReading.transport
#print axioms RelationalPerimeter.Relativity.Production.cover_selection_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.cover_selection_transport_square
#print axioms RelationalPerimeter.Relativity.Production.covered_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.covered_prolong_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.covered_transport_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.refine
#print axioms RelationalPerimeter.Relativity.Production.cover_refine_identity
#print axioms RelationalPerimeter.Relativity.Production.cover_refine_associates
#print axioms RelationalPerimeter.Relativity.Production.CoveredConstraintHead
#print axioms RelationalPerimeter.Relativity.Production.coverConstraintHead
#print axioms RelationalPerimeter.Relativity.Production.CoveredConstraintHead.refined
#print axioms RelationalPerimeter.Relativity.Production.CoveredConstraintHead.restrict
#print axioms RelationalPerimeter.Relativity.Production.constraint_cover_restricts_to_source
#print axioms RelationalPerimeter.Relativity.Production.constraint_cover_preserves_all_values
#print axioms RelationalPerimeter.Relativity.Production.coveredWindowIntersection
#print axioms RelationalPerimeter.Relativity.Production.covered_intersection_restrictions
/- AXIOM_AUDIT_END -/
