import RelationalPerimeter.Relativity.Production.ProductiveRelativePresentations
import RelationalPerimeter.Relativity.Production.PreciseReadingRefinements

/-!
# Open instrumental windows on generated relative presentations

A finite certificate bounds the complete produced bracket strictly inside
an existing open window. It survives actual resumption, not just a readout
equality. Bounded searches distinguish a failed budget from global absence.
Cover selection consumes stored prefixes and the positive overlap rule.
These constructions supply no physical location or memory-erasure license.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

def ReadingWindow.BracketContains {cursor : Cursor} (window : ReadingWindow)
    (reading : RelativePathReading cursor) : Prop :=
  RationalStrictLess window.lower reading.value ∧ RationalStrictLess reading.upper window.upper

instance {cursor : Cursor} (window : ReadingWindow) (reading : RelativePathReading cursor) :
    Decidable (window.BracketContains reading) :=
  inferInstanceAs (Decidable (RationalStrictLess _ _ ∧ RationalStrictLess _ _))

theorem bracket_contains_endpoints {cursor} {window : ReadingWindow} {reading : RelativePathReading cursor}
    (inside : window.BracketContains reading) :
    window.Contains reading.value ∧ window.Contains reading.upper :=
  ⟨⟨inside.1, rational_le_strict (relative_bracket_ordered reading) inside.2⟩,
    ⟨rational_strict_le inside.1 (relative_bracket_ordered reading), inside.2⟩⟩

theorem bracket_contains_every_between_reading {cursor} {window : ReadingWindow}
    {reading : RelativePathReading cursor} (inside : window.BracketContains reading)
    (value : Rational) (lower : Rational.Le reading.value value) (upper : Rational.Le value reading.upper) :
    window.Contains value := ⟨rational_strict_le inside.1 lower, rational_le_strict upper inside.2⟩

structure ProductiveWindowCertificate {source : RelativePathState}
    (presentation : RelativePathPresentation source) (window : ReadingWindow) where
  depth : Nat
  realization : RelativeRefinementRun source
  realizationExact : realization = presentation.realize depth
  inside : window.BracketContains realization.state.reading

def ProductiveWindowCertificate.advance {source presentation window}
    (certificate : @ProductiveWindowCertificate source presentation window) (steps : Nat) :
    ProductiveWindowCertificate presentation window :=
  let produced := certificate.realization.evolve presentation.rule steps
  ⟨certificate.depth + steps, produced,
    (congrArg (fun run => run.evolve presentation.rule steps) certificate.realizationExact).trans
      (relative_evolution_compose presentation.stored presentation.rule certificate.depth steps),
    rational_strict_le certificate.inside.1 (relative_evolution_brackets certificate.realization presentation.rule steps).1,
    rational_le_strict (relative_evolution_brackets certificate.realization presentation.rule steps).2 certificate.inside.2⟩

theorem productive_window_advance_exact {source presentation window}
    (certificate : @ProductiveWindowCertificate source presentation window) (steps : Nat) :
    (certificate.advance steps).realization = certificate.realization.evolve presentation.rule steps := rfl

theorem productive_window_all_later_readings {source presentation window}
    (certificate : @ProductiveWindowCertificate source presentation window) (steps : Nat) :
    window.Contains (presentation.realize (certificate.depth + steps)).state.reading.value := by
  have inside := (bracket_contains_endpoints (certificate.advance steps).inside).1
  rw [(certificate.advance steps).realizationExact] at inside
  exact inside

def ProductiveWindowCertificate.restrict {source presentation coarse fine}
    (certificate : @ProductiveWindowCertificate source presentation fine)
    (refinement : WindowRefinement coarse fine) : ProductiveWindowCertificate presentation coarse :=
  ⟨certificate.depth, certificate.realization, certificate.realizationExact,
    rational_le_strict refinement.lower certificate.inside.1,
    rational_strict_le certificate.inside.2 refinement.upper⟩

theorem productive_window_restriction_identity {source presentation window}
    (certificate : @ProductiveWindowCertificate source presentation window) :
    certificate.restrict (.identity window) = certificate := by cases certificate; rfl

theorem productive_window_restrictions_compose {source presentation one two three}
    (certificate : @ProductiveWindowCertificate source presentation three)
    (first : WindowRefinement one two) (second : WindowRefinement two three) :
    (certificate.restrict second).restrict first = certificate.restrict (first.compose second) := rfl

def ProductiveWindowCertificate.common {source presentation one two}
    (first : @ProductiveWindowCertificate source presentation one)
    (second : ProductiveWindowCertificate presentation two) :
    ProductiveWindowCertificate presentation (one.intersection two) := by
  let left := first.advance second.depth
  have right := (second.advance first.depth).inside
  have same : (second.advance first.depth).realization = left.realization :=
    (second.advance first.depth).realizationExact.trans
      ((congrArg presentation.realize (Nat.add_comm second.depth first.depth)).trans left.realizationExact.symm)
  rw [same] at right
  have lower := window_intersection_contains (bracket_contains_endpoints left.inside).1
    (bracket_contains_endpoints right).1
  have upper := window_intersection_contains (bracket_contains_endpoints left.inside).2
    (bracket_contains_endpoints right).2
  exact ⟨left.depth, left.realization, left.realizationExact, lower.1, upper.2⟩

theorem productive_common_uses_the_returned_prefix {source presentation one two}
    (first : @ProductiveWindowCertificate source presentation one)
    (second : ProductiveWindowCertificate presentation two) :
    (first.common second).realization = first.realization.evolve presentation.rule second.depth := rfl

def ProductiveWindowCertificate.toResumed {source presentation window}
    (certificate : @ProductiveWindowCertificate source presentation window) (steps : Nat) :
    ProductiveWindowCertificate (presentation.resume steps) window :=
  let produced := certificate.advance steps
  ⟨certificate.depth, produced.realization,
    produced.realizationExact.trans ((congrArg presentation.realize (Nat.add_comm certificate.depth steps)).trans
      (relative_presentation_resume_exact presentation steps certificate.depth).symm), produced.inside⟩

def ProductiveWindowCertificate.fromResumed {source}
    {presentation : RelativePathPresentation source} {window} (steps : Nat)
    (certificate : ProductiveWindowCertificate (presentation.resume steps) window) :
    ProductiveWindowCertificate presentation window :=
  ⟨steps + certificate.depth, certificate.realization,
    certificate.realizationExact.trans (relative_presentation_resume_exact presentation steps certificate.depth),
    certificate.inside⟩

theorem productive_window_resumption_iff {source} (presentation : RelativePathPresentation source)
    (window : ReadingWindow) (steps : Nat) :
    Nonempty (ProductiveWindowCertificate presentation window) ↔
      Nonempty (ProductiveWindowCertificate (presentation.resume steps) window) :=
  ⟨fun ⟨certificate⟩ => ⟨certificate.toResumed steps⟩,
    fun ⟨certificate⟩ => ⟨ProductiveWindowCertificate.fromResumed steps certificate⟩⟩

def RelativePathReading.bracketWindow {cursor} (reading : RelativePathReading cursor) : ReadingWindow :=
  let precision : Precision := ⟨1, reading.denominator.relayCount, Nat.zero_lt_succ 0, reading.positiveScale⟩
  ⟨(ReadingWindow.atPrecision reading.value precision).lower,
    (ReadingWindow.atPrecision reading.upper precision).upper⟩

theorem produced_bracket_window_contains {cursor} (reading : RelativePathReading cursor) :
    reading.bracketWindow.BracketContains reading := by
  let precision : Precision := ⟨1, reading.denominator.relayCount,
    Nat.zero_lt_succ 0, reading.positiveScale⟩
  exact ⟨(precision_window_contains reading.value precision).1,
    (precision_window_contains reading.upper precision).2⟩

def RelativePathPresentation.initialWindow {source} (presentation : RelativePathPresentation source) :
    ProductiveWindowCertificate presentation presentation.stored.state.reading.bracketWindow :=
  ⟨0, presentation.stored, rfl, produced_bracket_window_contains _⟩

private def gapLeft (one two : Rational) : Nat :=
  one.representation.numerator.positive * two.representation.denominator +
    two.representation.numerator.negative * one.representation.denominator

private def gapRight (one two : Rational) : Nat := gapLeft two one

private theorem gap_ordered {one two : Rational} (strict : RationalStrictLess one two) :
    gapLeft one two < gapRight one two := by
  have ordered : gapLeft one two ≤ gapRight one two := strict.1
  cases Nat.lt_or_eq_of_le ordered with
  | inl lower => exact lower
  | inr same => exact False.elim (strict.2 (Rational.equal_of_agree same))

def strictReadingGap (one two : Rational) (strict : RationalStrictLess one two) : Precision :=
  ⟨gapRight one two - gapLeft one two,
    one.representation.denominator * two.representation.denominator,
    Nat.pos_of_ne_zero (fun zero => by
      have rebuild := Natural.sub_add_of_le (Nat.le_of_lt (gap_ordered strict))
      rw [zero, Nat.zero_add] at rebuild
      exact (Nat.ne_of_lt (gap_ordered strict)) rebuild),
    Nat.mul_pos one.representation.positive two.representation.positive⟩

theorem strict_reading_gap_value (one two : Rational) (strict : RationalStrictLess one two) :
    (strictReadingGap one two strict).value = Rational.sub two one := by
  apply Rational.equal_of_agree
  apply Fraction.trans (Rational.normalize_agrees _)
  apply Fraction.trans _ (Fraction.symm (Rational.sub_representation_agrees two one))
  have rebuild := Natural.sub_add_of_le (Nat.le_of_lt (gap_ordered strict))
  unfold Precision.fraction strictReadingGap Fraction.Agree Fraction.sub Fraction.add Fraction.neg
    Balance.Agree Balance.scale Balance.add Balance.neg
  dsimp only
  rw [Nat.add_comm (two.representation.numerator.negative * one.representation.denominator)
    (one.representation.numerator.positive * two.representation.denominator)]
  change (gapRight one two - gapLeft one two) *
      (two.representation.denominator * one.representation.denominator) +
      gapLeft one two * (one.representation.denominator * two.representation.denominator) =
    gapRight one two * (one.representation.denominator * two.representation.denominator) +
      0 * (two.representation.denominator * one.representation.denominator)
  rw [Nat.mul_comm two.representation.denominator one.representation.denominator,
    ← Natural.add_mul, rebuild, Nat.zero_mul, Nat.add_zero]

/-- Exhaustion certifies only the inspected finite budget. The returned
prefix remains available to resume; this is not a proof of global absence. -/
structure ProductiveWindowExhaustion {source : RelativePathState}
    (presentation : RelativePathPresentation source) (window : ReadingWindow) (start fuel : Nat) where
  realization : RelativeRefinementRun source
  realizationExact : realization = presentation.realize (start + fuel)
  missed : ∀ offset, offset ≤ fuel →
    ¬ window.BracketContains (presentation.realize (start + offset)).state.reading

structure ProductiveWindowSearchHit {source : RelativePathState}
    (presentation : RelativePathPresentation source) (window : ReadingWindow) (start fuel : Nat) where
  certificate : ProductiveWindowCertificate presentation window
  lower : start ≤ certificate.depth
  upper : certificate.depth ≤ start + fuel

/-- Inspect the received prefix before producing another head. There are
at most fuel + 1 bracket tests and fuel new productions, not replayed prefixes. -/
def searchProductiveWindowFrom {source : RelativePathState}
    (presentation : RelativePathPresentation source) (window : ReadingWindow) :
    (fuel start : Nat) → (prior : RelativeRefinementRun source) →
    prior = presentation.realize start →
    PSum (ProductiveWindowSearchHit presentation window start fuel)
      (ProductiveWindowExhaustion presentation window start fuel)
  | fuel, start, prior, priorExact =>
    if inside : window.BracketContains prior.state.reading then
      .inl ⟨⟨start, prior, priorExact, inside⟩, Nat.le_refl _, Nat.le_add_right _ _⟩
    else
      match fuel with
      | 0 => .inr ⟨prior, priorExact.trans (congrArg presentation.realize (Nat.add_zero start).symm),
          fun offset bound => by
            have zero : offset = 0 := Nat.eq_zero_of_le_zero bound
            rw [zero, Nat.add_zero, ← priorExact]
            exact inside⟩
      | fuel + 1 =>
        let head := prior.next presentation.rule
        have headExact : head = presentation.realize (start + 1) :=
          (congrArg (fun run => run.next presentation.rule) priorExact).trans
            (relative_evolution_compose presentation.stored presentation.rule start 1)
        match searchProductiveWindowFrom presentation window fuel (start + 1) head headExact with
        | .inl found => .inl ⟨found.certificate,
            Nat.le_trans (Nat.le_succ start) found.lower,
            (show (start + 1) + fuel = start + (fuel + 1) from by exact_natural) ▸ found.upper⟩
        | .inr exhausted => .inr ⟨exhausted.realization,
            exhausted.realizationExact.trans (congrArg presentation.realize (by exact_natural)),
            fun offset bound => by
              cases offset with
              | zero =>
                rw [Nat.add_zero, ← priorExact]
                exact inside
              | succ offset =>
                have missed := exhausted.missed offset (Nat.le_of_succ_le_succ bound)
                have same : (start + 1) + offset = start + (offset + 1) := by exact_natural
                rw [same] at missed
                exact missed⟩
termination_by structural fuel _ _ _ => fuel

def RelativePathPresentation.searchWindow {source : RelativePathState}
    (presentation : RelativePathPresentation source) (window : ReadingWindow) (fuel : Nat) :
    PSum (ProductiveWindowSearchHit presentation window 0 fuel)
      (ProductiveWindowExhaustion presentation window 0 fuel) :=
  searchProductiveWindowFrom presentation window fuel 0 presentation.stored rfl

def ProductiveWindowExhaustion.resumeSearch {source presentation window start fuel}
    (exhausted : @ProductiveWindowExhaustion source presentation window start fuel) (extra : Nat) :
    PSum (ProductiveWindowSearchHit presentation window (start + fuel) extra)
      (ProductiveWindowExhaustion presentation window (start + fuel) extra) :=
  searchProductiveWindowFrom presentation window extra (start + fuel)
    exhausted.realization exhausted.realizationExact

def ProductiveSearchWithinBudget {source presentation window start fuel}
    (result : PSum (@ProductiveWindowSearchHit source presentation window start fuel)
      (ProductiveWindowExhaustion presentation window start fuel)) : Prop :=
  match result with
  | .inl found => start ≤ found.certificate.depth ∧ found.certificate.depth ≤ start + fuel
  | .inr _ => True

theorem productive_search_never_exceeds_its_budget {source}
    (presentation : RelativePathPresentation source) (window : ReadingWindow)
    (fuel start : Nat) (prior : RelativeRefinementRun source)
    (priorExact : prior = presentation.realize start) :
    ProductiveSearchWithinBudget
      (searchProductiveWindowFrom presentation window fuel start prior priorExact) := by
  cases result : searchProductiveWindowFrom presentation window fuel start prior priorExact with
  | inl found => exact ⟨found.lower, found.upper⟩
  | inr exhausted => exact True.intro

private theorem overlap_half_gap {window} (split : OverlappingWindowSplit window) :
    RationalStrictLess split.lowerCut
      (Rational.sub split.upperCut (strictReadingGap split.lowerCut split.upperCut split.overlap).half.value) := by
  let gap := strictReadingGap split.lowerCut split.upperCut split.overlap
  have upper : split.upperCut = Rational.add split.lowerCut gap.value := by
    rw [strict_reading_gap_value]
    unfold Rational.sub
    rw [Rational.add_left_comm, Rational.add_neg, Rational.add_zero]
  have center : Rational.sub split.upperCut gap.half.value =
      Rational.add split.lowerCut gap.half.value := by
    rw [upper, ← gap.half_add_half]
    unfold Rational.sub
    rw [Rational.add_assoc, Rational.add_assoc, Rational.add_neg, Rational.add_zero]
  rw [center]
  exact (precision_window_contains split.lowerCut gap).2

private theorem upper_minus_budget {cursor} (reading : RelativePathReading cursor)
    (precision : Precision) (bound : Rational.Le reading.resolution precision.value) :
    Rational.Le (Rational.sub reading.upper precision.value) reading.value := by
  have ordered := Rational.add_le_left bound reading.value
  rw [Rational.add_comm reading.resolution reading.value,
    Rational.add_comm precision.value reading.value] at ordered
  have cancelled := Rational.add_le_left ordered (Rational.neg precision.value)
  rw [Rational.add_assoc reading.value precision.value,
    Rational.add_neg, Rational.add_zero] at cancelled
  rw [relative_upper_is_reading_plus_resolution reading] at cancelled
  exact cancelled

/-- Positive overlap supplies the finite precision budget. Only the actual
returned bracket chooses a branch; no completed limit or branch is supplied. -/
def OverlappingWindowSplit.chooseProductive {source presentation window}
    (split : OverlappingWindowSplit window)
    (certificate : @ProductiveWindowCertificate source presentation window) :
    PSum (ProductiveWindowCertificate presentation split.left)
      (ProductiveWindowCertificate presentation split.right) :=
  let precision := (strictReadingGap split.lowerCut split.upperCut split.overlap).half
  let produced := certificate.advance precision.denominator
  if below : RationalStrictLess produced.realization.state.reading.upper split.upperCut then
    .inl ⟨produced.depth, produced.realization, produced.realizationExact, produced.inside.1, below⟩
  else
    have bound := relative_evolution_precision certificate.realization presentation.rule precision
      precision.denominator (Nat.le_refl _)
    have comparison := Rational.add_le_left (rational_not_strict below) (Rational.neg precision.value)
    have lower := rational_strict_le (overlap_half_gap split)
      (Rational.le_trans comparison (upper_minus_budget produced.realization.state.reading precision bound))
    .inr ⟨produced.depth, produced.realization, produced.realizationExact, lower, produced.inside.2⟩

theorem productive_split_data_exact {source presentation window}
    (split : OverlappingWindowSplit window)
    (certificate : @ProductiveWindowCertificate source presentation window) :
    (match split.chooseProductive certificate with
      | .inl narrowed => (narrowed.depth, narrowed.realization)
      | .inr narrowed => (narrowed.depth, narrowed.realization)) =
    (certificate.depth + (strictReadingGap split.lowerCut split.upperCut split.overlap).half.denominator,
      certificate.realization.evolve presentation.rule
        (strictReadingGap split.lowerCut split.upperCut split.overlap).half.denominator) := by
  unfold OverlappingWindowSplit.chooseProductive
  dsimp only
  by_cases below : RationalStrictLess
      (certificate.advance (strictReadingGap split.lowerCut split.upperCut split.overlap).half.denominator).realization.state.reading.upper
      split.upperCut
  · rw [dif_pos below]
    dsimp only [ProductiveWindowCertificate.advance]
  · rw [dif_neg below]
    dsimp only [ProductiveWindowCertificate.advance]

structure CoveredProductivePresentation {source : RelativePathState}
    (presentation : RelativePathPresentation source) {window : ReadingWindow}
    (cover : InstrumentalReadingCover window) where
  window : ReadingWindow
  leaf : cover.Leaf window
  certificate : ProductiveWindowCertificate presentation window

def InstrumentalReadingCover.selectProductive {source presentation window}
    (cover : InstrumentalReadingCover window)
    (certificate : @ProductiveWindowCertificate source presentation window) :
    CoveredProductivePresentation presentation cover :=
  match cover with
  | .identity _ => ⟨window, .here, certificate⟩
  | .split division first second =>
    match division.chooseProductive certificate with
    | .inl narrowed =>
      let chosen := first.selectProductive narrowed
      ⟨chosen.window, .left chosen.leaf, chosen.certificate⟩
    | .inr narrowed =>
      let chosen := second.selectProductive narrowed
      ⟨chosen.window, .right chosen.leaf, chosen.certificate⟩
termination_by structural cover

theorem productive_cover_extends_only_its_received_prefix {source presentation window}
    (cover : InstrumentalReadingCover window)
    (certificate : @ProductiveWindowCertificate source presentation window) :
    ∃ steps, (cover.selectProductive certificate).certificate.depth = certificate.depth + steps ∧
      (cover.selectProductive certificate).certificate.realization =
        certificate.realization.evolve presentation.rule steps := by
  induction cover with
  | identity window => exact ⟨0, (Nat.add_zero _).symm, rfl⟩
  | split division first second ihFirst ihSecond =>
    have data := productive_split_data_exact division certificate
    cases selected : division.chooseProductive certificate with
    | inl narrowed =>
      rw [selected] at data
      have fullDepth := congrArg Prod.fst data
      have fullRun := congrArg Prod.snd data
      dsimp only at fullDepth fullRun
      rw [InstrumentalReadingCover.selectProductive, selected]
      obtain ⟨steps, depth, actual⟩ := ihFirst narrowed
      refine ⟨(strictReadingGap division.lowerCut division.upperCut division.overlap).half.denominator + steps, ?_, ?_⟩
      · change (first.selectProductive narrowed).certificate.depth = _
        rw [depth, fullDepth, Nat.add_assoc]
      · change (first.selectProductive narrowed).certificate.realization = _
        rw [actual, fullRun, relative_evolution_compose]
    | inr narrowed =>
      rw [selected] at data
      have fullDepth := congrArg Prod.fst data
      have fullRun := congrArg Prod.snd data
      dsimp only at fullDepth fullRun
      rw [InstrumentalReadingCover.selectProductive, selected]
      obtain ⟨steps, depth, actual⟩ := ihSecond narrowed
      refine ⟨(strictReadingGap division.lowerCut division.upperCut division.overlap).half.denominator + steps, ?_, ?_⟩
      · change (second.selectProductive narrowed).certificate.depth = _
        rw [depth, fullDepth, Nat.add_assoc]
      · change (second.selectProductive narrowed).certificate.realization = _
        rw [actual, fullRun, relative_evolution_compose]

def CoveredProductivePresentation.restrict {source presentation window cover}
    (chosen : @CoveredProductivePresentation source presentation window cover) :
    ProductiveWindowCertificate presentation window := chosen.certificate.restrict chosen.leaf.refinement

theorem productive_cover_restriction_keeps_the_produced_prefix {source presentation window cover}
    (chosen : @CoveredProductivePresentation source presentation window cover) :
    chosen.restrict.realization = chosen.certificate.realization := rfl

theorem productive_cover_has_no_later_escape {source presentation window}
    (cover : InstrumentalReadingCover window)
    (certificate : @ProductiveWindowCertificate source presentation window) (steps : Nat) :
    (cover.selectProductive certificate).window.Contains
      (presentation.realize ((cover.selectProductive certificate).certificate.depth + steps)).state.reading.value :=
  productive_window_all_later_readings _ _

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ReadingWindow.BracketContains
#print axioms RelationalPerimeter.Relativity.Production.bracket_contains_endpoints
#print axioms RelationalPerimeter.Relativity.Production.bracket_contains_every_between_reading
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.advance
#print axioms RelationalPerimeter.Relativity.Production.productive_window_advance_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_window_all_later_readings
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.restrict
#print axioms RelationalPerimeter.Relativity.Production.productive_window_restriction_identity
#print axioms RelationalPerimeter.Relativity.Production.productive_window_restrictions_compose
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.common
#print axioms RelationalPerimeter.Relativity.Production.productive_common_uses_the_returned_prefix
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.toResumed
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.fromResumed
#print axioms RelationalPerimeter.Relativity.Production.productive_window_resumption_iff
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.bracketWindow
#print axioms RelationalPerimeter.Relativity.Production.produced_bracket_window_contains
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.initialWindow
#print axioms RelationalPerimeter.Relativity.Production.strictReadingGap
#print axioms RelationalPerimeter.Relativity.Production.strict_reading_gap_value
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowExhaustion
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowSearchHit
#print axioms RelationalPerimeter.Relativity.Production.searchProductiveWindowFrom
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.searchWindow
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowExhaustion.resumeSearch
#print axioms RelationalPerimeter.Relativity.Production.ProductiveSearchWithinBudget
#print axioms RelationalPerimeter.Relativity.Production.productive_search_never_exceeds_its_budget
#print axioms RelationalPerimeter.Relativity.Production.OverlappingWindowSplit.chooseProductive
#print axioms RelationalPerimeter.Relativity.Production.productive_split_data_exact
#print axioms RelationalPerimeter.Relativity.Production.CoveredProductivePresentation
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.selectProductive
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_extends_only_its_received_prefix
#print axioms RelationalPerimeter.Relativity.Production.CoveredProductivePresentation.restrict
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_restriction_keeps_the_produced_prefix
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_has_no_later_escape
/- AXIOM_AUDIT_END -/
