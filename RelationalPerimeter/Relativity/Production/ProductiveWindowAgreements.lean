import RelationalPerimeter.Relativity.Production.ProductivePresentationWindows

/-!
# Generated window certificates under positive numerical agreement

The received agreement supplies its explicit modulus, not an equality of
histories. Strict margins determine a sufficient finite request. Only the
second stored prefix is extended as data; comparison with the first family
is a proof. No physical localization, identification or transport between
source histories, or forgetting follows.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

private def smallerPrecision (first second : Precision) : Precision :=
  if Rational.Le first.value second.value then first else second

private theorem smaller_precision_bounds (first second : Precision) :
    Rational.Le (smallerPrecision first second).value first.value ∧
      Rational.Le (smallerPrecision first second).value second.value := by
  unfold smallerPrecision
  split
  · exact ⟨Rational.le_refl _, ‹_›⟩
  · exact ⟨(Rational.le_total _ _).resolve_left ‹_›, Rational.le_refl _⟩

private theorem gap_center (one two : Rational) (strict : RationalStrictLess one two) :
    Rational.sub two (strictReadingGap one two strict).half.value =
      Rational.add one (strictReadingGap one two strict).half.value := by
  let gap := strictReadingGap one two strict
  have rebuild : two = Rational.add one gap.value := by
    rw [strict_reading_gap_value]
    unfold Rational.sub
    rw [Rational.add_left_comm, Rational.add_neg, Rational.add_zero]
  change Rational.sub two gap.half.value = Rational.add one gap.half.value
  rw [rebuild, ← gap.half_add_half]
  unfold Rational.sub
  rw [Rational.add_assoc, Rational.add_assoc, Rational.add_neg, Rational.add_zero]

private theorem gap_midpoint (one two : Rational) (strict : RationalStrictLess one two) :
    (ReadingWindow.mk one two).Contains
      (Rational.add one (strictReadingGap one two strict).half.value) := by
  let gap := strictReadingGap one two strict
  have center := gap_center one two strict
  exact ⟨(precision_window_contains one gap).2,
    center ▸ (precision_window_contains two gap).1⟩

def ProductiveWindowCertificate.agreementPrecision {source : RelativePathState}
    {presentation : RelativePathPresentation source} {window : ReadingWindow}
    (certificate : ProductiveWindowCertificate presentation window) : Precision :=
  smallerPrecision
    (strictReadingGap window.lower certificate.realization.state.reading.value certificate.inside.1).half
    (strictReadingGap certificate.realization.state.reading.upper window.upper certificate.inside.2).half.half

theorem productive_agreement_precision_margins {source : RelativePathState}
    {presentation : RelativePathPresentation source} {window : ReadingWindow}
    (certificate : ProductiveWindowCertificate presentation window) :
    RationalStrictLess window.lower
      (Rational.sub certificate.realization.state.reading.value certificate.agreementPrecision.value) ∧
    RationalStrictLess
      (Rational.add certificate.realization.state.reading.upper
        (Rational.add certificate.agreementPrecision.value certificate.agreementPrecision.value)) window.upper := by
  let lower := strictReadingGap window.lower certificate.realization.state.reading.value certificate.inside.1
  let upper := strictReadingGap certificate.realization.state.reading.upper window.upper certificate.inside.2
  have bounds := smaller_precision_bounds lower.half upper.half.half
  have low : RationalStrictLess window.lower
      (Rational.sub certificate.realization.state.reading.value lower.half.value) := by
    rw [gap_center window.lower certificate.realization.state.reading.value certificate.inside.1]
    exact (gap_midpoint window.lower certificate.realization.state.reading.value certificate.inside.1).1
  have shrink := Rational.add_le (Rational.le_refl certificate.realization.state.reading.value)
    (Rational.neg_le_neg bounds.1)
  have twice := Rational.add_le bounds.2 bounds.2
  rw [upper.half.half_add_half] at twice
  have high := (gap_midpoint certificate.realization.state.reading.upper window.upper certificate.inside.2).2
  exact ⟨rational_strict_le low shrink,
    rational_le_strict (by
      exact Rational.add_le (Rational.le_refl certificate.realization.state.reading.upper) twice) high⟩

private theorem sub_bound_as_sum {one two budget : Rational}
    (bound : Rational.Le (Rational.sub one two) budget) :
    Rational.Le one (Rational.add two budget) := by
  have moved := Rational.add_le_left bound two
  unfold Rational.sub at moved
  rw [Rational.add_assoc, Rational.neg_add_cancel, Rational.add_zero,
    Rational.add_comm budget two] at moved
  exact moved

private theorem close_lower_bound {one two budget : Rational} (near : Close one two budget) :
    Rational.Le (Rational.sub one budget) two := by
  have moved := Rational.add_le_left (sub_bound_as_sum near.1) (Rational.neg budget)
  rw [Rational.add_assoc, Rational.add_neg, Rational.add_zero] at moved
  exact moved

private theorem equal_le_bounds {one two lower upper : Rational}
    (left : one = two) (right : lower = upper) :
    Rational.Le one lower = Rational.Le two upper := by
  cases left
  cases right
  rfl

private def agreedCertificateAt {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window : ReadingWindow} (agreement : Agreement first.numeric second.numeric)
    (certificate : ProductiveWindowCertificate first window) (precision : Precision) (steps : Nat)
    (enoughModulus : agreement.modulus precision ≤ steps)
    (enoughPrecision : precision.denominator ≤ steps)
    (margins : RationalStrictLess window.lower (Rational.sub certificate.realization.state.reading.value precision.value) ∧
      RationalStrictLess (Rational.add certificate.realization.state.reading.upper
        (Rational.add precision.value precision.value)) window.upper) :
    ProductiveWindowCertificate second window := by
  let produced := second.stored.evolve second.rule steps
  let firstFuture := certificate.realization.evolve first.rule steps
  have observed := agreement.close precision (certificate.depth + steps) steps
    (Nat.le_trans enoughModulus (Nat.le_add_left ..)) enoughModulus
  have firstRunExact := (@ProductiveWindowCertificate.advance source first window certificate steps).realizationExact
  dsimp only [ProductiveWindowCertificate.advance] at firstRunExact
  have firstValueExact :=
    congrArg (fun run : RelativeRefinementRun source => run.state.reading.value) firstRunExact
  dsimp only [RelativePathPresentation.realize] at firstValueExact
  dsimp only [RelativePathPresentation.numeric, RelativePathPresentation.realize] at observed
  have near : Close firstFuture.state.reading.value produced.state.reading.value precision.value := by
    with_reducible
      exact (congrArg (fun value : Rational => Close value produced.state.reading.value precision.value)
        firstValueExact).symm.mp observed
  have kept := relative_evolution_brackets certificate.realization first.rule steps
  have inside : window.BracketContains produced.state.reading := by
    with_reducible
      dsimp only [ReadingWindow.BracketContains]
      dsimp only [Rational.sub] at margins
      have lower := Rational.add_le_left kept.1 (Rational.neg precision.value)
      have lowerClose := close_lower_bound
        (one := firstFuture.state.reading.value) (two := produced.state.reading.value)
        (budget := precision.value) near
      dsimp only [Rational.sub] at lowerClose
      have lowerInside := rational_strict_le margins.1 (Rational.le_trans lower lowerClose)
      have resolution := relative_evolution_precision second.stored second.rule precision steps enoughPrecision
      have nearBounds := near
      dsimp only [Close] at nearBounds
      have upperClose := sub_bound_as_sum
        (one := produced.state.reading.value) (two := firstFuture.state.reading.value)
        (budget := precision.value) nearBounds.2
      have upper : Rational.Le produced.state.reading.upper
          (Rational.add firstFuture.state.reading.value (Rational.add precision.value precision.value)) :=
        Eq.mp (equal_le_bounds
          (relative_upper_is_reading_plus_resolution produced.state.reading)
          (Rational.add_assoc firstFuture.state.reading.value precision.value precision.value))
          (Rational.add_le upperClose resolution)
      have firstBound := Rational.le_trans (relative_bracket_ordered firstFuture.state.reading) kept.2
      have upperBound := Rational.add_le_left firstBound (Rational.add precision.value precision.value)
      have upperInside := @rational_le_strict produced.state.reading.upper
        (Rational.add certificate.realization.state.reading.upper (Rational.add precision.value precision.value))
        window.upper
        (@Rational.le_trans produced.state.reading.upper
          (Rational.add firstFuture.state.reading.value (Rational.add precision.value precision.value))
          (Rational.add certificate.realization.state.reading.upper (Rational.add precision.value precision.value))
          upper upperBound) margins.2
      exact And.intro lowerInside upperInside
  exact @ProductiveWindowCertificate.mk other second window steps produced
    (by dsimp only [produced, RelativePathPresentation.realize]) inside

/-- All premises of the private budget-generic builder are constructed here.
This is numerical certification, not a transport of source identity. -/
def ProductiveWindowCertificate.certifyAgreed {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window : ReadingWindow} (agreement : Agreement first.numeric second.numeric)
    (certificate : ProductiveWindowCertificate first window) :
    ProductiveWindowCertificate second window :=
  let precision := certificate.agreementPrecision
  let modulus := agreement.modulus precision
  let steps := modulus + precision.denominator
  agreedCertificateAt second agreement certificate precision steps
    (Nat.le_add_right ..) (Nat.le_add_left ..)
    (productive_agreement_precision_margins certificate)

theorem productive_agreed_certificate_exact {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window} (agreement : Agreement first.numeric second.numeric)
    (certificate : ProductiveWindowCertificate first window) :
    (certificate.certifyAgreed second agreement).realization =
      second.stored.evolve second.rule
        (agreement.modulus certificate.agreementPrecision + certificate.agreementPrecision.denominator) := by
  dsimp only [ProductiveWindowCertificate.certifyAgreed, agreedCertificateAt]

theorem productive_agreed_certificate_depth {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window} (agreement : Agreement first.numeric second.numeric)
    (certificate : ProductiveWindowCertificate first window) :
    (certificate.certifyAgreed second agreement).depth =
      agreement.modulus certificate.agreementPrecision + certificate.agreementPrecision.denominator := rfl

theorem productive_window_agreement_iff {source other : RelativePathState}
    (first : RelativePathPresentation source) (second : RelativePathPresentation other)
    (agreement : Agreement first.numeric second.numeric) (window : ReadingWindow) :
    Nonempty (ProductiveWindowCertificate first window) ↔
      Nonempty (ProductiveWindowCertificate second window) :=
  ⟨fun ⟨certificate⟩ => ⟨certificate.certifyAgreed second agreement⟩,
    fun ⟨certificate⟩ => ⟨certificate.certifyAgreed first agreement.reverse⟩⟩

def InstrumentalReadingCover.selectAgreed {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window} (agreement : Agreement first.numeric second.numeric)
    (cover : InstrumentalReadingCover window) (certificate : ProductiveWindowCertificate first window) :
    CoveredProductivePresentation second cover :=
  let received := certificate.certifyAgreed second agreement
  cover.selectProductive received

theorem productive_agreed_cover_uses_its_certificate {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window} (agreement : Agreement first.numeric second.numeric)
    (cover : InstrumentalReadingCover window) (certificate : ProductiveWindowCertificate first window) :
    cover.selectAgreed second agreement certificate =
      cover.selectProductive (certificate.certifyAgreed second agreement) := rfl

theorem productive_agreed_cover_extends_the_second_prefix {source other : RelativePathState}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    {window} (agreement : Agreement first.numeric second.numeric)
    (cover : InstrumentalReadingCover window) (certificate : ProductiveWindowCertificate first window) :
    ∃ steps, (cover.selectAgreed second agreement certificate).certificate.realization =
      second.stored.evolve second.rule steps := by
  obtain ⟨steps, _, actual⟩ := productive_cover_extends_only_its_received_prefix cover
    (certificate.certifyAgreed second agreement)
  refine ⟨(certificate.certifyAgreed second agreement).depth + steps, ?_⟩
  rw [productive_agreed_cover_uses_its_certificate, actual,
    productive_agreed_certificate_exact, productive_agreed_certificate_depth, relative_evolution_compose]

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.agreementPrecision
#print axioms RelationalPerimeter.Relativity.Production.productive_agreement_precision_margins
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.certifyAgreed
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_certificate_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_certificate_depth
#print axioms RelationalPerimeter.Relativity.Production.productive_window_agreement_iff
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalReadingCover.selectAgreed
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_cover_uses_its_certificate
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_cover_extends_the_second_prefix
/- AXIOM_AUDIT_END -/
