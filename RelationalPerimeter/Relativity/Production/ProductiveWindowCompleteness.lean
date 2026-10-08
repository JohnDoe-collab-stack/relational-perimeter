import RelationalPerimeter.Relativity.Production.ProductiveWindowAgreements

/-!
# Numerical agreement reconstructed from produced window certificates

A positive certificate transformer is executable data. A requested narrow
window is formed from an actual prefix and its proven resolution. Applying
the transformer once gives a second realized prefix; their returned depths
supply an agreement modulus for every later numerical reading. No source
identity, physical localization or memory-erasure license follows.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

private theorem padded_bracket_span {cursor} (reading : RelativePathReading cursor)
    (precision : Precision) (bound : Rational.Le reading.resolution precision.half.value) :
    Rational.Le
      (ReadingWindow.mk (Rational.sub reading.value precision.half.half.value)
        (Rational.add reading.upper precision.half.half.value)).span precision.value := by
  change Rational.Le (Rational.sub
    (Rational.add reading.upper precision.half.half.value)
    (Rational.add reading.value (Rational.neg precision.half.half.value))) precision.value
  rw [difference_of_sums]
  unfold Rational.sub
  rw [Rational.neg_neg]
  change Rational.Le
    (Rational.add (Rational.sub reading.upper reading.value)
      (Rational.add precision.half.half.value precision.half.half.value)) precision.value
  rw [relative_bracket_span, precision.half.half_add_half]
  have full := Rational.add_le bound (Rational.le_refl precision.half.value)
  rw [precision.half_add_half] at full
  exact full

structure ProductivePrecisionWindow {source : RelativePathState}
    (presentation : RelativePathPresentation source) (precision : Precision) where
  window : ReadingWindow
  certificate : ProductiveWindowCertificate presentation window
  diameter : Rational.Le window.span precision.value

/-- One realized prefix, two strict padding margins, no supplied limit. -/
def RelativePathPresentation.requestWindow {source : RelativePathState}
    (presentation : RelativePathPresentation source) (precision : Precision) :
    ProductivePrecisionWindow presentation precision :=
  let produced := presentation.realize precision.half.denominator
  let window : ReadingWindow :=
    ⟨Rational.sub produced.state.reading.value precision.half.half.value,
      Rational.add produced.state.reading.upper precision.half.half.value⟩
  ⟨window, ⟨precision.half.denominator, produced, rfl,
      (precision_window_contains produced.state.reading.value precision.half).1,
      (precision_window_contains produced.state.reading.upper precision.half).2⟩,
    padded_bracket_span produced.state.reading precision
      (relative_evolution_precision presentation.stored presentation.rule precision.half
        precision.half.denominator (Nat.le_refl _))⟩

theorem productive_requested_window_run_exact {source}
    (presentation : RelativePathPresentation source) (precision : Precision) :
    (presentation.requestWindow precision).certificate.realization =
      presentation.stored.evolve presentation.rule precision.half.denominator := rfl

theorem productive_requested_window_depth {source}
    (presentation : RelativePathPresentation source) (precision : Precision) :
    (presentation.requestWindow precision).certificate.depth = precision.half.denominator := rfl

structure ProductiveWindowTransfer {source other : RelativePathState}
    (first : RelativePathPresentation source) (second : RelativePathPresentation other) where
  apply : (window : ReadingWindow) → ProductiveWindowCertificate first window →
    ProductiveWindowCertificate second window

def ProductiveWindowTransfer.identity {source} (presentation : RelativePathPresentation source) :
    ProductiveWindowTransfer presentation presentation := ⟨fun _ certificate => certificate⟩

def ProductiveWindowTransfer.compose {source middle target}
    {first : RelativePathPresentation source} {second : RelativePathPresentation middle}
    {third : RelativePathPresentation target} (one : ProductiveWindowTransfer first second)
    (two : ProductiveWindowTransfer second third) : ProductiveWindowTransfer first third :=
  ⟨fun window certificate =>
    let returned := one.apply window certificate
    two.apply window returned⟩

def ProductiveWindowTransfer.ofAgreement {source other}
    {first : RelativePathPresentation source} (second : RelativePathPresentation other)
    (agreement : Agreement first.numeric second.numeric) : ProductiveWindowTransfer first second :=
  ⟨fun _ certificate => certificate.certifyAgreed second agreement⟩

structure ProductiveWindowComparison {source other}
    (first : RelativePathPresentation source) (second : RelativePathPresentation other)
    (precision : Precision) where
  window : ReadingWindow
  firstCertificate : ProductiveWindowCertificate first window
  secondCertificate : ProductiveWindowCertificate second window
  diameter : Rational.Le window.span precision.value

def ProductiveWindowTransfer.compare {source other}
    {first : RelativePathPresentation source} {second : RelativePathPresentation other}
    (transfer : ProductiveWindowTransfer first second) (precision : Precision) :
    ProductiveWindowComparison first second precision :=
  let request := first.requestWindow precision
  let returned := transfer.apply request.window request.certificate
  ⟨request.window, request.certificate, returned, request.diameter⟩

theorem productive_comparison_request_exact {source other}
    {first : RelativePathPresentation source} {second : RelativePathPresentation other}
    (transfer : ProductiveWindowTransfer first second) (precision : Precision) :
    (transfer.compare precision).firstCertificate.realization =
      first.stored.evolve first.rule precision.half.denominator := rfl

theorem productive_comparison_response_exact {source other}
    {first : RelativePathPresentation source} {second : RelativePathPresentation other}
    (transfer : ProductiveWindowTransfer first second) (precision : Precision) :
    (transfer.compare precision).secondCertificate =
      transfer.apply (first.requestWindow precision).window (first.requestWindow precision).certificate := rfl

theorem productive_certificate_all_later_indices {source presentation window}
    (certificate : @ProductiveWindowCertificate source presentation window) (index : Nat)
    (enough : certificate.depth ≤ index) : window.Contains (presentation.numeric.approximate index) := by
  have inside := productive_window_all_later_readings certificate (index - certificate.depth)
  rw [Nat.add_comm certificate.depth, Natural.sub_add_of_le enough] at inside
  exact inside

private theorem readings_in_small_window {window : ReadingWindow} {first second : Rational}
    {precision : Precision} (diameter : Rational.Le window.span precision.value)
    (left : window.Contains first) (right : window.Contains second) : Close first second precision.value :=
  ⟨Rational.le_trans (Rational.add_le left.2.1 (Rational.neg_le_neg right.1.1)) diameter,
    Rational.le_trans (Rational.add_le right.2.1 (Rational.neg_le_neg left.1.1)) diameter⟩

theorem ProductiveWindowComparison.allLaterClose {source other first second precision}
    (comparison : @ProductiveWindowComparison source other first second precision)
    (left right : Nat) (leftEnough : comparison.firstCertificate.depth ≤ left)
    (rightEnough : comparison.secondCertificate.depth ≤ right) :
    Close (first.numeric.approximate left) (second.numeric.approximate right) precision.value :=
  readings_in_small_window comparison.diameter
    (productive_certificate_all_later_indices comparison.firstCertificate left leftEnough)
    (productive_certificate_all_later_indices comparison.secondCertificate right rightEnough)

/-- Reconstruct an explicit modulus from returned depths, not from erased
existence or an external oracle. Future indices occur only in the proof. -/
def ProductiveWindowTransfer.toAgreement {source other}
    {first : RelativePathPresentation source} {second : RelativePathPresentation other}
    (transfer : ProductiveWindowTransfer first second) : Agreement first.numeric second.numeric where
  modulus precision :=
    let comparison := transfer.compare precision
    comparison.firstCertificate.depth + comparison.secondCertificate.depth
  close precision left right leftEnough rightEnough :=
    (transfer.compare precision).allLaterClose left right
      (Nat.le_trans (Nat.le_add_right ..) leftEnough)
      (Nat.le_trans (Nat.le_add_left ..) rightEnough)

theorem productive_transfer_modulus_uses_returned_depths {source other}
    {first : RelativePathPresentation source} {second : RelativePathPresentation other}
    (transfer : ProductiveWindowTransfer first second) (precision : Precision) :
    transfer.toAgreement.modulus precision =
      (transfer.compare precision).firstCertificate.depth +
        (transfer.compare precision).secondCertificate.depth := rfl

theorem productive_numeric_agreement_iff_window_transfer {source other}
    (first : RelativePathPresentation source) (second : RelativePathPresentation other) :
    Nonempty (Agreement first.numeric second.numeric) ↔ Nonempty (ProductiveWindowTransfer first second) :=
  ⟨fun ⟨agreement⟩ => ⟨ProductiveWindowTransfer.ofAgreement second agreement⟩,
    fun ⟨transfer⟩ => ⟨transfer.toAgreement⟩⟩

def ProductiveWindowTransfer.reverse {source other}
    {first : RelativePathPresentation source} {second : RelativePathPresentation other}
    (transfer : ProductiveWindowTransfer first second) : ProductiveWindowTransfer second first :=
  ProductiveWindowTransfer.ofAgreement first transfer.toAgreement.reverse

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionWindow
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.requestWindow
#print axioms RelationalPerimeter.Relativity.Production.productive_requested_window_run_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_requested_window_depth
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer.identity
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer.compose
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer.ofAgreement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowComparison
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer.compare
#print axioms RelationalPerimeter.Relativity.Production.productive_comparison_request_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_comparison_response_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_certificate_all_later_indices
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowComparison.allLaterClose
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer.toAgreement
#print axioms RelationalPerimeter.Relativity.Production.productive_transfer_modulus_uses_returned_depths
#print axioms RelationalPerimeter.Relativity.Production.productive_numeric_agreement_iff_window_transfer
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowTransfer.reverse
/- AXIOM_AUDIT_END -/
