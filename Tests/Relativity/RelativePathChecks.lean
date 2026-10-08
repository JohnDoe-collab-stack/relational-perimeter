import RelationalPerimeter

/-! Public clients of stored-path relative readings. All evaluations are
executability smoke checks, not physical or complexity experiments. -/
set_option genInjectivity false
namespace Tests.Relativity.RelativePathChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def family (numerator denominatorMinusOne : Nat) :=
  realizeRelativeReading (.received input) .here (.prior .here) (.prior (.prior .here))
    rfl numerator denominatorMinusOne

theorem every_finite_pair_is_realized (numerator denominatorMinusOne : Nat) :
    (family numerator denominatorMinusOne).reading.value =
      Rational.ofParts numerator 0 denominatorMinusOne := realized_relative_fraction_exact ..

theorem exact_number_of_shared_productions (numerator denominatorMinusOne : Nat) :
    StrongPerimetralTurning.History.length (family numerator denominatorMinusOne).history =
      numerator + (denominatorMinusOne + 1) + 3 := realized_relative_history_length ..

theorem every_numerator_is_the_actual_received_gap (numerator denominatorMinusOne : Nat) :
    (family numerator denominatorMinusOne).reading.numeratorGap = Rational.ofNat numerator :=
  (family numerator denominatorMinusOne).reading.numerator_gap_exact.trans
    (congrArg Rational.ofNat (family numerator denominatorMinusOne).numeratorCount)

theorem every_denominator_is_the_actual_received_gap (numerator denominatorMinusOne : Nat) :
    (family numerator denominatorMinusOne).reading.denominatorGap = Rational.ofNat (denominatorMinusOne + 1) :=
  (family numerator denominatorMinusOne).reading.denominator_gap_exact.trans
    (congrArg Rational.ofNat (family numerator denominatorMinusOne).denominatorCount)

theorem first_path_is_not_the_second_source (numerator denominatorMinusOne : Nat) :
    (family numerator denominatorMinusOne).reading.arrivals.first ≠
      (family numerator denominatorMinusOne).reading.arrivals.second :=
  (family numerator denominatorMinusOne).reading.arrivals.distinct

theorem recorded_reference_path_is_not_a_supplied_number (numerator denominatorMinusOne : Nat) :
    ((family numerator denominatorMinusOne).cursor.read
      (family numerator denominatorMinusOne).reading.arrivals.secondSignal).increments.length =
        denominatorMinusOne + 1 :=
  (family numerator denominatorMinusOne).reading.denominator.recorded_length.trans
    (family numerator denominatorMinusOne).denominatorCount

def half := family 1 1
def twiceHalf := family 2 3
def zero := family 0 1

theorem actual_half : half.reading.value = Rational.ofParts 1 0 1 := every_finite_pair_is_realized ..

theorem actual_zero : zero.reading.value = Rational.zero :=
  zero.value_exact.trans (Rational.zero_mul _)

theorem reader_really_changes_with_the_received_path : half.reading.value ≠ zero.reading.value := by
  intro same
  have equation := half.reading.measured_ratio_exact
  rw [same, actual_zero, Rational.zero_mul] at equation
  exact Rational.one_ne_zero
    (equation.trans (every_numerator_is_the_actual_received_gap 1 1)).symm

theorem different_paths_have_the_same_relative_reading : twiceHalf.reading.value = half.reading.value := by
  have fractions : Rational.ofParts 2 0 3 = Rational.ofParts 1 0 1 := by
    apply Rational.normalize_congr
    change 2 * 2 = 1 * 4
    rfl
  exact (every_finite_pair_is_realized 2 3).trans (fractions.trans actual_half.symm)

def pathLength : LocalReadout → Option Nat
  | .signal record => some record.increments.length
  | .reading _ => none
  | .payload _ => none
  | .calibration _ => none

theorem same_ratio_does_not_erase_future_path_effects :
    ¬ FutureEquivalent localContract half.cursor twiceHalf.cursor := by
  intro same
  have records := futures_preserve_available_readout half.cursor twiceHalf.cursor
    half.reading.arrivals.secondSignal twiceHalf.reading.arrivals.secondSignal rfl same
  have lengths := congrArg pathLength records
  change some ((half.cursor.read half.reading.arrivals.secondSignal).increments.length) =
    some ((twiceHalf.cursor.read twiceHalf.reading.arrivals.secondSignal).increments.length) at lengths
  have contradiction : (some 2 : Option Nat) = some 4 :=
    (congrArg some (recorded_reference_path_is_not_a_supplied_number 1 1)).symm.trans
      (lengths.trans (congrArg some (recorded_reference_path_is_not_a_supplied_number 2 3)))
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Option.some.inj contradiction)))

theorem recorded_ratio_survives_every_finite_suffix (numerator denominatorMinusOne : Nat)
    (schedule : Program (family numerator denominatorMinusOne).cursor.kinds) :
    ((family numerator denominatorMinusOne).continue schedule).reading.value =
      (family numerator denominatorMinusOne).reading.value := relative_continuation_value_exact ..

theorem source_separation_survives_every_finite_suffix (numerator denominatorMinusOne : Nat)
    (schedule : Program (family numerator denominatorMinusOne).cursor.kinds) :
    ((family numerator denominatorMinusOne).continue schedule).reading.arrivals.first ≠
      ((family numerator denominatorMinusOne).continue schedule).reading.arrivals.second :=
  relative_continuation_keeps_both_sources (family numerator denominatorMinusOne) schedule

def resumedHalf := half.continue (.step (.receive (.prior .here)) .done)

theorem genuine_continuation_does_not_change_the_recorded_ratio :
    resumedHalf.reading.value = Rational.ofParts 1 0 1 :=
  (relative_continuation_value_exact half _).trans actual_half

theorem old_received_reading_still_has_its_own_port :
    resumedHalf.cursor.read resumedHalf.reading.arrivals.first = Rational.one :=
  (history_preserves_reads (run half.cursor (.step (.receive (.prior .here)) .done)).history
    half.reading.arrivals.first).trans (by
      change Rational.add Rational.zero Rational.one = Rational.one
      exact Rational.zero_add _)

-- Compiled smoke checks consume each returned realization once.
def smoke : Nat × Nat × Nat :=
  let result := family 1 1
  (result.reading.value.index, result.reading.numerator.relayCount, result.reading.denominator.relayCount)
#eval smoke

end Tests.Relativity.RelativePathChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.RelativePathChecks.family
#print axioms Tests.Relativity.RelativePathChecks.every_finite_pair_is_realized
#print axioms Tests.Relativity.RelativePathChecks.exact_number_of_shared_productions
#print axioms Tests.Relativity.RelativePathChecks.every_numerator_is_the_actual_received_gap
#print axioms Tests.Relativity.RelativePathChecks.every_denominator_is_the_actual_received_gap
#print axioms Tests.Relativity.RelativePathChecks.first_path_is_not_the_second_source
#print axioms Tests.Relativity.RelativePathChecks.recorded_reference_path_is_not_a_supplied_number
#print axioms Tests.Relativity.RelativePathChecks.actual_half
#print axioms Tests.Relativity.RelativePathChecks.actual_zero
#print axioms Tests.Relativity.RelativePathChecks.reader_really_changes_with_the_received_path
#print axioms Tests.Relativity.RelativePathChecks.different_paths_have_the_same_relative_reading
#print axioms Tests.Relativity.RelativePathChecks.same_ratio_does_not_erase_future_path_effects
#print axioms Tests.Relativity.RelativePathChecks.recorded_ratio_survives_every_finite_suffix
#print axioms Tests.Relativity.RelativePathChecks.source_separation_survives_every_finite_suffix
#print axioms Tests.Relativity.RelativePathChecks.genuine_continuation_does_not_change_the_recorded_ratio
#print axioms Tests.Relativity.RelativePathChecks.old_received_reading_still_has_its_own_port
#print axioms Tests.Relativity.RelativePathChecks.smoke
/- AXIOM_AUDIT_END -/
