import RelationalPerimeter.Relativity.Production.EncounterRelativePaths
import RelationalPerimeter.Relativity.Arithmetic.OrderedFractions

/-!
# Reexpress an old relative determination through actual later measurements

A subdivision changes the measured ratio; it does not identify successive
encounters. Its affine change is derived from the two produced calibrated
journeys. Eliminating a stored chain reconstructs its cumulative change,
without replaying a producer or receiving an independently prescribed target.
These are instrumental laws, not physical localization laws.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production.Encounter
open Arithmetic
open ConstitutiveSearch.Resources

def pathFraction (numerator denominator : Nat) (positive : 0 < denominator) : Fraction :=
  ⟨⟨numerator, 0⟩, denominator, positive⟩

theorem paired_value_fraction {source} (reading : PairedPaths source) :
    reading.value = Rational.normalize
      (pathFraction reading.numerator.relayCount reading.denominator.relayCount reading.positiveScale) := by
  rw [reading.count_ratio_exact, path_count_fraction]
  have count : reading.denominator.relayCount - 1 + 1 = reading.denominator.relayCount :=
    Natural.sub_add_of_le reading.positiveScale
  apply Rational.normalize_congr
  change reading.numerator.relayCount * reading.denominator.relayCount +
      0 * (reading.denominator.relayCount - 1 + 1) =
    reading.numerator.relayCount * (reading.denominator.relayCount - 1 + 1) +
      0 * reading.denominator.relayCount
  rw [count]

def Refinement.drift {source choice} (result : Refinement source choice) : Rational :=
  Rational.normalize (pathFraction choice.extra result.next.reading.denominator.relayCount
    result.next.reading.positiveScale)

theorem refinement_affine_reading {source choice} (result : Refinement source choice) :
    result.next.reading.value = Rational.add source.reading.value result.drift := by
  rw [paired_value_fraction, paired_value_fraction]
  apply Rational.normalize_congr
  apply Fraction.trans ?_ (Fraction.symm (Fraction.add_congr
    (Rational.normalize_agrees _) (Rational.normalize_agrees _)))
  change result.next.reading.numerator.relayCount *
      (source.reading.denominator.relayCount * result.next.reading.denominator.relayCount) +
        (0 * result.next.reading.denominator.relayCount +
          0 * source.reading.denominator.relayCount) * result.next.reading.denominator.relayCount =
    (source.reading.numerator.relayCount * result.next.reading.denominator.relayCount +
      choice.extra * source.reading.denominator.relayCount) * result.next.reading.denominator.relayCount +
        0 * (source.reading.denominator.relayCount * result.next.reading.denominator.relayCount)
  rw [(refinement_counts result).1, (refinement_counts result).2]
  exact_natural

def MeasurementChain.drift {source target} (chain : MeasurementChain source target) : Rational :=
  match chain with
  | .root _ => Rational.zero
  | .step past _ head _ => Rational.add past.drift head.drift
termination_by structural chain

theorem measurement_chain_affine_reading {source target} (chain : MeasurementChain source target) :
    target.reading.value = Rational.add source.reading.value chain.drift := by
  induction chain with
  | root => exact (Rational.add_zero _).symm
  | step past choice head exactHead ih =>
    exact (refinement_affine_reading head).trans
      ((congrArg (fun q => Rational.add q head.drift) ih).trans (Rational.add_assoc ..))

theorem measurement_chain_returns_original_reading {source target} (chain : MeasurementChain source target) :
    Rational.sub target.reading.value chain.drift = source.reading.value := by
  rw [measurement_chain_affine_reading]
  unfold Rational.sub
  rw [Rational.add_assoc, Rational.add_neg, Rational.add_zero]

theorem measurement_anchor_is_fresh {source} (result : Measurement source)
    (old : Ref source.coupling.cursor.kinds .reading) :
    comparisonAnchor result.head.head ≠ result.history.transport.references old := by
  intro same
  let suffix : History result.ready result.head.next := .extend .root (.encountered result.head)
  have across := history_transport_append result.deliveries suffix old
  exact comparison_anchor_fresh result.head.head _ (same.trans across)

theorem refined_encounter_is_not_an_old_occurrence {source choice} (result : Refinement source choice)
    (old : Ref source.coupling.cursor.kinds .reading) :
    comparisonAnchor result.measurement.head.head ≠ result.history.transport.references old := by
  intro same
  have across := history_transport_append result.relays result.measurement.history old
  let suffix : History result.measurement.ready result.measurement.head.next :=
    .extend .root (.encountered result.measurement.head)
  have final := history_transport_append result.measurement.deliveries suffix
    (result.relays.transport.references old)
  exact comparison_anchor_fresh result.measurement.head.head _ ((same.trans across).trans final)

end RelationalPerimeter.Relativity.Production.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Encounter.pathFraction
#print axioms RelationalPerimeter.Relativity.Production.Encounter.paired_value_fraction
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Refinement.drift
#print axioms RelationalPerimeter.Relativity.Production.Encounter.refinement_affine_reading
#print axioms RelationalPerimeter.Relativity.Production.Encounter.MeasurementChain.drift
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_chain_affine_reading
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_chain_returns_original_reading
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_anchor_is_fresh
#print axioms RelationalPerimeter.Relativity.Production.Encounter.refined_encounter_is_not_an_old_occurrence
/- AXIOM_AUDIT_END -/
