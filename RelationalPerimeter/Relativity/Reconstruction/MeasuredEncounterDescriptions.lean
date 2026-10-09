import RelationalPerimeter.Relativity.Production.EncounterRelativePaths
import RelationalPerimeter.Relativity.Reconstruction.EncounterReadingConstraints

/-!
# Descriptions of the encounter that consumed the measured paths

The existing local agreement is consumed on the exact cached measurement
head. Its transported anchor still denotes that old encounter, not a future
event or an ideal spacetime point. Reading constraints apply to the raw
comparison anchor; the relative reader is kept distinct. Both rich path
effects remain accessible through every actual suffix.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources

def measuredFirst {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) :=
  (localizeParticipant result.head .left).prolong history

def measuredSecond {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) :=
  (localizeParticipant result.head .right).prolong history

def measuredEncounterAgreement {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) :
    LocationAgreement result.head (measuredFirst result history) (measuredSecond result history) :=
  continuedLocationAgreement result.head history

theorem measured_encounter_sources_stay_distinct {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) :
    (measuredFirst result history).attachment.readingReference ≠
      (measuredSecond result history).attachment.readingReference := by
  dsimp only [measuredFirst, measuredSecond, LocalizedPresentation.prolong, localizeParticipant,
    LocalizedPresentation.attachment]
  exact participants_remain_distinct result.head.head _

theorem measured_encounter_keeps_effects {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) :
    AttachedEffects (measuredFirst result history) = source.coupling.cursor.read source.reading.firstSignal ∧
    AttachedEffects (measuredSecond result history) = source.coupling.cursor.read source.reading.secondSignal :=
  ⟨(localized_prolong_effects _ history).trans (measurement_first_effect result),
    (localized_prolong_effects _ history).trans (measurement_second_effect result)⟩

def measuredRelativeValue {source} (result : Measurement source) : Rational :=
  Rational.mul (Rational.sub result.head.effects.1.reading
    (source.coupling.cursor.read source.reading.numerator.origin).reading)
      (Rational.inverseNatSucc (result.reading.denominator.relayCount - 1))

theorem measured_ratio_reads_consumed_effect {source} (result : Measurement source) :
    measuredRelativeValue result = result.next.reading.value := by
  rw [measurement_keeps_ratio]
  unfold measuredRelativeValue
  rw [measurement_first_effect, result.denominatorExact]
  rfl

/-- The existing constraint consumer now takes the exact measurement head.
It licenses descriptive transport only, never erasure of rich path effects. -/
def measuredAnchorConstraints {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints (measuredFirst result history).attachment (locationClauses windows)) :
    CertifiedReadingConstraints (measuredSecond result history).attachment (locationClauses windows) :=
  (measuredEncounterAgreement result history).transportConstraints windows readings

theorem measured_anchor_constraints_return_values {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints (measuredFirst result history).attachment (locationClauses windows)) :
    (measuredAnchorConstraints result history windows readings).values = readings.values :=
  location_constraint_transport_values (measuredEncounterAgreement result history) windows readings

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredFirst
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredSecond
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredEncounterAgreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_encounter_sources_stay_distinct
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_encounter_keeps_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredRelativeValue
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_ratio_reads_consumed_effect
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredAnchorConstraints
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_anchor_constraints_return_values
/- AXIOM_AUDIT_END -/
