import RelationalPerimeter.Relativity.Reconstruction.EncounterReadingConstraints
import RelationalPerimeter.Relativity.Production.ReadingCompatibility

/-!
# Positive precision descriptions of an actual encounter

Only interaction-anchor clauses are transported in this interface. A precision
step consumes its received certificates, intersects their windows with
windows computed from their stored values, and returns positive restrictions.
The next request starts from this result. Local agreement transports these
descriptions between participants without transporting their arrival effects.

This closes the descriptive part of R4.2 on an existing encounter. It does
not generate locations beyond executed events, nor identify this numerical
reader language with the physical neighborhood language required by R4.3.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Analysis

structure EncounterPrecisionDescription {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current)
    (coarse : List ReadingWindow) where
  windows : List ReadingWindow
  refinement : ReadingConstraintRefinement (locationClauses coarse) (locationClauses windows)
  readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows)

def EncounterPrecisionDescription.identity {source admitted production current presentation windows}
    (readings : CertifiedReadingConstraints
      (@LocalizedPresentation.attachment source admitted production current presentation) (locationClauses windows)) :
    EncounterPrecisionDescription presentation windows :=
  ⟨windows, .identity _, readings⟩

/-- No completed precision course is an input to this local step. -/
def refineEncounterPrecision {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current} :
    (windows : List ReadingWindow) →
    CertifiedReadingConstraints presentation.attachment (locationClauses windows) →
    Precision → EncounterPrecisionDescription presentation windows
  | [], .nil, _ => ⟨[], .nil, .nil⟩
  | window :: rest, .cons reading tail, precision =>
    let centered := reading.atPrecision precision
    let fine := reading.common centered
    let suffix := refineEncounterPrecision rest tail precision
    ⟨window.intersection (ReadingWindow.atPrecision reading.value precision) :: suffix.windows,
      .cons (window_intersection_left _ _) suffix.refinement, .cons fine suffix.readings⟩

theorem encounter_precision_restricts_exactly {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows)) (precision : Precision) :
    (refineEncounterPrecision windows readings precision).readings.restrict
      (refineEncounterPrecision windows readings precision).refinement = readings := by
  induction windows with
  | nil => cases readings; rfl
  | cons window rest ih => cases readings with
    | cons reading tail =>
      change CertifiedReadingConstraints.cons
        ((reading.common (reading.atPrecision precision)).restrict (window_intersection_left _ _))
        ((refineEncounterPrecision rest tail precision).readings.restrict
          (refineEncounterPrecision rest tail precision).refinement) = _
      rw [(numeric_common_restrictions reading (reading.atPrecision precision)).1, ih tail]
      rfl

theorem encounter_precision_bounds_every_window {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows)) (precision : Precision) :
    ReadingSpansBounded precision (locationClauses (refineEncounterPrecision windows readings precision).windows) := by
  induction windows with
  | nil => cases readings; exact True.intro
  | cons window rest ih => cases readings with
    | cons reading tail =>
      refine ⟨?_, ih tail⟩
      have bound := (window_intersection_right window (ReadingWindow.atPrecision reading.value precision)).span_le
      rw [precision_window_span] at bound
      exact bound

def EncounterPrecisionDescription.compose {source admitted production current presentation coarse}
    (first : @EncounterPrecisionDescription source admitted production current presentation coarse)
    (second : EncounterPrecisionDescription presentation first.windows) : EncounterPrecisionDescription presentation coarse :=
  ⟨second.windows, first.refinement.compose second.refinement, second.readings⟩

def LocationAgreement.transportPrecision {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target}
    (agreement : LocationAgreement production one two) {windows}
    (description : EncounterPrecisionDescription one windows) : EncounterPrecisionDescription two windows :=
  ⟨description.windows, description.refinement,
    agreement.transportConstraints description.windows description.readings⟩

def LocationAgreement.transportAnchorReading {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target}
    (agreement : LocationAgreement production one two) (window : ReadingWindow)
    (reading : CertifiedNumericReading one.attachment .interaction window) :
    CertifiedNumericReading two.attachment .interaction window :=
  match agreement.transportConstraints [window] (.cons reading .nil) with
  | .cons translated .nil => translated

theorem location_precision_transport_square {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target}
    (agreement : LocationAgreement production one two) (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints one.attachment (locationClauses windows)) (precision : Precision) :
    agreement.transportPrecision (refineEncounterPrecision windows readings precision) =
      refineEncounterPrecision windows (agreement.transportConstraints windows readings) precision := by
  induction windows with
  | nil => cases readings; rfl
  | cons window rest ih => cases readings with
    | cons reading tail =>
      exact congrArg (fun suffix : EncounterPrecisionDescription two rest =>
        @EncounterPrecisionDescription.mk source admitted production target two (window :: rest)
          (window.intersection (ReadingWindow.atPrecision reading.value precision) :: suffix.windows)
          (.cons (window_intersection_left window (ReadingWindow.atPrecision reading.value precision)) suffix.refinement)
          (@CertifiedReadingConstraints.cons source.cursor admitted.pair production.head target two.attachment
            ⟨.interaction, window.intersection (ReadingWindow.atPrecision reading.value precision)⟩
            (locationClauses suffix.windows)
            (agreement.transportAnchorReading _ (reading.common (reading.atPrecision precision)))
            suffix.readings)) (ih tail)

/-- The head is formed from the received certificates before the suffix. -/
def runEncounterPrecisions {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows)) :
    List Precision → EncounterPrecisionDescription presentation windows
  | [] => .identity readings
  | precision :: rest =>
    let head := refineEncounterPrecision windows readings precision
    let suffix := runEncounterPrecisions head.windows head.readings rest
    head.compose suffix

theorem encounter_precision_run_returns {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows))
    (requests : List Precision) :
    (runEncounterPrecisions windows readings requests).readings.restrict
      (runEncounterPrecisions windows readings requests).refinement = readings := by
  induction requests generalizing windows with
  | nil => exact constraint_restriction_identity readings
  | cons precision rest ih =>
    change ((runEncounterPrecisions _ _ rest).readings.restrict
      ((refineEncounterPrecision windows readings precision).refinement.compose
        (runEncounterPrecisions _ _ rest).refinement)) = _
    rw [← constraint_restriction_composes, ih, encounter_precision_restricts_exactly]

theorem encounter_precision_run_bounds {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows))
    (requests : List Precision) (precision : Precision) (requested : precision ∈ requests) :
    ReadingSpansBounded precision (locationClauses (runEncounterPrecisions windows readings requests).windows) := by
  induction requests generalizing windows with
  | nil => cases requested
  | cons head rest ih =>
    cases requested with
    | head =>
      let refined := refineEncounterPrecision windows readings precision
      have bound := encounter_precision_bounds_every_window windows readings precision
      exact span_bounds_survive_refinement
        (runEncounterPrecisions refined.windows refined.readings rest).refinement precision bound
    | tail _ later =>
      exact ih (refineEncounterPrecision windows readings head).windows
        (refineEncounterPrecision windows readings head).readings later

/-- A previously produced description is the input, not reconstructed. -/
def EncounterPrecisionDescription.resume {source admitted production current presentation coarse}
    (description : @EncounterPrecisionDescription source admitted production current presentation coarse)
    (requests : List Precision) : EncounterPrecisionDescription presentation coarse :=
  description.compose (runEncounterPrecisions description.windows description.readings requests)

theorem encounter_precision_resume_returns {source admitted production current presentation coarse}
    (description : @EncounterPrecisionDescription source admitted production current presentation coarse)
    (requests : List Precision) :
    (description.resume requests).readings.restrict (description.resume requests).refinement =
      description.readings.restrict description.refinement := by
  change ((runEncounterPrecisions _ _ requests).readings.restrict
    (description.refinement.compose (runEncounterPrecisions _ _ requests).refinement)) = _
  rw [← constraint_restriction_composes, encounter_precision_run_returns]

theorem encounter_precision_composition_associates {source admitted production current presentation coarse}
    (first : @EncounterPrecisionDescription source admitted production current presentation coarse)
    (second : EncounterPrecisionDescription presentation first.windows)
    (third : EncounterPrecisionDescription presentation second.windows) :
    (first.compose second).compose third = first.compose (second.compose third) := by
  exact congrArg (fun refinement => EncounterPrecisionDescription.mk third.windows refinement third.readings)
    (constraint_refinement_associates first.refinement second.refinement third.refinement)

theorem encounter_precision_run_append {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows))
    (first second : List Precision) :
    (runEncounterPrecisions windows readings first).resume second =
      runEncounterPrecisions windows readings (first ++ second) := by
  induction first generalizing windows with
  | nil =>
    apply congrArg (fun refinement => EncounterPrecisionDescription.mk _ refinement _)
    exact constraint_refinement_identity_left _
  | cons precision rest ih =>
    let head := refineEncounterPrecision windows readings precision
    let suffix := runEncounterPrecisions head.windows head.readings rest
    exact (encounter_precision_composition_associates head suffix
      (runEncounterPrecisions suffix.windows suffix.readings second)).trans
        (congrArg (fun tail => head.compose tail) (ih head.windows head.readings))

theorem location_precision_composition_transport {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target}
    (agreement : LocationAgreement production one two) {windows}
    (first : EncounterPrecisionDescription one windows)
    (second : EncounterPrecisionDescription one first.windows) :
    agreement.transportPrecision (first.compose second) =
      (agreement.transportPrecision first).compose (agreement.transportPrecision second) := rfl

theorem location_precision_run_transport_square {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target}
    (agreement : LocationAgreement production one two) (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints one.attachment (locationClauses windows)) (requests : List Precision) :
    agreement.transportPrecision (runEncounterPrecisions windows readings requests) =
      runEncounterPrecisions windows (agreement.transportConstraints windows readings) requests := by
  induction requests generalizing windows with
  | nil => rfl
  | cons precision rest ih =>
    let head := refineEncounterPrecision windows readings precision
    exact (location_precision_composition_transport agreement head
      (runEncounterPrecisions head.windows head.readings rest)).trans
      ((congrArg (fun suffix : EncounterPrecisionDescription two head.windows =>
        (agreement.transportPrecision head).compose suffix) (ih head.windows head.readings)).trans
        (congrArg (fun description : EncounterPrecisionDescription two windows =>
          description.compose (runEncounterPrecisions description.windows description.readings rest))
            (location_precision_transport_square agreement windows readings precision)))

theorem encounter_precision_run_keeps_values {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints presentation.attachment (locationClauses windows)) (requests : List Precision) :
    (runEncounterPrecisions windows readings requests).readings.values = readings.values := by
  have values := constraint_restriction_values (runEncounterPrecisions windows readings requests).readings
    (runEncounterPrecisions windows readings requests).refinement
  rw [encounter_precision_run_returns] at values
  exact values.symm

/-- Two actual descriptive courses have a positively realized common
refinement on the same encounter attachment, not a postulated limit point. -/
def commonEncounterPrecisions {source admitted production current presentation coarse}
    (first second : @EncounterPrecisionDescription source admitted production current presentation coarse) :
    CommonReadingRefinement presentation.attachment (locationClauses first.windows) (locationClauses second.windows) :=
  let alignment := ReadingConstraintIntersection.fromRefinements first.refinement second.refinement
  ⟨alignment, alignment.certify first.readings second.readings⟩

theorem common_encounter_precisions_return_both {source admitted production current presentation coarse}
    (first second : @EncounterPrecisionDescription source admitted production current presentation coarse) :
    (commonEncounterPrecisions first second).readings.restrict
        (commonEncounterPrecisions first second).alignment.left = first.readings ∧
      (commonEncounterPrecisions first second).readings.restrict
        (commonEncounterPrecisions first second).alignment.right = second.readings :=
  realized_intersection_returns _ _ _

theorem common_encounter_precisions_keep_bounds {source admitted production current presentation coarse}
    (first second : @EncounterPrecisionDescription source admitted production current presentation coarse)
    (one two : Precision) (firstBound : ReadingSpansBounded one (locationClauses first.windows))
    (secondBound : ReadingSpansBounded two (locationClauses second.windows)) :
    ReadingSpansBounded one (commonEncounterPrecisions first second).alignment.clauses ∧
      ReadingSpansBounded two (commonEncounterPrecisions first second).alignment.clauses :=
  ⟨span_bounds_survive_refinement (commonEncounterPrecisions first second).alignment.left one firstBound,
    span_bounds_survive_refinement (commonEncounterPrecisions first second).alignment.right two secondBound⟩

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterPrecisionDescription
#print axioms RelationalPerimeter.Relativity.Reconstruction.refineEncounterPrecision
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_restricts_exactly
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_bounds_every_window
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocationAgreement.transportPrecision
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocationAgreement.transportAnchorReading
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_precision_transport_square
#print axioms RelationalPerimeter.Relativity.Reconstruction.runEncounterPrecisions
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_run_returns
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_run_bounds
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterPrecisionDescription.resume
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_resume_returns
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_composition_associates
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_run_append
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_precision_composition_transport
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_precision_run_transport_square
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_precision_run_keeps_values
#print axioms RelationalPerimeter.Relativity.Reconstruction.commonEncounterPrecisions
#print axioms RelationalPerimeter.Relativity.Reconstruction.common_encounter_precisions_return_both
#print axioms RelationalPerimeter.Relativity.Reconstruction.common_encounter_precisions_keep_bounds
/- AXIOM_AUDIT_END -/
