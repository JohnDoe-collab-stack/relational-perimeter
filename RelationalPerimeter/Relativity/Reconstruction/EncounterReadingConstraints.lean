import RelationalPerimeter.Relativity.Reconstruction.LocationAgreement
import RelationalPerimeter.Relativity.Production.ConjunctiveReadingCovers

/-!
# Constraints and finite covers on an admitted encounter

The encounter's recorded reading is a consumer of its actual local anchor.
Local agreement carries constraints on that anchor between participants; it
does not carry arbitrary reception or path constraints between them. Rich
constraints follow an exact reexpression of the same participant. Numerical
refinement and cover selection do not produce a new encounter or erase its
effects. Their windows are readings, not physical neighborhoods of R4.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter

def LocalizedPresentation.richReexpression {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) :
    AttachedDescriptionAgreement presentation.attachment (presentation.reexpress raccord).attachment := by
  cases presentation with
  | mk participant path => cases participant with
    | left => exact .reexpression (InteractionAttachment.first production.head path) raccord
    | right => exact .reexpression (InteractionAttachment.second production.head path) raccord

def LocalizedPresentation.reading {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) : Rational :=
  current.read presentation.location

theorem location_reading_is_anchor {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) :
    presentation.reading = attachedNumericReading presentation.attachment .interaction := rfl

theorem location_reading_agreement {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target} (agreement : LocationAgreement production one two) :
    two.reading = one.reading := site_agreement_anchor_reading agreement.site

def locationClauses (windows : List ReadingWindow) : List AttachedReadingConstraint :=
  windows.map (fun window => ⟨.interaction, window⟩)

def LocationAgreement.transportConstraints {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target} (agreement : LocationAgreement production one two) :
    (windows : List ReadingWindow) → CertifiedReadingConstraints one.attachment (locationClauses windows) →
      CertifiedReadingConstraints two.attachment (locationClauses windows)
  | [], .nil => .nil
  | _ :: rest, .cons reading tail => .cons
      ⟨reading.value, reading.valueExact.trans (location_reading_agreement agreement).symm, reading.inside⟩
      (agreement.transportConstraints rest tail)

theorem location_constraint_transport_values {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target} (agreement : LocationAgreement production one two)
    (windows : List ReadingWindow) (readings : CertifiedReadingConstraints one.attachment (locationClauses windows)) :
    (agreement.transportConstraints windows readings).values = readings.values := by
  induction windows with
  | nil => cases readings; rfl
  | cons window rest ih => cases readings with
    | cons reading tail => exact congrArg (List.cons reading.value) (ih tail)

theorem location_constraints_agree {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target} (agreement : LocationAgreement production one two)
    (windows : List ReadingWindow) :
    ReadingConstraintsSatisfied two.attachment (locationClauses windows) ↔
      ReadingConstraintsSatisfied one.attachment (locationClauses windows) := by
  induction windows with
  | nil => exact ⟨id, id⟩
  | cons window rest ih =>
    change (_ ∧ _) ↔ (_ ∧ _)
    have same := location_reading_agreement agreement
    change two.reading = one.reading at same
    change (window.Contains two.reading ∧ _) ↔ (window.Contains one.reading ∧ _)
    rw [same]
    exact ⟨fun all => ⟨all.1, ih.mp all.2⟩, fun all => ⟨all.1, ih.mpr all.2⟩⟩

def LocationAgreement.selectCover {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target} (agreement : LocationAgreement production one two)
    (windows : List ReadingWindow) (cover : InstrumentalConstraintCover (locationClauses windows))
    (readings : CertifiedReadingConstraints one.attachment (locationClauses windows)) :
    CoveredReadingConstraints two.attachment cover := cover.select (agreement.transportConstraints windows readings)

theorem located_cover_uses_recorded_values {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target} (agreement : LocationAgreement production one two)
    (windows : List ReadingWindow) (cover : InstrumentalConstraintCover (locationClauses windows))
    (readings : CertifiedReadingConstraints one.attachment (locationClauses windows)) :
    (agreement.selectCover windows cover readings).refined.values = readings.values :=
  (selected_joint_cover_values cover _).trans (location_constraint_transport_values agreement windows readings)

theorem location_refinement_keeps_effects {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current)
    {coarse fine} (readings : CertifiedReadingConstraints presentation.attachment fine)
    (refinement : ReadingConstraintRefinement coarse fine) :
    (readings.restrict refinement).values = readings.values ∧
      AttachedEffects presentation = presentation.attachment.effects :=
  ⟨constraint_restriction_values readings refinement, rfl⟩

theorem located_constraints_prolong {source admitted production} {current target : State}
    (presentation : @LocalizedPresentation source admitted production current.cursor)
    (history : Encounter.History current target) (clauses : List AttachedReadingConstraint) :
    ReadingConstraintsSatisfied (presentation.prolong history).attachment clauses ↔
      ReadingConstraintsSatisfied presentation.attachment clauses := by
  cases presentation with
  | mk participant path => cases participant with
    | left => exact constraint_satisfaction_prolong (InteractionAttachment.first production.head path) history.resources clauses
    | right => exact constraint_satisfaction_prolong (InteractionAttachment.second production.head path) history.resources clauses

theorem located_constraints_reexpress {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) (clauses : List AttachedReadingConstraint) :
    ReadingConstraintsSatisfied (presentation.reexpress raccord).attachment clauses ↔
      ReadingConstraintsSatisfied presentation.attachment clauses :=
  constraint_satisfaction_transport (presentation.richReexpression raccord) clauses

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocalizedPresentation.richReexpression
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_reading_agreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocationAgreement.transportConstraints
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_constraint_transport_values
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_constraints_agree
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocationAgreement.selectCover
#print axioms RelationalPerimeter.Relativity.Reconstruction.located_cover_uses_recorded_values
#print axioms RelationalPerimeter.Relativity.Reconstruction.location_refinement_keeps_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.located_constraints_prolong
#print axioms RelationalPerimeter.Relativity.Reconstruction.located_constraints_reexpress
/- AXIOM_AUDIT_END -/
