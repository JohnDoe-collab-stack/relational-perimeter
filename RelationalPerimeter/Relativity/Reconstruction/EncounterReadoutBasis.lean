import RelationalPerimeter.Relativity.Reconstruction.EncounterPrecisionDescriptions
import RelationalPerimeter.Relativity.Reconstruction.LinkedEncounterLocations

/-!
# A finite open reading basis interpreted on constituted encounters

Each basic clause bounds an actual interaction reading strictly; membership
is a positive certificate on its recorded presentation. Finite meets, cover
selection and precision restriction preserve that realization. Agreement of
all these neighborhoods characterizes precisely equality of anchor readings,
not equality of occurrences or a physical location raccord.

This is the observational part of R4.3, not a reconstructed physical topology.
The last theorem retains the obstruction explicitly: an actual used passage
can have indistinguishable readings and distinct interaction occurrences.
It does not assert that those occurrences must be different spacetime points.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Analysis

structure EncounterReadoutNeighborhood where
  windows : List ReadingWindow

def EncounterReadoutNeighborhood.Member {source admitted production current}
    (neighborhood : EncounterReadoutNeighborhood)
    (presentation : @LocalizedPresentation source admitted production current) : Type :=
  CertifiedReadingConstraints presentation.attachment (locationClauses neighborhood.windows)

def EncounterReadoutNeighborhood.admitted {source admitted production current}
    (neighborhood : EncounterReadoutNeighborhood)
    (presentation : @LocalizedPresentation source admitted production current) : Bool :=
  readingConstraintsAdmitted presentation.attachment (locationClauses neighborhood.windows)

def EncounterReadoutNeighborhood.meet (first second : EncounterReadoutNeighborhood) : EncounterReadoutNeighborhood :=
  ⟨first.windows ++ second.windows⟩

theorem location_clauses_append (first second : List ReadingWindow) :
    locationClauses (first ++ second) = locationClauses first ++ locationClauses second := by
  induction first with
  | nil => rfl
  | cons window rest ih => exact congrArg (List.cons ⟨.interaction, window⟩) ih

def meetEncounterReadouts {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (first second : EncounterReadoutNeighborhood)
    (one : first.Member presentation) (two : second.Member presentation) :
    (first.meet second).Member presentation := by
  change CertifiedReadingConstraints presentation.attachment (locationClauses (first.windows ++ second.windows))
  rw [location_clauses_append]
  exact one.append two

theorem encounter_readout_meet_exact {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current)
    (first second : EncounterReadoutNeighborhood) :
    ReadingConstraintsSatisfied presentation.attachment (locationClauses (first.meet second).windows) ↔
      ReadingConstraintsSatisfied presentation.attachment (locationClauses first.windows) ∧
      ReadingConstraintsSatisfied presentation.attachment (locationClauses second.windows) := by
  cases first with | mk first =>
    induction first with
    | nil => exact ⟨fun satisfied => ⟨True.intro, satisfied⟩, fun both => both.2⟩
    | cons window rest ih =>
      exact ⟨fun satisfied =>
        ⟨⟨satisfied.1, (ih.mp satisfied.2).1⟩, (ih.mp satisfied.2).2⟩,
        fun both => ⟨both.1.1, ih.mpr ⟨both.1.2, both.2⟩⟩⟩

/-- Its center is read from the actual encounter, not supplied as a point. -/
def LocalizedPresentation.readoutNeighborhood {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current)
    (precision : Precision) : EncounterReadoutNeighborhood :=
  ⟨[ReadingWindow.atPrecision presentation.reading precision]⟩

def LocalizedPresentation.realizeReadoutNeighborhood {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) (precision : Precision) :
    (presentation.readoutNeighborhood precision).Member presentation :=
  .cons ⟨presentation.reading, rfl, precision_window_contains _ _⟩ .nil

theorem encountered_readout_basis_covers {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) (precision : Precision) :
    (presentation.readoutNeighborhood precision).admitted presentation = true :=
  (reading_constraints_admission_exact ..).mpr (presentation.realizeReadoutNeighborhood precision).satisfied

theorem encountered_basis_has_requested_precision {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) (precision : Precision) :
    ReadingSpansBounded precision (locationClauses (presentation.readoutNeighborhood precision).windows) :=
  ⟨(precision_window_span _ _).symm ▸ Rational.le_refl precision.value, True.intro⟩

def LocationAgreement.transportNeighborhood {source admitted production current target}
    {one : @LocalizedPresentation source admitted production current}
    {two : @LocalizedPresentation source admitted production target}
    (agreement : LocationAgreement production one two) (neighborhood : EncounterReadoutNeighborhood)
    (member : neighborhood.Member one) : neighborhood.Member two :=
  agreement.transportConstraints neighborhood.windows member

def selectEncounterReadoutCover {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (neighborhood : EncounterReadoutNeighborhood)
    (cover : InstrumentalConstraintCover (locationClauses neighborhood.windows))
    (member : neighborhood.Member presentation) : CoveredReadingConstraints presentation.attachment cover :=
  cover.select member

theorem encountered_cover_returns_realization {source admitted production current}
    {presentation : @LocalizedPresentation source admitted production current}
    (neighborhood : EncounterReadoutNeighborhood)
    (cover : InstrumentalConstraintCover (locationClauses neighborhood.windows))
    (member : neighborhood.Member presentation) :
    (selectEncounterReadoutCover neighborhood cover member).restrict = member := selected_joint_cover_restricts ..

theorem encounter_readout_neighborhoods_determine_reading
    {sourceOne admittedOne productionOne currentOne sourceTwo admittedTwo productionTwo currentTwo}
    (one : @LocalizedPresentation sourceOne admittedOne productionOne currentOne)
    (two : @LocalizedPresentation sourceTwo admittedTwo productionTwo currentTwo) :
    (∀ neighborhood : EncounterReadoutNeighborhood, neighborhood.admitted one = neighborhood.admitted two) ↔
      one.reading = two.reading := by
  constructor
  · intro agree
    apply (numerical_readers_determine_values one.attachment .interaction two.attachment .interaction).mp
    intro window
    have singleton := agree ⟨[window]⟩
    change readingConstraintsAdmitted one.attachment [⟨.interaction, window⟩] =
      readingConstraintsAdmitted two.attachment [⟨.interaction, window⟩] at singleton
    rw [constraint_admission_singleton, constraint_admission_singleton] at singleton
    exact singleton
  · intro same neighborhood
    cases neighborhood with | mk windows =>
      induction windows with
      | nil => rfl
      | cons window rest ih =>
        change readingConstraintsAdmitted one.attachment (⟨.interaction, window⟩ :: locationClauses rest) =
          readingConstraintsAdmitted two.attachment (⟨.interaction, window⟩ :: locationClauses rest)
        rw [constraint_admission_cons, constraint_admission_cons,
          (numerical_readers_determine_values one.attachment .interaction two.attachment .interaction).mpr same window]
        exact congrArg (fun tail => numericWindowAdmitted two.attachment .interaction window && tail) ih

/-- Positive separation of two actual readings, not separation of locations. -/
def separateEncounterReadouts
    {sourceOne admittedOne productionOne currentOne sourceTwo admittedTwo productionTwo currentTwo}
    (one : @LocalizedPresentation sourceOne admittedOne productionOne currentOne)
    (two : @LocalizedPresentation sourceTwo admittedTwo productionTwo currentTwo)
    (different : one.reading ≠ two.reading) : NumericReadingSeparation one.attachment .interaction two.attachment .interaction :=
  numericReadingSeparationOfDifferent one.attachment .interaction two.attachment .interaction different

theorem passage_readouts_do_not_determine_occurrence {source admitted origin}
    (link : @LinkedEncounter source admitted origin)
    (same : (localizeParticipant link.production .left).reading = (priorEncounterLeft link).reading) :
    (∀ neighborhood : EncounterReadoutNeighborhood,
      neighborhood.admitted (localizeParticipant link.production .left) = neighborhood.admitted (priorEncounterLeft link)) ∧
      (localizeParticipant link.production .left).location ≠ (priorEncounterLeft link).location :=
  ⟨(encounter_readout_neighborhoods_determine_reading _ _).mpr same, passage_does_not_identify_locations link⟩

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterReadoutNeighborhood
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterReadoutNeighborhood.Member
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterReadoutNeighborhood.admitted
#print axioms RelationalPerimeter.Relativity.Reconstruction.meetEncounterReadouts
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_readout_meet_exact
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocalizedPresentation.realizeReadoutNeighborhood
#print axioms RelationalPerimeter.Relativity.Reconstruction.encountered_readout_basis_covers
#print axioms RelationalPerimeter.Relativity.Reconstruction.encountered_basis_has_requested_precision
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocationAgreement.transportNeighborhood
#print axioms RelationalPerimeter.Relativity.Reconstruction.selectEncounterReadoutCover
#print axioms RelationalPerimeter.Relativity.Reconstruction.encountered_cover_returns_realization
#print axioms RelationalPerimeter.Relativity.Reconstruction.encounter_readout_neighborhoods_determine_reading
#print axioms RelationalPerimeter.Relativity.Reconstruction.separateEncounterReadouts
#print axioms RelationalPerimeter.Relativity.Reconstruction.passage_readouts_do_not_determine_occurrence
/- AXIOM_AUDIT_END -/
