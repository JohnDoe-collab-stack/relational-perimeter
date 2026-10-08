import RelationalPerimeter

/-! Public client of joint covers on real receptions and their comparison.
The exchanged receptions remain distinct; numerical overlap identifies none. -/
set_option genInjectivity false
namespace Tests.Relativity.ConjunctiveCoverChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def arrivals (value : Rational) : (source : Cursor) ×' ArrivalPair source :=
  let supplied := Cursor.received ⟨value, 7, Calibration.unit⟩
  let emitted := (perform supplied emission).successor
  let first := perform emitted (.receive .here)
  let second := perform first.successor (.receive (.prior .here))
  ⟨second.successor, ⟨.prior .here, .here, .prior (.prior .here), .prior (.prior .here),
    .inherited second.determination.2 (arrivalOfProduction first), arrivalOfProduction second,
    fun same => fresh_distinct first.successor second.determination .here same.symm⟩⟩

def stored (value : Rational) :=
  produceStoredPair (arrivals value).1 (.receive (arrivals value).2.firstSignal)
    (.receive (.prior (arrivals value).2.secondSignal))

theorem an_exchange_is_actually_found (value : Rational) : exchangeFound (stored value) = true := rfl

def found (value : Rational) := discoveredExchangeOfFound (stored value) (an_exchange_is_actually_found value)

def origin (value : Rational) : RecurringCursor := .fromCursor (stored value).cursor

def pair (value : Rational) : RecurringPair (origin value) :=
  ⟨.prior .here, .here, .prior (.prior (arrivals value).2.firstSignal),
    .prior (.prior (arrivals value).2.secondSignal),
    .fromCursor (.inherited (stored value).secondDetermination.2
      (Arrived.ofReception (arrivals value).1.formation (stored value).firstDetermination.2)),
    .fromCursor (Arrived.ofReception ((arrivals value).1.extend (stored value).firstDetermination).formation
      (stored value).secondDetermination.2), fun same =>
        fresh_distinct ((arrivals value).1.extend (stored value).firstDetermination)
          (stored value).secondDetermination .here same.symm⟩

def head (value : Rational) := performRecurring (origin value) (.compare (pair value))
def attached (value : Rational) := InteractionAttachment.first (head value) .root
def partner (value : Rational) := InteractionAttachment.second (head value) .root

def transportedHead (value : Rational) := transportRecurringProduction (found value).raccord.constitution (head value)
def changed (value : Rational) := (found value).raccord.afterProduction (head value) (transportedHead value)
def renamed (value : Rational) := (attached value).reexpress (changed value)
def agreement (value : Rational) := AttachedDescriptionAgreement.reexpression (attached value) (changed value)

def arrivalWindow : ReadingWindow := ⟨Rational.neg Rational.one, Rational.ofNat 4⟩
def comparisonWindow : ReadingWindow := ⟨Rational.neg Rational.one, Rational.one⟩
def arrivalSplit : OverlappingWindowSplit arrivalWindow :=
  ⟨Rational.one, Rational.ofNat 2, by decide, by decide, by decide⟩
def comparisonSplit : OverlappingWindowSplit comparisonWindow :=
  ⟨Rational.neg (Rational.ofParts 1 0 1), Rational.neg (Rational.ofParts 1 0 3),
    by decide, by decide, by decide⟩
def arrivalCover : InstrumentalReadingCover arrivalWindow := .split arrivalSplit (.identity _) (.identity _)
def comparisonCover : InstrumentalReadingCover comparisonWindow := .split comparisonSplit (.identity _) (.identity _)
def clauses : List AttachedReadingConstraint := [⟨.arrival, arrivalWindow⟩, ⟨.interaction, comparisonWindow⟩]
def cover : InstrumentalConstraintCover clauses := .cons arrivalCover (.cons comparisonCover .nil)

def accepted (value : Rational) : Bool :=
  match decideConjunctiveCover (attached value) cover with | .inl _ => true | .inr _ => false

theorem zero_joint_admitted : readingConstraintsAdmitted (attached Rational.zero) clauses = true := rfl
theorem one_joint_admitted : readingConstraintsAdmitted (attached Rational.one) clauses = true := rfl
theorem three_joint_admitted : readingConstraintsAdmitted (attached (Rational.ofNat 3)) clauses = true := rfl

def zeroReadings := certifiedReadingConstraintsOfAdmitted (attached Rational.zero) clauses zero_joint_admitted
def oneReadings := certifiedReadingConstraintsOfAdmitted (attached Rational.one) clauses one_joint_admitted
def threeReadings := certifiedReadingConstraintsOfAdmitted (attached (Rational.ofNat 3)) clauses three_joint_admitted
def zeroChoice := cover.select zeroReadings
def oneChoice := cover.select oneReadings
def threeChoice := cover.select threeReadings

theorem one_decision_returns_its_actual_choice : decideConjunctiveCover (attached Rational.one) cover = .inl oneChoice := rfl
theorem accepted_run : accepted Rational.one = true := rfl
theorem outer_boundary_refused : accepted (Rational.ofNat 4) = false := rfl
/- Only the elaboration depth of these closed, positive reception fixtures
is raised; the equations are still checked by kernel reduction. -/
set_option maxRecDepth 2048 in
theorem the_first_actual_values : oneChoice.refined.values = [Rational.one, Rational.zero] := rfl
set_option maxRecDepth 2048 in
theorem the_second_actual_values : threeChoice.refined.values = [Rational.ofNat 3, Rational.zero] := rfl
set_option maxRecDepth 2048 in
theorem mixed_local_choices : oneChoice.paths = [[true], [false]] := rfl
set_option maxRecDepth 2048 in
theorem different_received_value_changes_a_choice : threeChoice.paths = [[false], [false]] := rfl
theorem choices_are_not_prescribed : oneChoice.paths ≠ threeChoice.paths := by decide
theorem neither_clause_is_dropped : oneChoice.fine.map AttachedReadingConstraint.port = [.arrival, .interaction] :=
  joint_cover_keeps_ports oneChoice
theorem restriction_returns_all_inputs : oneChoice.restrict = oneReadings := selected_joint_cover_restricts cover oneReadings
theorem identity_keeps_the_constraint_list :
    ((InstrumentalConstraintCover.identity clauses).select oneReadings).fine = clauses := joint_identity_fine oneReadings
theorem identity_has_no_selection_steps :
    ((InstrumentalConstraintCover.identity clauses).select oneReadings).paths = [[], []] := joint_identity_paths oneReadings
theorem joint_coverage_is_exact : ReadingConstraintsSatisfied (attached Rational.one) clauses ↔
    Nonempty (CoveredReadingConstraints (attached Rational.one) cover) := conjunctive_cover_exact _ _

def doubled := (cover.append cover).select (oneReadings.append oneReadings)
theorem concatenate_without_listing_combinations : doubled = oneChoice.append oneChoice := joint_selection_append ..
set_option maxRecDepth 2048 in
theorem all_four_local_choices_remain : doubled.paths = [[true], [false], [true], [false]] := rfl

def fineArrivalWindow : ReadingWindow := ⟨Rational.zero, Rational.ofNat 3⟩
def fineComparisonWindow : ReadingWindow := ⟨Rational.neg (Rational.ofParts 1 0 1), Rational.ofParts 1 0 1⟩
def fineClauses : List AttachedReadingConstraint :=
  [⟨.arrival, fineArrivalWindow⟩, ⟨.interaction, fineComparisonWindow⟩]
def refinement : ReadingConstraintRefinement clauses fineClauses :=
  .cons ⟨by decide, by decide⟩ (.cons ⟨by decide, by decide⟩ .nil)
def fineReadings := certifiedReadingConstraintsOfAdmitted (attached Rational.one) fineClauses (by rfl)
def pulled := pullbackConjunctiveCover cover refinement fineReadings

set_option maxRecDepth 2048 in
theorem pulled_intersection_has_both_actual_values : pulled.2.2.values = [Rational.one, Rational.zero] := rfl
theorem pulled_intersection_returns_both_inputs :
    pulled.2.2.restrict pulled.2.1.left = pulled.1.refined ∧
      pulled.2.2.restrict pulled.2.1.right = fineReadings := conjunctive_pullback_returns ..
theorem pulled_intersection_returns_the_coarse_source :
    pulled.2.2.restrict (pulled.1.refinement.compose pulled.2.1.left) = fineReadings.restrict refinement :=
  conjunctive_pullback_coarse_return ..
theorem intersection_is_exactly_a_joint_satisfaction :
    ReadingConstraintsSatisfied (attached Rational.one) pulled.2.1.clauses ↔
      ReadingConstraintsSatisfied (attached Rational.one) pulled.1.fine ∧
        ReadingConstraintsSatisfied (attached Rational.one) fineClauses := constraint_intersection_satisfaction_iff _ _

def separatedClauses : List AttachedReadingConstraint :=
  [⟨.arrival, ⟨Rational.ofNat 4, Rational.ofNat 6⟩⟩, ⟨.interaction, comparisonWindow⟩]
def incompatible : ReadingConstraintIntersection clauses separatedClauses := .cons (.cons .nil)
theorem aligned_ports_do_not_supply_a_realization (value : Rational) :
    ¬ ReadingConstraintsSatisfied (attached value) incompatible.clauses := by
  intro realized
  have both := (constraint_intersection_satisfaction_iff (attached value) incompatible).mp realized
  exact disjoint_constraints_unrealizable (attached value) .arrival arrivalWindow
    ⟨Rational.ofNat 4, Rational.ofNat 6⟩ (Rational.le_refl _) [] ⟨both.1.1, both.2.1, True.intro⟩
theorem incompatible_intersection_is_refused :
    readingConstraintsAdmitted (attached Rational.one) incompatible.clauses = false := rfl
theorem incompatible_certificate_cannot_be_installed (value : Rational)
    (readings : CertifiedReadingConstraints (attached value) incompatible.clauses) : False :=
  aligned_ports_do_not_supply_a_realization value readings.satisfied
theorem different_ports_cannot_align
    (alignment : ReadingConstraintIntersection [⟨.arrival, arrivalWindow⟩] [⟨.interaction, arrivalWindow⟩]) : False := by
  cases alignment

theorem the_presentation_change_moves_the_reference :
    (attached Rational.one).readingReference.position = 2 ∧ (renamed Rational.one).readingReference.position = 1 := ⟨rfl, rfl⟩
theorem joint_choices_transport_exactly : oneChoice.transport (agreement Rational.one) =
    cover.select (oneReadings.transport (agreement Rational.one)) := joint_selection_transport_square ..
theorem every_choice_path_survives_transport :
    (oneChoice.transport (agreement Rational.one)).paths = oneChoice.paths := joint_transport_paths ..
theorem the_realized_intersection_transports :
    (pulled.2.1.certify pulled.1.refined fineReadings).transport (agreement Rational.one) =
      pulled.2.1.certify (pulled.1.refined.transport (agreement Rational.one))
        (fineReadings.transport (agreement Rational.one)) := realized_intersection_transport_square ..

def requests : List RecurringRequest :=
  [.local (.inspect .reading (attached Rational.one).readingReference.position),
   .compare (attached Rational.one).readingReference.position (partner Rational.one).readingReference.position,
   .compare 0 0]
@[irreducible] def extension := runDescriptionExtension (agreement Rational.one).raccord requests
theorem extension_is_actual : extension = runDescriptionExtension (agreement Rational.one).raccord requests := by
  unfold extension; rfl

theorem one_shared_production_only : StrongPerimetralTurning.History.length extension.execution.first.history = 1 := by
  rw [extension_is_actual]
  change StrongPerimetralTurning.History.length (runSharedRecurring (agreement Rational.one).raccord requests).first.history = 1
  rw [(shared_recurring_runners_exact (agreement Rational.one).raccord requests).1]
  rfl
theorem selection_commutes_with_the_cached_history :
    oneChoice.prolong extension.execution.first.history = cover.select (oneReadings.prolong extension.execution.first.history) :=
  joint_selection_prolong_square ..
theorem joint_choices_and_continuation_commute :
    (oneChoice.prolong extension.execution.first.history).transport (extension.rich (agreement Rational.one)) =
      (oneChoice.transport (agreement Rational.one)).prolong extension.execution.second.history := joint_continuation_square ..
theorem the_intersection_follows_the_same_production :
    (pulled.2.1.certify pulled.1.refined fineReadings).prolong extension.execution.first.history =
      pulled.2.1.certify (pulled.1.refined.prolong extension.execution.first.history)
        (fineReadings.prolong extension.execution.first.history) := realized_intersection_prolong_square ..
theorem unchanged_contract : extension.execution.first.report = recurringContract.outcome (head Rational.one).successor requests := by
  rw [extension_is_actual]
  exact (description_extension_reports_exact (agreement Rational.one).raccord requests).1
theorem every_further_suffix_is_preserved (future : List RecurringRequest) :
    (extension.resume future).execution.first.report = recurringContract.outcome extension.execution.first.cursor future :=
  (description_extension_resume_exact extension future).1
theorem sources_still_have_their_own_identity :
    (attached Rational.one).readingReference ≠ (partner Rational.one).readingReference := participants_remain_distinct _ _

/- Requested precision is a description of already certified readings,
not a new physical production or a horizon of allowed futures. -/
def precisionRequests : List Analysis.Precision := [Analysis.Precision.unit, Analysis.Precision.unit.half]
def precise := oneChoice.precise precisionRequests
def firstPrecision := refineReadingPrecisions oneChoice.refined [Analysis.Precision.unit]
def resumedPrecision := firstPrecision.resume [Analysis.Precision.unit.half]

theorem both_requested_precisions_are_positive :
    RationalStrictLess Rational.zero Analysis.Precision.unit.value ∧
      RationalStrictLess Rational.zero Analysis.Precision.unit.half.value :=
  ⟨reading_precision_positive _, reading_precision_positive _⟩
theorem the_last_precision_is_effective : ReadingSpansBounded Analysis.Precision.unit.half precise.fine :=
  covered_precisions_last_bound oneChoice [Analysis.Precision.unit] Analysis.Precision.unit.half
theorem a_later_request_keeps_the_earlier_bound : ReadingSpansBounded Analysis.Precision.unit precise.fine :=
  covered_precisions_bound_every_request oneChoice precisionRequests Analysis.Precision.unit (.head _)
theorem precise_return_is_the_received_source : precise.readings.restrict precise.refinement = oneReadings :=
  (covered_precisions_return_the_selected_source oneChoice precisionRequests).trans restriction_returns_all_inputs
set_option maxRecDepth 2048 in
theorem precise_values_remain_the_actual_values : precise.readings.values = [Rational.one, Rational.zero] :=
  (precision_run_keeps_values oneChoice.refined precisionRequests).trans the_first_actual_values
set_option maxRecDepth 2048 in
theorem precise_ports_remain_the_actual_ports : precise.fine.map AttachedReadingConstraint.port = [.arrival, .interaction] :=
  (refinement_preserves_all_ports precise.refinement)
theorem resumption_consumes_the_existing_prefix :
    resumedPrecision = refineReadingPrecisions oneChoice.refined precisionRequests :=
  (precision_runs_append oneChoice.refined [Analysis.Precision.unit] [Analysis.Precision.unit.half]).symm
theorem resumption_returns_every_received_certificate :
    resumedPrecision.readings.restrict resumedPrecision.refinement = oneChoice.refined := by
  rw [resumption_consumes_the_existing_prefix]
  exact precision_run_restricts_exactly _ _
theorem arbitrary_finite_resumption (first second : List Analysis.Precision) :
    (firstPrecision.resume first).resume second = firstPrecision.resume (first ++ second) := precision_resume_associates ..
theorem every_requested_bound_remains (precisions : List Analysis.Precision) (precision : Analysis.Precision)
    (requested : precision ∈ precisions) : ReadingSpansBounded precision (oneChoice.precise precisions).fine :=
  covered_precisions_bound_every_request oneChoice precisions precision requested

theorem a_nonpositive_radius_is_not_a_precision (precision : Analysis.Precision)
    (nonpositive : Rational.Le precision.value Rational.zero) : False :=
  (reading_precision_positive precision).2
    (Rational.le_antisymm precision.zero_le_value nonpositive)
theorem incompatible_constraints_cannot_start_precision (value : Rational)
    (readings : CertifiedReadingConstraints (attached value) incompatible.clauses) : False :=
  incompatible_certificate_cannot_be_installed value readings

theorem precision_changes_the_window_not_just_its_label : precise.fine ≠ clauses := by
  intro same
  have bound := the_last_precision_is_effective
  rw [same] at bound
  have tooWide : ¬ Rational.Le arrivalWindow.span Analysis.Precision.unit.half.value := by decide
  exact tooWide bound.1
set_option maxRecDepth 2048 in
theorem different_received_readings_cannot_have_the_same_precision_windows :
    (oneChoice.precise precisionRequests).fine ≠ (threeChoice.precise precisionRequests).fine := by
  intro same
  have first := (oneChoice.precise precisionRequests).readings.satisfied
  have second := (threeChoice.precise precisionRequests).readings.satisfied
  rw [← same] at second
  have bounded := the_last_precision_is_effective
  have ports := precise_ports_remain_the_actual_ports
  change ReadingConstraintsSatisfied (attached Rational.one) precise.fine at first
  change ReadingConstraintsSatisfied (attached (Rational.ofNat 3)) precise.fine at second
  cases fineExact : precise.fine with
  | nil =>
    rw [fineExact] at ports
    have impossible := congrArg List.length ports
    exact Nat.noConfusion impossible
  | cons clause rest =>
    rw [fineExact] at ports first second bounded
    have port : clause.port = .arrival := by
      exact (List.cons.inj ports).1
    have v1 : attachedNumericReading (attached Rational.one) clause.port = Rational.one := by rw [port]; rfl
    have v3 : attachedNumericReading (attached (Rational.ofNat 3)) clause.port = Rational.ofNat 3 := by rw [port]; rfl
    change clause.window.Contains (attachedNumericReading (attached Rational.one) clause.port) ∧ _ at first
    change clause.window.Contains (attachedNumericReading (attached (Rational.ofNat 3)) clause.port) ∧ _ at second
    rw [v1] at first
    rw [v3] at second
    have lower := first.1.1.1
    have upper := second.1.2.1
    have span := Rational.add_le upper (Rational.neg_le_neg lower)
    have gap : Rational.Le (Rational.sub (Rational.ofNat 3) Rational.one) Analysis.Precision.unit.half.value :=
      Rational.le_trans span bounded.1
    have impossible : ¬ Rational.Le (Rational.sub (Rational.ofNat 3) Rational.one) Analysis.Precision.unit.half.value := by decide
    exact impossible gap

theorem full_precision_run_transports_without_reselecting :
    (refineReadingPrecisions oneChoice.refined precisionRequests).transport (agreement Rational.one) =
      refineReadingPrecisions (oneChoice.refined.transport (agreement Rational.one)) precisionRequests :=
  precision_run_transport_square ..
theorem full_precision_run_follows_the_cached_history :
    (refineReadingPrecisions oneChoice.refined precisionRequests).prolong extension.execution.first.history =
      refineReadingPrecisions (oneChoice.refined.prolong extension.execution.first.history) precisionRequests :=
  precision_run_prolong_square ..
theorem precise_continuation_square :
    (precise.prolong extension.execution.first.history).transport (extension.rich (agreement Rational.one)) =
      (precise.transport (agreement Rational.one)).prolong extension.execution.second.history :=
  realized_refinement_continuation_square ..
theorem arbitrary_precision_does_not_change_the_future_contract (precisions : List Analysis.Precision)
    (future : List RecurringRequest) :
    ((oneChoice.precise precisions).prolong extension.execution.first.history).fine =
        (oneChoice.precise precisions).fine ∧
      (extension.resume future).execution.first.report = recurringContract.outcome extension.execution.first.cursor future :=
  ⟨rfl, every_further_suffix_is_preserved future⟩

/- Two finite descriptions of the same received certificates have an actual
joint refinement. Its constructor consumes these results, not their requests. -/
def otherPrecision := oneChoice.precise [Analysis.Precision.unit.half]
def joinedPrecision := precise.common otherPrecision

theorem two_precision_descriptions_return_exactly :
    joinedPrecision.left.readings.restrict joinedPrecision.left.refinement = precise.readings ∧
      joinedPrecision.right.readings.restrict joinedPrecision.right.refinement = otherPrecision.readings :=
  realized_common_returns precise otherPrecision
theorem both_returns_recover_the_initial_certificates :
    joinedPrecision.readings.restrict (precise.refinement.compose joinedPrecision.alignment.left) = oneReadings ∧
      joinedPrecision.readings.restrict (otherPrecision.refinement.compose joinedPrecision.alignment.right) = oneReadings := by
  have returns := realized_common_coarse_returns precise otherPrecision
  have otherReturn : otherPrecision.readings.restrict otherPrecision.refinement = oneReadings :=
    (covered_precisions_return_the_selected_source oneChoice [Analysis.Precision.unit.half]).trans
      restriction_returns_all_inputs
  exact ⟨returns.1.trans precise_return_is_the_received_source, returns.2.trans otherReturn⟩
theorem common_description_keeps_the_precision :
    ReadingSpansBounded Analysis.Precision.unit.half joinedPrecision.alignment.clauses :=
  (common_keeps_both_precision_bounds precise otherPrecision _ _ the_last_precision_is_effective
    (covered_precisions_last_bound oneChoice [] Analysis.Precision.unit.half)).1
theorem arbitrary_finite_descriptions_have_common_returns (first second : List Analysis.Precision) :
    let one := refineReadingPrecisions oneReadings first
    let two := refineReadingPrecisions oneReadings second
    let common := one.common two
    common.readings.restrict (one.refinement.compose common.alignment.left) = oneReadings ∧
      common.readings.restrict (two.refinement.compose common.alignment.right) = oneReadings :=
  precision_courses_common_return oneReadings first second
set_option maxRecDepth 2048 in
theorem common_description_transports_as_a_whole :
    joinedPrecision.transport (agreement Rational.one) =
      (precise.transport (agreement Rational.one)).common (otherPrecision.transport (agreement Rational.one)) :=
  realized_common_transport_square ..
set_option maxRecDepth 2048 in
theorem common_description_follows_the_cached_history :
    joinedPrecision.prolong extension.execution.first.history =
      (precise.prolong extension.execution.first.history).common (otherPrecision.prolong extension.execution.first.history) :=
  realized_common_prolong_square ..
theorem common_description_continuation_square :
    (joinedPrecision.prolong extension.execution.first.history).transport (extension.rich (agreement Rational.one)) =
      (joinedPrecision.transport (agreement Rational.one)).prolong extension.execution.second.history :=
  common_continuation_square ..

theorem received_arrival_values_differ :
    attachedNumericReading (attached Rational.one) .arrival ≠ attachedNumericReading (attached (Rational.ofNat 3)) .arrival := by
  change Rational.one ≠ Rational.ofNat 3
  decide
def separatedReadings := numericReadingSeparationOfDifferent
  (attached Rational.one) .arrival (attached (Rational.ofNat 3)) .arrival received_arrival_values_differ
def reversedSeparation := numericReadingSeparationOfDifferent
  (attached (Rational.ofNat 3)) .arrival (attached Rational.one) .arrival received_arrival_values_differ.symm

theorem the_computed_separator_admits_and_refuses :
    numericWindowAdmitted (attached Rational.one) .arrival separatedReadings.window = true ∧
      numericWindowAdmitted (attached (Rational.ofNat 3)) .arrival separatedReadings.window = false :=
  numeric_separator_admissions separatedReadings
theorem the_reverse_direction_is_also_constructed :
    numericWindowAdmitted (attached (Rational.ofNat 3)) .arrival reversedSeparation.window = true ∧
      numericWindowAdmitted (attached Rational.one) .arrival reversedSeparation.window = false :=
  numeric_separator_admissions reversedSeparation
set_option maxRecDepth 2048 in
theorem the_upper_boundary_comes_from_the_second_reading : separatedReadings.window.upper = Rational.ofNat 3 := rfl
set_option maxRecDepth 2048 in
theorem the_lower_boundary_comes_from_the_second_reading : reversedSeparation.window.lower = Rational.one := rfl
theorem different_readings_cannot_agree_on_all_windows :
    ¬ (∀ window, numericWindowAdmitted (attached Rational.one) .arrival window =
      numericWindowAdmitted (attached (Rational.ofNat 3)) .arrival window) :=
  fun agree => received_arrival_values_differ (numerical_readers_determine_values _ _ _ _ |>.mp agree)
theorem one_shared_interaction_readout_does_not_determine_the_arrival :
    (∀ window, numericWindowAdmitted (attached Rational.one) .interaction window =
      numericWindowAdmitted (attached (Rational.ofNat 3)) .interaction window) ∧
      attachedNumericReading (attached Rational.one) .arrival ≠ attachedNumericReading (attached (Rational.ofNat 3)) .arrival :=
  by
    have same : attachedNumericReading (attached Rational.one) .interaction =
        attachedNumericReading (attached (Rational.ofNat 3)) .interaction := by
      change Rational.sub Rational.one Rational.one = Rational.sub (Rational.ofNat 3) (Rational.ofNat 3)
      unfold Rational.sub
      rw [Rational.add_neg, Rational.add_neg]
    exact ⟨(numerical_readers_determine_values _ _ _ _).mpr same, received_arrival_values_differ⟩
theorem all_numerical_constraints_can_agree_without_identifying_participants :
    (∀ clauses, readingConstraintsAdmitted (attached Rational.one) clauses =
      readingConstraintsAdmitted (partner Rational.one) clauses) ∧
      (attached Rational.one).readingReference ≠ (partner Rational.one).readingReference :=
  ⟨(joint_numerical_readers_determine_values _ _).mpr (fun port => by cases port <;> rfl),
    sources_still_have_their_own_identity⟩
theorem the_discriminator_returns_equality_for_equal_values :
    separateNumericReadings (attached Rational.one) .arrival (partner Rational.one) .arrival = .inl (by rfl) := rfl
theorem the_separating_window_survives_reference_transport :
    (separatedReadings.transport (agreement Rational.one) (agreement (Rational.ofNat 3))).window =
      separatedReadings.window := rfl
theorem transported_separation_still_admits_and_refuses :
    let moved := separatedReadings.transport (agreement Rational.one) (agreement (Rational.ofNat 3))
    numericWindowAdmitted (renamed Rational.one) .arrival moved.window = true ∧
      numericWindowAdmitted (renamed (Rational.ofNat 3)) .arrival moved.window = false :=
  numeric_separator_admissions _
theorem the_separation_follows_the_cached_first_history :
    let continued := separatedReadings.prolong extension.execution.first.history .root
    numericWindowAdmitted ((attached Rational.one).prolong extension.execution.first.history) .arrival continued.window = true ∧
      numericWindowAdmitted ((attached (Rational.ofNat 3)).prolong .root) .arrival continued.window = false :=
  numeric_separator_admissions _

/- Suffix cover decisions consume the stored positive prefix choices. -/
def leftArrivalSuffix : OverlappingWindowSplit arrivalSplit.left :=
  ⟨Rational.zero, Rational.ofParts 3 0 1, by decide, by decide, by decide⟩

def rightArrivalSuffix : OverlappingWindowSplit arrivalSplit.right :=
  ⟨Rational.ofNat 2, Rational.ofNat 3, by decide, by decide, by decide⟩

def rightComparisonSuffix : OverlappingWindowSplit comparisonSplit.right :=
  ⟨Rational.zero, Rational.ofParts 1 0 1, by decide, by decide, by decide⟩

def arrivalSuffixCovers : ReadingCoverSubstitution arrivalCover :=
  .split (.leaf (.split leftArrivalSuffix (.identity _) (.identity _)))
    (.leaf (.split rightArrivalSuffix (.identity _) (.identity _)))

def suffixCovers : ConstraintCoverSubstitution cover :=
  .cons arrivalSuffixCovers
    (.cons (.split (.leaf (.identity _))
      (.leaf (.split rightComparisonSuffix (.identity _) (.identity _)))) .nil)

def oneContinued := suffixCovers.resume oneChoice
def threeContinued := suffixCovers.resume threeChoice

set_option maxRecDepth 2048 in
theorem a_real_suffix_decision_is_taken : oneContinued.paths = [[true, true], [false, true]] := rfl
set_option maxRecDepth 2048 in
theorem a_different_received_reading_takes_a_different_suffix :
    threeContinued.paths = [[false, false], [false, true]] := rfl

theorem resumed_selection_is_the_whole_composed_selection :
    suffixCovers.flatten.select oneReadings = oneContinued := composed_joint_selection_is_resumption ..

theorem resumed_selection_returns_the_complete_received_source : oneContinued.restrict = oneReadings :=
  (resumed_joint_cover_returns_every_source suffixCovers oneChoice).trans restriction_returns_all_inputs

theorem resumed_selection_keeps_the_actual_values : oneContinued.refined.values = oneChoice.refined.values :=
  resumed_joint_cover_keeps_values ..

theorem resumed_selection_keeps_every_port : oneContinued.fine.map AttachedReadingConstraint.port =
    clauses.map AttachedReadingConstraint.port := joint_cover_keeps_ports oneContinued

theorem every_local_prefix_is_retained
    {source pair head current attached port window original}
    (substitution : @ReadingCoverSubstitution window original)
    (chosen : @CoveredNumericReading source pair head current attached port window original) :
    (substitution.resume chosen).leaf.branches = chosen.leaf.branches ++
      ((substitution.atLeaf chosen.leaf).select chosen.reading).leaf.branches := resumed_cover_keeps_the_prefix ..

theorem joint_substitution_composes_on_the_same_cover
    (later : ConstraintCoverSubstitution suffixCovers.flatten) :
    (suffixCovers.compose later).flatten = later.flatten := composed_joint_substitution_flattens_exactly ..

def coverCourse : ReadingCoverCourse cover :=
  .step suffixCovers (.step (.identity suffixCovers.flatten) .done)

def courseChoice := coverCourse.run oneChoice

theorem the_course_result_is_exact : coverCourse.finalCover.select oneReadings = courseChoice :=
  cover_course_selection_is_exact ..

theorem every_course_returns_its_actual_prefix (course : ReadingCoverCourse cover) :
    (course.run oneChoice).restrict = oneReadings :=
  (cover_course_returns_every_source course oneChoice).trans restriction_returns_all_inputs

theorem a_course_suffix_consumes_the_stored_result (tail : ReadingCoverCourse suffixCovers.flatten) :
    (ReadingCoverCourse.step suffixCovers tail).run oneChoice = tail.run oneContinued :=
  cover_course_consumes_its_produced_choice ..

theorem the_resumed_cover_transports_as_a_whole :
    oneContinued.transport (agreement Rational.one) = suffixCovers.resume (oneChoice.transport (agreement Rational.one)) :=
  resumed_joint_cover_transport_square ..

theorem the_resumed_cover_uses_the_cached_history :
    oneContinued.prolong extension.execution.first.history =
      suffixCovers.resume (oneChoice.prolong extension.execution.first.history) := resumed_joint_cover_prolong_square ..

theorem resumed_cover_and_shared_continuation_commute :
    (oneContinued.prolong extension.execution.first.history).transport (extension.rich (agreement Rational.one)) =
      (suffixCovers.resume (oneChoice.transport (agreement Rational.one))).prolong extension.execution.second.history :=
  resumed_joint_cover_continuation_square ..

theorem every_course_transports_as_a_whole (course : ReadingCoverCourse cover) :
    (course.run oneChoice).transport (agreement Rational.one) = course.run (oneChoice.transport (agreement Rational.one)) :=
  cover_course_transport_square ..

theorem every_course_and_shared_continuation_commute (course : ReadingCoverCourse cover) :
    ((course.run oneChoice).prolong extension.execution.first.history).transport (extension.rich (agreement Rational.one)) =
      (course.run (oneChoice.transport (agreement Rational.one))).prolong extension.execution.second.history :=
  cover_course_continuation_square ..

def continuedPrecision := oneContinued.precise precisionRequests

theorem precision_consumes_the_resumed_certificates :
    continuedPrecision.readings.restrict continuedPrecision.refinement = oneReadings :=
  (covered_precisions_return_the_selected_source oneContinued precisionRequests).trans
    resumed_selection_returns_the_complete_received_source

theorem precision_keeps_its_bounds_after_cover_resumption :
    ReadingSpansBounded Analysis.Precision.unit.half continuedPrecision.fine :=
  covered_precisions_last_bound oneContinued [Analysis.Precision.unit] Analysis.Precision.unit.half

theorem incompatible_constraints_still_cannot_supply_a_choice (value : Rational)
    (chosen : CoveredReadingConstraints (attached value) (InstrumentalConstraintCover.identity incompatible.clauses)) : False :=
  aligned_ports_do_not_supply_a_realization value chosen.restrict.satisfied

/- A received positive choice in the overlap need not be the canonical
chooser's preferred branch. Resumption must keep it, not silently reselect.
This is a valid descriptive input, not a second execution entry. -/
def overlapChoice : CoveredNumericReading (attached Rational.one) .arrival arrivalSuffixCovers.flatten :=
  ⟨leftArrivalSuffix.right, .left (.right .here), ⟨Rational.one, rfl, by decide⟩⟩

def overlapResume := (ReadingCoverSubstitution.identity arrivalSuffixCovers.flatten).resume overlapChoice

set_option maxRecDepth 2048 in
theorem a_received_overlap_choice_is_not_replaced : overlapResume.leaf.branches = [true, false] := rfl

set_option maxRecDepth 2048 in
theorem replaying_the_prefix_would_change_that_received_choice :
    (arrivalSuffixCovers.flatten.select
      (CertifiedNumericReading.mk Rational.one (by rfl) (by decide) :
        CertifiedNumericReading (attached Rational.one) .arrival arrivalWindow)).leaf.branches = [true, true] := rfl

theorem a_replayed_prefix_cannot_equal_the_resumed_path :
    overlapResume.leaf.branches ≠ [true, true] := by
  rw [a_received_overlap_choice_is_not_replaced]
  decide

/- Intersections consume finer certificates without replacing recorded leaves. -/
def recordedIntersection := oneChoice.intersect precise
def returnedChoice := oneChoice.recoverFromIntersection recordedIntersection

theorem recorded_intersection_has_two_complete_returns :
    recordedIntersection.readings.restrict recordedIntersection.alignment.left = oneChoice.refined ∧
      recordedIntersection.readings.restrict recordedIntersection.alignment.right = precise.readings :=
  recorded_intersection_returns_both_certificates oneChoice precise

theorem recorded_intersection_keeps_the_original_source :
    recordedIntersection.readings.restrict (oneChoice.refinement.compose recordedIntersection.alignment.left) = oneReadings :=
  (recorded_intersection_returns_both_coarse_sources oneChoice precise).1.trans restriction_returns_all_inputs

theorem returned_choice_is_the_complete_original : returnedChoice = oneChoice :=
  received_intersection_recovers_the_recorded_choice oneChoice recordedIntersection

theorem the_suffix_consumes_the_intersection_return :
    suffixCovers.resumeAfterIntersection oneChoice precise = suffixCovers.resume returnedChoice :=
  resumed_intersection_consumes_the_returned_choice ..

theorem the_suffix_after_intersection_is_exact :
    suffixCovers.resumeAfterIntersection oneChoice precise = oneContinued := intersection_resumption_is_exact ..

theorem every_fine_realization_keeps_the_same_recorded_choice
    (fine : RealizedReadingRefinement (attached Rational.one) clauses) : oneChoice.recoverIntersection fine = oneChoice :=
  intersection_recovers_the_recorded_choice ..

theorem every_course_after_intersection_keeps_its_whole_result (course : ReadingCoverCourse cover) :
    course.runAfterIntersection oneChoice precise = course.run oneChoice := intersection_course_is_exact ..

theorem every_course_after_intersection_returns_the_source (course : ReadingCoverCourse cover) :
    (course.runAfterIntersection oneChoice precise).restrict = oneReadings :=
  (intersection_course_returns_every_source course oneChoice precise).trans restriction_returns_all_inputs

theorem the_returned_choice_transports_as_a_whole :
    returnedChoice.transport (agreement Rational.one) =
      (oneChoice.transport (agreement Rational.one)).recoverIntersection (precise.transport (agreement Rational.one)) :=
  intersection_return_transport_square ..

theorem the_suffix_after_intersection_uses_the_cached_history :
    (suffixCovers.resumeAfterIntersection oneChoice precise).prolong extension.execution.first.history =
      suffixCovers.resumeAfterIntersection (oneChoice.prolong extension.execution.first.history)
        (precise.prolong extension.execution.first.history) := intersection_resumption_prolong_square ..

theorem the_suffix_after_intersection_and_continuation_commute :
    ((suffixCovers.resumeAfterIntersection oneChoice precise).prolong extension.execution.first.history).transport
        (extension.rich (agreement Rational.one)) =
      (suffixCovers.resumeAfterIntersection (oneChoice.transport (agreement Rational.one))
        (precise.transport (agreement Rational.one))).prolong extension.execution.second.history :=
  intersection_resumption_continuation_square ..

theorem every_intersection_course_and_continuation_commute (course : ReadingCoverCourse cover) :
    ((course.runAfterIntersection oneChoice precise).prolong extension.execution.first.history).transport
        (extension.rich (agreement Rational.one)) =
      (course.runAfterIntersection (oneChoice.transport (agreement Rational.one))
        (precise.transport (agreement Rational.one))).prolong extension.execution.second.history :=
  intersection_course_continuation_square ..

def recordedOverlap : CoveredReadingConstraints (attached Rational.one)
    (InstrumentalConstraintCover.cons (port := .arrival) arrivalSuffixCovers.flatten .nil) := .cons overlapChoice .nil

def overlapPrecision := recordedOverlap.precise [Analysis.Precision.unit.half]
def overlapIntersection := recordedOverlap.intersect overlapPrecision
def overlapReturned := recordedOverlap.recoverFromIntersection overlapIntersection

theorem the_noncanonical_intersection_returns_both_inputs :
    overlapIntersection.readings.restrict overlapIntersection.alignment.left = recordedOverlap.refined ∧
      overlapIntersection.readings.restrict overlapIntersection.alignment.right = overlapPrecision.readings :=
  recorded_intersection_returns_both_certificates ..

theorem a_noncanonical_choice_is_recovered_as_a_whole : overlapReturned = recordedOverlap :=
  received_intersection_recovers_the_recorded_choice ..

set_option maxRecDepth 2048 in
theorem intersection_return_keeps_the_noncanonical_leaf : overlapReturned.paths = [[true, false]] := by
  rw [a_noncanonical_choice_is_recovered_as_a_whole]
  rfl

theorem reselecting_cannot_replace_the_noncanonical_intersection_return : overlapReturned.paths ≠ [[true, true]] := by
  rw [intersection_return_keeps_the_noncanonical_leaf]
  decide

theorem the_actual_intersection_keeps_the_fine_precision :
    ReadingSpansBounded Analysis.Precision.unit.half overlapIntersection.alignment.clauses :=
  span_bounds_survive_refinement overlapIntersection.alignment.right Analysis.Precision.unit.half
    (covered_precisions_last_bound recordedOverlap [] Analysis.Precision.unit.half)

theorem the_stored_intersection_is_consumed_without_rebuilding :
    returnedChoice = oneChoice.withReadings
      (recordedIntersection.readings.restrict recordedIntersection.alignment.left) :=
  received_intersection_return_consumes_its_certificates ..

theorem the_new_suffix_accepts_the_stored_intersection :
    suffixCovers.resumeFromIntersection oneChoice recordedIntersection = oneContinued :=
  stored_intersection_resumption_is_exact ..

theorem every_course_accepts_the_stored_intersection (course : ReadingCoverCourse cover) :
    course.runFromIntersection oneChoice recordedIntersection = course.run oneChoice :=
  stored_intersection_course_is_exact ..

end Tests.Relativity.ConjunctiveCoverChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ConjunctiveCoverChecks.arrivals
#print axioms Tests.Relativity.ConjunctiveCoverChecks.an_exchange_is_actually_found
#print axioms Tests.Relativity.ConjunctiveCoverChecks.found
#print axioms Tests.Relativity.ConjunctiveCoverChecks.pair
#print axioms Tests.Relativity.ConjunctiveCoverChecks.agreement
#print axioms Tests.Relativity.ConjunctiveCoverChecks.cover
#print axioms Tests.Relativity.ConjunctiveCoverChecks.one_decision_returns_its_actual_choice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.accepted_run
#print axioms Tests.Relativity.ConjunctiveCoverChecks.outer_boundary_refused
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_first_actual_values
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_second_actual_values
#print axioms Tests.Relativity.ConjunctiveCoverChecks.mixed_local_choices
#print axioms Tests.Relativity.ConjunctiveCoverChecks.different_received_value_changes_a_choice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.choices_are_not_prescribed
#print axioms Tests.Relativity.ConjunctiveCoverChecks.neither_clause_is_dropped
#print axioms Tests.Relativity.ConjunctiveCoverChecks.restriction_returns_all_inputs
#print axioms Tests.Relativity.ConjunctiveCoverChecks.identity_keeps_the_constraint_list
#print axioms Tests.Relativity.ConjunctiveCoverChecks.identity_has_no_selection_steps
#print axioms Tests.Relativity.ConjunctiveCoverChecks.joint_coverage_is_exact
#print axioms Tests.Relativity.ConjunctiveCoverChecks.concatenate_without_listing_combinations
#print axioms Tests.Relativity.ConjunctiveCoverChecks.all_four_local_choices_remain
#print axioms Tests.Relativity.ConjunctiveCoverChecks.pulled_intersection_has_both_actual_values
#print axioms Tests.Relativity.ConjunctiveCoverChecks.pulled_intersection_returns_both_inputs
#print axioms Tests.Relativity.ConjunctiveCoverChecks.pulled_intersection_returns_the_coarse_source
#print axioms Tests.Relativity.ConjunctiveCoverChecks.intersection_is_exactly_a_joint_satisfaction
#print axioms Tests.Relativity.ConjunctiveCoverChecks.aligned_ports_do_not_supply_a_realization
#print axioms Tests.Relativity.ConjunctiveCoverChecks.incompatible_intersection_is_refused
#print axioms Tests.Relativity.ConjunctiveCoverChecks.incompatible_certificate_cannot_be_installed
#print axioms Tests.Relativity.ConjunctiveCoverChecks.different_ports_cannot_align
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_presentation_change_moves_the_reference
#print axioms Tests.Relativity.ConjunctiveCoverChecks.joint_choices_transport_exactly
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_choice_path_survives_transport
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_realized_intersection_transports
#print axioms Tests.Relativity.ConjunctiveCoverChecks.extension_is_actual
#print axioms Tests.Relativity.ConjunctiveCoverChecks.one_shared_production_only
#print axioms Tests.Relativity.ConjunctiveCoverChecks.selection_commutes_with_the_cached_history
#print axioms Tests.Relativity.ConjunctiveCoverChecks.joint_choices_and_continuation_commute
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_intersection_follows_the_same_production
#print axioms Tests.Relativity.ConjunctiveCoverChecks.unchanged_contract
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_further_suffix_is_preserved
#print axioms Tests.Relativity.ConjunctiveCoverChecks.sources_still_have_their_own_identity
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precisionRequests
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precise
#print axioms Tests.Relativity.ConjunctiveCoverChecks.firstPrecision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumedPrecision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.both_requested_precisions_are_positive
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_last_precision_is_effective
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_later_request_keeps_the_earlier_bound
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precise_return_is_the_received_source
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precise_values_remain_the_actual_values
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precise_ports_remain_the_actual_ports
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumption_consumes_the_existing_prefix
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumption_returns_every_received_certificate
#print axioms Tests.Relativity.ConjunctiveCoverChecks.arbitrary_finite_resumption
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_requested_bound_remains
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_nonpositive_radius_is_not_a_precision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.incompatible_constraints_cannot_start_precision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precision_changes_the_window_not_just_its_label
#print axioms Tests.Relativity.ConjunctiveCoverChecks.different_received_readings_cannot_have_the_same_precision_windows
#print axioms Tests.Relativity.ConjunctiveCoverChecks.full_precision_run_transports_without_reselecting
#print axioms Tests.Relativity.ConjunctiveCoverChecks.full_precision_run_follows_the_cached_history
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precise_continuation_square
#print axioms Tests.Relativity.ConjunctiveCoverChecks.arbitrary_precision_does_not_change_the_future_contract
#print axioms Tests.Relativity.ConjunctiveCoverChecks.otherPrecision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.joinedPrecision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.two_precision_descriptions_return_exactly
#print axioms Tests.Relativity.ConjunctiveCoverChecks.both_returns_recover_the_initial_certificates
#print axioms Tests.Relativity.ConjunctiveCoverChecks.common_description_keeps_the_precision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.arbitrary_finite_descriptions_have_common_returns
#print axioms Tests.Relativity.ConjunctiveCoverChecks.common_description_transports_as_a_whole
#print axioms Tests.Relativity.ConjunctiveCoverChecks.common_description_follows_the_cached_history
#print axioms Tests.Relativity.ConjunctiveCoverChecks.common_description_continuation_square
#print axioms Tests.Relativity.ConjunctiveCoverChecks.received_arrival_values_differ
#print axioms Tests.Relativity.ConjunctiveCoverChecks.separatedReadings
#print axioms Tests.Relativity.ConjunctiveCoverChecks.reversedSeparation
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_computed_separator_admits_and_refuses
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_reverse_direction_is_also_constructed
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_upper_boundary_comes_from_the_second_reading
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_lower_boundary_comes_from_the_second_reading
#print axioms Tests.Relativity.ConjunctiveCoverChecks.different_readings_cannot_agree_on_all_windows
#print axioms Tests.Relativity.ConjunctiveCoverChecks.one_shared_interaction_readout_does_not_determine_the_arrival
#print axioms Tests.Relativity.ConjunctiveCoverChecks.all_numerical_constraints_can_agree_without_identifying_participants
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_discriminator_returns_equality_for_equal_values
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_separating_window_survives_reference_transport
#print axioms Tests.Relativity.ConjunctiveCoverChecks.transported_separation_still_admits_and_refuses
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_separation_follows_the_cached_first_history
#print axioms Tests.Relativity.ConjunctiveCoverChecks.leftArrivalSuffix
#print axioms Tests.Relativity.ConjunctiveCoverChecks.rightArrivalSuffix
#print axioms Tests.Relativity.ConjunctiveCoverChecks.rightComparisonSuffix
#print axioms Tests.Relativity.ConjunctiveCoverChecks.arrivalSuffixCovers
#print axioms Tests.Relativity.ConjunctiveCoverChecks.suffixCovers
#print axioms Tests.Relativity.ConjunctiveCoverChecks.oneContinued
#print axioms Tests.Relativity.ConjunctiveCoverChecks.threeContinued
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_real_suffix_decision_is_taken
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_different_received_reading_takes_a_different_suffix
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumed_selection_is_the_whole_composed_selection
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumed_selection_returns_the_complete_received_source
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumed_selection_keeps_the_actual_values
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumed_selection_keeps_every_port
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_local_prefix_is_retained
#print axioms Tests.Relativity.ConjunctiveCoverChecks.joint_substitution_composes_on_the_same_cover
#print axioms Tests.Relativity.ConjunctiveCoverChecks.coverCourse
#print axioms Tests.Relativity.ConjunctiveCoverChecks.courseChoice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_course_result_is_exact
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_course_returns_its_actual_prefix
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_course_suffix_consumes_the_stored_result
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_resumed_cover_transports_as_a_whole
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_resumed_cover_uses_the_cached_history
#print axioms Tests.Relativity.ConjunctiveCoverChecks.resumed_cover_and_shared_continuation_commute
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_course_transports_as_a_whole
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_course_and_shared_continuation_commute
#print axioms Tests.Relativity.ConjunctiveCoverChecks.continuedPrecision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precision_consumes_the_resumed_certificates
#print axioms Tests.Relativity.ConjunctiveCoverChecks.precision_keeps_its_bounds_after_cover_resumption
#print axioms Tests.Relativity.ConjunctiveCoverChecks.incompatible_constraints_still_cannot_supply_a_choice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.overlapChoice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.overlapResume
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_received_overlap_choice_is_not_replaced
#print axioms Tests.Relativity.ConjunctiveCoverChecks.replaying_the_prefix_would_change_that_received_choice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_replayed_prefix_cannot_equal_the_resumed_path
#print axioms Tests.Relativity.ConjunctiveCoverChecks.recordedIntersection
#print axioms Tests.Relativity.ConjunctiveCoverChecks.returnedChoice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.recorded_intersection_has_two_complete_returns
#print axioms Tests.Relativity.ConjunctiveCoverChecks.recorded_intersection_keeps_the_original_source
#print axioms Tests.Relativity.ConjunctiveCoverChecks.returned_choice_is_the_complete_original
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_suffix_consumes_the_intersection_return
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_suffix_after_intersection_is_exact
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_fine_realization_keeps_the_same_recorded_choice
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_course_after_intersection_keeps_its_whole_result
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_course_after_intersection_returns_the_source
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_returned_choice_transports_as_a_whole
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_suffix_after_intersection_uses_the_cached_history
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_suffix_after_intersection_and_continuation_commute
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_intersection_course_and_continuation_commute
#print axioms Tests.Relativity.ConjunctiveCoverChecks.recordedOverlap
#print axioms Tests.Relativity.ConjunctiveCoverChecks.overlapPrecision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.overlapIntersection
#print axioms Tests.Relativity.ConjunctiveCoverChecks.overlapReturned
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_noncanonical_intersection_returns_both_inputs
#print axioms Tests.Relativity.ConjunctiveCoverChecks.a_noncanonical_choice_is_recovered_as_a_whole
#print axioms Tests.Relativity.ConjunctiveCoverChecks.intersection_return_keeps_the_noncanonical_leaf
#print axioms Tests.Relativity.ConjunctiveCoverChecks.reselecting_cannot_replace_the_noncanonical_intersection_return
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_actual_intersection_keeps_the_fine_precision
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_stored_intersection_is_consumed_without_rebuilding
#print axioms Tests.Relativity.ConjunctiveCoverChecks.the_new_suffix_accepts_the_stored_intersection
#print axioms Tests.Relativity.ConjunctiveCoverChecks.every_course_accepts_the_stored_intersection
/- AXIOM_AUDIT_END -/
