import RelationalPerimeter

/-! Finite constraints and positive covers consume the same actual receptions
and comparison. Window choice is descriptive, not a new production or place. -/
set_option genInjectivity false
namespace Tests.Relativity.ReadingCoverChecks
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

def origin (value : Rational) : RecurringCursor := .fromCursor (arrivals value).1
def pair (value : Rational) : RecurringPair (origin value) :=
  let data := (arrivals value).2
  ⟨data.first, data.second, data.firstSignal, data.secondSignal,
    .fromCursor data.firstArrival, .fromCursor data.secondArrival, data.distinct⟩
def head (value : Rational) := performRecurring (origin value) (.compare (pair value))
def attached (value : Rational) := InteractionAttachment.first (head value) .root
def partner (value : Rational) := InteractionAttachment.second (head value) .root

def coarse : ReadingWindow := ⟨Rational.neg Rational.one, Rational.ofNat 4⟩
def comparisonWindow : ReadingWindow := ⟨Rational.neg Rational.one, Rational.one⟩
def division : OverlappingWindowSplit coarse :=
  ⟨Rational.one, Rational.ofNat 2, by decide, by decide, by decide⟩
def innerDivision : OverlappingWindowSplit division.left :=
  ⟨Rational.zero, Rational.one, by decide, by decide, by decide⟩
def simpleCover : InstrumentalReadingCover coarse := .split division (.identity _) (.identity _)
def nestedCover : InstrumentalReadingCover coarse :=
  .split division (.split innerDivision (.identity _) (.identity _)) (.identity _)
def clauses : List AttachedReadingConstraint := [⟨.arrival, coarse⟩, ⟨.interaction, comparisonWindow⟩]

theorem zero_joint_admitted : readingConstraintsAdmitted (attached Rational.zero) clauses = true := rfl
theorem one_joint_admitted : readingConstraintsAdmitted (attached Rational.one) clauses = true := rfl
theorem two_joint_admitted : readingConstraintsAdmitted (attached (Rational.ofNat 2)) clauses = true := rfl
theorem outer_boundary_refused : readingConstraintsAdmitted (attached (Rational.ofNat 4)) clauses = false := rfl

def joint := certifiedReadingConstraintsOfAdmitted (attached Rational.one) clauses one_joint_admitted
theorem joint_is_the_executed_decision : certifyReadingConstraints (attached Rational.one) clauses = .inl joint :=
  admitted_constraints_are_the_decision_output _ _ _
theorem joint_uses_both_actual_ports : joint.values = [Rational.one, Rational.zero] := rfl
theorem empty_constraints_are_admitted : readingConstraintsAdmitted (attached Rational.one) [] = true := rfl

def incompatible : List AttachedReadingConstraint :=
  [⟨.arrival, division.left⟩, ⟨.arrival, ⟨Rational.ofNat 2, Rational.ofNat 4⟩⟩]
theorem incompatible_constraints_refused : readingConstraintsAdmitted (attached Rational.one) incompatible = false := rfl
theorem no_joint_realization (value : Rational) :
    ¬ ReadingConstraintsSatisfied (attached value) incompatible :=
  disjoint_constraints_unrealizable _ _ _ _ (Rational.le_refl _) []
theorem cannot_supply_incompatible_certificates (value : Rational)
    (readings : CertifiedReadingConstraints (attached value) incompatible) : False :=
  no_joint_realization value readings.satisfied

def zeroReading := certifiedNumericReadingOfAdmitted (attached Rational.zero) .arrival coarse (by rfl)
def oneReading := certifiedNumericReadingOfAdmitted (attached Rational.one) .arrival coarse (by rfl)
def twoReading := certifiedNumericReadingOfAdmitted (attached (Rational.ofNat 2)) .arrival coarse (by rfl)
def threeReading := certifiedNumericReadingOfAdmitted (attached (Rational.ofNat 3)) .arrival coarse (by rfl)
def overlapValue : Rational := Rational.ofParts 3 0 1
def overlapReading := certifiedNumericReadingOfAdmitted (attached overlapValue) .arrival coarse (by rfl)

theorem first_branch_from_zero : (simpleCover.select zeroReading).leaf.branches = [true] := rfl
theorem first_branch_at_lower_cut : (simpleCover.select oneReading).leaf.branches = [true] := rfl
theorem other_branch_at_upper_cut : (simpleCover.select twoReading).leaf.branches = [false] := rfl
theorem other_branch_from_three : (simpleCover.select threeReading).leaf.branches = [false] := rfl
theorem overlap_chooses_first : (simpleCover.select overlapReading).leaf.branches = [true] := rfl
theorem overlap_really_has_both_windows :
    division.left.Contains overlapValue ∧ division.right.Contains overlapValue :=
  split_contains_overlap division (by decide)
theorem a_shared_boundary_is_not_lost : division.right.Contains (Rational.ofNat 2) := by decide
theorem an_open_boundary_is_excluded : ¬ division.left.Contains (Rational.ofNat 2) :=
  window_upper_boundary_excluded _
theorem both_windows_strictly_improve :
    RationalStrictLess division.left.span coarse.span ∧ RationalStrictLess division.right.span coarse.span :=
  split_windows_strictly_shrink division

theorem composed_choice_from_zero : (nestedCover.select zeroReading).leaf.branches = [true, true] := rfl
theorem composed_choice_from_one : (nestedCover.select oneReading).leaf.branches = [true, false] := rfl
theorem composed_choice_from_two : (nestedCover.select twoReading).leaf.branches = [false] := rfl
theorem selected_leaf_returns_the_original : (nestedCover.select oneReading).restrict = oneReading :=
  selected_cover_restricts_to_source nestedCover oneReading
theorem identity_is_neutral : nestedCover.refine InstrumentalReadingCover.identity = nestedCover :=
  cover_refine_identity nestedCover
theorem composed_covers_associate (one two : (window : ReadingWindow) → InstrumentalReadingCover window) :
    (nestedCover.refine one).refine two = nestedCover.refine (fun window => (one window).refine two) :=
  cover_refine_associates nestedCover one two

def coveredJoint := coverConstraintHead nestedCover joint
theorem suffix_is_still_certified : coveredJoint.refined.values = joint.values :=
  constraint_cover_preserves_all_values nestedCover joint
theorem the_joint_restriction_is_exact : coveredJoint.restrict = joint :=
  constraint_cover_restricts_to_source nestedCover joint

def fineWindow : ReadingWindow := ⟨Rational.zero, Rational.ofNat 3⟩
theorem fineRefinement : WindowRefinement coarse fineWindow := ⟨by decide, by decide⟩
def fineReading := certifiedNumericReadingOfAdmitted (attached Rational.one) .arrival fineWindow (by rfl)
def pulledBack := coveredWindowIntersection simpleCover fineRefinement fineReading
theorem selected_intersection_is_realized : pulledBack.value = Rational.one := rfl
theorem intersection_has_exact_returns :
    pulledBack.restrict (window_intersection_left _ _) =
        (simpleCover.select (fineReading.restrict fineRefinement)).reading ∧
      pulledBack.restrict (window_intersection_right _ _) = fineReading :=
  covered_intersection_restrictions simpleCover fineRefinement fineReading

def agreement := AttachedDescriptionAgreement.identity (attached Rational.one)
def requests : List RecurringRequest :=
  [.local (.inspect .reading (attached Rational.one).readingReference.position),
   .compare (attached Rational.one).readingReference.position (partner Rational.one).readingReference.position,
   .compare 0 0]
@[irreducible] def extension := runDescriptionExtension agreement.raccord requests
theorem extension_is_actual : extension = runDescriptionExtension agreement.raccord requests := by unfold extension; rfl

theorem one_new_shared_production : StrongPerimetralTurning.History.length extension.execution.first.history = 1 := by
  rw [extension_is_actual]
  change StrongPerimetralTurning.History.length (runSharedRecurring agreement.raccord requests).first.history = 1
  rw [(shared_recurring_runners_exact agreement.raccord requests).1]
  rfl

theorem constraints_follow_the_cached_production :
    (joint.prolong extension.execution.first.history).values = [Rational.one, Rational.zero] :=
  (constraint_prolong_values joint _).trans joint_uses_both_actual_ports

theorem constraints_and_change_commute :
    (joint.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (joint.transport agreement).prolong extension.execution.second.history :=
  constraint_continuation_square agreement extension joint

theorem cover_and_continuation_commute :
    (nestedCover.select oneReading).prolong extension.execution.first.history =
      nestedCover.select (oneReading.prolong extension.execution.first.history) :=
  cover_selection_prolong_square nestedCover oneReading _

theorem cover_and_description_change_commute :
    (nestedCover.select oneReading).transport agreement = nestedCover.select (oneReading.transport agreement) :=
  cover_selection_transport_square agreement nestedCover oneReading

theorem all_future_suffixes_keep_joint_admission (future : List RecurringRequest) :
    ReadingConstraintsSatisfied ((extension.resume future).first (extension.first (attached Rational.one))) clauses :=
  (((constraint_satisfaction_prolong _ _ _).mpr
    ((constraint_satisfaction_prolong _ _ _).mpr joint.satisfied)))

theorem sources_are_not_identified :
    (attached Rational.one).readingReference ≠ (partner Rational.one).readingReference :=
  participants_remain_distinct (head Rational.one) DescriptionPath.root

theorem the_existing_contract_is_preserved : extension.execution.first.report =
    recurringContract.outcome (head Rational.one).successor requests := by
  rw [extension_is_actual]
  exact (description_extension_reports_exact agreement.raccord requests).1

end Tests.Relativity.ReadingCoverChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ReadingCoverChecks.arrivals
#print axioms Tests.Relativity.ReadingCoverChecks.division
#print axioms Tests.Relativity.ReadingCoverChecks.innerDivision
#print axioms Tests.Relativity.ReadingCoverChecks.zero_joint_admitted
#print axioms Tests.Relativity.ReadingCoverChecks.one_joint_admitted
#print axioms Tests.Relativity.ReadingCoverChecks.two_joint_admitted
#print axioms Tests.Relativity.ReadingCoverChecks.outer_boundary_refused
#print axioms Tests.Relativity.ReadingCoverChecks.joint_is_the_executed_decision
#print axioms Tests.Relativity.ReadingCoverChecks.joint_uses_both_actual_ports
#print axioms Tests.Relativity.ReadingCoverChecks.empty_constraints_are_admitted
#print axioms Tests.Relativity.ReadingCoverChecks.incompatible_constraints_refused
#print axioms Tests.Relativity.ReadingCoverChecks.no_joint_realization
#print axioms Tests.Relativity.ReadingCoverChecks.cannot_supply_incompatible_certificates
#print axioms Tests.Relativity.ReadingCoverChecks.first_branch_from_zero
#print axioms Tests.Relativity.ReadingCoverChecks.first_branch_at_lower_cut
#print axioms Tests.Relativity.ReadingCoverChecks.other_branch_at_upper_cut
#print axioms Tests.Relativity.ReadingCoverChecks.other_branch_from_three
#print axioms Tests.Relativity.ReadingCoverChecks.overlap_chooses_first
#print axioms Tests.Relativity.ReadingCoverChecks.overlap_really_has_both_windows
#print axioms Tests.Relativity.ReadingCoverChecks.a_shared_boundary_is_not_lost
#print axioms Tests.Relativity.ReadingCoverChecks.an_open_boundary_is_excluded
#print axioms Tests.Relativity.ReadingCoverChecks.both_windows_strictly_improve
#print axioms Tests.Relativity.ReadingCoverChecks.composed_choice_from_zero
#print axioms Tests.Relativity.ReadingCoverChecks.composed_choice_from_one
#print axioms Tests.Relativity.ReadingCoverChecks.composed_choice_from_two
#print axioms Tests.Relativity.ReadingCoverChecks.selected_leaf_returns_the_original
#print axioms Tests.Relativity.ReadingCoverChecks.identity_is_neutral
#print axioms Tests.Relativity.ReadingCoverChecks.composed_covers_associate
#print axioms Tests.Relativity.ReadingCoverChecks.suffix_is_still_certified
#print axioms Tests.Relativity.ReadingCoverChecks.the_joint_restriction_is_exact
#print axioms Tests.Relativity.ReadingCoverChecks.selected_intersection_is_realized
#print axioms Tests.Relativity.ReadingCoverChecks.intersection_has_exact_returns
#print axioms Tests.Relativity.ReadingCoverChecks.extension_is_actual
#print axioms Tests.Relativity.ReadingCoverChecks.one_new_shared_production
#print axioms Tests.Relativity.ReadingCoverChecks.constraints_follow_the_cached_production
#print axioms Tests.Relativity.ReadingCoverChecks.constraints_and_change_commute
#print axioms Tests.Relativity.ReadingCoverChecks.cover_and_continuation_commute
#print axioms Tests.Relativity.ReadingCoverChecks.cover_and_description_change_commute
#print axioms Tests.Relativity.ReadingCoverChecks.all_future_suffixes_keep_joint_admission
#print axioms Tests.Relativity.ReadingCoverChecks.sources_are_not_identified
#print axioms Tests.Relativity.ReadingCoverChecks.the_existing_contract_is_preserved
/- AXIOM_AUDIT_END -/
