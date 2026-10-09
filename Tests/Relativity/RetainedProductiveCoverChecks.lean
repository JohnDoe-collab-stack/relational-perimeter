import RelationalPerimeter
import Tests.Relativity.SharedProductiveCoverChecks

/-! Reuse the closed three-prefix fixtures from the preceding client, without
creating a production entry. Full-course equalities quantify over arbitrary
finite adaptive requests. The only evaluated smoke is an empty resumption. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.RetainedProductiveCoverChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open SharedProductiveCoverChecks

def retained (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :=
  (course steps requests).resumeRetaining more agreement (secondThirdAgreement steps)

theorem retaining_is_the_whole_continuous_course (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    retained steps requests more = course steps (requests ++ more) :=
  productive_retained_cover_is_whole_continuous_course ..

theorem returning_keeps_the_complete_suffix_endpoint (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps requests more).endpoint =
      ((course steps requests).resume more agreement (secondThirdAgreement steps)).endpoint :=
  productive_retained_cover_returns_actual_suffix_endpoint ..

theorem old_head_is_kept_entirely (steps : Nat)
    (head : ProductiveCoverRequest first second (third steps))
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps (head :: requests) more).headProduction =
      (course steps (head :: requests)).headProduction :=
  productive_retained_cover_keeps_whole_head ..

theorem retaining_the_left_choice_does_not_select_it_again (steps : Nat)
    (more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps [request steps] more).headProduction.chosen.leaf.branches = [true] := by
  rw [old_head_is_kept_entirely]
  exact one_closed_cover_selects_left steps

theorem retaining_the_right_choice_does_not_select_it_again (steps : Nat)
    (more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps [oppositeRequest steps] more).headProduction.chosen.leaf.branches = [false] := by
  rw [old_head_is_kept_entirely]
  exact the_other_closed_cover_selects_right steps

theorem recorded_choices_are_concatenated_in_order (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps requests more).recordedChoices = (course steps requests).recordedChoices ++
      ((course steps requests).resume more agreement (secondThirdAgreement steps)).recordedChoices :=
  productive_retained_cover_choices ..

theorem recorded_budgets_are_concatenated_in_order (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps requests more).recordedBudgets = (course steps requests).recordedBudgets ++
      ((course steps requests).resume more agreement (secondThirdAgreement steps)).recordedBudgets :=
  productive_retained_cover_budgets ..

theorem all_three_received_prefixes_are_extended (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    ProductiveTripleExtension (received steps) (retained steps requests more).endpoint :=
  productive_retained_cover_extends_three_received_prefixes ..

theorem all_later_readings_remain_admissible (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) (later : Nat) :
    initialWindow.Contains ((retained steps requests more).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
    initialWindow.Contains ((retained steps requests more).endpoint.secondCertificate.advance later).realization.state.reading.value ∧
    initialWindow.Contains ((retained steps requests more).endpoint.thirdCertificate.advance later).realization.state.reading.value :=
  productive_retained_cover_all_later_readings (course steps requests) more agreement
    (secondThirdAgreement steps) later

theorem repeated_retention_returns_the_continuous_endpoint (steps : Nat)
    (requests more last : List (ProductiveCoverRequest first second (third steps))) :
    ((retained steps requests more).resumeRetaining last agreement (secondThirdAgreement steps)).endpoint =
      (course steps (requests ++ (more ++ last))).endpoint :=
  productive_retained_covers_twice_same_endpoint (received steps) requests more last
    agreement (secondThirdAgreement steps)

theorem every_retained_head_is_independent_of_the_new_horizon (steps : Nat)
    (head : ProductiveCoverRequest first second (third steps))
    (requests one two : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps (head :: requests) one).headProduction =
      (retained steps (head :: requests) two).headProduction := by
  rw [old_head_is_kept_entirely, old_head_is_kept_entirely]

theorem all_three_sources_stay_distinct (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    (historyTransport (retained steps requests more).endpoint.firstCertificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (retained steps requests more).endpoint.firstCertificate.realization.chain.history).references
        leftSource.reading.arrivals.second ∧
    (historyTransport (retained steps requests more).endpoint.secondCertificate.realization.chain.history).references
        rightSource.reading.arrivals.first ≠
      (historyTransport (retained steps requests more).endpoint.secondCertificate.realization.chain.history).references
        rightSource.reading.arrivals.second ∧
    (historyTransport (retained steps requests more).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (retained steps requests more).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.second := by
  rw [retaining_is_the_whole_continuous_course]
  exact all_three_continued_sources_stay_distinct ..

theorem the_retained_third_source_record_is_readable (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    (retained steps requests more).endpoint.thirdCertificate.realization.state.cursor.read
      ((historyTransport (retained steps requests more).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.secondSignal) = leftSource.cursor.read leftSource.reading.arrivals.secondSignal := by
  rw [retaining_is_the_whole_continuous_course]
  exact the_third_continuation_keeps_its_source_record ..

theorem retained_precision_endpoints_are_valid_received_prefixes (steps : Nat)
    (requests more : List Precision)
    (covers later : List (ProductiveCoverRequest first second (third steps))) :
    ProductiveTripleExtension (retainedEndpoint steps requests more)
      (((retainedEndpoint steps requests more).runCovers covers agreement (secondThirdAgreement steps)).resumeRetaining
        later agreement (secondThirdAgreement steps)).endpoint :=
  productive_retained_cover_extends_three_received_prefixes ..

def emptySmoke : Nat := (retained 1 [] []).endpoint.thirdCertificate.depth
#eval emptySmoke

end Tests.Relativity.RetainedProductiveCoverChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.retained
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.retaining_is_the_whole_continuous_course
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.returning_keeps_the_complete_suffix_endpoint
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.old_head_is_kept_entirely
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.retaining_the_left_choice_does_not_select_it_again
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.retaining_the_right_choice_does_not_select_it_again
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.recorded_choices_are_concatenated_in_order
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.recorded_budgets_are_concatenated_in_order
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.all_three_received_prefixes_are_extended
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.all_later_readings_remain_admissible
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.repeated_retention_returns_the_continuous_endpoint
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.every_retained_head_is_independent_of_the_new_horizon
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.all_three_sources_stay_distinct
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.the_retained_third_source_record_is_readable
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.retained_precision_endpoints_are_valid_received_prefixes
#print axioms Tests.Relativity.RetainedProductiveCoverChecks.emptySmoke
/- AXIOM_AUDIT_END -/
