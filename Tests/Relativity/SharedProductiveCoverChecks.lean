import RelationalPerimeter

/-! Closed public clients for actual three-prefix cover selection and resumption.
The cover trees are inputs; only the leaf is selected from the first produced
bracket. The only evaluated smoke is the empty course, not a cost experiment. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.SharedProductiveCoverChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl
def leftSource := (refineRelativePaths initial .lower).state
def rightSource := (refineRelativePaths initial .upper).state
def first := RelativePathPresentation.fromState leftSource .upper
def second := RelativePathPresentation.fromState rightSource .lower
def agreement : Agreement first.numeric second.numeric := relative_children_boundary_agreement initial
def initialWindow : ReadingWindow := ⟨Rational.neg (Rational.ofNat 2), Rational.ofNat 5⟩
def firstCertificate : ProductiveWindowCertificate first initialWindow :=
  first.initialWindow.restrict ⟨by decide, by decide⟩
def secondCertificate : ProductiveWindowCertificate second initialWindow :=
  second.initialWindow.restrict ⟨by decide, by decide⟩
def thirdSeed (steps : Nat) := firstCertificate.advance steps
def third (steps : Nat) := (thirdSeed steps).receivedPresentation
def thirdCertificate (steps : Nat) := (thirdSeed steps).receivedCertificate
def secondThirdAgreement (steps : Nat) : Agreement second.numeric (third steps).numeric :=
  (thirdSeed steps).agreementFromReceived agreement.reverse
def received (steps : Nat) : ProductiveTripleEndpoint first second (third steps) :=
  ⟨initialWindow, firstCertificate, secondCertificate, thirdCertificate steps⟩

def request (steps : Nat) : ProductiveCoverRequest first second (third steps) := fun received =>
  if lower : RationalStrictLess received.window.lower Rational.zero then
    if upper : RationalStrictLess Rational.one received.window.upper then
      .split ⟨Rational.zero, Rational.one, lower, by decide, upper⟩ (.identity _) (.identity _)
    else .identity _
  else .identity _

def oppositeRequest (steps : Nat) : ProductiveCoverRequest first second (third steps) := fun received =>
  if lower : RationalStrictLess received.window.lower (Rational.neg Rational.one) then
    if upper : RationalStrictLess Rational.zero received.window.upper then
      .split ⟨Rational.neg Rational.one, Rational.zero, lower, by decide, upper⟩ (.identity _) (.identity _)
    else .identity _
  else .identity _

def course (steps : Nat) (requests : List (ProductiveCoverRequest first second (third steps))) :=
  (received steps).runCovers requests agreement (secondThirdAgreement steps)

def precisionPair (requests : List Precision) :=
  (firstCertificate.runPrecisions requests).matchAgreed secondCertificate agreement
def precisionThird (steps : Nat) (requests : List Precision) :=
  (precisionPair requests).composeAgreed (thirdCertificate steps) (secondThirdAgreement steps)
def retainedPrecisions (steps : Nat) (requests more : List Precision) :=
  (precisionPair requests).resumeComposedRetaining (precisionThird steps requests)
    agreement (secondThirdAgreement steps) more
def retainedEndpoint (steps : Nat) (requests more : List Precision) :=
  (retainedPrecisions steps requests more).1.coverEndpoint (retainedPrecisions steps requests more).2

theorem the_selected_leaf_is_not_reselected (steps : Nat) :
    ((received steps).selectSharedCover (request steps (received steps)) agreement
      (secondThirdAgreement steps)).chosen =
        (request steps (received steps)).selectProductive firstCertificate :=
  productive_shared_cover_keeps_the_selected_leaf ..

theorem one_closed_cover_selects_left (steps : Nat) :
    (course steps [request steps]).headProduction.chosen.leaf.branches = [true] := by
  dsimp only [course]
  rw [productive_cover_course_head_exact, productive_shared_cover_keeps_the_selected_leaf]
  change ((request steps (received steps)).selectProductive firstCertificate).leaf.branches = [true]
  simp only [request, received]
  apply productive_single_split_left_branches
  exact rational_le_strict (relative_evolution_brackets firstCertificate.realization first.rule _).2
    (show RationalStrictLess firstCertificate.realization.state.reading.upper Rational.one from by decide)

theorem first_bracket_never_falls_below_zero (depth : Nat) :
    ¬ RationalStrictLess (firstCertificate.realization.evolve .upper depth).state.reading.upper Rational.zero := by
  rw [relative_evolution_upper_endpoint]
  decide

theorem the_other_closed_cover_selects_right (steps : Nat) :
    (course steps [oppositeRequest steps]).headProduction.chosen.leaf.branches = [false] := by
  dsimp only [course]
  rw [productive_cover_course_head_exact, productive_shared_cover_keeps_the_selected_leaf]
  change ((oppositeRequest steps (received steps)).selectProductive firstCertificate).leaf.branches = [false]
  simp only [oppositeRequest, received]
  apply productive_single_split_right_branches
  dsimp only [ProductiveWindowCertificate.advance]
  rw [show first.rule = RelativeRefinementRule.upper from rfl]
  exact first_bracket_never_falls_below_zero _

theorem all_three_certificates_have_the_same_selected_window (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps (request steps :: requests)).headProduction.endpoint.window =
      (course steps (request steps :: requests)).headProduction.chosen.window :=
  productive_cover_head_window_exact _

theorem the_third_budget_reads_the_produced_second_margins (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps (request steps :: requests)).headProduction.third.steps =
      (secondThirdAgreement steps).modulus
        (course steps (request steps :: requests)).headProduction.second.certificate.agreementPrecision +
      (course steps (request steps :: requests)).headProduction.second.certificate.agreementPrecision.denominator := by
  dsimp only [course]
  rw [productive_cover_course_head_exact]
  exact productive_shared_cover_third_budget ..

theorem second_head_extends_the_actual_received_prefix (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps (request steps :: requests)).headProduction.second.certificate.realization =
      secondCertificate.realization.evolve second.rule
        (course steps (request steps :: requests)).headProduction.second.steps :=
  (course steps (request steps :: requests)).headProduction.second.runExact

theorem third_head_extends_the_actual_received_prefix (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps (request steps :: requests)).headProduction.third.certificate.realization =
      (thirdCertificate steps).realization.evolve (third steps).rule
        (course steps (request steps :: requests)).headProduction.third.steps :=
  (course steps (request steps :: requests)).headProduction.third.runExact

theorem every_head_is_independent_of_its_suffix (steps : Nat)
    (head : ProductiveCoverRequest first second (third steps))
    (one two : List (ProductiveCoverRequest first second (third steps))) :
    (course steps (head :: one)).headProduction = (course steps (head :: two)).headProduction :=
  productive_cover_course_head_horizon_independent ..

theorem every_finite_course_extends_all_received_prefixes (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    ProductiveTripleExtension (received steps) (course steps requests).endpoint :=
  (course steps requests).extendsReceived

theorem all_final_readings_stay_in_the_initial_window (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) (later : Nat) :
    initialWindow.Contains ((course steps requests).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
    initialWindow.Contains ((course steps requests).endpoint.secondCertificate.advance later).realization.state.reading.value ∧
    initialWindow.Contains ((course steps requests).endpoint.thirdCertificate.advance later).realization.state.reading.value :=
  (course steps requests).allLaterReadings later

theorem empty_course_returns_the_complete_received_triple (steps : Nat) :
    (course steps []).endpoint = received steps := rfl

theorem resumption_extends_all_three_actual_endpoints (steps : Nat)
    (requests more : List (ProductiveCoverRequest first second (third steps))) :
    ProductiveTripleExtension (course steps requests).endpoint
      ((course steps requests).resume more agreement (secondThirdAgreement steps)).endpoint :=
  productive_cover_resumption_extends_actual_endpoints ..

theorem repeated_resumption_extends_the_original_prefixes (steps : Nat)
    (requests more last : List (ProductiveCoverRequest first second (third steps))) :
    ProductiveTripleExtension (received steps)
      (((course steps requests).resume more agreement (secondThirdAgreement steps)).resume
        last agreement (secondThirdAgreement steps)).endpoint :=
  productive_triple_extensions_compose
    (productive_triple_extensions_compose (course steps requests).extendsReceived
      ((course steps requests).resume more agreement (secondThirdAgreement steps)).extendsReceived)
    (((course steps requests).resume more agreement (secondThirdAgreement steps)).resume
      last agreement (secondThirdAgreement steps)).extendsReceived

theorem covering_continues_all_three_retained_precision_endpoints (steps : Nat)
    (requests more : List Precision)
    (covers : List (ProductiveCoverRequest first second (third steps))) :
    ProductiveTripleExtension (retainedEndpoint steps requests more)
      ((retainedEndpoint steps requests more).runCovers covers agreement (secondThirdAgreement steps)).endpoint :=
  ((retainedEndpoint steps requests more).runCovers covers agreement (secondThirdAgreement steps)).extendsReceived

theorem the_three_precision_certificates_are_reused_entirely (steps : Nat) (requests more : List Precision) :
    (retainedEndpoint steps requests more).firstCertificate =
        ((firstCertificate.runPrecisions requests).append
          ((firstCertificate.runPrecisions requests).endpoint.certificate.runPrecisions more)).endpoint.certificate ∧
    (retainedEndpoint steps requests more).secondCertificate = (retainedPrecisions steps requests more).1.endpoint ∧
    (retainedEndpoint steps requests more).thirdCertificate = (retainedPrecisions steps requests more).2.endpoint :=
  productive_cover_endpoint_keeps_three_actual_certificates ..

theorem all_three_continued_sources_stay_distinct (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (historyTransport (course steps requests).endpoint.firstCertificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (course steps requests).endpoint.firstCertificate.realization.chain.history).references
        leftSource.reading.arrivals.second ∧
    (historyTransport (course steps requests).endpoint.secondCertificate.realization.chain.history).references
        rightSource.reading.arrivals.first ≠
      (historyTransport (course steps requests).endpoint.secondCertificate.realization.chain.history).references
        rightSource.reading.arrivals.second ∧
    (historyTransport (course steps requests).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (course steps requests).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.second :=
  ⟨relative_refinement_chain_keeps_sources _, relative_refinement_chain_keeps_sources _,
    relative_refinement_chain_keeps_sources _⟩

theorem the_third_continuation_keeps_its_source_record (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps requests).endpoint.thirdCertificate.realization.state.cursor.read
      ((historyTransport (course steps requests).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.secondSignal) = leftSource.cursor.read leftSource.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

def emptySmoke : Nat := (course 1 []).endpoint.thirdCertificate.depth
#eval emptySmoke

end Tests.Relativity.SharedProductiveCoverChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.SharedProductiveCoverChecks.input
#print axioms Tests.Relativity.SharedProductiveCoverChecks.initial
#print axioms Tests.Relativity.SharedProductiveCoverChecks.leftSource
#print axioms Tests.Relativity.SharedProductiveCoverChecks.rightSource
#print axioms Tests.Relativity.SharedProductiveCoverChecks.first
#print axioms Tests.Relativity.SharedProductiveCoverChecks.second
#print axioms Tests.Relativity.SharedProductiveCoverChecks.agreement
#print axioms Tests.Relativity.SharedProductiveCoverChecks.initialWindow
#print axioms Tests.Relativity.SharedProductiveCoverChecks.firstCertificate
#print axioms Tests.Relativity.SharedProductiveCoverChecks.secondCertificate
#print axioms Tests.Relativity.SharedProductiveCoverChecks.thirdSeed
#print axioms Tests.Relativity.SharedProductiveCoverChecks.third
#print axioms Tests.Relativity.SharedProductiveCoverChecks.thirdCertificate
#print axioms Tests.Relativity.SharedProductiveCoverChecks.secondThirdAgreement
#print axioms Tests.Relativity.SharedProductiveCoverChecks.received
#print axioms Tests.Relativity.SharedProductiveCoverChecks.request
#print axioms Tests.Relativity.SharedProductiveCoverChecks.oppositeRequest
#print axioms Tests.Relativity.SharedProductiveCoverChecks.course
#print axioms Tests.Relativity.SharedProductiveCoverChecks.precisionPair
#print axioms Tests.Relativity.SharedProductiveCoverChecks.precisionThird
#print axioms Tests.Relativity.SharedProductiveCoverChecks.retainedPrecisions
#print axioms Tests.Relativity.SharedProductiveCoverChecks.retainedEndpoint
#print axioms Tests.Relativity.SharedProductiveCoverChecks.the_selected_leaf_is_not_reselected
#print axioms Tests.Relativity.SharedProductiveCoverChecks.one_closed_cover_selects_left
#print axioms Tests.Relativity.SharedProductiveCoverChecks.first_bracket_never_falls_below_zero
#print axioms Tests.Relativity.SharedProductiveCoverChecks.the_other_closed_cover_selects_right
#print axioms Tests.Relativity.SharedProductiveCoverChecks.all_three_certificates_have_the_same_selected_window
#print axioms Tests.Relativity.SharedProductiveCoverChecks.the_third_budget_reads_the_produced_second_margins
#print axioms Tests.Relativity.SharedProductiveCoverChecks.second_head_extends_the_actual_received_prefix
#print axioms Tests.Relativity.SharedProductiveCoverChecks.third_head_extends_the_actual_received_prefix
#print axioms Tests.Relativity.SharedProductiveCoverChecks.every_head_is_independent_of_its_suffix
#print axioms Tests.Relativity.SharedProductiveCoverChecks.every_finite_course_extends_all_received_prefixes
#print axioms Tests.Relativity.SharedProductiveCoverChecks.all_final_readings_stay_in_the_initial_window
#print axioms Tests.Relativity.SharedProductiveCoverChecks.empty_course_returns_the_complete_received_triple
#print axioms Tests.Relativity.SharedProductiveCoverChecks.resumption_extends_all_three_actual_endpoints
#print axioms Tests.Relativity.SharedProductiveCoverChecks.repeated_resumption_extends_the_original_prefixes
#print axioms Tests.Relativity.SharedProductiveCoverChecks.covering_continues_all_three_retained_precision_endpoints
#print axioms Tests.Relativity.SharedProductiveCoverChecks.the_three_precision_certificates_are_reused_entirely
#print axioms Tests.Relativity.SharedProductiveCoverChecks.all_three_continued_sources_stay_distinct
#print axioms Tests.Relativity.SharedProductiveCoverChecks.the_third_continuation_keeps_its_source_record
#print axioms Tests.Relativity.SharedProductiveCoverChecks.emptySmoke
/- AXIOM_AUDIT_END -/
