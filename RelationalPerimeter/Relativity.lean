import RelationalPerimeter.Relativity.Analysis.ReadoutInterpretation
import RelationalPerimeter.Relativity.Analysis.PolynomialCalculus
import RelationalPerimeter.Relativity.Analysis.PolynomialInterpretation
import RelationalPerimeter.Relativity.Production.CalibratedRelay
import RelationalPerimeter.Relativity.Production.RequestedExecution
import RelationalPerimeter.Relativity.Production.TransportedContinuations
import RelationalPerimeter.Relativity.Production.TransportedRequests
import RelationalPerimeter.Relativity.Production.SignalJourneys
import RelationalPerimeter.Relativity.Production.TransportedInfluences
import RelationalPerimeter.Relativity.Production.ArrivalComparisons
import RelationalPerimeter.Relativity.Production.InstrumentFutures
import RelationalPerimeter.Relativity.Production.RecurringFutures
import RelationalPerimeter.Relativity.Production.TransportedRecurringRequests
import RelationalPerimeter.Relativity.Production.GroupedRecurringContinuation
import RelationalPerimeter.Relativity.Production.ConstitutedDescriptions

/-!
The numerical prerequisites and first declared local-production candidate.
No relativistic certificate is exported: the complete physical contract,
grouping and intrinsic geometry obligations remain open. The candidate has
its own executable request contract, including refusals and path-record reads.
Independent old-port instructions can be exchanged with exact occurrence and
used-dependency transports, extended to arbitrary finite typed programs. The
complete local addressed request contract is preserved through the current
occurrence transport, including admissions, refusals and full path-record reads.
Permitted finite local influences are distinct from executed dependencies; their
realizer produces a used path and exactly the existing runner's history. Stored
signal productions reconstruct emission and relay provenance without replay.
Positive reception contexts distinguish arrivals from given initial readings.
A declared two-arrival comparison forms a new reading on the same resource
support, then feeds the existing signal instructions through a shared head.
This instrumental extension is not spacetime colocation. Its signal-instruction
futures now have their own explicit full-read contract and paired runner,
preserving all finite interleavings and refusals from the comparison's actual
successor. A further closed extension admits repeated comparisons of actual
receptions on that same support, with a fixed contract covering every finite
interleaving, transported arrivals and used dependencies. Comparison outputs
are not receptions; new receptions must be executed before such outputs can
serve as arrival ports. This recurring contract is now transported through
actual independent exchanges and all later shared productions, in both
directions, including exact refusals. Typed receptions and used dependencies
return positively; numerical addresses follow the current occurrence map.
A local recognizer now finds old-port exchanges or a positively used fresh
port that refuses this exchange grammar. Its action reorders the cached
determinations without rerunning either producer. The recurring continuation
then executes one shared action and positively transports that same output
and role into the other presentation, preserving the full existing contract.
Both presented histories and their source distinctions remain available;
this is not yet an exact memory reduction or the final physical contract.
Occurrence-attached descriptions now incorporate cached productions and exact
presentation changes. Complementary signal readers have common refinements
whose restrictions need no support reread; selecting them creates no event.
Partial reading agreement cannot erase a path still exposed by the contract.
The calibrated signal law
neither receives nor reconstructs a spacetime metric.
The computation master and its contracts are unchanged.
-/

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.reads
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.arrival
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.used
#print axioms RelationalPerimeter.Relativity.Production.described_signal_common_refinement
#print axioms RelationalPerimeter.Relativity.Production.continued_exchange_description_exact
#print axioms RelationalPerimeter.Relativity.Production.differing_paths_separate_futures
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.interpretationAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.rationalReading
#print axioms RelationalPerimeter.Relativity.Rational.equal_iff_agree
#print axioms RelationalPerimeter.Relativity.Rational.mul_add
#print axioms RelationalPerimeter.Relativity.Rational.normalize_le_iff
#print axioms RelationalPerimeter.Relativity.Analysis.Agreement.compose
#print axioms RelationalPerimeter.Relativity.Analysis.constant_agreement_iff_equality
#print axioms RelationalPerimeter.Relativity.Analysis.vanishingAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.vanishing_encoding_distinct
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.jet_exact
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.derivative_primitive
#print axioms RelationalPerimeter.Relativity.Production.perform
#print axioms RelationalPerimeter.Relativity.Production.producedOccurrenceTransport
#print axioms RelationalPerimeter.Relativity.Production.run_step_history_exact
#print axioms RelationalPerimeter.Relativity.Production.relay_history_length
#print axioms RelationalPerimeter.Relativity.Production.equal_readings_distinct_occurrences
#print axioms RelationalPerimeter.Relativity.Production.historyTransportUsed
#print axioms RelationalPerimeter.Relativity.Production.historyTransportPath
#print axioms RelationalPerimeter.Relativity.Production.resolve
#print axioms RelationalPerimeter.Relativity.Production.localContract
#print axioms RelationalPerimeter.Relativity.Production.futures_preserve_available_readout
#print axioms RelationalPerimeter.Relativity.Production.requests_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.continuation_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.independentPairConstitution
#print axioms RelationalPerimeter.Relativity.Production.continueCorresponding_source_exact
#print axioms RelationalPerimeter.Relativity.Production.independentPairAddressed
#print axioms RelationalPerimeter.Relativity.Production.transported_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.signalJourney
#print axioms RelationalPerimeter.Relativity.Production.receptionJourney
#print axioms RelationalPerimeter.Relativity.Production.realizeInfluence_execution_exact
#print axioms RelationalPerimeter.Relativity.Production.transported_influence_iff
#print axioms RelationalPerimeter.Relativity.Production.resolveArrivalAt
#print axioms RelationalPerimeter.Relativity.Production.requestComparison
#print axioms RelationalPerimeter.Relativity.Production.comparison_equal_readings_not_equal_sources
#print axioms RelationalPerimeter.Relativity.Production.runCompared
#print axioms RelationalPerimeter.Relativity.Production.compared_head_independent
#print axioms RelationalPerimeter.Relativity.Production.emitted_comparison_reading
#print axioms RelationalPerimeter.Relativity.Production.instrumentContract
#print axioms RelationalPerimeter.Relativity.Production.instrument_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_futures_preserve_readout
#print axioms RelationalPerimeter.Relativity.Production.compared_requests_all_futures
#print axioms RelationalPerimeter.Relativity.Production.compared_requests_keep_sources
#print axioms RelationalPerimeter.Relativity.Production.RecurringCursor.fromInstrument
#print axioms RelationalPerimeter.Relativity.Production.recurring_comparison_not_reception
#print axioms RelationalPerimeter.Relativity.Production.recurringHistoryArrival
#print axioms RelationalPerimeter.Relativity.Production.recurringHistoryUsed
#print axioms RelationalPerimeter.Relativity.Production.recurringContract
#print axioms RelationalPerimeter.Relativity.Production.recurring_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_repetition_length
#print axioms RelationalPerimeter.Relativity.Production.recurring_futures_preserve_readout
#print axioms RelationalPerimeter.Relativity.Production.independentRecurringPair
#print axioms RelationalPerimeter.Relativity.Production.recurring_transported_admission_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_transported_all_futures
#print axioms RelationalPerimeter.Relativity.Production.recurring_corresponding_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.searchStoredExchange
#print axioms RelationalPerimeter.Relativity.Production.exchange_found_iff_old
#print axioms RelationalPerimeter.Relativity.Production.exchanged_outputs_are_cached
#print axioms RelationalPerimeter.Relativity.Production.shared_recurring_all_futures
#print axioms RelationalPerimeter.Relativity.Production.shared_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.discovered_exchange_all_futures
/- AXIOM_AUDIT_END -/
