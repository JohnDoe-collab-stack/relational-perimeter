import RelationalPerimeter

/-! Closed clients of the first local candidate. Not a geometry or cost audit. -/
set_option genInjectivity false
namespace Tests.Relativity.LocalProductionChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

theorem received_has_no_signal (ref : Ref receivedKinds Kind.signal) : False := by
  cases ref with
  | prior ref => cases ref with
    | prior ref => cases ref with
      | prior ref => cases ref

theorem cannot_prescribe_emission (output : SignalRecord)
    (role : Produces input.values emission output)
    (wrong : output.payload ≠ input.payload) : False :=
  wrong (congrArg SignalRecord.payload role.output_exact)

theorem cannot_supply_zero_increment (calibration : Calibration)
    (zero : calibration.increment = Rational.zero) : False := calibration.nonzero zero

theorem reception_uses_emission (received : Received) :
    (receiveEmission received).determination.1 = received.reading :=
  reception_reads_produced_emission received

theorem same_formed_resource_interpretation (source : Cursor) {kind}
    (instruction : Instruction source.kinds kind) :
    ResourceInterpretation (perform source instruction).successor.formation
      (perform source instruction).successor.resourceFormation :=
  (perform source instruction).successor.resourceExact

theorem equal_values_do_not_identify_resources (received : Received) :
    (receiveEmission received).successor.read
      (Ref.here : Ref (.reading :: (emittedCursor received).kinds) .reading) =
        (receiveEmission received).successor.read (.prior (.prior .here)) ∧
    (Ref.here : Ref (.reading :: (emittedCursor received).kinds) .reading) ≠ .prior (.prior .here) :=
  equal_readings_distinct_occurrences received

theorem exact_occurrence_return (source : Cursor) {kind}
    {instruction : Instruction source.kinds kind} (production : Determination source instruction)
    (old : Occurrence source.kinds ⊕ Unit) :
    (producedOccurrenceTransport source production).backward
      ((producedOccurrenceTransport source production).forward old) = old :=
  (producedOccurrenceTransport source production).forwardBackward old

theorem exact_reverse_return (source : Cursor) {kind}
    {instruction : Instruction source.kinds kind} (production : Determination source instruction)
    (occurrence : Occurrence (source.extend production).kinds) :
    (producedOccurrenceTransport source production).forward
      ((producedOccurrenceTransport source production).backward occurrence) = occurrence :=
  (producedOccurrenceTransport source production).backwardForward occurrence

theorem arbitrary_finite_length (received : Received) (count : Nat) :
    StrongPerimetralTurning.History.length (relayExecution received count).history = count + 1 :=
  relay_history_length received count

theorem old_read_survives_all_relays (received : Received) (count : Nat) :
    (relayExecution received count).cursor.read
      ((historyTransport (relayExecution received count).history).references
        (Ref.here : Ref receivedKinds Kind.reading)) = received.reading :=
  history_preserves_reads (relayExecution received count).history .here

theorem actual_head_before_suffix (source : Cursor) {kind}
    (instruction : Instruction source.kinds kind) (tail : Program (kind :: source.kinds)) :
    (run source (.step instruction tail)).history =
      StrongPerimetralTurning.History.append (oneStepHistory source instruction)
        (run (perform source instruction).successor tail).history :=
  run_step_history_exact source instruction tail

theorem emitted_zero_and_one_differ :
    (perform (Cursor.received input) emission).determination.1 ≠
      (perform (Cursor.received ⟨Rational.one, input.payload, input.calibration⟩) emission).determination.1 :=
  emission_depends_on_received_reading _ _ (fun same => Rational.one_ne_zero same.symm)

theorem relay_reads_calibration (received : Received) :
    (execute (emittedCursor received).values
      (.relay .here (.prior (.prior (.prior .here))))).1.reading ≠ received.reading :=
  relay_output_changes (emittedCursor received).values .here (.prior (.prior (.prior .here)))

theorem empty_suffix_is_single_production :
    (run (Cursor.received input) (.step emission .done)).history = oneStepHistory (Cursor.received input) emission :=
  rfl

theorem smoke_zero : relaySmoke 0 = some 0 := rfl

theorem smoke_three : relaySmoke 3 = some 3 := by decide

-- Executability only: not a confirmatory experiment, duration or complexity claim.
#eval relaySmoke 3

end Tests.Relativity.LocalProductionChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.LocalProductionChecks.input
#print axioms Tests.Relativity.LocalProductionChecks.received_has_no_signal
#print axioms Tests.Relativity.LocalProductionChecks.cannot_prescribe_emission
#print axioms Tests.Relativity.LocalProductionChecks.cannot_supply_zero_increment
#print axioms Tests.Relativity.LocalProductionChecks.reception_uses_emission
#print axioms Tests.Relativity.LocalProductionChecks.same_formed_resource_interpretation
#print axioms Tests.Relativity.LocalProductionChecks.equal_values_do_not_identify_resources
#print axioms Tests.Relativity.LocalProductionChecks.exact_occurrence_return
#print axioms Tests.Relativity.LocalProductionChecks.exact_reverse_return
#print axioms Tests.Relativity.LocalProductionChecks.arbitrary_finite_length
#print axioms Tests.Relativity.LocalProductionChecks.old_read_survives_all_relays
#print axioms Tests.Relativity.LocalProductionChecks.actual_head_before_suffix
#print axioms Tests.Relativity.LocalProductionChecks.emitted_zero_and_one_differ
#print axioms Tests.Relativity.LocalProductionChecks.relay_reads_calibration
#print axioms Tests.Relativity.LocalProductionChecks.empty_suffix_is_single_production
#print axioms Tests.Relativity.LocalProductionChecks.smoke_zero
#print axioms Tests.Relativity.LocalProductionChecks.smoke_three
/- AXIOM_AUDIT_END -/
