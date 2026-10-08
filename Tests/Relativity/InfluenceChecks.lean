import RelationalPerimeter

/-! Public clients of permitted and used local influence. Executability checks
are smoke tests, not physical observations or complexity measurements. -/
set_option genInjectivity false
namespace Tests.Relativity.InfluenceChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := Cursor.received input

/-- The length is finite but arbitrary; no enumeration of other histories. -/
def relayedReception : (count : Nat) → {context : List Kind} →
    (signal : Ref context .signal) → Ref context .calibration →
    InfluencePlan context ⟨.signal, signal⟩ .reading
  | 0, _, signal, _ => .finish (.receive signal) signal (.receptionSignal signal)
  | count + 1, _, signal, calibration => .follow (.relay signal calibration) signal
      (.relaySignal signal calibration) (relayedReception count .here (.prior calibration))
termination_by structural count _context _signal _calibration => count

def readingToReception (count : Nat) : InfluencePlan receivedKinds ⟨.reading, .here⟩ .reading :=
  .follow emission .here (.emissionReading .here (.prior .here))
    (relayedReception count .here (.prior (.prior (.prior .here))))

theorem relayedReception_steps (count : Nat) {context : List Kind}
    (signal : Ref context .signal) (calibration : Ref context .calibration) :
    (relayedReception count signal calibration).schedule.steps = count + 1 := by
  induction count generalizing context with
  | zero => rfl
  | succ count ih => exact congrArg (fun n => n + 1) (ih .here (.prior calibration))

theorem arbitrary_finite_realization (received : Received) (count : Nat) :
    StrongPerimetralTurning.History.length
      (realizeInfluence (Cursor.received received) (readingToReception count)).execution.history = count + 2 :=
  (congrArg (fun execution => StrongPerimetralTurning.History.length execution.history)
    (realizeInfluence_execution_exact (Cursor.received received) (readingToReception count))).trans
    ((run_history_length _ _).trans (congrArg (fun n => n + 1) (relayedReception_steps count _ _)))

def permittedReception : InfluencePlan receivedKinds ⟨.reading, .here⟩ .reading := readingToReception 3
def receivedAfterRelays := realizeInfluence source permittedReception

theorem no_present_edge (one two : Occurrence receivedKinds)
    (edge : Used source.formation one two) : False := received_has_no_used_edge input edge

/-- An empty used relation at the root does not refute permitted future use. -/
def permitted_future_is_realized := receivedAfterRelays.path

theorem realized_reading_is_three :
    receivedAfterRelays.execution.cursor.read receivedAfterRelays.target = Rational.ofNat 3 := rfl

theorem root_and_arrival_remain_distinct :
    extensionOccurrence (historyTransport receivedAfterRelays.execution.history) ⟨.reading, .here⟩ ≠
      ⟨.reading, receivedAfterRelays.target⟩ := realized_influence_distinct source permittedReception

theorem no_payload_output {context : List Kind} {origin : Occurrence context}
    (plan : InfluencePlan context origin .payload) : False := plan.target_not_payload rfl

def emitted := perform source emission
def delayedReception : InfluencePlan emitted.successor.kinds ⟨.signal, .here⟩ .reading :=
  .delay (.emit (.prior .here) (.prior (.prior .here)))
    (.finish (.receive (.prior .here)) (.prior .here) (.receptionSignal (.prior .here)))

def delayed := realizeInfluence emitted.successor delayedReception

theorem intervening_emission_preserves_source :
    extensionOccurrence (historyTransport delayed.execution.history) ⟨.signal, .here⟩ =
      (⟨.signal, .prior (.prior .here)⟩ : Occurrence delayed.execution.cursor.kinds) := rfl

theorem delay_keeps_old_signal_influence :
    delayed.execution.cursor.read delayed.target = input.reading := rfl

def duplicated := produceIndependentPair source emission emission
def firstJourney := signalJourney duplicated.cursor.formation (.prior .here)
def secondJourney := signalJourney duplicated.cursor.formation .here

theorem equal_signal_values : duplicated.cursor.read (.prior .here) = duplicated.cursor.read .here := rfl
theorem distinct_emissions : firstJourney.origin ≠ secondJourney.origin := by
  intro same
  have position := congrArg Ref.position same
  change (1 : Nat) = 0 at position
  cases position

def firstEmission := firstJourney.originEvent
def secondEmission := secondJourney.originEvent

def relayed := perform emitted.successor (.relay .here (.prior (.prior (.prior .here))))
def relayJourney := signalJourney relayed.successor.formation .here

theorem relay_origin_is_emission : relayJourney.origin = .prior .here := rfl
theorem relay_has_one_increment : relayJourney.relayCount = 1 := rfl
theorem record_agrees_with_real_relays :
    (relayed.successor.read (Ref.here : Ref relayed.successor.kinds .signal)).increments.length =
      relayJourney.relayCount := relayJourney.recorded_length

def actual_relay_path := relayJourney.reaches
def arrival := perform relayed.successor (.receive .here)
def arrivalJourney := receptionJourney arrival

theorem arriving_origin_preserved : arrivalJourney.origin = .prior (.prior .here) := rfl
theorem actual_arrival_reading : arrival.determination.1 = (relayed.successor.read .here).reading :=
  reception_reads_arriving_signal arrival

def swapped := independentPairConstitution duplicated duplicated
def fromFirstEmission : InfluencePlan duplicated.cursor.kinds ⟨.signal, .prior .here⟩ .reading :=
  .finish (.receive (.prior .here)) (.prior .here) (.receptionSignal (.prior .here))

theorem transported_plan_uses_corresponding_occurrence :
    (fromFirstEmission.rename swapped.reading.references).schedule =
      Program.step (.receive .here) .done := rfl

theorem both_permitted_directions :
    Nonempty (InfluencePlan duplicated.cursor.kinds
      (swapped.reading.references.occurrences.forward ⟨.signal, .prior .here⟩) .reading) ↔
      Nonempty (InfluencePlan duplicated.cursor.kinds ⟨.signal, .prior .here⟩ .reading) :=
  transported_influence_iff swapped.reading.references _ _

theorem transported_execution_exact :
    (continueCorresponding swapped fromFirstEmission.schedule).first =
      (realizeInfluence duplicated.cursor fromFirstEmission).execution ∧
    (continueCorresponding swapped fromFirstEmission.schedule).second =
      (realizeInfluence duplicated.cursor (fromFirstEmission.rename swapped.reading.references)).execution :=
  corresponding_influence_executions swapped fromFirstEmission

#eval receivedAfterRelays.execution.cursor.read receivedAfterRelays.target
#eval (relayJourney.relayCount, (relayed.successor.read (Ref.here : Ref relayed.successor.kinds .signal)).payload)

end Tests.Relativity.InfluenceChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.InfluenceChecks.relayedReception
#print axioms Tests.Relativity.InfluenceChecks.readingToReception
#print axioms Tests.Relativity.InfluenceChecks.relayedReception_steps
#print axioms Tests.Relativity.InfluenceChecks.arbitrary_finite_realization
#print axioms Tests.Relativity.InfluenceChecks.no_present_edge
#print axioms Tests.Relativity.InfluenceChecks.permitted_future_is_realized
#print axioms Tests.Relativity.InfluenceChecks.realized_reading_is_three
#print axioms Tests.Relativity.InfluenceChecks.root_and_arrival_remain_distinct
#print axioms Tests.Relativity.InfluenceChecks.no_payload_output
#print axioms Tests.Relativity.InfluenceChecks.intervening_emission_preserves_source
#print axioms Tests.Relativity.InfluenceChecks.delay_keeps_old_signal_influence
#print axioms Tests.Relativity.InfluenceChecks.distinct_emissions
#print axioms Tests.Relativity.InfluenceChecks.firstEmission
#print axioms Tests.Relativity.InfluenceChecks.secondEmission
#print axioms Tests.Relativity.InfluenceChecks.relay_origin_is_emission
#print axioms Tests.Relativity.InfluenceChecks.relay_has_one_increment
#print axioms Tests.Relativity.InfluenceChecks.record_agrees_with_real_relays
#print axioms Tests.Relativity.InfluenceChecks.actual_relay_path
#print axioms Tests.Relativity.InfluenceChecks.arriving_origin_preserved
#print axioms Tests.Relativity.InfluenceChecks.actual_arrival_reading
#print axioms Tests.Relativity.InfluenceChecks.transported_plan_uses_corresponding_occurrence
#print axioms Tests.Relativity.InfluenceChecks.both_permitted_directions
#print axioms Tests.Relativity.InfluenceChecks.transported_execution_exact
/- AXIOM_AUDIT_END -/
