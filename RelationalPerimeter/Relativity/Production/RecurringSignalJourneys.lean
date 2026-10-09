import RelationalPerimeter.Relativity.Production.RecurringInteractions
import RelationalPerimeter.Relativity.Production.RelativePathReadings

/-!
# Signal ancestry on the support that also carries interactions

The old positive signal journeys enter without replay. Emissions and relays
after a comparison are accounted for by their actual roles. Comparisons and
other intervening productions transport the origin and the recorded effects;
they do not restart a journey. No location, prescribed reading or future tail
is an input to this ancestry. Unit calibration concerns each consumed relay,
not merely an equality of its final numerical reading.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive InstrumentJourney : {context : List Kind} → {values : Values Value context} →
    InstrumentFormation (context := context) values → Ref context .signal → Type where
  | compared {source : Cursor} {pair : ArrivalPair source} {output : Rational}
      (role : ComparisonProduces pair output) {signal : Ref source.kinds .signal}
      (journey : SignalJourney source.formation signal) :
      InstrumentJourney (.compared pair role) (.prior signal)
  | emitted {context} {values : Values Value context} (past : InstrumentFormation values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      InstrumentJourney (.produced past (.emitted reading payload)) .here
  | relayed {context} {values : Values Value context} {past : InstrumentFormation values}
      {signal : Ref context .signal} (calibration : Ref context .calibration)
      (journey : InstrumentJourney past signal) :
      InstrumentJourney (.produced past (.relayed signal calibration)) .here
  | inherited {context} {values : Values Value context} {past : InstrumentFormation values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {signal : Ref context .signal}
      (journey : InstrumentJourney past signal) : InstrumentJourney (.produced past role) (.prior signal)

def InstrumentJourney.origin {context} {values : Values Value context} {past : InstrumentFormation values}
    {signal : Ref context .signal} (journey : InstrumentJourney past signal) : Ref context .signal := by
  cases journey with
  | compared _ old => exact .prior old.origin
  | emitted _ _ _ => exact .here
  | relayed _ old => exact .prior old.origin
  | inherited _ old => exact .prior old.origin
termination_by structural journey

def InstrumentJourney.relayCount {context} {values : Values Value context} {past : InstrumentFormation values}
    {signal : Ref context .signal} (journey : InstrumentJourney past signal) : Nat := by
  cases journey with
  | compared _ old => exact old.relayCount
  | emitted _ _ _ => exact 0
  | relayed _ old => exact old.relayCount + 1
  | inherited _ old => exact old.relayCount
termination_by structural journey

def instrumentJourney {context} {values : Values Value context}
    (past : InstrumentFormation values) (signal : Ref context .signal) : InstrumentJourney past signal := by
  cases past with
  | compared pair role =>
    cases signal with | prior old => exact .compared role (signalJourney _ old)
  | produced past role =>
    cases signal with
    | here => cases role with
      | emitted reading payload => exact .emitted past reading payload
      | relayed previous calibration => exact .relayed calibration (instrumentJourney past previous)
    | prior old => exact .inherited role (instrumentJourney past old)
termination_by structural past

inductive InstrumentUnitJourney : {context : List Kind} → {values : Values Value context} →
    {past : InstrumentFormation values} → {signal : Ref context .signal} →
    InstrumentJourney past signal → Type where
  | compared {source : Cursor} {pair : ArrivalPair source} {output : Rational}
      (role : ComparisonProduces pair output) {signal : Ref source.kinds .signal}
      {journey : SignalJourney source.formation signal} (unit : UnitJourney journey) :
      InstrumentUnitJourney (.compared role journey)
  | emitted {context} {values : Values Value context} (past : InstrumentFormation values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      InstrumentUnitJourney (.emitted past reading payload)
  | relayed {context} {values : Values Value context} {past : InstrumentFormation values}
      {signal : Ref context .signal} {calibration : Ref context .calibration}
      {journey : InstrumentJourney past signal} (prior : InstrumentUnitJourney journey)
      (unit : (read values calibration).increment = Rational.one) :
      InstrumentUnitJourney (.relayed calibration journey)
  | inherited {context} {values : Values Value context} {past : InstrumentFormation values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {signal : Ref context .signal}
      {journey : InstrumentJourney past signal} (unit : InstrumentUnitJourney journey) :
      InstrumentUnitJourney (.inherited role journey)

theorem InstrumentUnitJourney.reading_exact {context} {values : Values Value context}
    {past : InstrumentFormation values} {signal : Ref context .signal}
    {journey : InstrumentJourney past signal} (unit : InstrumentUnitJourney journey) :
    (read values signal).reading = Rational.add (read values journey.origin).reading
      (Rational.ofNat journey.relayCount) := by
  induction unit with
  | compared role unit => exact unit.reading_exact
  | emitted past reading payload => exact (Rational.add_zero _).symm
  | @relayed context values past signal calibration journey prior unit ih =>
    change Rational.add (read values signal).reading (read values calibration).increment =
      Rational.add (read values journey.origin).reading (Rational.ofNat (journey.relayCount + 1))
    rw [unit, ih, Rational.add_assoc, show Rational.one = Rational.ofNat 1 from rfl, Rational.nat_add]
  | inherited role unit ih => exact ih

inductive RecurringJourney : {context : List Kind} → {values : Values Value context} →
    RecurringFormation values → Ref context .signal → Type where
  | fromCursor {source : Cursor} {signal : Ref source.kinds .signal}
      (journey : SignalJourney source.formation signal) : RecurringJourney (.fromCursor source) signal
  | fromInstrument {source : InstrumentCursor} {signal : Ref source.kinds .signal}
      (journey : InstrumentJourney source.formation signal) : RecurringJourney (.fromInstrument source) signal
  | emitted {context} {values : Values Value context} (past : RecurringFormation values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      RecurringJourney (.signal past (.emitted reading payload)) .here
  | relayed {context} {values : Values Value context} {past : RecurringFormation values}
      {signal : Ref context .signal} (calibration : Ref context .calibration)
      (journey : RecurringJourney past signal) :
      RecurringJourney (.signal past (.relayed signal calibration)) .here
  | throughSignal {context} {values : Values Value context} {past : RecurringFormation values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {signal : Ref context .signal}
      (journey : RecurringJourney past signal) : RecurringJourney (.signal past role) (.prior signal)
  | throughComparison {context} {values : Values Value context} {past : RecurringFormation values}
      {first second : Ref context .reading} {output : Rational}
      (role : RecurringComputed values first second output) {signal : Ref context .signal}
      (journey : RecurringJourney past signal) : RecurringJourney (.comparison past first second role) (.prior signal)

def RecurringJourney.origin {context} {values : Values Value context} {past : RecurringFormation values}
    {signal : Ref context .signal} (journey : RecurringJourney past signal) : Ref context .signal := by
  cases journey with
  | fromCursor old => exact old.origin
  | fromInstrument old => exact old.origin
  | emitted _ _ _ => exact .here
  | relayed _ old => exact .prior old.origin
  | throughSignal _ old => exact .prior old.origin
  | throughComparison _ old => exact .prior old.origin
termination_by structural journey

def RecurringJourney.relayCount {context} {values : Values Value context} {past : RecurringFormation values}
    {signal : Ref context .signal} (journey : RecurringJourney past signal) : Nat := by
  cases journey with
  | fromCursor old => exact old.relayCount
  | fromInstrument old => exact old.relayCount
  | emitted _ _ _ => exact 0
  | relayed _ old => exact old.relayCount + 1
  | throughSignal _ old => exact old.relayCount
  | throughComparison _ old => exact old.relayCount
termination_by structural journey

def recurringJourney {context} {values : Values Value context}
    (past : RecurringFormation values) (signal : Ref context .signal) : RecurringJourney past signal := by
  cases past with
  | fromCursor source => exact .fromCursor (signalJourney source.formation signal)
  | fromInstrument source => exact .fromInstrument (instrumentJourney source.formation signal)
  | signal past role =>
    cases signal with
    | here => cases role with
      | emitted reading payload => exact .emitted past reading payload
      | relayed previous calibration => exact .relayed calibration (recurringJourney past previous)
    | prior old => exact .throughSignal role (recurringJourney past old)
  | comparison past first second role =>
    cases signal with | prior old => exact .throughComparison role (recurringJourney past old)
termination_by structural past

theorem InstrumentJourney.recorded_length {context} {values : Values Value context}
    {past : InstrumentFormation values} {signal : Ref context .signal} (journey : InstrumentJourney past signal) :
    (read values signal).increments.length = journey.relayCount := by
  induction journey with
  | compared role old => exact old.recorded_length
  | emitted past reading payload => rfl
  | relayed calibration old ih => exact (increments_length_append _ _).trans (congrArg (fun n => n + 1) ih)
  | inherited role old ih => exact ih

theorem InstrumentJourney.payload_from_origin {context} {values : Values Value context}
    {past : InstrumentFormation values} {signal : Ref context .signal} (journey : InstrumentJourney past signal) :
    (read values signal).payload = (read values journey.origin).payload := by
  induction journey with
  | compared role old => exact old.payload_from_origin
  | emitted past reading payload => rfl
  | relayed calibration old ih => exact ih
  | inherited role old ih => exact ih

theorem RecurringJourney.recorded_length {context} {values : Values Value context}
    {past : RecurringFormation values} {signal : Ref context .signal} (journey : RecurringJourney past signal) :
    (read values signal).increments.length = journey.relayCount := by
  induction journey with
  | fromCursor old => exact old.recorded_length
  | fromInstrument old => exact old.recorded_length
  | emitted past reading payload => rfl
  | relayed calibration old ih => exact (increments_length_append _ _).trans (congrArg (fun n => n + 1) ih)
  | throughSignal role old ih => exact ih
  | throughComparison role old ih => exact ih

theorem RecurringJourney.payload_from_origin {context} {values : Values Value context}
    {past : RecurringFormation values} {signal : Ref context .signal} (journey : RecurringJourney past signal) :
    (read values signal).payload = (read values journey.origin).payload := by
  induction journey with
  | fromCursor old => exact old.payload_from_origin
  | fromInstrument old => exact old.payload_from_origin
  | emitted past reading payload => rfl
  | relayed calibration old ih => exact ih
  | throughSignal role old ih => exact ih
  | throughComparison role old ih => exact ih

inductive RecurringUnitJourney : {context : List Kind} → {values : Values Value context} →
    {past : RecurringFormation values} → {signal : Ref context .signal} →
    RecurringJourney past signal → Type where
  | fromCursor {source : Cursor} {signal : Ref source.kinds .signal}
      {journey : SignalJourney source.formation signal} (unit : UnitJourney journey) :
      RecurringUnitJourney (.fromCursor journey)
  | fromInstrument {source : InstrumentCursor} {signal : Ref source.kinds .signal}
      {journey : InstrumentJourney source.formation signal} (unit : InstrumentUnitJourney journey) :
      RecurringUnitJourney (.fromInstrument journey)
  | emitted {context} {values : Values Value context} (past : RecurringFormation values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      RecurringUnitJourney (.emitted past reading payload)
  | relayed {context} {values : Values Value context} {past : RecurringFormation values}
      {signal : Ref context .signal} {calibration : Ref context .calibration}
      {journey : RecurringJourney past signal} (prior : RecurringUnitJourney journey)
      (unit : (read values calibration).increment = Rational.one) :
      RecurringUnitJourney (.relayed calibration journey)
  | throughSignal {context} {values : Values Value context} {past : RecurringFormation values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {signal : Ref context .signal}
      {journey : RecurringJourney past signal} (unit : RecurringUnitJourney journey) :
      RecurringUnitJourney (.throughSignal role journey)
  | throughComparison {context} {values : Values Value context} {past : RecurringFormation values}
      {first second : Ref context .reading} {output : Rational}
      (role : RecurringComputed values first second output) {signal : Ref context .signal}
      {journey : RecurringJourney past signal} (unit : RecurringUnitJourney journey) :
      RecurringUnitJourney (.throughComparison role journey)

theorem RecurringUnitJourney.reading_exact {context} {values : Values Value context}
    {past : RecurringFormation values} {signal : Ref context .signal}
    {journey : RecurringJourney past signal} (unit : RecurringUnitJourney journey) :
    (read values signal).reading = Rational.add (read values journey.origin).reading
      (Rational.ofNat journey.relayCount) := by
  induction unit with
  | fromCursor unit => exact unit.reading_exact
  | fromInstrument unit => exact unit.reading_exact
  | emitted past reading payload => exact (Rational.add_zero _).symm
  | @relayed context values past signal calibration journey prior unit ih =>
    change Rational.add (read values signal).reading (read values calibration).increment =
      Rational.add (read values journey.origin).reading (Rational.ofNat (journey.relayCount + 1))
    rw [unit, ih, Rational.add_assoc, show Rational.one = Rational.ofNat 1 from rfl, Rational.nat_add]
  | throughSignal role unit ih => exact ih
  | throughComparison role unit ih => exact ih

def RecurringJourney.transportStep {source target : RecurringCursor} (step : RecurringStep source target)
    {signal : Ref source.kinds .signal} (journey : RecurringJourney source.formation signal) :
    RecurringJourney target.formation (step.transport.references signal) := by
  cases step with
  | mk kind action determination exactTarget =>
    cases exactTarget
    cases action with
    | signal instruction => cases determination with
      | mk output role => cases role with | signal localRole => exact .throughSignal localRole journey
    | compare pair => cases determination with
      | mk output role => cases role with | compared localRole => exact .throughComparison localRole journey

def RecurringJourney.transport {source target : RecurringCursor} (history : RecurringHistory source target)
    {signal : Ref source.kinds .signal} (journey : RecurringJourney source.formation signal) :
    RecurringJourney target.formation ((recurringHistoryTransport history).references signal) :=
  match history with
  | .root => journey
  | .extend past step => (journey.transport past).transportStep step
termination_by structural history

theorem RecurringJourney.transport_origin {source target : RecurringCursor} (history : RecurringHistory source target)
    {signal : Ref source.kinds .signal} (journey : RecurringJourney source.formation signal) :
    (journey.transport history).origin = (recurringHistoryTransport history).references journey.origin := by
  induction history with
  | root => rfl
  | extend past step ih =>
    cases step with
    | mk kind action determination exactTarget =>
      cases exactTarget
      cases action with
      | signal instruction => cases determination with
        | mk output role => cases role with | signal localRole => exact congrArg Ref.prior ih
      | compare pair => cases determination with
        | mk output role => cases role with | compared localRole => exact congrArg Ref.prior ih

theorem RecurringJourney.transport_count {source target : RecurringCursor} (history : RecurringHistory source target)
    {signal : Ref source.kinds .signal} (journey : RecurringJourney source.formation signal) :
    (journey.transport history).relayCount = journey.relayCount := by
  exact (journey.transport history).recorded_length.symm.trans
    ((congrArg (fun record : SignalRecord => record.increments.length)
      ((recurringHistoryTransport history).reads signal)).trans journey.recorded_length)

def RecurringUnitJourney.transportStep {source target : RecurringCursor} (step : RecurringStep source target)
    {signal : Ref source.kinds .signal} {journey : RecurringJourney source.formation signal}
    (unit : RecurringUnitJourney journey) : RecurringUnitJourney (journey.transportStep step) := by
  cases step with
  | mk kind action determination exactTarget =>
    cases exactTarget
    cases action with
    | signal instruction => cases determination with
      | mk output role => cases role with | signal localRole => exact .throughSignal localRole unit
    | compare pair => cases determination with
      | mk output role => cases role with | compared localRole => exact .throughComparison localRole unit

def RecurringUnitJourney.transport {source target : RecurringCursor} (history : RecurringHistory source target)
    {signal : Ref source.kinds .signal} {journey : RecurringJourney source.formation signal}
    (unit : RecurringUnitJourney journey) : RecurringUnitJourney (journey.transport history) :=
  match history with
  | .root => unit
  | .extend past step => (unit.transport past).transportStep step
termination_by structural history

theorem InstrumentArrived.signal_reading {context} {values : Values Value context}
    {past : InstrumentFormation values} {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : InstrumentArrived past reading signal) :
    read values reading = (read values signal).reading := by
  induction arrival with
  | priorComparison role old => exact old.reading_exact
  | received past signal => rfl
  | inherited role old ih => exact ih

theorem RecurringArrival.signal_reading {context} {values : Values Value context}
    {past : RecurringFormation values} {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : RecurringArrival past reading signal) :
    read values reading = (read values signal).reading := by
  induction arrival with
  | fromCursor old => exact old.reading_exact
  | fromInstrument old => exact old.signal_reading
  | received past signal => rfl
  | throughSignal role old ih => exact ih
  | throughComparison role old ih => exact ih

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.instrumentJourney
#print axioms RelationalPerimeter.Relativity.Production.InstrumentJourney.origin
#print axioms RelationalPerimeter.Relativity.Production.InstrumentJourney.relayCount
#print axioms RelationalPerimeter.Relativity.Production.InstrumentJourney.recorded_length
#print axioms RelationalPerimeter.Relativity.Production.InstrumentJourney.payload_from_origin
#print axioms RelationalPerimeter.Relativity.Production.InstrumentUnitJourney.reading_exact
#print axioms RelationalPerimeter.Relativity.Production.recurringJourney
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.origin
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.relayCount
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.recorded_length
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.payload_from_origin
#print axioms RelationalPerimeter.Relativity.Production.RecurringUnitJourney.reading_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.transportStep
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.transport
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.transport_origin
#print axioms RelationalPerimeter.Relativity.Production.RecurringJourney.transport_count
#print axioms RelationalPerimeter.Relativity.Production.RecurringUnitJourney.transportStep
#print axioms RelationalPerimeter.Relativity.Production.RecurringUnitJourney.transport
#print axioms RelationalPerimeter.Relativity.Production.InstrumentArrived.signal_reading
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrival.signal_reading
/- AXIOM_AUDIT_END -/
