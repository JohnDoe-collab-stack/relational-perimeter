import RelationalPerimeter.Relativity.Production.RecurringRelativeReadings
import RelationalPerimeter.Relativity.Production.ConstitutedEncounters
import RelationalPerimeter.Relativity.Production.RefinedRelativePaths

/-!
# Relative-path measurements resumed through actual encounters

The stored signal-only prefix is attached once. Thereafter relays, separate
deliveries and consumed encounters all extend the same coupling state. The
next measurement starts from the returned encounter successor, never from
the pre-encounter cursor. Its ratio uses the actual two arrivals; its raw
encounter response remains their difference, not a supplied relative value.
Subdivision schedules are received instrumental requests, not physical laws.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources

structure PairedPaths (source : RecurringCursor) where
  firstSignal : Ref source.kinds .signal
  secondSignal : Ref source.kinds .signal
  numerator : RecurringJourney source.formation firstSignal
  denominator : RecurringJourney source.formation secondSignal
  numeratorUnit : RecurringUnitJourney numerator
  denominatorUnit : RecurringUnitJourney denominator
  commonOrigin : numerator.origin = denominator.origin
  positiveScale : 0 < denominator.relayCount

def PairedPaths.ofReading {source} (reading : RecurringRelativeReading source) : PairedPaths source :=
  ⟨reading.arrivals.firstSignal, reading.arrivals.secondSignal, reading.numerator, reading.denominator,
    reading.numeratorUnit, reading.denominatorUnit, reading.commonOrigin, reading.positiveScale⟩

def PairedPaths.value {source} (paths : PairedPaths source) : Rational :=
  Rational.mul (Rational.sub (source.read paths.firstSignal).reading
    (source.read paths.numerator.origin).reading) (Rational.inverseNatSucc (paths.denominator.relayCount - 1))

theorem PairedPaths.count_ratio_exact {source} (paths : PairedPaths source) :
    paths.value = Rational.mul (Rational.ofNat paths.numerator.relayCount)
      (Rational.inverseNatSucc (paths.denominator.relayCount - 1)) := by
  unfold value
  dsimp only [RecurringCursor.read]
  rw [paths.numeratorUnit.reading_exact]
  unfold Rational.sub
  rw [Rational.add_comm _ (Rational.ofNat paths.numerator.relayCount), Rational.add_assoc,
    Rational.add_neg, Rational.add_zero]

structure RelativeState where
  coupling : State
  reading : PairedPaths coupling.cursor
  calibration : Ref coupling.cursor.kinds .calibration
  calibrationUnit : (coupling.cursor.read calibration).increment = Rational.one
  empty : coupling.phase = .empty

def RelativeState.attach (source : RelativePathState) : RelativeState :=
  ⟨Encounter.attach source.cursor source.calibration, .ofReading (.fromReading source.reading),
    source.calibration, source.calibrationUnit, rfl⟩

structure RelayRun (source : State) {signal : Ref source.cursor.kinds .signal}
    (startJourney : RecurringJourney source.cursor.formation signal) (count : Nat) where
  state : State
  history : History source state
  lastSignal : Ref state.cursor.kinds .signal
  calibration : Ref state.cursor.kinds .calibration
  calibrationUnit : (state.cursor.read calibration).increment = Rational.one
  journey : RecurringJourney state.cursor.formation lastSignal
  unitJourney : RecurringUnitJourney journey
  originExact : journey.origin = history.transport.references startJourney.origin
  countExact : journey.relayCount = startJourney.relayCount + count
  keepsEmpty : source.phase = .empty → state.phase = .empty

/-- Only the returned prefix supplies the next relay. -/
def runRelays (source : State) {signal : Ref source.cursor.kinds .signal}
    (journey : RecurringJourney source.cursor.formation signal) (unit : RecurringUnitJourney journey)
    (calibration : Ref source.cursor.kinds .calibration)
    (calibrationUnit : (source.cursor.read calibration).increment = Rational.one) :
    (count : Nat) → RelayRun source journey count
  | 0 => ⟨source, .root, signal, calibration, calibrationUnit, journey, unit, rfl,
      (Nat.add_zero _).symm, fun same => same⟩
  | count + 1 =>
    let prior := runRelays source journey unit calibration calibrationUnit count
    let head := performSignal prior.state (.relay prior.lastSignal prior.calibration)
    let history : History source head.next := .extend prior.history (.signal head)
    ⟨head.next, history, .here, .prior prior.calibration, prior.calibrationUnit,
      .relayed prior.calibration prior.journey, .relayed prior.unitJourney prior.calibrationUnit,
      congrArg Ref.prior prior.originExact,
      (congrArg (fun n => n + 1) prior.countExact).trans (Nat.add_assoc _ _ _), by
        intro empty
        change Phase.transport prior.state.phase _ = .empty
        rw [prior.keepsEmpty empty]
        rfl⟩

theorem relay_run_length (source : State) {signal : Ref source.cursor.kinds .signal}
    (journey : RecurringJourney source.cursor.formation signal) (unit : RecurringUnitJourney journey)
    (calibration : Ref source.cursor.kinds .calibration)
    (calibrationUnit : (source.cursor.read calibration).increment = Rational.one) (count : Nat) :
    StrongPerimetralTurning.History.length (runRelays source journey unit calibration calibrationUnit count).history =
      count := by
  induction count with
  | zero => rfl
  | succ n ih => exact congrArg (fun k => k + 1) ih

private theorem append_reference {source middle target : State} (one : History source middle)
    (two : History middle target) {kind} (ref : Ref source.cursor.kinds kind) :
    (History.transport (StrongPerimetralTurning.History.append one two)).references ref =
      two.transport.references (one.transport.references ref) := history_transport_append one two ref

structure Measurement (source : RelativeState) where
  ready : State
  deliveries : History source.coupling ready
  reading : RecurringRelativeReading ready.cursor
  admission : EncounterAdmission ready
  pairExact : admission.pair = reading.arrivals
  head : EncounterProduction ready admission
  numeratorExact : reading.numerator.relayCount = source.reading.numerator.relayCount
  denominatorExact : reading.denominator.relayCount = source.reading.denominator.relayCount
  originExact : reading.numerator.origin = deliveries.transport.references source.reading.numerator.origin
  firstSignalExact : reading.arrivals.firstSignal =
    deliveries.transport.references source.reading.firstSignal
  secondSignalExact : reading.arrivals.secondSignal =
    deliveries.transport.references source.reading.secondSignal

/-- Deliver the two respective stored endpoints. Port admission is derived
from those deliveries, not from old archived receptions or equality of values. -/
def measure (source : RelativeState) : Measurement source := by
  cases source with
  | mk coupling reading calibration unit empty =>
    cases coupling with
    | mk cursor phase formation =>
      cases phase with
      | left held => cases empty
      | right held => cases empty
      | ready pair => cases empty
      | empty =>
        let initial : State := ⟨cursor, .empty, formation⟩
        let first := performDelivery initial .left reading.firstSignal (.empty .left)
        let firstHistory : History initial first.next := .extend .root (.delivered first)
        let denominator := reading.denominator.transport firstHistory.resources
        let second := performDelivery first.next .right
          (firstHistory.transport.references reading.secondSignal) .right
        let suffix : History first.next second.next := .extend .root (.delivered second)
        let history : History initial second.next := StrongPerimetralTurning.History.append firstHistory suffix
        let pair := rightPair (Held.received first.head) second.head
        let numerator := reading.numerator.transport history.resources
        let denominator := denominator.transport suffix.resources
        have common : numerator.origin = denominator.origin :=
          (reading.numerator.transport_origin history.resources).trans
            ((congrArg history.transport.references reading.commonOrigin).trans
              ((append_reference firstHistory suffix _).trans
                ((congrArg suffix.transport.references
                  (reading.denominator.transport_origin firstHistory.resources).symm).trans
                    (RecurringJourney.transport_origin suffix.resources _).symm)))
        let result : RecurringRelativeReading second.next.cursor :=
          ⟨pair, numerator, denominator, reading.numeratorUnit.transport history.resources,
            (reading.denominatorUnit.transport firstHistory.resources).transport suffix.resources,
          common, (RecurringJourney.transport_count suffix.resources _).symm ▸
              (reading.denominator.transport_count firstHistory.resources).symm ▸ reading.positiveScale⟩
        let admitted : EncounterAdmission second.next := ⟨pair, rfl⟩
        let head := performEncounter second.next admitted
        exact ⟨second.next, history, result, admitted, rfl, head,
          reading.numerator.transport_count history.resources,
          (RecurringJourney.transport_count suffix.resources _).trans
            (reading.denominator.transport_count firstHistory.resources),
          reading.numerator.transport_origin history.resources, rfl, rfl⟩

def Measurement.history {source} (result : Measurement source) : History source.coupling result.head.next :=
  .extend result.deliveries (.encountered result.head)

def Measurement.next {source} (result : Measurement source) : RelativeState :=
  let suffix : History result.ready result.head.next := .extend .root (.encountered result.head)
  let calibration := result.deliveries.transport.references source.calibration
  ⟨result.head.next, .ofReading (result.reading.transport suffix.resources), suffix.transport.references calibration,
    (congrArg Calibration.increment (history_keeps_reads suffix calibration)).trans
      ((congrArg Calibration.increment (history_keeps_reads result.deliveries source.calibration)).trans
        source.calibrationUnit), rfl⟩

theorem measurement_keeps_ratio {source} (result : Measurement source) :
    result.next.reading.value = source.reading.value := by
  rw [PairedPaths.count_ratio_exact, source.reading.count_ratio_exact]
  change Rational.mul (Rational.ofNat (result.reading.numerator.transport _).relayCount)
    (Rational.inverseNatSucc ((result.reading.denominator.transport _).relayCount - 1)) = _
  rw [result.reading.numerator.transport_count, result.reading.denominator.transport_count,
    result.numeratorExact, result.denominatorExact]

theorem measurement_keeps_origin {source} (result : Measurement source) :
    result.next.reading.numerator.origin = result.history.transport.references source.reading.numerator.origin :=
  (result.reading.numerator.transport_origin _).trans
    (congrArg (History.transport (.extend .root (.encountered result.head))).references result.originExact)

theorem measurement_keeps_counts {source} (result : Measurement source) :
    result.next.reading.numerator.relayCount = source.reading.numerator.relayCount ∧
    result.next.reading.denominator.relayCount = source.reading.denominator.relayCount :=
  ⟨(result.reading.numerator.transport_count _).trans result.numeratorExact,
    (result.reading.denominator.transport_count _).trans result.denominatorExact⟩

theorem measurement_length (source : RelativeState) :
    StrongPerimetralTurning.History.length (measure source).history = 3 := by
  cases source with
  | mk coupling reading calibration unit empty =>
    cases coupling with
    | mk cursor phase formation =>
      cases phase with
      | empty => rfl
      | left held => cases empty
      | right held => cases empty
      | ready pair => cases empty

theorem measurement_first_effect {source} (result : Measurement source) :
    result.head.effects.1 = source.coupling.cursor.read source.reading.firstSignal := by
  rw [encounter_first_effect_exact, result.pairExact, result.firstSignalExact]
  exact history_keeps_reads result.deliveries _

theorem measurement_second_effect {source} (result : Measurement source) :
    result.head.effects.2 = source.coupling.cursor.read source.reading.secondSignal := by
  rw [encounter_second_effect_exact, result.pairExact, result.secondSignalExact]
  exact history_keeps_reads result.deliveries _

theorem measurement_raw_output {source} (result : Measurement source) :
    result.head.head.determination.1 =
      Rational.sub (source.coupling.cursor.read source.reading.secondSignal).reading
        (source.coupling.cursor.read source.reading.firstSignal).reading := by
  rw [encounter_output_exact, result.pairExact, RecurringPair.gap,
    result.reading.arrivals.firstArrival.measure_exact, result.reading.arrivals.secondArrival.measure_exact,
    result.reading.arrivals.firstArrival.signal_reading, result.reading.arrivals.secondArrival.signal_reading,
    result.firstSignalExact, result.secondSignalExact]
  have second : (result.ready.cursor.read
      (result.deliveries.transport.references source.reading.secondSignal)).reading =
      (source.coupling.cursor.read source.reading.secondSignal).reading :=
    congrArg SignalRecord.reading (history_keeps_reads result.deliveries source.reading.secondSignal)
  have first : (result.ready.cursor.read
      (result.deliveries.transport.references source.reading.firstSignal)).reading =
      (source.coupling.cursor.read source.reading.firstSignal).reading :=
    congrArg SignalRecord.reading (history_keeps_reads result.deliveries source.reading.firstSignal)
  exact (congrArg (fun value => Rational.sub value
      (result.ready.cursor.read (result.deliveries.transport.references source.reading.firstSignal)).reading)
        second).trans (congrArg (Rational.sub (source.coupling.cursor.read source.reading.secondSignal).reading) first)

structure Refinement (source : RelativeState) (choice : RelativeSubdivision) where
  prepared : RelativeState
  relays : History source.coupling prepared.coupling
  numeratorExact : prepared.reading.numerator.relayCount =
    source.reading.numerator.relayCount + (source.reading.numerator.relayCount + choice.extra)
  denominatorExact : prepared.reading.denominator.relayCount =
    source.reading.denominator.relayCount + source.reading.denominator.relayCount
  originExact : prepared.reading.numerator.origin = relays.transport.references source.reading.numerator.origin
  measurement : Measurement prepared

def Refinement.next {source choice} (result : Refinement source choice) : RelativeState := result.measurement.next

def Refinement.history {source choice} (result : Refinement source choice) :
    History source.coupling result.next.coupling :=
  StrongPerimetralTurning.History.append result.relays result.measurement.history

/-- Extend both cached journeys and then consume their separate deliveries.
The old arrived readings remain available, but cannot authorize the new contact. -/
def refine (source : RelativeState) (choice : RelativeSubdivision) : Refinement source choice := by
  let first := runRelays source.coupling source.reading.numerator source.reading.numeratorUnit
    source.calibration source.calibrationUnit (source.reading.numerator.relayCount + choice.extra)
  let denominator := source.reading.denominator.transport first.history.resources
  let second := runRelays first.state denominator
    (source.reading.denominatorUnit.transport first.history.resources) first.calibration first.calibrationUnit
    source.reading.denominator.relayCount
  let history : History source.coupling second.state :=
    StrongPerimetralTurning.History.append first.history second.history
  let numerator := first.journey.transport second.history.resources
  have common : numerator.origin = second.journey.origin :=
    (first.journey.transport_origin second.history.resources).trans
      ((congrArg second.history.transport.references first.originExact).trans
        ((congrArg second.history.transport.references
          ((congrArg first.history.transport.references source.reading.commonOrigin).trans
            (source.reading.denominator.transport_origin first.history.resources).symm)).trans
              second.originExact.symm))
  have numeratorCount : numerator.relayCount = source.reading.numerator.relayCount +
      (source.reading.numerator.relayCount + choice.extra) :=
    (first.journey.transport_count second.history.resources).trans first.countExact
  have denominatorCount : second.journey.relayCount = source.reading.denominator.relayCount +
      source.reading.denominator.relayCount :=
    second.countExact.trans (congrArg (fun n => n + source.reading.denominator.relayCount)
      (source.reading.denominator.transport_count first.history.resources))
  let newPaths : PairedPaths second.state.cursor :=
    ⟨second.history.transport.references first.lastSignal, second.lastSignal, numerator, second.journey,
      first.unitJourney.transport second.history.resources, second.unitJourney, common,
      denominatorCount.symm ▸ Nat.lt_of_lt_of_le source.reading.positiveScale (Nat.le_add_right ..)⟩
  let prepared : RelativeState :=
    ⟨second.state, newPaths, second.calibration, second.calibrationUnit,
      second.keepsEmpty (first.keepsEmpty source.empty)⟩
  let measurement := measure prepared
  exact ⟨prepared, history, numeratorCount, denominatorCount,
    (first.journey.transport_origin second.history.resources).trans
      ((congrArg second.history.transport.references first.originExact).trans
        (append_reference first.history second.history _).symm), measurement⟩

theorem refinement_keeps_origin {source choice} (result : Refinement source choice) :
    result.next.reading.numerator.origin = result.history.transport.references source.reading.numerator.origin :=
  (measurement_keeps_origin result.measurement).trans
    ((congrArg result.measurement.history.transport.references result.originExact).trans
      (append_reference result.relays result.measurement.history _).symm)

theorem refinement_counts {source choice} (result : Refinement source choice) :
    result.next.reading.numerator.relayCount =
      source.reading.numerator.relayCount + (source.reading.numerator.relayCount + choice.extra) ∧
    result.next.reading.denominator.relayCount =
      source.reading.denominator.relayCount + source.reading.denominator.relayCount :=
  ⟨(measurement_keeps_counts result.measurement).1.trans result.numeratorExact,
    (measurement_keeps_counts result.measurement).2.trans result.denominatorExact⟩

theorem refinement_length (source : RelativeState) (choice : RelativeSubdivision) :
    StrongPerimetralTurning.History.length (refine source choice).history =
      (source.reading.numerator.relayCount + choice.extra) + source.reading.denominator.relayCount + 3 := by
  refine (StrongPerimetralTurning.History.length_append
    (refine source choice).relays (refine source choice).measurement.history).trans ?_
  dsimp only [refine]
  rw [StrongPerimetralTurning.History.length_append,
    relay_run_length, relay_run_length, measurement_length]

inductive MeasurementChain : RelativeState → RelativeState → Type where
  | root (source) : MeasurementChain source source
  | step {source middle} (past : MeasurementChain source middle) (choice : RelativeSubdivision)
      (head : Refinement middle choice) (headExact : head = refine middle choice) :
      MeasurementChain source head.next

def MeasurementChain.history {source target} (chain : MeasurementChain source target) :
    History source.coupling target.coupling :=
  match chain with
  | .root _ => .root
  | .step past _ head _ => StrongPerimetralTurning.History.append past.history head.history
termination_by structural chain

def MeasurementChain.requests {source target} (chain : MeasurementChain source target) : List RelativeSubdivision :=
  match chain with
  | .root _ => []
  | .step past choice _ _ => past.requests ++ [choice]
termination_by structural chain

structure MeasurementRun (source : RelativeState) where
  state : RelativeState
  chain : MeasurementChain source state

def MeasurementRun.resume {source} (prior : MeasurementRun source) (choice : RelativeSubdivision) :
    MeasurementRun source :=
  let head := refine prior.state choice
  ⟨head.next, .step prior.chain choice head rfl⟩

def MeasurementRun.runMore {source} (prior : MeasurementRun source) : List RelativeSubdivision → MeasurementRun source
  | [] => prior
  | choice :: tail =>
    let next := prior.resume choice
    next.runMore tail

def runMeasurements (source : RelativeState) (requests : List RelativeSubdivision) : MeasurementRun source :=
  (⟨source, .root source⟩ : MeasurementRun source).runMore requests

theorem measurement_runs_append {source} (prior : MeasurementRun source) (first second : List RelativeSubdivision) :
    (prior.runMore first).runMore second = prior.runMore (first ++ second) := by
  induction first generalizing prior with
  | nil => rfl
  | cons choice tail ih => exact ih (prior.resume choice)

theorem measurement_requested_order {source} (prior : MeasurementRun source) (requests : List RelativeSubdivision) :
    (prior.runMore requests).chain.requests = prior.chain.requests ++ requests := by
  induction requests generalizing prior with
  | nil =>
    have empty (items : List RelativeSubdivision) : items ++ [] = items := by
      induction items with
      | nil => rfl
      | cons choice rest ih => exact congrArg (List.cons choice) ih
    exact (empty _).symm
  | cons choice tail ih =>
    have associative (first second third : List RelativeSubdivision) :
        (first ++ second) ++ third = first ++ (second ++ third) := by
      induction first with
      | nil => rfl
      | cons item rest ih => exact congrArg (List.cons item) ih
    exact (ih (prior.resume choice)).trans (associative _ [choice] tail)

theorem measurement_chain_origin {source target} (chain : MeasurementChain source target) :
    target.reading.numerator.origin = chain.history.transport.references source.reading.numerator.origin := by
  induction chain with
  | root => rfl
  | step past choice head exactHead ih =>
    exact (refinement_keeps_origin head).trans
      ((congrArg head.history.transport.references ih).trans
        (append_reference past.history head.history _).symm)

/-- Form the local head before the suffix is consumed. -/
def measureThen (source : RelativeState) (requests : List RelativeSubdivision) :
    (head : Measurement source) ×' MeasurementRun head.next :=
  let head := measure source
  let tail := runMeasurements head.next requests
  ⟨head, tail⟩

theorem measurement_head_independent (source : RelativeState) (one two : List RelativeSubdivision) :
    (measureThen source one).1 = (measureThen source two).1 := rfl

theorem measurement_suffix_from_produced_successor (source : RelativeState) (requests : List RelativeSubdivision) :
    (measureThen source requests).2 = runMeasurements (measure source).next requests := rfl

theorem measurement_chain_keeps_sources {source target} (chain : MeasurementChain source target)
    {kind} (one two : Ref source.coupling.cursor.kinds kind) (different : one ≠ two) :
    chain.history.transport.references one ≠ chain.history.transport.references two :=
  history_keeps_sources chain.history one two different

theorem measurement_chain_keeps_record {source target} (chain : MeasurementChain source target)
    (signal : Ref source.coupling.cursor.kinds .signal) :
    target.coupling.cursor.read (chain.history.transport.references signal) = source.coupling.cursor.read signal :=
  history_keeps_reads chain.history signal

end RelationalPerimeter.Relativity.Production.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Encounter.RelativeState.attach
#print axioms RelationalPerimeter.Relativity.Production.Encounter.PairedPaths.count_ratio_exact
#print axioms RelationalPerimeter.Relativity.Production.Encounter.runRelays
#print axioms RelationalPerimeter.Relativity.Production.Encounter.relay_run_length
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measure
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Measurement.next
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Measurement.history
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_keeps_ratio
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_keeps_origin
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_keeps_counts
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_length
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_first_effect
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_second_effect
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_raw_output
#print axioms RelationalPerimeter.Relativity.Production.Encounter.refine
#print axioms RelationalPerimeter.Relativity.Production.Encounter.refinement_keeps_origin
#print axioms RelationalPerimeter.Relativity.Production.Encounter.refinement_counts
#print axioms RelationalPerimeter.Relativity.Production.Encounter.refinement_length
#print axioms RelationalPerimeter.Relativity.Production.Encounter.MeasurementChain.history
#print axioms RelationalPerimeter.Relativity.Production.Encounter.MeasurementChain.requests
#print axioms RelationalPerimeter.Relativity.Production.Encounter.MeasurementRun.resume
#print axioms RelationalPerimeter.Relativity.Production.Encounter.MeasurementRun.runMore
#print axioms RelationalPerimeter.Relativity.Production.Encounter.runMeasurements
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_runs_append
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_requested_order
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_chain_origin
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measureThen
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_head_independent
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_suffix_from_produced_successor
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_chain_keeps_sources
#print axioms RelationalPerimeter.Relativity.Production.Encounter.measurement_chain_keeps_record
/- AXIOM_AUDIT_END -/
