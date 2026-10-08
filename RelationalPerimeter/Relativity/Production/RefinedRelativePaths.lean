import RelationalPerimeter.Relativity.Production.RealizedRelativePaths

/-!
# Productive refinement of already received relative paths

A local request chooses the lower or upper instrumental subdivision. Its
runner extends the two stored paths, then receives each new endpoint once.
It consumes their counts and calibration, not a supplied numerical target.
The old receptions, emitted origin and complete records are retained through
the actual suffix. Subdivision is declared input, not a discovered physical
law or a spacetime localization. No completed future is a head parameter.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive RelativeSubdivision where
  | lower | upper

def RelativeSubdivision.extra : RelativeSubdivision → Nat
  | .lower => 0
  | .upper => 1

theorem RelativeSubdivision.extra_le_one (choice : RelativeSubdivision) : choice.extra ≤ 1 := by
  cases choice
  · exact Nat.zero_le _
  · exact Nat.le_refl _

structure RelativePathState where
  cursor : Cursor
  reading : RelativePathReading cursor
  calibration : Ref cursor.kinds .calibration
  calibrationUnit : (cursor.read calibration).increment = Rational.one

def RelativePathState.fromExecution {source : Cursor} {numerator denominatorMinusOne : Nat}
    (result : RelativeReadingExecution source numerator denominatorMinusOne)
    (calibration : Ref source.kinds .calibration)
    (unit : (source.read calibration).increment = Rational.one) : RelativePathState :=
  ⟨result.cursor, result.reading, (historyTransport result.history).references calibration,
    (congrArg Calibration.increment (history_preserves_reads result.history calibration)).trans unit⟩

def RelativePathState.prolong {target : Cursor} (state : RelativePathState)
    (history : LocalHistory state.cursor target) : RelativePathState :=
  ⟨target, state.reading.transport history, (historyTransport history).references state.calibration,
    (congrArg Calibration.increment (history_preserves_reads history state.calibration)).trans
      state.calibrationUnit⟩

theorem local_history_append_reference {source middle target : Cursor}
    (first : LocalHistory source middle) (second : LocalHistory middle target)
    {kind} (ref : Ref source.kinds kind) :
    (historyTransport (StrongPerimetralTurning.History.append first second)).references ref =
      (historyTransport second).references ((historyTransport first).references ref) := by
  induction second with
  | root => rfl
  | extend past step ih => exact congrArg step.transport.references ih

structure RelativePathRefinement (source : RelativePathState) (choice : RelativeSubdivision) where
  state : RelativePathState
  history : LocalHistory source.cursor state.cursor
  numeratorExact : state.reading.numerator.relayCount =
    source.reading.numerator.relayCount + (source.reading.numerator.relayCount + choice.extra)
  denominatorExact : state.reading.denominator.relayCount =
    source.reading.denominator.relayCount + source.reading.denominator.relayCount
  originExact : state.reading.numerator.origin =
    (historyTransport history).references source.reading.numerator.origin

/-- Each loop and reception is evaluated once. The second loop starts from
the stored denominator transported through the actual first reception,
not from a newly emitted signal or the new numerator endpoint. -/
def refineRelativePaths (source : RelativePathState) (choice : RelativeSubdivision) :
    RelativePathRefinement source choice := by
  let first := runUnitRelays source.cursor source.reading.numerator source.reading.numeratorUnit
    source.calibration source.calibrationUnit (source.reading.numerator.relayCount + choice.extra)
  let firstReception := perform first.cursor (.receive first.lastSignal)
  let firstHistory : LocalHistory source.cursor firstReception.successor :=
    .extend first.history ⟨.reading, .receive first.lastSignal,
      firstReception.determination, firstReception.successorExact⟩
  let firstJourney : SignalJourney firstReception.successor.formation (.prior first.lastSignal) :=
    .inherited firstReception.determination.2 first.journey
  let firstUnit : UnitJourney firstJourney := .inherited firstReception.determination.2 first.unitJourney
  let denominator := source.reading.denominator.transport firstHistory
  let calibration := (historyTransport firstHistory).references source.calibration
  have unit : (firstReception.successor.read calibration).increment = Rational.one :=
    (congrArg Calibration.increment (history_preserves_reads firstHistory source.calibration)).trans
      source.calibrationUnit
  let second := runUnitRelays firstReception.successor denominator
    (source.reading.denominatorUnit.transport firstHistory) calibration unit
    source.reading.denominator.relayCount
  let secondReception := perform second.cursor (.receive second.lastSignal)
  let secondHistory : LocalHistory firstReception.successor secondReception.successor :=
    .extend second.history ⟨.reading, .receive second.lastSignal,
      secondReception.determination, secondReception.successorExact⟩
  let history := StrongPerimetralTurning.History.append firstHistory secondHistory
  let arrivals : ArrivalPair secondReception.successor :=
    ⟨(historyTransport secondHistory).references .here, .here,
      (historyTransport secondHistory).references (.prior first.lastSignal), .prior second.lastSignal,
      historyTransportArrival secondHistory (arrivalOfProduction firstReception),
      arrivalOfProduction secondReception, fun same =>
        fresh_position_distinct ((historyTransport second.history).references .here)
          (congrArg Ref.position same.symm)⟩
  let numeratorJourney := firstJourney.transport secondHistory
  let denominatorJourney : SignalJourney secondReception.successor.formation (.prior second.lastSignal) :=
    .inherited secondReception.determination.2 second.journey
  have firstOrigin : firstJourney.origin =
      (historyTransport firstHistory).references source.reading.numerator.origin :=
    congrArg Ref.prior first.originExact
  have originExact : numeratorJourney.origin = (historyTransport history).references
      source.reading.numerator.origin :=
    (firstJourney.transport_origin secondHistory).trans
      ((congrArg (historyTransport secondHistory).references firstOrigin).trans
        (local_history_append_reference firstHistory secondHistory _).symm)
  have common : numeratorJourney.origin = denominatorJourney.origin :=
    (firstJourney.transport_origin secondHistory).trans
      ((congrArg (historyTransport secondHistory).references firstOrigin).trans
        ((congrArg (historyTransport secondHistory).references
          ((congrArg (historyTransport firstHistory).references source.reading.commonOrigin).trans
            (source.reading.denominator.transport_origin firstHistory).symm)).trans
          (congrArg Ref.prior second.originExact).symm))
  have firstCount : numeratorJourney.relayCount = source.reading.numerator.relayCount +
      (source.reading.numerator.relayCount + choice.extra) :=
    (firstJourney.transport_count secondHistory).trans first.countExact
  have secondCount : denominatorJourney.relayCount = source.reading.denominator.relayCount +
      source.reading.denominator.relayCount :=
    second.countExact.trans (congrArg (fun n => n + source.reading.denominator.relayCount)
      (source.reading.denominator.transport_count firstHistory))
  let result : RelativePathReading secondReception.successor :=
    ⟨arrivals, numeratorJourney, denominatorJourney, firstUnit.transport secondHistory,
      .inherited secondReception.determination.2 second.unitJourney, common,
      secondCount.symm ▸ Nat.lt_of_lt_of_le source.reading.positiveScale (Nat.le_add_right ..)⟩
  exact ⟨⟨secondReception.successor, result, .prior second.calibration, second.calibrationUnit⟩,
    history, firstCount, secondCount, originExact⟩

def RelativePathRefinement.previous {source choice} (result : RelativePathRefinement source choice) :
    RelativePathReading result.state.cursor := source.reading.transport result.history

theorem relative_refinement_keeps_previous_value {source choice}
    (result : RelativePathRefinement source choice) : result.previous.value = source.reading.value :=
  source.reading.transport_value result.history

theorem relative_refinement_keeps_previous_sources {source choice}
    (result : RelativePathRefinement source choice) :
    result.previous.arrivals.first ≠ result.previous.arrivals.second := result.previous.arrivals.distinct

theorem relative_refinement_keeps_previous_record {source choice}
    (result : RelativePathRefinement source choice) :
    result.state.cursor.read result.previous.arrivals.secondSignal =
      source.cursor.read source.reading.arrivals.secondSignal :=
  history_preserves_reads result.history _

theorem relative_refinement_history_length (source : RelativePathState) (choice : RelativeSubdivision) :
    StrongPerimetralTurning.History.length (refineRelativePaths source choice).history =
      (source.reading.numerator.relayCount + choice.extra) + source.reading.denominator.relayCount + 2 := by
  dsimp only [refineRelativePaths]
  rw [StrongPerimetralTurning.History.length_append]
  change (_ + 1) + (_ + 1) = _
  rw [unit_relays_history_length, unit_relays_history_length]
  change (_ + 1) + (_ + 1) = _ + _ + (1 + 1)
  exact_natural

/-- The positive chain records the exact already returned head, rather than
reexecuting it to recover its history. Future inputs are not head fields. -/
inductive RelativeRefinementChain : RelativePathState → RelativePathState → Type where
  | root (source) : RelativeRefinementChain source source
  | step {source middle} (past : RelativeRefinementChain source middle)
      (choice : RelativeSubdivision) (head : RelativePathRefinement middle choice)
      (headExact : head = refineRelativePaths middle choice) : RelativeRefinementChain source head.state

def RelativeRefinementChain.history {source target} (chain : RelativeRefinementChain source target) :
    LocalHistory source.cursor target.cursor :=
  match chain with
  | .root _ => .root
  | .step past _ head _ => StrongPerimetralTurning.History.append past.history head.history
termination_by structural chain

def RelativeRefinementChain.requests {source target} (chain : RelativeRefinementChain source target) :
    List RelativeSubdivision :=
  match chain with
  | .root _ => []
  | .step past choice _ _ => past.requests ++ [choice]
termination_by structural chain

structure RelativeRefinementRun (source : RelativePathState) where
  state : RelativePathState
  chain : RelativeRefinementChain source state

/-- A stored prefix is consumed once; the local head reads only its returned
state and the current request. Requests contain no future cursor or target. -/
def RelativeRefinementRun.resume {source} (prior : RelativeRefinementRun source)
    (choice : RelativeSubdivision) : RelativeRefinementRun source :=
  let head := refineRelativePaths prior.state choice
  ⟨head.state, .step prior.chain choice head rfl⟩

/-- Execute requests in their declared order, with the accumulated prefix
passed into the next recursive call. No previous run is reconstructed. -/
def RelativeRefinementRun.runMore {source} (prior : RelativeRefinementRun source) :
    List RelativeSubdivision → RelativeRefinementRun source
  | [] => prior
  | choice :: tail =>
    let head := prior.resume choice
    head.runMore tail

def runRelativeRefinements (source : RelativePathState) (requests : List RelativeSubdivision) :
    RelativeRefinementRun source :=
  (⟨source, .root source⟩ : RelativeRefinementRun source).runMore requests

theorem relative_refinement_resume_is_shared {source} (prior : RelativeRefinementRun source)
    (choice : RelativeSubdivision) : (prior.resume choice).state = (refineRelativePaths prior.state choice).state := rfl

theorem relative_refinement_runs_append {source} (prior : RelativeRefinementRun source)
    (first second : List RelativeSubdivision) :
    (prior.runMore first).runMore second = prior.runMore (first ++ second) := by
  induction first generalizing prior with
  | nil => rfl
  | cons choice tail ih => exact ih (prior.resume choice)

private theorem subdivision_append_associative (first second third : List RelativeSubdivision) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons choice tail ih => exact congrArg (List.cons choice) ih

private theorem subdivision_append_empty (first : List RelativeSubdivision) : first ++ [] = first := by
  induction first with
  | nil => rfl
  | cons choice tail ih => exact congrArg (List.cons choice) ih

theorem relative_refinement_requested_order {source} (prior : RelativeRefinementRun source)
    (requests : List RelativeSubdivision) :
    (prior.runMore requests).chain.requests = prior.chain.requests ++ requests := by
  induction requests generalizing prior with
  | nil => exact (subdivision_append_empty _).symm
  | cons choice tail ih =>
    exact (ih (prior.resume choice)).trans (subdivision_append_associative _ [choice] tail)

theorem relative_refinement_chain_keeps_sources {source target}
    (chain : RelativeRefinementChain source target) :
    (historyTransport chain.history).references source.reading.arrivals.first ≠
      (historyTransport chain.history).references source.reading.arrivals.second :=
  history_preserves_distinction chain.history _ _ source.reading.arrivals.distinct

theorem relative_refinement_chain_keeps_reading {source target}
    (chain : RelativeRefinementChain source target) :
    (source.reading.transport chain.history).value = source.reading.value :=
  source.reading.transport_value chain.history

theorem relative_refinement_chain_origin {source target}
    (chain : RelativeRefinementChain source target) :
    target.reading.numerator.origin = (historyTransport chain.history).references source.reading.numerator.origin := by
  induction chain with
  | root => rfl
  | step past choice head exactHead ih =>
    exact head.originExact.trans ((congrArg (historyTransport head.history).references ih).trans
      (local_history_append_reference past.history head.history _).symm)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.RelativeSubdivision
#print axioms RelationalPerimeter.Relativity.Production.RelativeSubdivision.extra
#print axioms RelationalPerimeter.Relativity.Production.RelativeSubdivision.extra_le_one
#print axioms RelationalPerimeter.Relativity.Production.RelativePathState.fromExecution
#print axioms RelationalPerimeter.Relativity.Production.RelativePathState
#print axioms RelationalPerimeter.Relativity.Production.RelativePathState.prolong
#print axioms RelationalPerimeter.Relativity.Production.local_history_append_reference
#print axioms RelationalPerimeter.Relativity.Production.RelativePathRefinement
#print axioms RelationalPerimeter.Relativity.Production.refineRelativePaths
#print axioms RelationalPerimeter.Relativity.Production.RelativePathRefinement.previous
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_keeps_previous_value
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_keeps_previous_sources
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_keeps_previous_record
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_history_length
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementChain.history
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementChain
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRun
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementChain.requests
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRun.resume
#print axioms RelationalPerimeter.Relativity.Production.runRelativeRefinements
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRun.runMore
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_resume_is_shared
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_runs_append
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_requested_order
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_chain_keeps_sources
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_chain_keeps_reading
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_chain_origin
/- AXIOM_AUDIT_END -/
