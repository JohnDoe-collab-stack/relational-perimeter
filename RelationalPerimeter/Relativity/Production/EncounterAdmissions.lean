import RelationalPerimeter.Relativity.Production.InteractionAttachments

/-!
# Admission of a local two-port coupling

The additional primitive law is explicit: a routed reception occupies one
vacant port of a local instrument, persists through the declared signal
operations, and is consumed by one joint interaction. This is an ideal
local coupling model, not a derived propagation speed, metric or continuum.
The instrument is attached to an actual calibration occurrence in a received
constituted prefix. No geometrical position or common point is supplied.

Archived receptions are not occupied ports. Port occupancy is formed by the
delivery transition, and joint consumption empties both ports. The formation
below is mandatory; an independently assembled phase is not a state.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources

inductive Port where
  | left | right

structure Held (cursor : RecurringCursor) where
  reading : Ref cursor.kinds .reading
  signal : Ref cursor.kinds .signal
  arrival : RecurringArrival cursor.formation reading signal

def Held.transport {source target} (held : Held source)
    (history : RecurringHistory source target) : Held target :=
  ⟨(recurringHistoryTransport history).references held.reading,
    (recurringHistoryTransport history).references held.signal,
    recurringHistoryArrival history held.arrival⟩

def Held.received {source} {signal : Ref source.kinds .signal}
    (head : RecurringProduction source (.signal (.receive signal))) : Held head.successor :=
  ⟨head.successorExact.symm ▸ Ref.here, head.successorExact.symm ▸ Ref.prior signal,
    recurringArrivalOfProduction head⟩

inductive Phase (cursor : RecurringCursor) where
  | empty
  | left (held : Held cursor)
  | right (held : Held cursor)
  | ready (pair : RecurringPair cursor)

def Phase.transport {source target} (phase : Phase source)
    (history : RecurringHistory source target) : Phase target :=
  match phase with
  | .empty => .empty
  | .left held => .left (held.transport history)
  | .right held => .right (held.transport history)
  | .ready pair => .ready (pair.transport history)

inductive Vacant {cursor} : Phase cursor → Port → Type where
  | empty (port : Port) : Vacant .empty port
  | right {held} : Vacant (.left held) .right
  | left {held} : Vacant (.right held) .left

def decideVacant {cursor} (phase : Phase cursor) (port : Port) :
    PSum (Vacant phase port) (Vacant phase port → False) := by
  cases phase with
  | empty => exact .inl (.empty port)
  | left held => cases port with
    | left => exact .inr (fun impossible => nomatch impossible)
    | right => exact .inl .right
  | right held => cases port with
    | left => exact .inl .left
    | right => exact .inr (fun impossible => nomatch impossible)
  | ready pair => exact .inr (fun impossible => nomatch impossible)

def rightPair {source} (held : Held source) {signal : Ref source.kinds .signal}
    (head : RecurringProduction source (.signal (.receive signal))) : RecurringPair head.successor := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role =>
      cases role with
      | signal localRole =>
        cases localRole
        exact ⟨.prior held.reading, .here, .prior held.signal, .prior signal,
          .throughSignal (.received signal) held.arrival,
          .received source.formation signal,
          fun same => fresh_position_distinct held.reading (congrArg Ref.position same.symm)⟩

def leftPair {source} (held : Held source) {signal : Ref source.kinds .signal}
    (head : RecurringProduction source (.signal (.receive signal))) : RecurringPair head.successor := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role =>
      cases role with
      | signal localRole =>
        cases localRole
        exact ⟨.here, .prior held.reading, .prior signal, .prior held.signal,
          .received source.formation signal,
          .throughSignal (.received signal) held.arrival,
          fun same => fresh_position_distinct held.reading (congrArg Ref.position same)⟩

def deliveredPhase {source} {phase : Phase source} {port : Port}
    (vacant : Vacant phase port) {signal : Ref source.kinds .signal}
    (head : RecurringProduction source (.signal (.receive signal))) : Phase head.successor :=
  match vacant with
  | .empty .left => .left (Held.received head)
  | .empty .right => .right (Held.received head)
  | @Vacant.right _ held => .ready (rightPair held head)
  | @Vacant.left _ held => .ready (leftPair held head)

/-- Physical availability is a positive history of this declared coupling
law, not a claim inferred from the mere persistence of a signal reference. -/
inductive CouplingFormation : (cursor : RecurringCursor) → Phase cursor → Type where
  | attached (source : Cursor) (instrument : Ref source.kinds .calibration) :
      CouplingFormation (.fromCursor source) .empty
  | signal {source phase} (past : CouplingFormation source phase) {kind}
      {instruction : Instruction source.kinds kind}
      (head : RecurringProduction source (.signal instruction)) :
      CouplingFormation head.successor (phase.transport (recurringProductionHistory head))
  | delivered {source phase port} (past : CouplingFormation source phase)
      (vacant : Vacant phase port) {signal : Ref source.kinds .signal}
      (head : RecurringProduction source (.signal (.receive signal))) :
      CouplingFormation head.successor (deliveredPhase vacant head)
  | consumed {source} {pair : RecurringPair source}
      (past : CouplingFormation source (.ready pair))
      (head : RecurringProduction source (.compare pair)) :
      CouplingFormation head.successor .empty

def CouplingFormation.instrument {cursor phase} (formation : CouplingFormation cursor phase) :
    Ref cursor.kinds .calibration :=
  match formation with
  | .attached _ instrument => instrument
  | .signal past head => (recurringHistoryTransport (recurringProductionHistory head)).references past.instrument
  | .delivered past _ head => (recurringHistoryTransport (recurringProductionHistory head)).references past.instrument
  | .consumed past head => (recurringHistoryTransport (recurringProductionHistory head)).references past.instrument
termination_by structural formation

structure State where
  cursor : RecurringCursor
  phase : Phase cursor
  formation : CouplingFormation cursor phase

/-- Attach at the actual supplied prefix, without creating another resource
root, replaying its history or declaring its archived arrivals available. -/
def attach (source : Cursor) (instrument : Ref source.kinds .calibration) : State :=
  ⟨.fromCursor source, .empty, .attached source instrument⟩

def afterSignal (source : State) {kind} {instruction : Instruction source.cursor.kinds kind}
    (head : RecurringProduction source.cursor (.signal instruction)) : State :=
  ⟨head.successor, source.phase.transport (recurringProductionHistory head), .signal source.formation head⟩

def afterDelivery (source : State) {port} (vacant : Vacant source.phase port)
    {signal : Ref source.cursor.kinds .signal}
    (head : RecurringProduction source.cursor (.signal (.receive signal))) : State :=
  ⟨head.successor, deliveredPhase vacant head, .delivered source.formation vacant head⟩

structure EncounterAdmission (source : State) where
  pair : RecurringPair source.cursor
  ready : source.phase = .ready pair

def decideEncounter (source : State) :
    PSum (EncounterAdmission source) (EncounterAdmission source → False) :=
  match exactPhase : source.phase with
  | .ready pair => .inl ⟨pair, exactPhase⟩
  | .empty => .inr (fun admitted => by have same := exactPhase.symm.trans admitted.ready; cases same)
  | .left held => .inr (fun admitted => by have same := exactPhase.symm.trans admitted.ready; cases same)
  | .right held => .inr (fun admitted => by have same := exactPhase.symm.trans admitted.ready; cases same)

def encounterEnabled (source : State) : Bool :=
  match decideEncounter source with | .inl _ => true | .inr _ => false

theorem encounter_enabled (source : State) (admitted : EncounterAdmission source) :
    encounterEnabled source = true := by
  unfold encounterEnabled
  cases decideEncounter source with
  | inl witness => rfl
  | inr impossible => exact False.elim (impossible admitted)

theorem attach_refuses (source : Cursor) (instrument : Ref source.kinds .calibration) :
    encounterEnabled (attach source instrument) = false := rfl

def afterEncounter (source : State) (admitted : EncounterAdmission source)
    (head : RecurringProduction source.cursor (.compare admitted.pair)) : State :=
  ⟨head.successor, .empty, .consumed (admitted.ready ▸ source.formation) head⟩

theorem consumed_refuses (source : State) (admitted : EncounterAdmission source)
    (head : RecurringProduction source.cursor (.compare admitted.pair)) :
    encounterEnabled (afterEncounter source admitted head) = false := rfl

end RelationalPerimeter.Relativity.Production.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Held.transport
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Held.received
#print axioms RelationalPerimeter.Relativity.Production.Encounter.decideVacant
#print axioms RelationalPerimeter.Relativity.Production.Encounter.rightPair
#print axioms RelationalPerimeter.Relativity.Production.Encounter.leftPair
#print axioms RelationalPerimeter.Relativity.Production.Encounter.deliveredPhase
#print axioms RelationalPerimeter.Relativity.Production.Encounter.CouplingFormation
#print axioms RelationalPerimeter.Relativity.Production.Encounter.CouplingFormation.instrument
#print axioms RelationalPerimeter.Relativity.Production.Encounter.attach
#print axioms RelationalPerimeter.Relativity.Production.Encounter.afterSignal
#print axioms RelationalPerimeter.Relativity.Production.Encounter.afterDelivery
#print axioms RelationalPerimeter.Relativity.Production.Encounter.decideEncounter
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_enabled
#print axioms RelationalPerimeter.Relativity.Production.Encounter.attach_refuses
#print axioms RelationalPerimeter.Relativity.Production.Encounter.afterEncounter
#print axioms RelationalPerimeter.Relativity.Production.Encounter.consumed_refuses
/- AXIOM_AUDIT_END -/
