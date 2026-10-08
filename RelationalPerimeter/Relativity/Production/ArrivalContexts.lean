import RelationalPerimeter.Relativity.Production.SignalJourneys
import RelationalPerimeter.Relativity.Production.PortAdmissions

/-!
# Positive reception contexts, not merely available readings

An arrival is the reading occurrence of an actual reception, together with
the exact received signal occurrence in the same constituted history. The
resolver eliminates stored productions; it does not replay them. A supplied
initial reading is not an arrival, even when its value equals a received one.
Neither simultaneous availability nor numerical equality asserts a physical
meeting or identifies the sources.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive Arrived : {context : List Kind} → {values : Values Value context} →
    Formed (context := context) values → Ref context .reading → Ref context .signal → Type where
  | received {context} {values : Values Value context}
      (past : Formed (context := context) values) (signal : Ref context .signal) :
      Arrived (.produced past (.received signal)) .here (.prior signal)
  | inherited {context} {values : Values Value context} {past : Formed (context := context) values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output)
      {reading : Ref context .reading} {signal : Ref context .signal}
      (arrival : Arrived past reading signal) :
      Arrived (.produced past role) (.prior reading) (.prior signal)

def Arrived.usedEdge {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) :
    Used formation ⟨.signal, signal⟩ ⟨.reading, reading⟩ := by
  cases arrival with
  | received past signal => exact .produced past (.received signal) signal (.receptionSignal signal)
  | inherited role prior => exact .inherited role prior.usedEdge
termination_by structural arrival

/-- Reading this witness follows its constituted reception. It does not
accept an independently supplied numerical target. -/
def Arrived.measure {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) : Rational := by
  cases arrival with
  | @received context values _ signal => exact SignalRecord.reading (read values signal)
  | inherited _ prior => exact prior.measure
termination_by structural arrival

theorem Arrived.measure_exact {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) : arrival.measure = read values reading := by
  induction arrival with
  | received past signal => rfl
  | inherited role prior ih => exact ih

theorem Arrived.reading_exact {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) :
    read values reading = (read values signal).reading := by
  induction arrival with
  | received past signal => rfl
  | inherited role prior ih => exact ih

def receptionSource {context} {values : Values Value context}
    (formation : Formed (context := context) values) (reading : Ref context .reading) :
    Option (Ref context .signal) := by
  cases formation with
  | received _ => exact none
  | produced past role =>
    cases reading with
    | here => cases role with | received signal => exact some (.prior signal)
    | prior old => exact (receptionSource past old).map Ref.prior
termination_by structural formation

theorem Arrived.source_exact {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) : receptionSource formation reading = some signal := by
  induction arrival with
  | received past signal => rfl
  | inherited role prior ih =>
    change (receptionSource _ _).map Ref.prior = _
    rw [ih]; rfl

theorem Arrived.signal_unique {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) :
    ∀ {other : Ref context .signal}, Arrived formation reading other → signal = other := by
  intro other second
  exact Option.some.inj (arrival.source_exact.symm.trans second.source_exact)

def Arrived.journey {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (_arrival : Arrived formation reading signal) : SignalJourney formation signal :=
  signalJourney formation signal

def arrivalOfProduction {source : Cursor} {signal : Ref source.kinds .signal}
    (head : Production source (.receive signal)) :
    Arrived head.successor.formation
      (head.successorExact.symm ▸ (Ref.here : Ref (source.extend head.determination).kinds .reading))
      (head.successorExact.symm ▸ (Ref.prior signal : Ref (source.extend head.determination).kinds .signal)) := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role => cases role; exact .received source.formation signal

def Step.transportArrival {source target : Cursor} (step : Step source target)
    {reading : Ref source.kinds .reading} {signal : Ref source.kinds .signal}
    (arrival : Arrived source.formation reading signal) :
    Arrived target.formation (step.transport.references reading) (step.transport.references signal) := by
  cases step with
  | mk kind instruction determination exactTarget =>
    cases exactTarget
    exact .inherited determination.2 arrival

def historyTransportArrival {source target : Cursor} (history : LocalHistory source target)
    {reading : Ref source.kinds .reading} {signal : Ref source.kinds .signal}
    (arrival : Arrived source.formation reading signal) :
    Arrived target.formation ((historyTransport history).references reading)
      ((historyTransport history).references signal) :=
  match history with
  | .root => arrival
  | .extend past step => step.transportArrival (historyTransportArrival past arrival)
termination_by structural history

theorem Step.preserves_no_reception {source target : Cursor} (step : Step source target)
    (reading : Ref source.kinds .reading) (absent : receptionSource source.formation reading = none) :
    receptionSource target.formation (step.transport.references reading) = none := by
  cases step with
  | mk kind instruction determination exactTarget =>
    cases exactTarget
    change (receptionSource source.formation reading).map Ref.prior = none
    rw [absent]; rfl

theorem history_preserves_no_reception {source target : Cursor} (history : LocalHistory source target)
    (reading : Ref source.kinds .reading) (absent : receptionSource source.formation reading = none) :
    receptionSource target.formation ((historyTransport history).references reading) = none := by
  induction history with
  | root => exact absent
  | extend past step ih => exact step.preserves_no_reception _ ih

theorem historyTransport_append_reference {source middle target : Cursor}
    (one : LocalHistory source middle) (two : LocalHistory middle target)
    {kind} (ref : Ref source.kinds kind) :
    (historyTransport (StrongPerimetralTurning.History.append one two)).references ref =
      (historyTransport two).references ((historyTransport one).references ref) := by
  induction two with
  | root => rfl
  | extend past step ih => exact congrArg (fun old => step.transport.references old) ih

abbrev ArrivalSource {context} {values : Values Value context}
    (formation : Formed (context := context) values) (reading : Ref context .reading) :=
  (signal : Ref context .signal) ×' Arrived formation reading signal

def findArrival {context} {values : Values Value context}
    (formation : Formed (context := context) values) (reading : Ref context .reading) :
    Option (ArrivalSource formation reading) := by
  cases formation with
  | received _ => exact none
  | produced past role =>
    cases reading with
    | here =>
      cases role with
      | received signal => exact some ⟨.prior signal, .received past signal⟩
    | prior old =>
      exact (findArrival past old).map (fun source => ⟨.prior source.1, .inherited role source.2⟩)
termination_by structural formation

theorem Arrived.find_present {context} {values : Values Value context}
    {formation : Formed (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : Arrived formation reading signal) :
    ∃ source, findArrival formation reading = some source := by
  induction arrival with
  | received past signal => exact ⟨⟨.prior signal, .received past signal⟩, rfl⟩
  | inherited role prior ih =>
    obtain ⟨source, exactSource⟩ := ih
    refine ⟨⟨.prior source.1, .inherited role source.2⟩, ?_⟩
    change (findArrival _ _).map _ = _
    rw [exactSource]; rfl

def resolveArrival {context} {values : Values Value context}
    (formation : Formed (context := context) values) (reading : Ref context .reading) :
    PSum (ArrivalSource formation reading) (ArrivalSource formation reading → False) :=
  match found : findArrival formation reading with
  | some source => .inl source
  | none => .inr (fun source => by
      obtain ⟨located, exactLocated⟩ := source.2.find_present
      rw [found] at exactLocated
      cases exactLocated)

structure ArrivalAt (source : Cursor) (address : Nat) where
  reading : ReferenceAt source.kinds .reading address
  signal : Ref source.kinds .signal
  arrival : Arrived source.formation reading.ref signal

def resolveArrivalAt (source : Cursor) (address : Nat) :
    PSum (ArrivalAt source address) (ArrivalAt source address → False) :=
  match resolve source.kinds .reading address with
  | .inr impossible => .inr (fun arrival => impossible arrival.reading)
  | .inl reading =>
    match resolveArrival source.formation reading.ref with
    | .inl found => .inl ⟨reading, found.1, found.2⟩
    | .inr impossible => .inr (fun arrival => by
        have same := reference_position_injective reading.ref arrival.reading.ref
          (reading.exactPosition.trans arrival.reading.exactPosition.symm)
        exact impossible ⟨arrival.signal, same.symm ▸ arrival.arrival⟩)

def arrivalEnabled (source : Cursor) (address : Nat) : Bool :=
  match resolveArrivalAt source address with | .inl _ => true | .inr _ => false

theorem given_reading_not_arrived (input : Received)
    {reading : Ref receivedKinds .reading} {signal : Ref receivedKinds .signal}
    (arrival : Arrived (.received input) reading signal) : False := by
  have impossible := arrival.source_exact
  change none = some signal at impossible
  cases impossible

theorem transported_given_reading_not_arrived (input : Received) {target : Cursor}
    (history : LocalHistory (.received input) target) (reading : Ref receivedKinds .reading)
    {signal : Ref target.kinds .signal}
    (arrival : Arrived target.formation ((historyTransport history).references reading) signal) : False := by
  have absent := history_preserves_no_reception history reading rfl
  have impossible := absent.symm.trans arrival.source_exact
  cases impossible

theorem received_root_refuses_arrivals (input : Received) (address : Nat) :
    arrivalEnabled (.received input) address = false := by
  cases selected : resolveArrivalAt (.received input) address with
  | inl found => exact False.elim (given_reading_not_arrived input found.arrival)
  | inr impossible => unfold arrivalEnabled; rw [selected]

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Arrived
#print axioms RelationalPerimeter.Relativity.Production.Arrived.usedEdge
#print axioms RelationalPerimeter.Relativity.Production.Arrived.measure
#print axioms RelationalPerimeter.Relativity.Production.Arrived.measure_exact
#print axioms RelationalPerimeter.Relativity.Production.Arrived.reading_exact
#print axioms RelationalPerimeter.Relativity.Production.receptionSource
#print axioms RelationalPerimeter.Relativity.Production.Arrived.source_exact
#print axioms RelationalPerimeter.Relativity.Production.Arrived.signal_unique
#print axioms RelationalPerimeter.Relativity.Production.Arrived.journey
#print axioms RelationalPerimeter.Relativity.Production.arrivalOfProduction
#print axioms RelationalPerimeter.Relativity.Production.Step.transportArrival
#print axioms RelationalPerimeter.Relativity.Production.historyTransportArrival
#print axioms RelationalPerimeter.Relativity.Production.Step.preserves_no_reception
#print axioms RelationalPerimeter.Relativity.Production.history_preserves_no_reception
#print axioms RelationalPerimeter.Relativity.Production.historyTransport_append_reference
#print axioms RelationalPerimeter.Relativity.Production.findArrival
#print axioms RelationalPerimeter.Relativity.Production.Arrived.find_present
#print axioms RelationalPerimeter.Relativity.Production.resolveArrival
#print axioms RelationalPerimeter.Relativity.Production.resolveArrivalAt
#print axioms RelationalPerimeter.Relativity.Production.arrivalEnabled
#print axioms RelationalPerimeter.Relativity.Production.given_reading_not_arrived
#print axioms RelationalPerimeter.Relativity.Production.transported_given_reading_not_arrived
#print axioms RelationalPerimeter.Relativity.Production.received_root_refuses_arrivals
/- AXIOM_AUDIT_END -/
