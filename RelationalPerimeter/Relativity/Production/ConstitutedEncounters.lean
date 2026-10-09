import RelationalPerimeter.Relativity.Production.EncounterAdmissions

/-!
# Shared production of an admitted local coupling

The numerical response uses the existing calibrated comparison operation.
What is new is its physical admission in the declared two-port model:
positive delivered occupancy is required and consumed. A bare archived
comparison is not a coupling. No completed suffix enters these producers.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources

structure SignalProduction (source : State) {kind} (instruction : Instruction source.cursor.kinds kind) where
  head : RecurringProduction source.cursor (.signal instruction)

def SignalProduction.next {source kind} {instruction : Instruction source.cursor.kinds kind}
    (production : SignalProduction source instruction) : State := afterSignal source production.head

def performSignal (source : State) {kind} (instruction : Instruction source.cursor.kinds kind) :
    SignalProduction source instruction := ⟨performRecurring source.cursor (.signal instruction)⟩

structure DeliveryProduction (source : State) (port : Port)
    (signal : Ref source.cursor.kinds .signal) (vacant : Vacant source.phase port) where
  head : RecurringProduction source.cursor (.signal (.receive signal))

def DeliveryProduction.next {source port signal vacant}
    (production : DeliveryProduction source port signal vacant) : State :=
  afterDelivery source vacant production.head

def performDelivery (source : State) (port : Port) (signal : Ref source.cursor.kinds .signal)
    (vacant : Vacant source.phase port) : DeliveryProduction source port signal vacant :=
  ⟨performRecurring source.cursor (.signal (.receive signal))⟩

structure EncounterProduction (source : State) (admitted : EncounterAdmission source) where
  head : RecurringProduction source.cursor (.compare admitted.pair)

def EncounterProduction.next {source admitted} (production : EncounterProduction source admitted) : State :=
  afterEncounter source admitted production.head

def performEncounter (source : State) (admitted : EncounterAdmission source) :
    EncounterProduction source admitted :=
  ⟨performRecurring source.cursor (.compare admitted.pair)⟩

def EncounterProduction.first {source admitted} (production : EncounterProduction source admitted) :=
  InteractionAttachment.first production.head DescriptionPath.root

def EncounterProduction.second {source admitted} (production : EncounterProduction source admitted) :=
  InteractionAttachment.second production.head DescriptionPath.root

/-- Exact pair of packets consumed by this produced contact, not equalized
signals and not a freely supplied response. -/
def EncounterProduction.effects {source admitted} (production : EncounterProduction source admitted) :
    SignalRecord × SignalRecord := (production.first.effects, production.second.effects)

theorem encounter_output_exact {source admitted} (production : EncounterProduction source admitted) :
    production.head.determination.1 = admitted.pair.gap := comparison_output_uses_arrivals production.head

theorem encounter_sources_distinct {source admitted} (production : EncounterProduction source admitted) :
    production.first.readingReference ≠ production.second.readingReference :=
  participants_remain_distinct production.head .root

theorem encounter_first_effect_exact {source admitted} (production : EncounterProduction source admitted) :
    production.effects.1 = source.cursor.read admitted.pair.firstSignal := attached_effects_exact production.first

theorem encounter_second_effect_exact {source admitted} (production : EncounterProduction source admitted) :
    production.effects.2 = source.cursor.read admitted.pair.secondSignal := attached_effects_exact production.second

theorem encounter_consumes_occupancy {source admitted} (production : EncounterProduction source admitted) :
    production.next.phase = .empty ∧ encounterEnabled production.next = false := ⟨rfl, rfl⟩

inductive Step (source : State) : State → Type where
  | signal {kind} {instruction : Instruction source.cursor.kinds kind}
      (production : SignalProduction source instruction) : Step source production.next
  | delivered {port signal vacant} (production : DeliveryProduction source port signal vacant) :
      Step source production.next
  | encountered {admitted} (production : EncounterProduction source admitted) : Step source production.next

abbrev History := StrongPerimetralTurning.History Step

def Step.resources {source target} (step : Step source target) :
    RecurringHistory source.cursor target.cursor :=
  match step with
  | .signal production => recurringProductionHistory production.head
  | .delivered production => recurringProductionHistory production.head
  | .encountered production => recurringProductionHistory production.head

def History.resources {source target} (history : History source target) :
    RecurringHistory source.cursor target.cursor :=
  match history with
  | .root => .root
  | .extend past step => StrongPerimetralTurning.History.append (History.resources past) step.resources
termination_by structural history

def History.transport {source target} (history : History source target) :
    Support.Extension source.cursor.support target.cursor.support := recurringHistoryTransport history.resources

theorem history_keeps_reads {source target} (history : History source target)
    {kind} (ref : Ref source.cursor.kinds kind) :
    target.cursor.read (history.transport.references ref) = source.cursor.read ref := history.transport.reads ref

theorem history_keeps_sources {source target} (history : History source target)
    {kind} (one two : Ref source.cursor.kinds kind) (different : one ≠ two) :
    history.transport.references one ≠ history.transport.references two :=
  fun same => different (history.transport.injective one two same)

def History.describe {origin source target} (path : DescriptionPath origin source.cursor)
    (history : History source target) : DescriptionPath origin target.cursor := path.prolong history.resources

theorem history_description_exact {origin source target} (path : DescriptionPath origin source.cursor)
    (history : History source target) {kind} (ref : Ref origin.kinds kind) :
    (history.describe path).reference ref = history.transport.references (path.reference ref) :=
  DescriptionPath.prolong_reference path history.resources ref

theorem history_resources_append {source middle target} (one : History source middle)
    (two : History middle target) :
    History.resources (StrongPerimetralTurning.History.append one two) =
      StrongPerimetralTurning.History.append one.resources two.resources := by
  induction two with
  | root => rfl
  | extend past step ih =>
    change StrongPerimetralTurning.History.append
      (History.resources (StrongPerimetralTurning.History.append one past)) step.resources = _
    rw [ih]
    exact StrongPerimetralTurning.History.append_associative one.resources (History.resources past) step.resources

private theorem recurring_append_reference {source middle target} (one : RecurringHistory source middle)
    (two : RecurringHistory middle target) {kind} (ref : Ref source.kinds kind) :
    (recurringHistoryTransport (StrongPerimetralTurning.History.append one two)).references ref =
      (recurringHistoryTransport two).references ((recurringHistoryTransport one).references ref) := by
  induction two with
  | root => rfl
  | extend past step ih => exact congrArg step.transport.references ih

theorem history_transport_append {source middle target} (one : History source middle) (two : History middle target)
    {kind} (ref : Ref source.cursor.kinds kind) :
    (History.transport (StrongPerimetralTurning.History.append one two)).references ref =
      two.transport.references (one.transport.references ref) := by
  change (recurringHistoryTransport (History.resources (StrongPerimetralTurning.History.append one two))).references ref = _
  rw [history_resources_append]
  exact recurring_append_reference one.resources two.resources ref

end RelationalPerimeter.Relativity.Production.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Encounter.performSignal
#print axioms RelationalPerimeter.Relativity.Production.Encounter.performDelivery
#print axioms RelationalPerimeter.Relativity.Production.Encounter.performEncounter
#print axioms RelationalPerimeter.Relativity.Production.Encounter.EncounterProduction.next
#print axioms RelationalPerimeter.Relativity.Production.Encounter.EncounterProduction.effects
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_output_exact
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_sources_distinct
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_first_effect_exact
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_second_effect_exact
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_consumes_occupancy
#print axioms RelationalPerimeter.Relativity.Production.Encounter.History.resources
#print axioms RelationalPerimeter.Relativity.Production.Encounter.History.transport
#print axioms RelationalPerimeter.Relativity.Production.Encounter.history_keeps_reads
#print axioms RelationalPerimeter.Relativity.Production.Encounter.history_keeps_sources
#print axioms RelationalPerimeter.Relativity.Production.Encounter.history_description_exact
#print axioms RelationalPerimeter.Relativity.Production.Encounter.history_resources_append
#print axioms RelationalPerimeter.Relativity.Production.Encounter.history_transport_append
/- AXIOM_AUDIT_END -/
