import RelationalPerimeter.Relativity.Production.EncounterPassages

/-!
# Constitutive assembly of finitely many local couplings

The declared assembly law gives each attachment its own pair of holding
ports. One admitted delivery or interaction changes only that attachment;
the other cells carry their actual arrivals through the same stored resource
production. A cell index selects an attachment, not a geometrical position.
Attachments may share a calibration. Their independence is this explicit
ideal assembly law, not a theorem inferred from distinct numerical readings.

All cells share the received constituted support. There is no new resource
root, supplied interaction target, distance or propagation-speed law.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production.Network
open ConstitutiveSearch.Resources
open Encounter

structure Cells (cursor : RecurringCursor) (count : Nat) where
  instrument : Fin count → Ref cursor.kinds .calibration
  phase : Fin count → Phase cursor

def Cells.initial (source : Cursor) {count}
    (instruments : Fin count → Ref source.kinds .calibration) : Cells (.fromCursor source) count :=
  ⟨instruments, fun _ => .empty⟩

def Cells.transport {source target count} (cells : Cells source count)
    (history : RecurringHistory source target) : Cells target count :=
  ⟨fun cell => (recurringHistoryTransport history).references (cells.instrument cell),
    fun cell => (cells.phase cell).transport history⟩

def Cells.deliver {source count} (cells : Cells source count) (cell : Fin count)
    {port} (vacant : Vacant (cells.phase cell) port) {signal : Ref source.kinds .signal}
    (head : RecurringProduction source (.signal (.receive signal))) : Cells head.successor count :=
  let carried := cells.transport (recurringProductionHistory head)
  ⟨carried.instrument, fun other =>
    if other = cell then deliveredPhase vacant head else carried.phase other⟩

def Cells.consume {source count} (cells : Cells source count) (cell : Fin count)
    {pair : RecurringPair source} (head : RecurringProduction source (.compare pair)) :
    Cells head.successor count :=
  let carried := cells.transport (recurringProductionHistory head)
  ⟨carried.instrument, fun other => if other = cell then .empty else carried.phase other⟩

inductive Formation {count : Nat} : (cursor : RecurringCursor) → Cells cursor count → Type where
  | attached (source : Cursor) (instruments : Fin count → Ref source.kinds .calibration) :
      Formation (.fromCursor source) (Cells.initial source instruments)
  | signal {source cells} (past : Formation source cells) {kind}
      {instruction : Instruction source.kinds kind}
      (head : RecurringProduction source (.signal instruction)) :
      Formation head.successor (cells.transport (recurringProductionHistory head))
  | delivered {source cells} (past : Formation source cells) (cell : Fin count)
      {port signal} (vacant : Vacant (cells.phase cell) port)
      (head : RecurringProduction source (.signal (.receive signal))) :
      Formation head.successor (cells.deliver cell vacant head)
  | consumed {source cells} (past : Formation source cells) (cell : Fin count)
      {pair : RecurringPair source} (ready : cells.phase cell = .ready pair)
      (head : RecurringProduction source (.compare pair)) :
      Formation head.successor (cells.consume cell head)

structure State (count : Nat) where
  cursor : RecurringCursor
  cells : Cells cursor count
  formation : Formation cursor cells

def attach (source : Cursor) {count} (instruments : Fin count → Ref source.kinds .calibration) : State count :=
  ⟨.fromCursor source, .initial source instruments, .attached source instruments⟩

structure Admission {count} (source : State count) (cell : Fin count) where
  pair : RecurringPair source.cursor
  ready : source.cells.phase cell = .ready pair

def decideEncounter {count} (source : State count) (cell : Fin count) :
    PSum (Admission source cell) (Admission source cell → False) :=
  match exactPhase : source.cells.phase cell with
  | .ready pair => .inl ⟨pair, exactPhase⟩
  | .empty => .inr (fun admitted => by have same := exactPhase.symm.trans admitted.ready; cases same)
  | .left held => .inr (fun admitted => by have same := exactPhase.symm.trans admitted.ready; cases same)
  | .right held => .inr (fun admitted => by have same := exactPhase.symm.trans admitted.ready; cases same)

def enabled {count} (source : State count) (cell : Fin count) : Bool :=
  match decideEncounter source cell with | .inl _ => true | .inr _ => false

theorem admission_enabled {count source cell} (admitted : @Admission count source cell) :
    enabled source cell = true := by
  unfold enabled
  cases decideEncounter source cell with
  | inl witness => rfl
  | inr impossible => exact False.elim (impossible admitted)

structure SignalProduction {count} (source : State count) {kind}
    (instruction : Instruction source.cursor.kinds kind) where
  head : RecurringProduction source.cursor (.signal instruction)

def SignalProduction.next {count source kind instruction}
    (production : @SignalProduction count source kind instruction) : State count :=
  ⟨production.head.successor, source.cells.transport (recurringProductionHistory production.head),
    .signal source.formation production.head⟩

def performSignal {count} (source : State count) {kind} (instruction : Instruction source.cursor.kinds kind) :
    SignalProduction source instruction := ⟨performRecurring source.cursor (.signal instruction)⟩

structure DeliveryProduction {count} (source : State count) (cell : Fin count) (port : Port)
    (signal : Ref source.cursor.kinds .signal) (vacant : Vacant (source.cells.phase cell) port) where
  head : RecurringProduction source.cursor (.signal (.receive signal))

def DeliveryProduction.next {count source cell port signal vacant}
    (production : @DeliveryProduction count source cell port signal vacant) : State count :=
  ⟨production.head.successor, source.cells.deliver cell vacant production.head,
    .delivered source.formation cell vacant production.head⟩

def performDelivery {count} (source : State count) (cell : Fin count) (port : Port)
    (signal : Ref source.cursor.kinds .signal) (vacant : Vacant (source.cells.phase cell) port) :
    DeliveryProduction source cell port signal vacant :=
  ⟨performRecurring source.cursor (.signal (.receive signal))⟩

structure EncounterProduction {count} (source : State count) (cell : Fin count) (admitted : Admission source cell) where
  head : RecurringProduction source.cursor (.compare admitted.pair)

def EncounterProduction.next {count source cell admitted}
    (production : @EncounterProduction count source cell admitted) : State count :=
  ⟨production.head.successor, source.cells.consume cell production.head,
    .consumed source.formation cell admitted.ready production.head⟩

def performEncounter {count} (source : State count) (cell : Fin count) (admitted : Admission source cell) :
    EncounterProduction source cell admitted := ⟨performRecurring source.cursor (.compare admitted.pair)⟩

theorem delivered_selected {count source cell port signal vacant}
    (production : @DeliveryProduction count source cell port signal vacant) :
    production.next.cells.phase cell = deliveredPhase vacant production.head := by
  change (if cell = cell then _ else _) = _
  exact if_pos rfl

theorem delivered_other {count source cell port signal vacant}
    (production : @DeliveryProduction count source cell port signal vacant)
    (other : Fin count) (different : other ≠ cell) :
    production.next.cells.phase other =
      (source.cells.phase other).transport (recurringProductionHistory production.head) := by
  change (if other = cell then _ else _) = _
  exact if_neg different

theorem consumed_selected {count source cell admitted}
    (production : @EncounterProduction count source cell admitted) : production.next.cells.phase cell = .empty := by
  change (if cell = cell then _ else _) = _
  exact if_pos rfl

theorem consumed_refuses {count source cell admitted}
    (production : @EncounterProduction count source cell admitted) : enabled production.next cell = false := by
  unfold enabled
  cases decideEncounter production.next cell with
  | inr refused => rfl
  | inl allowed =>
    have impossible := (consumed_selected production).symm.trans allowed.ready
    cases impossible

theorem consumed_other {count source cell admitted}
    (production : @EncounterProduction count source cell admitted)
    (other : Fin count) (different : other ≠ cell) :
    production.next.cells.phase other =
      (source.cells.phase other).transport (recurringProductionHistory production.head) := by
  change (if other = cell then _ else _) = _
  exact if_neg different

/-- The other admission is reconstructed from its own carried receptions;
the selected cell's consumption neither supplies nor consumes it. -/
def Admission.afterOtherEncounter {count source cell admitted}
    (production : @EncounterProduction count source cell admitted)
    {other : Fin count} (different : other ≠ cell) (available : Admission source other) :
    Admission production.next other :=
  ⟨available.pair.transport (recurringProductionHistory production.head),
    (consumed_other production other different).trans
      (congrArg (fun phase => phase.transport (recurringProductionHistory production.head)) available.ready)⟩

def Admission.afterOtherDelivery {count source cell port signal vacant}
    (production : @DeliveryProduction count source cell port signal vacant)
    {other : Fin count} (different : other ≠ cell) (available : Admission source other) :
    Admission production.next other :=
  ⟨available.pair.transport (recurringProductionHistory production.head),
    (delivered_other production other different).trans
      (congrArg (fun phase => phase.transport (recurringProductionHistory production.head)) available.ready)⟩

inductive Step {count} (source : State count) : State count → Type where
  | signal {kind instruction} (production : @SignalProduction count source kind instruction) : Step source production.next
  | delivered {cell port signal vacant} (production : @DeliveryProduction count source cell port signal vacant) :
      Step source production.next
  | encountered {cell admitted} (production : @EncounterProduction count source cell admitted) : Step source production.next

abbrev History {count} := StrongPerimetralTurning.History (@Step count)

def Step.resources {count source target} (step : @Step count source target) :
    RecurringHistory source.cursor target.cursor :=
  match step with
  | .signal production => recurringProductionHistory production.head
  | .delivered production => recurringProductionHistory production.head
  | .encountered production => recurringProductionHistory production.head

def History.resources {count source target} (history : @History count source target) :
    RecurringHistory source.cursor target.cursor :=
  match history with
  | .root => .root
  | .extend past step => StrongPerimetralTurning.History.append (History.resources past) step.resources
termination_by structural history

def History.transport {count source target} (history : @History count source target) :
    Support.Extension source.cursor.support target.cursor.support := recurringHistoryTransport history.resources

theorem network_history_keeps_reads {count source target} (history : @History count source target)
    {kind} (ref : Ref source.cursor.kinds kind) :
    target.cursor.read (history.transport.references ref) = source.cursor.read ref := history.transport.reads ref

theorem network_history_keeps_sources {count source target} (history : @History count source target)
    {kind} (one two : Ref source.cursor.kinds kind) (different : one ≠ two) :
    history.transport.references one ≠ history.transport.references two :=
  fun same => different (history.transport.injective one two same)

end RelationalPerimeter.Relativity.Production.Network
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Network.Formation
#print axioms RelationalPerimeter.Relativity.Production.Network.attach
#print axioms RelationalPerimeter.Relativity.Production.Network.decideEncounter
#print axioms RelationalPerimeter.Relativity.Production.Network.admission_enabled
#print axioms RelationalPerimeter.Relativity.Production.Network.performSignal
#print axioms RelationalPerimeter.Relativity.Production.Network.performDelivery
#print axioms RelationalPerimeter.Relativity.Production.Network.performEncounter
#print axioms RelationalPerimeter.Relativity.Production.Network.delivered_selected
#print axioms RelationalPerimeter.Relativity.Production.Network.delivered_other
#print axioms RelationalPerimeter.Relativity.Production.Network.consumed_selected
#print axioms RelationalPerimeter.Relativity.Production.Network.consumed_refuses
#print axioms RelationalPerimeter.Relativity.Production.Network.consumed_other
#print axioms RelationalPerimeter.Relativity.Production.Network.Admission.afterOtherEncounter
#print axioms RelationalPerimeter.Relativity.Production.Network.Admission.afterOtherDelivery
#print axioms RelationalPerimeter.Relativity.Production.Network.History.resources
#print axioms RelationalPerimeter.Relativity.Production.Network.network_history_keeps_reads
#print axioms RelationalPerimeter.Relativity.Production.Network.network_history_keeps_sources
/- AXIOM_AUDIT_END -/
