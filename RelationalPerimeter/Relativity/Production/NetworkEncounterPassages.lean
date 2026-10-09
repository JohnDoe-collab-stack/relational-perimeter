import RelationalPerimeter.Relativity.Production.CouplingNetworks

/-!
# A shared used passage between two coupling attachments

The destination must actually have two vacant ports. The source encounter
output feeds an emission, two new deliveries, then an admitted destination
interaction. Its four productions are recorded once, before their histories
and used paths are assembled. This is a passage in the declared finite
assembly, not a speed, distance or a rule identifying its endpoints.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production.Network
open ConstitutiveSearch.Resources
open Encounter (Port Phase Vacant Held rightPair deliveredPhase)

def emptyVacancy {cursor} {phase : Phase cursor} (empty : phase = .empty) (port : Port) : Vacant phase port :=
  empty.symm ▸ .empty port

theorem empty_delivery_phase {cursor} {phase : Phase cursor} (empty : phase = .empty)
    {signal : Ref cursor.kinds .signal} (head : RecurringProduction cursor (.signal (.receive signal))) :
    deliveredPhase (emptyVacancy empty .left) head = .left (Held.received head) := by
  cases empty
  rfl

def rightVacancy {cursor} {phase : Phase cursor} {held : Held cursor}
    (left : phase = .left held) : Vacant phase .right := left.symm ▸ .right

theorem second_delivery_phase {cursor} {phase : Phase cursor} {held : Held cursor}
    (left : phase = .left held) {signal : Ref cursor.kinds .signal}
    (head : RecurringProduction cursor (.signal (.receive signal))) :
    deliveredPhase (rightVacancy left) head = .ready (rightPair held head) := by
  cases left
  rfl

theorem right_pair_first_is_carried {cursor} (held : Held cursor)
    {signal : Ref cursor.kinds .signal} (head : RecurringProduction cursor (.signal (.receive signal))) :
    (rightPair held head).first =
      (recurringHistoryTransport (recurringProductionHistory head)).references held.reading := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role => cases role with | signal localRole => cases localRole; rfl

def freshSignal {count source instruction} (head : @SignalProduction count source .signal instruction) :
    Ref head.next.cursor.kinds .signal := by
  change Ref head.head.successor.kinds .signal
  exact head.head.successorExact.symm ▸ .here

theorem emission_record_exact {count source reading payload}
    (production : @SignalProduction count source .signal (.emit reading payload)) :
    production.next.cursor.read (freshSignal production) =
      SignalRecord.emit (source.cursor.read reading) (source.cursor.read payload) := by
  cases production with
  | mk head => cases head with
    | mk determination successor exactSuccessor =>
      cases exactSuccessor
      cases determination with
      | mk output role => cases role with | signal localRole => cases localRole; rfl

theorem right_pair_signal_is_carried {cursor} (held : Held cursor)
    {signal : Ref cursor.kinds .signal} (head : RecurringProduction cursor (.signal (.receive signal))) :
    (rightPair held head).firstSignal =
      (recurringHistoryTransport (recurringProductionHistory head)).references held.signal := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
      | mk output role => cases role with | signal localRole => cases localRole; rfl

theorem held_received_signal_is_carried {cursor signal}
    (head : RecurringProduction cursor (.signal (.receive signal))) :
    (Held.received head).signal =
      (recurringHistoryTransport (recurringProductionHistory head)).references signal := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role => cases role with | signal localRole => cases localRole; rfl

def carriedSignal {count source cell port signal vacant}
    (head : @DeliveryProduction count source cell port signal vacant)
    (old : Ref source.cursor.kinds .signal) : Ref head.next.cursor.kinds .signal :=
  by
    change Ref head.head.successor.kinds .signal
    exact head.head.successorExact.symm ▸ .prior old

structure FillProduction {count} (source : State count) (cell : Fin count)
    (signal : Ref source.cursor.kinds .signal) (empty : source.cells.phase cell = .empty) where
  first : DeliveryProduction source cell .left signal (emptyVacancy empty .left)
  firstPhase : first.next.cells.phase cell = .left (Held.received first.head)
  second : DeliveryProduction first.next cell .right (carriedSignal first signal) (rightVacancy firstPhase)

def FillProduction.admitted {count source cell signal empty}
    (fill : @FillProduction count source cell signal empty) : Admission fill.second.next cell :=
  ⟨rightPair (Held.received fill.first.head) fill.second.head,
    (delivered_selected fill.second).trans (second_delivery_phase fill.firstPhase fill.second.head)⟩

def performFill {count} (source : State count) (cell : Fin count)
    (signal : Ref source.cursor.kinds .signal) (empty : source.cells.phase cell = .empty) :
    FillProduction source cell signal empty :=
  let first := performDelivery source cell .left signal (emptyVacancy empty .left)
  let left := (delivered_selected first).trans (empty_delivery_phase empty first.head)
  let secondVacant := rightVacancy left
  let second := performDelivery first.next cell .right (carriedSignal first signal) secondVacant
  ⟨first, left, second⟩

def FillProduction.history {count source cell signal empty}
    (fill : @FillProduction count source cell signal empty) : History source fill.second.next :=
  .extend (.extend .root (.delivered fill.first)) (.delivered fill.second)

structure PassageHeads {count source cell admitted}
    (origin : @EncounterProduction count source cell admitted) (destination : Fin count)
    (payload : Ref origin.next.cursor.kinds .payload)
    (empty : origin.next.cells.phase destination = .empty) where
  emitted : SignalProduction origin.next (.emit (comparisonAnchor origin.head) payload)
  vacant : emitted.next.cells.phase destination = .empty
  filled : FillProduction emitted.next destination (freshSignal emitted) vacant
  produced : EncounterProduction filled.second.next destination filled.admitted

def producePassageHeads {count source cell admitted}
    (origin : @EncounterProduction count source cell admitted) (destination : Fin count)
    (payload : Ref origin.next.cursor.kinds .payload)
    (empty : origin.next.cells.phase destination = .empty) : PassageHeads origin destination payload empty :=
  let emitted := performSignal origin.next (.emit (comparisonAnchor origin.head) payload)
  let vacant := congrArg (fun phase => phase.transport (recurringProductionHistory emitted.head)) empty
  let filled := performFill emitted.next destination (freshSignal emitted) vacant
  let produced := performEncounter filled.second.next destination filled.admitted
  ⟨emitted, vacant, filled, produced⟩

def PassageHeads.history {count source cell admitted origin destination payload empty}
    (heads : @PassageHeads count source cell admitted origin destination payload empty) :
    History origin.next heads.produced.next :=
  .extend (.extend (.extend (.extend .root (.signal heads.emitted))
    (.delivered heads.filled.first)) (.delivered heads.filled.second)) (.encountered heads.produced)

def PassageHeads.used {count source cell admitted origin destination payload empty}
    (heads : @PassageHeads count source cell admitted origin destination payload empty) :
    RecurringUsedPath heads.produced.next.cursor.formation
      ⟨.reading, heads.history.transport.references (comparisonAnchor origin.head)⟩
      ⟨.reading, comparisonAnchor heads.produced.head⟩ := by
  let afterEmission : History heads.emitted.next heads.produced.next :=
    .extend (.extend (.extend .root (.delivered heads.filled.first))
      (.delivered heads.filled.second)) (.encountered heads.produced)
  let afterFirst : History heads.filled.first.next heads.produced.next :=
    .extend (.extend .root (.delivered heads.filled.second)) (.encountered heads.produced)
  let emissionUsed := Encounter.cachedSignalPortUsed heads.emitted.head (.emissionReading _ _)
  let receptionUsed := Encounter.cachedSignalPortUsed heads.filled.first.head (.receptionSignal _)
  have comparisonUsed := comparisonPortUsed heads.produced.head .first
  have portExact := right_pair_first_is_carried (Held.received heads.filled.first.head) heads.filled.second.head
  change heads.filled.admitted.pair.first = _ at portExact
  rw [portExact] at comparisonUsed
  exact .cons (recurringHistoryUsed afterEmission.resources emissionUsed)
    (.cons (recurringHistoryUsed afterFirst.resources receptionUsed) (.single comparisonUsed))

theorem passage_heads_history_length {count source cell admitted origin destination payload empty}
    (heads : @PassageHeads count source cell admitted origin destination payload empty) :
    StrongPerimetralTurning.History.length heads.history = 4 := rfl

theorem passage_keeps_distinct_occurrences {count source cell admitted origin destination payload empty}
    (heads : @PassageHeads count source cell admitted origin destination payload empty) :
    comparisonAnchor heads.produced.head ≠ heads.history.transport.references (comparisonAnchor origin.head) := by
  intro same
  have strict := heads.used.position_decreases
  rw [same] at strict
  exact Nat.lt_irrefl _ strict

inductive SignalSuffix where
  | emitOutput | receiveFirstRecord | relayFirstRecord

def SignalSuffix.instruction {count source cell admitted origin destination payload empty}
    (request : SignalSuffix) (heads : @PassageHeads count source cell admitted origin destination payload empty) :
    (kind : Kind) ×' Instruction heads.produced.next.cursor.kinds kind :=
  let old := (comparisonExtension heads.produced.head).references heads.filled.admitted.pair.firstSignal
  match request with
  | .emitOutput => ⟨.signal, .emit (comparisonAnchor heads.produced.head) (heads.history.transport.references payload)⟩
  | .receiveFirstRecord => ⟨.reading, .receive old⟩
  | .relayFirstRecord => ⟨.signal, .relay old (heads.produced.next.cells.instrument destination)⟩

structure ContinuedPassage {count source cell admitted}
    (origin : @EncounterProduction count source cell admitted) (destination : Fin count)
    (payload : Ref origin.next.cursor.kinds .payload)
    (empty : origin.next.cells.phase destination = .empty) where
  heads : PassageHeads origin destination payload empty
  kind : Kind
  instruction : Instruction heads.produced.next.cursor.kinds kind
  suffix : SignalProduction heads.produced.next instruction

/-- A closed local suffix consumes the actual head's output or records.
No callback, completed successor or future history is a head input. -/
def runContinuedPassage {count source cell admitted}
    (origin : @EncounterProduction count source cell admitted) (destination : Fin count)
    (payload : Ref origin.next.cursor.kinds .payload)
    (empty : origin.next.cells.phase destination = .empty)
    (continuation : SignalSuffix) :
    ContinuedPassage origin destination payload empty :=
  let heads := producePassageHeads origin destination payload empty
  let requested := continuation.instruction heads
  let suffix := performSignal heads.produced.next requested.2
  ⟨heads, requested.1, requested.2, suffix⟩

theorem passage_head_independent {count source cell admitted}
    (origin : @EncounterProduction count source cell admitted) (destination : Fin count)
    (payload : Ref origin.next.cursor.kinds .payload)
    (empty : origin.next.cells.phase destination = .empty)
    (one two : SignalSuffix) :
    (runContinuedPassage origin destination payload empty one).heads =
      (runContinuedPassage origin destination payload empty two).heads := rfl

theorem signal_keeps_empty {count source kind instruction}
    (production : @SignalProduction count source kind instruction) {cell : Fin count}
    (empty : source.cells.phase cell = .empty) : production.next.cells.phase cell = .empty :=
  congrArg (fun phase => phase.transport (recurringProductionHistory production.head)) empty

theorem delivery_keeps_other_empty {count source cell port signal vacant}
    (production : @DeliveryProduction count source cell port signal vacant) {other : Fin count}
    (different : other ≠ cell) (empty : source.cells.phase other = .empty) :
    production.next.cells.phase other = .empty :=
  (delivered_other production other different).trans
    (congrArg (fun phase => phase.transport (recurringProductionHistory production.head)) empty)

theorem encounter_keeps_other_empty {count source cell admitted}
    (production : @EncounterProduction count source cell admitted) {other : Fin count}
    (different : other ≠ cell) (empty : source.cells.phase other = .empty) :
    production.next.cells.phase other = .empty :=
  (consumed_other production other different).trans
    (congrArg (fun phase => phase.transport (recurringProductionHistory production.head)) empty)

theorem passage_returns_empty_cells {count source cell admitted origin destination payload empty}
    (heads : @PassageHeads count source cell admitted origin destination payload empty)
    (emptyCells : ∀ other, origin.next.cells.phase other = .empty) :
    ∀ other, heads.produced.next.cells.phase other = .empty := by
  intro other
  cases decEq other destination with
  | isTrue same => cases same; exact consumed_selected heads.produced
  | isFalse different =>
    exact encounter_keeps_other_empty heads.produced different
      (delivery_keeps_other_empty heads.filled.second different
        (delivery_keeps_other_empty heads.filled.first different
          (signal_keeps_empty heads.emitted (emptyCells other))))

inductive PassageChain {count source cell admitted} (origin : @EncounterProduction count source cell admitted) :
    {state : State count} → {station : Fin count} → {allowed : Admission state station} →
    (last : EncounterProduction state station allowed) → History origin.next last.next → Nat → Type where
  | root : PassageChain origin origin .root 0
  | extended {state station allowed last history links}
      (past : @PassageChain count source cell admitted origin state station allowed last history links)
      {destination payload empty} (heads : PassageHeads last destination payload empty) :
      PassageChain origin heads.produced (StrongPerimetralTurning.History.append history heads.history) (links + 1)

structure Course {count source cell admitted} (origin : @EncounterProduction count source cell admitted) where
  state : State count
  station : Fin count
  allowed : Admission state station
  last : EncounterProduction state station allowed
  history : History origin.next last.next
  payload : Ref last.next.cursor.kinds .payload
  emptyCells : ∀ other, last.next.cells.phase other = .empty
  links : Nat
  formation : PassageChain origin last history links

def startCourse {count source cell admitted} (origin : @EncounterProduction count source cell admitted)
    (payload : Ref origin.next.cursor.kinds .payload)
    (emptyCells : ∀ other, origin.next.cells.phase other = .empty) : Course origin :=
  ⟨source, cell, admitted, origin, .root, payload, emptyCells, 0, .root⟩

def Course.advance {count source cell admitted origin}
    (course : @Course count source cell admitted origin) (destination : Fin count) : Course origin :=
  let heads := producePassageHeads course.last destination course.payload (course.emptyCells destination)
  ⟨heads.filled.second.next, destination, heads.filled.admitted, heads.produced,
    StrongPerimetralTurning.History.append course.history heads.history,
    heads.history.transport.references course.payload, passage_returns_empty_cells heads course.emptyCells,
    course.links + 1, .extended course.formation heads⟩

/-- Arbitrary finite requests, not a completed future; each suffix receives
the actual previous passage, its transported payload and its vacant cells. -/
def Course.extend {count source cell admitted origin}
    (course : @Course count source cell admitted origin) : List (Fin count) → Course origin
  | [] => course
  | destination :: rest => (course.advance destination).extend rest
termination_by structural requests => requests

theorem course_requested_length {count source cell admitted origin}
    (course : @Course count source cell admitted origin) (requests : List (Fin count)) :
    (course.extend requests).links = course.links + requests.length := by
  induction requests generalizing course with
  | nil => exact (Nat.add_zero _).symm
  | cons destination rest ih =>
    exact (ih (course.advance destination)).trans
      ((Nat.add_assoc course.links 1 rest.length).trans
        (congrArg (Nat.add course.links) (Nat.add_comm 1 rest.length)))

theorem course_resume_exact {count source cell admitted origin}
    (course : @Course count source cell admitted origin) (one two : List (Fin count)) :
    (course.extend (one ++ two)) = (course.extend one).extend two := by
  induction one generalizing course with
  | nil => rfl
  | cons destination rest ih => exact ih (course.advance destination)

end RelationalPerimeter.Relativity.Production.Network
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Network.emptyVacancy
#print axioms RelationalPerimeter.Relativity.Production.Network.empty_delivery_phase
#print axioms RelationalPerimeter.Relativity.Production.Network.second_delivery_phase
#print axioms RelationalPerimeter.Relativity.Production.Network.right_pair_first_is_carried
#print axioms RelationalPerimeter.Relativity.Production.Network.emission_record_exact
#print axioms RelationalPerimeter.Relativity.Production.Network.right_pair_signal_is_carried
#print axioms RelationalPerimeter.Relativity.Production.Network.held_received_signal_is_carried
#print axioms RelationalPerimeter.Relativity.Production.Network.performFill
#print axioms RelationalPerimeter.Relativity.Production.Network.FillProduction.admitted
#print axioms RelationalPerimeter.Relativity.Production.Network.FillProduction.history
#print axioms RelationalPerimeter.Relativity.Production.Network.producePassageHeads
#print axioms RelationalPerimeter.Relativity.Production.Network.PassageHeads.history
#print axioms RelationalPerimeter.Relativity.Production.Network.PassageHeads.used
#print axioms RelationalPerimeter.Relativity.Production.Network.passage_heads_history_length
#print axioms RelationalPerimeter.Relativity.Production.Network.passage_keeps_distinct_occurrences
#print axioms RelationalPerimeter.Relativity.Production.Network.SignalSuffix.instruction
#print axioms RelationalPerimeter.Relativity.Production.Network.runContinuedPassage
#print axioms RelationalPerimeter.Relativity.Production.Network.passage_head_independent
#print axioms RelationalPerimeter.Relativity.Production.Network.signal_keeps_empty
#print axioms RelationalPerimeter.Relativity.Production.Network.delivery_keeps_other_empty
#print axioms RelationalPerimeter.Relativity.Production.Network.encounter_keeps_other_empty
#print axioms RelationalPerimeter.Relativity.Production.Network.passage_returns_empty_cells
#print axioms RelationalPerimeter.Relativity.Production.Network.startCourse
#print axioms RelationalPerimeter.Relativity.Production.Network.Course.advance
#print axioms RelationalPerimeter.Relativity.Production.Network.Course.extend
#print axioms RelationalPerimeter.Relativity.Production.Network.course_requested_length
#print axioms RelationalPerimeter.Relativity.Production.Network.course_resume_exact
/- AXIOM_AUDIT_END -/
