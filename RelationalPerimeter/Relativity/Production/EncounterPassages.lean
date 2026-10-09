import RelationalPerimeter.Relativity.Production.ConstitutedEncounters
import RelationalPerimeter.Relativity.Production.CouplingDescriptions

/-!
# Actual used passages between produced encounters

Temporal succession alone is not a signal dependency. Each link below has a
positive path of ports actually used: the preceding interaction output feeds
an emission, a delivered reception, then the next admitted interaction.
The ideal holding law permits two new deliveries of the same record; their
arrival occurrences remain distinct. No distance or propagation speed is
inferred. This is a causal encounter course on one constituted instrument,
not a network of independent physical instruments or a continuous domain.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive RecurringUsedPath {context} {values : Values Value context}
    (past : RecurringFormation values) : Occurrence context → Occurrence context → Type where
  | single {one two} (edge : RecurringUsed past one two) : RecurringUsedPath past one two
  | cons {one middle two} (edge : RecurringUsed past one middle)
      (rest : RecurringUsedPath past middle two) : RecurringUsedPath past one two

def RecurringUsedPath.append {context} {values : Values Value context} {past : RecurringFormation values}
    {one middle two} (first : RecurringUsedPath past one middle) (second : RecurringUsedPath past middle two) :
    RecurringUsedPath past one two :=
  match first with
  | .single edge => .cons edge second
  | .cons edge rest => .cons edge (rest.append second)

theorem RecurringUsedPath.position_decreases {context} {values : Values Value context}
    {past : RecurringFormation values} {one two} (path : RecurringUsedPath past one two) :
    two.2.position < one.2.position := by
  induction path with
  | single edge => exact edge.position_decreases
  | cons edge rest ih => exact Nat.lt_trans ih edge.position_decreases

def RecurringUsedPath.prolong {source target} (history : RecurringHistory source target)
    {one two} (path : RecurringUsedPath source.formation one two) :
    RecurringUsedPath target.formation
      ⟨one.1, (recurringHistoryTransport history).references one.2⟩
      ⟨two.1, (recurringHistoryTransport history).references two.2⟩ :=
  match path with
  | .single edge => .single (recurringHistoryUsed history edge)
  | .cons edge rest => .cons (recurringHistoryUsed history edge) (rest.prolong history)

def RecurringUsedPath.rename {source target} (raccord : RecurringRaccord source target)
    {one two} (path : RecurringUsedPath source.formation one two) :
    RecurringUsedPath target.formation
      ⟨one.1, raccord.references.forward one.2⟩ ⟨two.1, raccord.references.forward two.2⟩ :=
  match path with
  | .single edge => .single (raccord.forwardUsed edge)
  | .cons edge rest => .cons (raccord.forwardUsed edge) (rest.rename raccord)

namespace Encounter

def cachedSignalPortUsed {source kind} {instruction : Instruction source.kinds kind}
    (head : RecurringProduction source (.signal instruction)) {inputKind}
    {ref : Ref source.kinds inputKind} (port : InputPort instruction ref) :
    RecurringUsed head.successor.formation
      ⟨inputKind, (recurringHistoryTransport (recurringProductionHistory head)).references ref⟩
      ⟨kind, head.successorExact.symm ▸ Ref.here⟩ := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role => cases role with
      | signal localRole => exact .signal source.formation localRole ref port

structure LinkedEncounter {source admitted} (origin : EncounterProduction source admitted) where
  state : State
  admission : EncounterAdmission state
  production : EncounterProduction state admission
  history : History origin.next production.next
  used : RecurringUsedPath production.next.cursor.formation
    ⟨.reading, history.transport.references (comparisonAnchor origin.head)⟩
    ⟨.reading, comparisonAnchor production.head⟩

theorem linked_encounters_are_distinct {source admitted origin}
    (link : @LinkedEncounter source admitted origin) :
    comparisonAnchor link.production.head ≠ link.history.transport.references (comparisonAnchor origin.head) := by
  intro same
  have strict := link.used.position_decreases
  rw [same] at strict
  exact Nat.lt_irrefl _ strict

/-- Producers are bound once, before their histories and used-port proofs
are assembled. The payload is an actual input reference, not a target. -/
def emittedSignal {source} {instruction : Instruction source.cursor.kinds .signal}
    (head : SignalProduction source instruction) : Ref head.next.cursor.kinds .signal := by
  change Ref head.head.successor.kinds .signal
  exact head.head.successorExact.symm ▸ Ref.here

def deliveryOldSignal {source port signal vacant} (head : DeliveryProduction source port signal vacant)
    (old : Ref source.cursor.kinds .signal) : Ref head.next.cursor.kinds .signal := by
  change Ref head.head.successor.kinds .signal
  exact head.head.successorExact.symm ▸ Ref.prior old

structure PassageHeads {source admitted} (origin : EncounterProduction source admitted)
    (payload : Ref origin.next.cursor.kinds .payload) where
  emitted : SignalProduction origin.next (.emit (comparisonAnchor origin.head) payload)
  first : DeliveryProduction emitted.next .left (emittedSignal emitted) (.empty .left)
  second : DeliveryProduction first.next .right (deliveryOldSignal first (emittedSignal emitted)) .right
  produced : EncounterProduction second.next ⟨rightPair (Held.received first.head) second.head, rfl⟩

def producePassageHeads {source admitted} (origin : EncounterProduction source admitted)
    (payload : Ref origin.next.cursor.kinds .payload) : PassageHeads origin payload :=
  let emitted := performSignal origin.next (.emit (comparisonAnchor origin.head) payload)
  let first := performDelivery emitted.next .left .here (.empty .left)
  let second := performDelivery first.next .right (.prior .here) .right
  let allowed : EncounterAdmission second.next := ⟨rightPair (Held.received first.head) second.head, rfl⟩
  let produced := performEncounter second.next allowed
  ⟨emitted, first, second, produced⟩

def produceLinkedEncounter {source admitted} (origin : EncounterProduction source admitted)
    (payload : Ref origin.next.cursor.kinds .payload) : LinkedEncounter origin := by
  let heads := producePassageHeads origin payload
  let emitted := heads.emitted
  let first := heads.first
  let second := heads.second
  let allowed : EncounterAdmission second.next := ⟨rightPair (Held.received first.head) second.head, rfl⟩
  let produced := heads.produced
  let history : History origin.next produced.next :=
    .extend (.extend (.extend (.extend .root (.signal emitted)) (.delivered first)) (.delivered second)) (.encountered produced)
  let emissionUsed := cachedSignalPortUsed emitted.head (.emissionReading _ _)
  let receptionUsed := cachedSignalPortUsed first.head (.receptionSignal _)
  let suffix : History emitted.next produced.next :=
    .extend (.extend (.extend .root (.delivered first)) (.delivered second)) (.encountered produced)
  let afterFirst : History first.next produced.next :=
    .extend (.extend .root (.delivered second)) (.encountered produced)
  let comparisonUsed := comparisonPortUsed produced.head .first
  exact ⟨second.next, allowed, produced, history,
    .cons (recurringHistoryUsed suffix.resources emissionUsed)
      (.cons (recurringHistoryUsed afterFirst.resources receptionUsed) (.single comparisonUsed))⟩

inductive PassageCourse {source admitted} (origin : EncounterProduction source admitted) :
    {state : State} → {admission : EncounterAdmission state} → (last : EncounterProduction state admission) →
      History origin.next last.next → Nat → Type where
  | root : PassageCourse origin origin .root 0
  | linked {state admission last history count} (past : @PassageCourse source admitted origin state admission last history count)
      (link : LinkedEncounter last) : PassageCourse origin link.production
        (StrongPerimetralTurning.History.append history link.history) (count + 1)

def PassageCourse.connection {source admitted origin state admission last history count}
    (course : @PassageCourse source admitted origin state admission last history count) :
    PSum (history.transport.references (comparisonAnchor origin.head) = comparisonAnchor last.head)
      (RecurringUsedPath last.next.cursor.formation
        ⟨.reading, history.transport.references (comparisonAnchor origin.head)⟩
        ⟨.reading, comparisonAnchor last.head⟩) := by
  cases course with
  | root => exact .inl rfl
  | @linked state admission last priorHistory count past link =>
    have square := history_transport_append priorHistory link.history (comparisonAnchor origin.head)
    cases past.connection with
    | inl same =>
      exact .inr (by rw [square, same]; exact link.used)
    | inr path =>
      exact .inr (by rw [square]; exact (path.prolong link.history.resources).append link.used)
termination_by structural course

def PassageCourse.used {source admitted origin state admission last history count}
    (course : @PassageCourse source admitted origin state admission last history count) (positive : 0 < count) :
    RecurringUsedPath last.next.cursor.formation
      ⟨.reading, history.transport.references (comparisonAnchor origin.head)⟩
      ⟨.reading, comparisonAnchor last.head⟩ := by
  cases course with
  | root => exact False.elim (Nat.not_lt_zero _ positive)
  | @linked state admission last priorHistory count past link =>
    have square := history_transport_append priorHistory link.history (comparisonAnchor origin.head)
    cases past.connection with
    | inl same => rw [square, same]; exact link.used
    | inr path => rw [square]; exact (path.prolong link.history.resources).append link.used

structure EncounterCourse {source admitted} (origin : EncounterProduction source admitted) where
  state : State
  admission : EncounterAdmission state
  last : EncounterProduction state admission
  history : History origin.next last.next
  payload : Ref last.next.cursor.kinds .payload
  links : Nat
  formation : PassageCourse origin last history links

def startEncounterCourse {source admitted} (origin : EncounterProduction source admitted)
    (payload : Ref origin.next.cursor.kinds .payload) : EncounterCourse origin :=
  ⟨source, admitted, origin, .root, payload, 0, .root⟩

def EncounterCourse.advance {source admitted origin} (course : @EncounterCourse source admitted origin) :
    EncounterCourse origin :=
  let link := produceLinkedEncounter course.last course.payload
  ⟨link.state, link.admission, link.production,
    StrongPerimetralTurning.History.append course.history link.history,
    link.history.transport.references course.payload, course.links + 1, .linked course.formation link⟩

def EncounterCourse.extend {source admitted origin} (course : @EncounterCourse source admitted origin) :
    Nat → EncounterCourse origin
  | 0 => course
  | count + 1 => (course.advance).extend count
termination_by structural count => count

theorem encounter_course_length {source admitted origin} (course : @EncounterCourse source admitted origin)
    (count : Nat) : (course.extend count).links = course.links + count := by
  induction count generalizing course with
  | zero => rfl
  | succ count ih => exact (ih course.advance).trans (by
      change course.links + 1 + count = course.links + (count + 1)
      exact (Nat.add_assoc course.links 1 count).trans (congrArg (Nat.add course.links) (Nat.add_comm 1 count)))

end Encounter
end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsedPath.append
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsedPath.position_decreases
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsedPath.prolong
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsedPath.rename
#print axioms RelationalPerimeter.Relativity.Production.Encounter.linked_encounters_are_distinct
#print axioms RelationalPerimeter.Relativity.Production.Encounter.cachedSignalPortUsed
#print axioms RelationalPerimeter.Relativity.Production.Encounter.emittedSignal
#print axioms RelationalPerimeter.Relativity.Production.Encounter.deliveryOldSignal
#print axioms RelationalPerimeter.Relativity.Production.Encounter.producePassageHeads
#print axioms RelationalPerimeter.Relativity.Production.Encounter.produceLinkedEncounter
#print axioms RelationalPerimeter.Relativity.Production.Encounter.PassageCourse.connection
#print axioms RelationalPerimeter.Relativity.Production.Encounter.PassageCourse.used
#print axioms RelationalPerimeter.Relativity.Production.Encounter.startEncounterCourse
#print axioms RelationalPerimeter.Relativity.Production.Encounter.EncounterCourse.advance
#print axioms RelationalPerimeter.Relativity.Production.Encounter.EncounterCourse.extend
#print axioms RelationalPerimeter.Relativity.Production.Encounter.encounter_course_length
/- AXIOM_AUDIT_END -/
