import RelationalPerimeter.Relativity.Reconstruction.LocationAgreement
import RelationalPerimeter.Relativity.Production.CalibratedRelay

/-!
# Finite futures of the declared two-port coupling

Requests preserve all old typed inspections and signal operations. Delivery
requires a signal reference and a presently vacant port; coupling requires
both positively delivered arrivals. Refused requests leave the state intact.
The executable runner binds each production once and resumes at its actual
successor. The generic contract is a specification by projections, not the
single-production execution path.

This local contract permits full path-record inspection. A local agreement
therefore does not authorize forgetting different paths. Neither a final
physical future contract nor relativistic geometry is claimed here.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Continuation.Encounter
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

inductive Request where
  | local : LocalRequest → Request
  | deliver (port : Port) (signal : Nat)
  | encounter

inductive Event where
  | local : LocalEvent → Event
  | delivered : Port → Rational → Event
  | encountered : Rational → Event

def Admission (source : State) : Request → Type
  | .local request => RecurringLocalAdmission source.cursor request
  | .deliver port signal => ReferenceAt source.cursor.kinds .signal signal × Vacant source.phase port
  | .encounter => EncounterAdmission source

def decide (source : State) : (request : Request) → PSum (Admission source request) (Admission source request → False)
  | .local request => decideRecurringLocal source.cursor request
  | .deliver port signal => pairDecision (resolve source.cursor.kinds .signal signal) (decideVacant source.phase port)
  | .encounter => decideEncounter source

def enabled (source : State) (request : Request) : Bool :=
  match decide source request with | .inl _ => true | .inr _ => false

theorem admission_enabled (source : State) (request : Request) (admitted : Admission source request) :
    enabled source request = true := by
  unfold enabled
  cases decide source request with
  | inl _ => rfl
  | inr impossible => exact False.elim (impossible admitted)

theorem refusal_refutes (source : State) (request : Request) (no : enabled source request = false)
    (admitted : Admission source request) : False := by
  unfold enabled at no
  cases chosen : decide source request with
  | inl _ => rw [chosen] at no; cases no
  | inr impossible => exact impossible admitted

structure Response (source : State) where
  state : State
  event : Event
  allowed : Bool
  history : Production.Encounter.History source state

def respondAdmitted (source : State) : (request : Request) → Admission source request → Response source
  | .local (.emit _ _), admitted =>
      let head := performSignal source (.emit admitted.1.ref admitted.2.ref)
      ⟨head.next, .local (.emitted head.head.determination.1), true, .extend .root (.signal head)⟩
  | .local (.relay _ _), admitted =>
      let head := performSignal source (.relay admitted.1.ref admitted.2.ref)
      ⟨head.next, .local (.relayed head.head.determination.1), true, .extend .root (.signal head)⟩
  | .local (.receive _), admitted =>
      let head := performSignal source (.receive admitted.ref)
      ⟨head.next, .local (.received head.head.determination.1), true, .extend .root (.signal head)⟩
  | .local (.inspect kind _), admitted =>
      ⟨source, .local (.inspected (localReadout kind (source.cursor.read admitted.ref))), true, .root⟩
  | .deliver port _, admitted =>
      let head := performDelivery source port admitted.1.ref admitted.2
      ⟨head.next, .delivered port head.head.determination.1, true, .extend .root (.delivered head)⟩
  | .encounter, admitted =>
      let head := performEncounter source admitted
      ⟨head.next, .encountered head.head.determination.1, true, .extend .root (.encountered head)⟩

def respond (source : State) (request : Request) : Response source :=
  match decide source request with
  | .inl admitted => respondAdmitted source request admitted
  | .inr _ => ⟨source, .local .refused, false, .root⟩

def contract : FutureContract State Request Event Unit where
  next := fun source request => (respond source request).state
  event := fun source request => (respond source request).event
  read := fun _ => ()
  Allow := Admission
  decision := decide

theorem admitted_response_allowed (source : State) (request : Request) (admitted : Admission source request) :
    (respondAdmitted source request admitted).allowed = true := by
  cases request with
  | «local» request => cases request <;> rfl
  | deliver port signal => rfl
  | encounter => rfl

theorem response_enabled_exact (source : State) (request : Request) :
    (respond source request).allowed = contract.enabled source request := by
  dsimp only [FutureContract.enabled, contract]
  unfold respond
  cases decide source request with
  | inl admitted => exact admitted_response_allowed source request admitted
  | inr _ => rfl

theorem refusal_unchanged (source : State) (request : Request) (no : enabled source request = false) :
    respond source request = ⟨source, .local .refused, false, .root⟩ := by
  unfold respond
  cases decide source request with
  | inl admitted => exact False.elim (refusal_refutes source request no admitted)
  | inr _ => rfl

theorem inspection_response (source : State) {kind} (ref : Ref source.cursor.kinds kind) :
    respond source (.local (.inspect kind ref.position)) =
      ⟨source, .local (.inspected (localReadout kind (source.cursor.read ref))), true, .root⟩ := by
  unfold respond
  cases decide source (.local (.inspect kind ref.position)) with
  | inl admitted =>
      dsimp only [respondAdmitted]
      rw [reference_position_injective admitted.ref ref admitted.exactPosition]
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

structure Execution (source : State) where
  state : State
  history : Production.Encounter.History source state
  report : Outcome Event Unit

def run (source : State) : List Request → Execution source
  | [] => ⟨source, .root, .stop ()⟩
  | request :: rest =>
      let head := respond source request
      let suffix := run head.state rest
      ⟨suffix.state, StrongPerimetralTurning.History.append head.history suffix.history,
        .step () head.allowed head.event suffix.report⟩
termination_by structural requests => requests

theorem all_futures_exact (source : State) (requests : List Request) :
    (run source requests).report = contract.outcome source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
      change Outcome.step () _ _ _ = Outcome.step () _ _ _
      rw [response_enabled_exact]
      exact congrArg (Outcome.step () _ _) (ih _)

theorem final_state_exact (source : State) (requests : List Request) :
    (run source requests).state = ConstitutiveSearch.Grouping.Continuation.run contract.next source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
      change (run (respond source request).state rest).state =
        ConstitutiveSearch.Grouping.Continuation.run contract.next (respond source request).state rest
      exact ih _

def Execution.continue {source} (prior : Execution source) (requests : List Request) : Execution prior.state :=
  run prior.state requests

theorem continuation_exact {source} (prior : Execution source) (requests : List Request) :
    (prior.continue requests).report = contract.outcome prior.state requests := all_futures_exact ..

theorem run_append_state (source : State) (one two : List Request) :
    (run source (one ++ two)).state = (run (run source one).state two).state := by
  induction one generalizing source with
  | nil => rfl
  | cons request rest ih =>
      change (run (respond source request).state (rest ++ two)).state =
        (run (run (respond source request).state rest).state two).state
      exact ih _

theorem requests_keep_reads (source : State) (requests : List Request) {kind}
    (ref : Ref source.cursor.kinds kind) :
    (run source requests).state.cursor.read ((run source requests).history.transport.references ref) =
      source.cursor.read ref := history_keeps_reads _ ref

theorem requests_keep_sources (source : State) (requests : List Request) {kind}
    (one two : Ref source.cursor.kinds kind) (different : one ≠ two) :
    (run source requests).history.transport.references one ≠ (run source requests).history.transport.references two :=
  history_keeps_sources _ one two different

structure EncounterRun (source : State) (admitted : EncounterAdmission source) where
  production : EncounterProduction source admitted
  continuation : Execution production.next

def encounterThen (source : State) (admitted : EncounterAdmission source) (requests : List Request) :
    EncounterRun source admitted :=
  let production := performEncounter source admitted
  ⟨production, run production.next requests⟩

theorem head_independent (source : State) (admitted : EncounterAdmission source) (one two : List Request) :
    (encounterThen source admitted one).production = (encounterThen source admitted two).production := rfl

theorem encounter_continuation_exact (source : State) (admitted : EncounterAdmission source) (requests : List Request) :
    (encounterThen source admitted requests).continuation.report =
      contract.outcome (performEncounter source admitted).next requests := all_futures_exact ..

def EncounterRun.first {source admitted} (execution : EncounterRun source admitted) :=
  (localizeParticipant execution.production .left).prolong execution.continuation.history

def EncounterRun.second {source admitted} (execution : EncounterRun source admitted) :=
  (localizeParticipant execution.production .right).prolong execution.continuation.history

def EncounterRun.agreement {source admitted} (execution : EncounterRun source admitted) :
    LocationAgreement execution.production execution.first execution.second :=
  continuedLocationAgreement execution.production execution.continuation.history

theorem continued_effects_exact {source admitted} (execution : EncounterRun source admitted) :
    AttachedEffects execution.first = execution.production.effects.1 ∧
      AttachedEffects execution.second = execution.production.effects.2 :=
  ⟨localized_prolong_effects _ _, localized_prolong_effects _ _⟩

def firstInspection : Outcome Event Unit → Option LocalReadout
  | .stop _ => none
  | .step _ _ (.local (.inspected reading)) _ => some reading
  | .step _ _ (.local (.emitted _)) _ => none
  | .step _ _ (.local (.relayed _)) _ => none
  | .step _ _ (.local (.received _)) _ => none
  | .step _ _ (.local .refused) _ => none
  | .step _ _ (.delivered _ _) _ => none
  | .step _ _ (.encountered _) _ => none

theorem inspection_report (source : State) {kind} (ref : Ref source.cursor.kinds kind) :
    (run source [.local (.inspect kind ref.position)]).report =
      .step () true (.local (.inspected (localReadout kind (source.cursor.read ref)))) (.stop ()) :=
  congrArg (fun response : Response source =>
    Outcome.step () response.allowed response.event (run response.state []).report) (inspection_response source ref)

/-- The requests follow the actual transported references. They need not
have the same numerical address, and agreement does not equate their effects. -/
theorem effects_separate_futures {source admitted} (execution : EncounterRun source admitted)
    (different : execution.production.effects.1 ≠ execution.production.effects.2) :
    (run execution.continuation.state
      [.local (.inspect .signal execution.first.attachment.signalReference.position)]).report ≠
    (run execution.continuation.state
      [.local (.inspect .signal execution.second.attachment.signalReference.position)]).report := by
  intro same
  have reports := (inspection_report _ execution.first.attachment.signalReference).symm.trans
    (same.trans (inspection_report _ execution.second.attachment.signalReference))
  have records := Option.some.inj (congrArg firstInspection reports)
  have signals := LocalReadout.noConfusion records (fun same => same)
  exact different ((continued_effects_exact execution).1.symm.trans
    (signals.trans (continued_effects_exact execution).2))

/-- Translate an old typed inspection along an actual extension. This
does not equate an old prefix with its richer successor or renew admission. -/
def transportedInspection {source target : State} (history : Production.Encounter.History source target)
    {kind} (ref : Ref source.cursor.kinds kind) : Request :=
  .local (.inspect kind (history.transport.references ref).position)

theorem transported_inspection_exact {source target : State} (history : Production.Encounter.History source target)
    {kind} (ref : Ref source.cursor.kinds kind) :
    (respond target (transportedInspection history ref)).event =
      .local (.inspected (localReadout kind (source.cursor.read ref))) := by
  unfold transportedInspection
  rw [inspection_response, history_keeps_reads]

/-- A rich participant description travels with the actual coupling state.
Its observation request is the SAME request for both participants: the path
selects the attached occurrence. Comparing different raw addresses alone
would not establish inequivalence under a fixed contract. -/
structure DescribedState {source admitted} (production : EncounterProduction source admitted) where
  state : State
  presentation : LocalizedPresentation production state.cursor

inductive ReaderRequest where
  | attachedEffects
  | operate : Request → ReaderRequest

inductive ReaderEvent where
  | effects : SignalRecord → ReaderEvent
  | operation : Event → ReaderEvent

structure ReaderResponse {source admitted production} (prior : @DescribedState source admitted production) where
  current : DescribedState production
  event : ReaderEvent

def readerRespond {source admitted production} (prior : @DescribedState source admitted production) :
    ReaderRequest → ReaderResponse prior
  | .attachedEffects => ⟨prior, .effects (AttachedEffects prior.presentation)⟩
  | .operate request =>
      let shared := respond prior.state request
      ⟨⟨shared.state, prior.presentation.prolong shared.history⟩, .operation shared.event⟩

def ReaderAdmission {source admitted production} (prior : @DescribedState source admitted production) : ReaderRequest → Type
  | .attachedEffects => PUnit
  | .operate request => Admission prior.state request

def readerDecision {source admitted production} (prior : @DescribedState source admitted production) :
    (request : ReaderRequest) → PSum (ReaderAdmission prior request) (ReaderAdmission prior request → False)
  | .attachedEffects => .inl .unit
  | .operate request => decide prior.state request

/-- Rich-description reference contract. Its generic next/event projections
are not advertised as a single-production execution path. -/
def readerContract {source admitted} (production : EncounterProduction source admitted) :
    FutureContract (DescribedState production) ReaderRequest ReaderEvent Unit where
  next := fun prior request => (readerRespond prior request).current
  event := fun prior request => (readerRespond prior request).event
  read := fun _ => ()
  Allow := ReaderAdmission
  decision := readerDecision

def firstEffects : Outcome ReaderEvent Unit → Option SignalRecord
  | .stop _ => none
  | .step _ _ (.effects record) _ => some record
  | .step _ _ (.operation _) _ => none

theorem rich_futures_require_effects {source admitted production}
    (one two : @DescribedState source admitted production)
    (same : FutureEquivalent (readerContract production) one two) :
    AttachedEffects one.presentation = AttachedEffects two.presentation :=
  Option.some.inj (congrArg firstEffects (same [.attachedEffects]))

theorem different_effects_forbid_rich_grouping {source admitted production}
    (one two : @DescribedState source admitted production)
    (different : AttachedEffects one.presentation ≠ AttachedEffects two.presentation) :
    ¬ FutureEquivalent (readerContract production) one two :=
  fun same => different (rich_futures_require_effects one two same)

/- A closed client of the same constituted support and interpreter. Received
calibration and the ideal holding law are inputs, not discovered physics. -/
namespace Example

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def emitted := perform (.received input) emission
def once := perform emitted.successor (.relay .here (.prior (.prior (.prior .here))))
def twice := perform once.successor (.relay .here (.prior (.prior (.prior (.prior .here)))))
def received := perform twice.successor (.receive .here)
def reemitted := perform received.successor
  (.emit .here (.prior (.prior (.prior (.prior (.prior .here))))))
def receivedAgain := perform reemitted.successor (.receive .here)
def receivedPrefix := receivedAgain.successor

def firstSignal : Ref receivedPrefix.kinds .signal := .prior (.prior (.prior .here))
def secondSignal : Ref receivedPrefix.kinds .signal := .prior .here
def instrument : Ref receivedPrefix.kinds .calibration :=
  .prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior .here)))))))
def initial := attach receivedPrefix instrument
def archivedPair : RecurringPair initial.cursor :=
  ⟨.prior (.prior .here), .here, firstSignal, secondSignal,
    .fromCursor (.inherited receivedAgain.determination.2
      (.inherited reemitted.determination.2 (arrivalOfProduction received))),
    .fromCursor (arrivalOfProduction receivedAgain), fun same => by
      have positions := congrArg Ref.position same
      change 2 = 0 at positions
      cases positions⟩
def left := performDelivery initial .left firstSignal (.empty .left)
def right := performDelivery left.next .right (.prior secondSignal) .right
def ready := right.next
def admission : EncounterAdmission ready := ⟨rightPair (Held.received left.head) right.head, rfl⟩
def produced := performEncounter ready admission
def execution (requests : List Request) := encounterThen ready admission requests

def agreement := producedLocationAgreement produced

theorem equal_readings : produced.effects.1.reading = produced.effects.2.reading := rfl
theorem first_path : produced.effects.1.increments = [Rational.one, Rational.one] := rfl
theorem second_path : produced.effects.2.increments = [] := rfl

theorem different_effects : produced.effects.1 ≠ produced.effects.2 := by
  intro same
  have lengths := congrArg (fun record : SignalRecord => record.increments.length) same
  change 2 = 0 at lengths
  cases lengths

theorem admission_is_real : encounterEnabled ready = true := encounter_enabled ready admission
theorem sources_remain_distinct : produced.first.readingReference ≠ produced.second.readingReference :=
  encounter_sources_distinct produced

theorem signal_sources_remain_distinct : produced.first.signalReference ≠ produced.second.signalReference := by
  apply attached_signal_distinction
  intro same
  have positions := congrArg Ref.position same
  change 5 = 3 at positions
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj positions)))

theorem no_archived_admission : encounterEnabled initial = false := attach_refuses receivedPrefix instrument
theorem equal_archived_readings : initial.cursor.read archivedPair.first = initial.cursor.read archivedPair.second := rfl
theorem equal_archive_cannot_admit (attempt : EncounterAdmission initial) : False := by
  have wrong := encounter_enabled initial attempt
  change false = true at wrong
  cases wrong
theorem one_port_refused : encounterEnabled left.next = false := rfl
theorem consumed_refused : encounterEnabled produced.next = false := rfl
theorem repeated_request_refused : respond produced.next .encounter =
    ⟨produced.next, .local .refused, false, .root⟩ := rfl

theorem full_port_refused : enabled ready (.deliver .left 0) = false := rfl

theorem common_location :
    (localizeParticipant produced .left).location = (localizeParticipant produced .right).location := rfl

theorem every_suffix_keeps_the_head (requests : List Request) :
    (execution requests).production = produced := rfl

theorem every_suffix_preserves_the_difference (requests : List Request) :
    AttachedEffects (execution requests).first ≠ AttachedEffects (execution requests).second := by
  intro same
  exact different_effects ((continued_effects_exact (execution requests)).1.symm.trans
    (same.trans (continued_effects_exact (execution requests)).2))

theorem every_suffix_reveals_the_difference (requests : List Request) :
    (run (execution requests).continuation.state
      [.local (.inspect .signal (execution requests).first.attachment.signalReference.position)]).report ≠
    (run (execution requests).continuation.state
      [.local (.inspect .signal (execution requests).second.attachment.signalReference.position)]).report :=
  effects_separate_futures (execution requests) different_effects

def richFirst (requests : List Request) : DescribedState produced :=
  ⟨(execution requests).continuation.state, (execution requests).first⟩
def richSecond (requests : List Request) : DescribedState produced :=
  ⟨(execution requests).continuation.state, (execution requests).second⟩

theorem same_request_forbids_rich_grouping (requests : List Request) :
    ¬ FutureEquivalent (readerContract produced) (richFirst requests) (richSecond requests) :=
  different_effects_forbid_rich_grouping _ _ (every_suffix_preserves_the_difference requests)

/-- Equal numerical outputs of two freshly admitted couplings still give
different interaction occurrences. Reusing a signal record requires new
delivery productions; the earlier occupied arrivals are not consumed again. -/
def againLeft := performDelivery produced.next .left (.prior admission.pair.firstSignal) (.empty .left)
def againRight := performDelivery againLeft.next .right (.prior (.prior admission.pair.secondSignal)) .right
def againAdmission : EncounterAdmission againRight.next :=
  ⟨rightPair (Held.received againLeft.head) againRight.head, rfl⟩
def again := performEncounter againRight.next againAdmission
def redeliveryHistory : Production.Encounter.History produced.next againRight.next :=
  .extend (.extend .root (.delivered againLeft)) (.delivered againRight)
def nextEncounterHistory : Production.Encounter.History produced.next again.next :=
  .extend redeliveryHistory (.encountered again)

theorem different_encounter_occurrences :
    commonEncounterLocation again ≠ nextEncounterHistory.transport.references (commonEncounterLocation produced) := by
  change comparisonAnchor again.head ≠ (comparisonExtension again.head).references
    (redeliveryHistory.transport.references (commonEncounterLocation produced))
  exact comparison_anchor_fresh again.head _

theorem same_output_not_same_occurrence :
    again.head.determination.1 = produced.head.determination.1 ∧
      commonEncounterLocation again ≠ nextEncounterHistory.transport.references (commonEncounterLocation produced) := by
  constructor
  · change Rational.sub admission.pair.secondArrival.measure admission.pair.firstArrival.measure = _
    exact encounter_output_exact produced |>.symm
  · exact different_encounter_occurrences

def continuedAgreement := continuedLocationAgreement produced nextEncounterHistory

end Example

end RelationalPerimeter.Relativity.Continuation.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Admission
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.decide
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.admission_enabled
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.refusal_refutes
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.respondAdmitted
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.respond
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.contract
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.response_enabled_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.refusal_unchanged
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.inspection_response
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.run
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.all_futures_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.final_state_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.continuation_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.run_append_state
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.requests_keep_reads
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.requests_keep_sources
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.encounterThen
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.head_independent
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.encounter_continuation_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.EncounterRun.agreement
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.continued_effects_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.effects_separate_futures
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.inspection_report
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.firstInspection
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transportedInspection
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transported_inspection_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.readerRespond
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.readerDecision
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.readerContract
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.firstEffects
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.rich_futures_require_effects
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.different_effects_forbid_rich_grouping
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.admission
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.produced
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.agreement
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.equal_readings
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.first_path
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.second_path
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.different_effects
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.admission_is_real
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.sources_remain_distinct
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.signal_sources_remain_distinct
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.no_archived_admission
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.archivedPair
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.equal_archived_readings
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.equal_archive_cannot_admit
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.one_port_refused
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.consumed_refused
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.repeated_request_refused
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.full_port_refused
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.common_location
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.every_suffix_keeps_the_head
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.every_suffix_preserves_the_difference
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.every_suffix_reveals_the_difference
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.same_request_forbids_rich_grouping
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.nextEncounterHistory
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.different_encounter_occurrences
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.same_output_not_same_occurrence
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Example.continuedAgreement
/- AXIOM_AUDIT_END -/
