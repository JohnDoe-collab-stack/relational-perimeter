import RelationalPerimeter.Relativity.Production.RecurringInteractions
import RelationalPerimeter.Relativity.Production.LocalFutureContract

/-!
# A fixed contract including repeated arrival comparisons

Every finite interleaving of the declared signal operations, comparison and
full typed-resource inspection is covered, including exact refusals. The
request resolver uses the current constituted prefix only. `runRecurringRequests`
shares one head determination between its event, successor and history.
The next/event projections are the separate reference specification, not a
claim that this generic specification evaluates an action only once.

The older signal-only and one-comparison contracts are left unchanged. No
grouping is authorized here and no final physical contract is claimed.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

structure RecurringArrivalAt (source : RecurringCursor) (address : Nat) where
  reading : ReferenceAt source.kinds .reading address
  signal : Ref source.kinds .signal
  arrival : RecurringArrival source.formation reading.ref signal

def resolveRecurringArrivalAt (source : RecurringCursor) (address : Nat) :
    PSum (RecurringArrivalAt source address) (RecurringArrivalAt source address → False) :=
  match resolve source.kinds .reading address with
  | .inr impossible => .inr (fun arrival => impossible arrival.reading)
  | .inl reading =>
    match resolveRecurringArrival source.formation reading.ref with
    | .inl found => .inl ⟨reading, found.1, found.2⟩
    | .inr impossible => .inr (fun arrival => by
        have same := reference_position_injective reading.ref arrival.reading.ref
          (reading.exactPosition.trans arrival.reading.exactPosition.symm)
        exact impossible ⟨arrival.signal, same.symm ▸ arrival.arrival⟩)

structure RecurringComparisonAdmission (source : RecurringCursor) (one two : Nat) where
  first : RecurringArrivalAt source one
  second : RecurringArrivalAt source two
  distinct : first.reading.ref ≠ second.reading.ref

def RecurringComparisonAdmission.pair {source : RecurringCursor} {one two : Nat}
    (admitted : RecurringComparisonAdmission source one two) : RecurringPair source :=
  ⟨admitted.first.reading.ref, admitted.second.reading.ref, admitted.first.signal, admitted.second.signal,
    admitted.first.arrival, admitted.second.arrival, admitted.distinct⟩

def decideRecurringComparison (source : RecurringCursor) (one two : Nat) :
    PSum (RecurringComparisonAdmission source one two) (RecurringComparisonAdmission source one two → False) :=
  match pairDecision (resolveRecurringArrivalAt source one) (resolveRecurringArrivalAt source two) with
  | .inr impossible => .inr (fun admitted => impossible (admitted.first, admitted.second))
  | .inl arrivals =>
    match Nat.decEq one two with
    | .isTrue same => .inr (fun admitted => admitted.distinct (reference_position_injective _ _
        (admitted.first.reading.exactPosition.trans (same.trans admitted.second.reading.exactPosition.symm))))
    | .isFalse distinct => .inl ⟨arrivals.1, arrivals.2, fun same => distinct
        (arrivals.1.reading.exactPosition.symm.trans
          ((congrArg Ref.position same).trans arrivals.2.reading.exactPosition))⟩

inductive RecurringRequest where
  | local : LocalRequest → RecurringRequest
  | compare (first second : Nat)

inductive RecurringEvent where
  | local : LocalEvent → RecurringEvent
  | compared : Rational → RecurringEvent

def RecurringLocalAdmission (source : RecurringCursor) : LocalRequest → Type
  | .emit reading payload => ReferenceAt source.kinds .reading reading × ReferenceAt source.kinds .payload payload
  | .relay signal calibration => ReferenceAt source.kinds .signal signal × ReferenceAt source.kinds .calibration calibration
  | .receive signal => ReferenceAt source.kinds .signal signal
  | .inspect kind position => ReferenceAt source.kinds kind position

def decideRecurringLocal (source : RecurringCursor) :
    (request : LocalRequest) → PSum (RecurringLocalAdmission source request) (RecurringLocalAdmission source request → False)
  | .emit reading payload => pairDecision (resolve source.kinds .reading reading) (resolve source.kinds .payload payload)
  | .relay signal calibration => pairDecision (resolve source.kinds .signal signal) (resolve source.kinds .calibration calibration)
  | .receive signal => resolve source.kinds .signal signal
  | .inspect kind position => resolve source.kinds kind position

def RecurringAdmission (source : RecurringCursor) : RecurringRequest → Type
  | .local request => RecurringLocalAdmission source request
  | .compare one two => RecurringComparisonAdmission source one two

def decideRecurringAdmission (source : RecurringCursor) :
    (request : RecurringRequest) → PSum (RecurringAdmission source request) (RecurringAdmission source request → False)
  | .local request => decideRecurringLocal source request
  | .compare one two => decideRecurringComparison source one two

def recurringEnabled (source : RecurringCursor) (request : RecurringRequest) : Bool :=
  match decideRecurringAdmission source request with | .inl _ => true | .inr _ => false

def recurringAdmissionOfEnabled (source : RecurringCursor) (request : RecurringRequest)
    (yes : recurringEnabled source request = true) : RecurringAdmission source request := by
  cases chosen : decideRecurringAdmission source request with
  | inl admitted => exact admitted
  | inr impossible => unfold recurringEnabled at yes; rw [chosen] at yes; cases yes

theorem recurring_refusal_refutes (source : RecurringCursor) (request : RecurringRequest)
    (no : recurringEnabled source request = false) (admitted : RecurringAdmission source request) : False := by
  cases chosen : decideRecurringAdmission source request with
  | inl witness => unfold recurringEnabled at no; rw [chosen] at no; cases no
  | inr impossible => exact impossible admitted

def recurringAdmittedNext (source : RecurringCursor) :
    (request : RecurringRequest) → RecurringAdmission source request → RecurringCursor
  | .local (.emit _ _), admitted => source.extend
      (executeRecurring source (.signal (.emit admitted.1.ref admitted.2.ref)))
  | .local (.relay _ _), admitted => source.extend
      (executeRecurring source (.signal (.relay admitted.1.ref admitted.2.ref)))
  | .local (.receive _), admitted => source.extend (executeRecurring source (.signal (.receive admitted.ref)))
  | .local (.inspect _ _), _ => source
  | .compare _ _, admitted => source.extend (executeRecurring source (.compare admitted.pair))

def recurringAdmittedEvent (source : RecurringCursor) :
    (request : RecurringRequest) → RecurringAdmission source request → RecurringEvent
  | .local (.emit _ _), admitted => .local (.emitted ((Instruction.emit admitted.1.ref admitted.2.ref).interpret source.values))
  | .local (.relay _ _), admitted => .local (.relayed ((Instruction.relay admitted.1.ref admitted.2.ref).interpret source.values))
  | .local (.receive _), admitted => .local (.received ((Instruction.receive admitted.ref).interpret source.values))
  | .local (.inspect kind _), admitted => .local (.inspected (localReadout kind (source.read admitted.ref)))
  | .compare _ _, admitted => .compared admitted.pair.gap

def recurringReferenceNext (source : RecurringCursor) (request : RecurringRequest) : RecurringCursor :=
  match decideRecurringAdmission source request with
  | .inl admitted => recurringAdmittedNext source request admitted
  | .inr _ => source

def recurringReferenceEvent (source : RecurringCursor) (request : RecurringRequest) : RecurringEvent :=
  match decideRecurringAdmission source request with
  | .inl admitted => recurringAdmittedEvent source request admitted
  | .inr _ => .local .refused

def recurringContract : FutureContract RecurringCursor RecurringRequest RecurringEvent Unit where
  next := recurringReferenceNext
  event := recurringReferenceEvent
  read := fun _ => ()
  Allow := RecurringAdmission
  decision := decideRecurringAdmission

theorem recurring_contract_enabled_exact (source : RecurringCursor) (request : RecurringRequest) :
    recurringContract.enabled source request = recurringEnabled source request := by
  dsimp only [FutureContract.enabled, recurringContract, recurringEnabled, FutureContract.decision]
  cases decideRecurringAdmission source request <;> rfl

theorem recurring_same_arrival_refused (source : RecurringCursor) (address : Nat) :
    recurringEnabled source (.compare address address) = false := by
  cases chosen : decideRecurringAdmission source (.compare address address) with
  | inl admitted => exact False.elim (admitted.distinct (reference_position_injective _ _
      (admitted.first.reading.exactPosition.trans admitted.second.reading.exactPosition.symm)))
  | inr impossible => unfold recurringEnabled; rw [chosen]

structure RecurringResponse (source : RecurringCursor) where
  cursor : RecurringCursor
  event : RecurringEvent
  allowed : Bool
  history : RecurringHistory source cursor

def performRecurringAdmitted (source : RecurringCursor) :
    (request : RecurringRequest) → RecurringAdmission source request → RecurringResponse source
  | .local (.emit _ _), admitted =>
      let head := performRecurring source (.signal (.emit admitted.1.ref admitted.2.ref))
      ⟨head.successor, .local (.emitted head.determination.1), true, recurringProductionHistory head⟩
  | .local (.relay _ _), admitted =>
      let head := performRecurring source (.signal (.relay admitted.1.ref admitted.2.ref))
      ⟨head.successor, .local (.relayed head.determination.1), true, recurringProductionHistory head⟩
  | .local (.receive _), admitted =>
      let head := performRecurring source (.signal (.receive admitted.ref))
      ⟨head.successor, .local (.received head.determination.1), true, recurringProductionHistory head⟩
  | .local (.inspect kind _), admitted =>
      ⟨source, .local (.inspected (localReadout kind (source.read admitted.ref))), true, .root⟩
  | .compare _ _, admitted =>
      let head := performRecurring source (.compare admitted.pair)
      ⟨head.successor, .compared head.determination.1, true, recurringProductionHistory head⟩

def performRecurringRequest (source : RecurringCursor) (request : RecurringRequest) : RecurringResponse source :=
  match decideRecurringAdmission source request with
  | .inl admitted => performRecurringAdmitted source request admitted
  | .inr _ => ⟨source, .local .refused, false, .root⟩

theorem recurring_admitted_next_exact (source : RecurringCursor) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) :
    (performRecurringAdmitted source request admitted).cursor = recurringAdmittedNext source request admitted := by
  cases request with
  | «local» request => cases request <;> rfl
  | compare one two => rfl

theorem recurring_admitted_event_exact (source : RecurringCursor) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) :
    (performRecurringAdmitted source request admitted).event = recurringAdmittedEvent source request admitted := by
  cases request with
  | «local» request => cases request <;> rfl
  | compare one two => rfl

theorem recurring_admitted_allowed (source : RecurringCursor) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) :
    (performRecurringAdmitted source request admitted).allowed = true := by
  cases request with
  | «local» request => cases request <;> rfl
  | compare one two => rfl

theorem recurring_request_next_exact (source : RecurringCursor) (request : RecurringRequest) :
    (performRecurringRequest source request).cursor = recurringContract.next source request := by
  dsimp only [recurringContract, FutureContract.next]
  unfold performRecurringRequest recurringReferenceNext
  cases decideRecurringAdmission source request with
  | inl admitted => exact recurring_admitted_next_exact source request admitted
  | inr _ => rfl

theorem recurring_request_event_exact (source : RecurringCursor) (request : RecurringRequest) :
    (performRecurringRequest source request).event = recurringContract.event source request := by
  dsimp only [recurringContract, FutureContract.event]
  unfold performRecurringRequest recurringReferenceEvent
  cases decideRecurringAdmission source request with
  | inl admitted => exact recurring_admitted_event_exact source request admitted
  | inr _ => rfl

theorem recurring_request_allowed_exact (source : RecurringCursor) (request : RecurringRequest) :
    (performRecurringRequest source request).allowed = recurringContract.enabled source request := by
  rw [recurring_contract_enabled_exact]
  unfold performRecurringRequest recurringEnabled
  cases decideRecurringAdmission source request with
  | inl admitted => exact recurring_admitted_allowed source request admitted
  | inr _ => rfl

theorem recurring_refusal_is_unchanged (source : RecurringCursor) (request : RecurringRequest)
    (no : recurringEnabled source request = false) :
    performRecurringRequest source request = ⟨source, .local .refused, false, .root⟩ := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted => exact False.elim (recurring_refusal_refutes source request no admitted)
  | inr _ => rfl

theorem recurring_inspection_response (source : RecurringCursor) {kind} (ref : Ref source.kinds kind) :
    performRecurringRequest source (.local (.inspect kind ref.position)) =
      ⟨source, .local (.inspected (localReadout kind (source.read ref))), true, .root⟩ := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source (.local (.inspect kind ref.position)) with
  | inl admitted =>
    dsimp only [performRecurringAdmitted]
    rw [reference_position_injective admitted.ref ref admitted.exactPosition]
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

theorem recurring_response_length_bound (source : RecurringCursor) (request : RecurringRequest) :
    StrongPerimetralTurning.History.length (performRecurringRequest source request).history ≤ 1 := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted =>
    cases request with
    | «local» request => cases request <;> first | exact Nat.le_refl 1 | exact Nat.zero_le 1
    | compare one two => exact Nat.le_refl 1
  | inr _ => exact Nat.zero_le _

structure RecurringRequestedExecution (source : RecurringCursor) where
  cursor : RecurringCursor
  history : RecurringHistory source cursor
  report : Outcome RecurringEvent Unit

def runRecurringRequests (source : RecurringCursor) : List RecurringRequest → RecurringRequestedExecution source
  | [] => ⟨source, .root, .stop ()⟩
  | request :: rest =>
      let head := performRecurringRequest source request
      let suffix := runRecurringRequests head.cursor rest
      ⟨suffix.cursor, StrongPerimetralTurning.History.append head.history suffix.history,
        .step () head.allowed head.event suffix.report⟩
termination_by structural requests => requests

theorem recurring_all_futures_exact (source : RecurringCursor) (requests : List RecurringRequest) :
    (runRecurringRequests source requests).report = recurringContract.outcome source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    change Outcome.step () _ _ _ = Outcome.step () _ _ _
    rw [recurring_request_allowed_exact, recurring_request_event_exact]
    apply congrArg (Outcome.step () _ _)
    exact (ih _).trans (congrArg (fun state => recurringContract.outcome state rest)
      (recurring_request_next_exact source request))

theorem recurring_final_cursor_exact (source : RecurringCursor) (requests : List RecurringRequest) :
    (runRecurringRequests source requests).cursor =
      ConstitutiveSearch.Grouping.Continuation.run recurringContract.next source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    exact (ih _).trans (congrArg
      (fun state => ConstitutiveSearch.Grouping.Continuation.run recurringContract.next state rest)
      (recurring_request_next_exact source request))

theorem recurring_history_length_bound (source : RecurringCursor) (requests : List RecurringRequest) :
    StrongPerimetralTurning.History.length (runRecurringRequests source requests).history ≤ requests.length := by
  induction requests generalizing source with
  | nil => exact Nat.le_refl _
  | cons request rest ih =>
    change StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _) ≤ _
    exact Nat.le_trans (Nat.le_of_eq (StrongPerimetralTurning.History.length_append
      (performRecurringRequest source request).history
      (runRecurringRequests (performRecurringRequest source request).cursor rest).history))
      (Nat.le_trans (Nat.add_le_add (recurring_response_length_bound source request) (ih _))
        (Nat.le_of_eq (Nat.add_comm 1 rest.length)))

def RecurringRequestedExecution.continue {source} (prior : RecurringRequestedExecution source)
    (requests : List RecurringRequest) : RecurringRequestedExecution prior.cursor :=
  runRecurringRequests prior.cursor requests

def RecurringRequestedExecution.continuedHistory {source} (prior : RecurringRequestedExecution source)
    (suffix : RecurringRequestedExecution prior.cursor) : RecurringHistory source suffix.cursor :=
  StrongPerimetralTurning.History.append prior.history suffix.history

theorem recurring_continuation_exact {source} (prior : RecurringRequestedExecution source)
    (requests : List RecurringRequest) :
    (prior.continue requests).report = recurringContract.outcome prior.cursor requests :=
  recurring_all_futures_exact ..

theorem recurring_requests_preserve_reads (source : RecurringCursor) (requests : List RecurringRequest)
    {kind} (ref : Ref source.kinds kind) :
    (runRecurringRequests source requests).cursor.read
      ((recurringHistoryTransport (runRecurringRequests source requests).history).references ref) = source.read ref :=
  (recurringHistoryTransport (runRecurringRequests source requests).history).reads ref

theorem recurring_requests_preserve_distinction (source : RecurringCursor) (requests : List RecurringRequest)
    {kind} (one two : Ref source.kinds kind) (distinct : one ≠ two) :
    (recurringHistoryTransport (runRecurringRequests source requests).history).references one ≠
      (recurringHistoryTransport (runRecurringRequests source requests).history).references two :=
  fun same => distinct ((recurringHistoryTransport (runRecurringRequests source requests).history).injective _ _ same)

def firstRecurringInspection : Outcome RecurringEvent Unit → Option LocalReadout
  | .stop _ => none
  | .step _ _ (.local (.inspected value)) _ => some value
  | .step _ _ (.local (.emitted _)) _ => none
  | .step _ _ (.local (.relayed _)) _ => none
  | .step _ _ (.local (.received _)) _ => none
  | .step _ _ (.local .refused) _ => none
  | .step _ _ (.compared _) _ => none

theorem recurring_inspection_exact (source : RecurringCursor) {kind} (ref : Ref source.kinds kind) :
    recurringReferenceEvent source (.local (.inspect kind ref.position)) =
      .local (.inspected (localReadout kind (source.read ref))) :=
  (recurring_request_event_exact source _).symm.trans (congrArg RecurringResponse.event
    (recurring_inspection_response source ref))

/-- A differing full path record remains a permitted future distinction. This
necessary condition is not a complete physical memory-minimality result. -/
theorem recurring_futures_preserve_readout (source target : RecurringCursor) {kind}
    (one : Ref source.kinds kind) (two : Ref target.kinds kind)
    (samePosition : two.position = one.position)
    (same : FutureEquivalent recurringContract source target) :
    localReadout kind (source.read one) = localReadout kind (target.read two) := by
  have observed := congrArg firstRecurringInspection (same [.local (.inspect kind one.position)])
  dsimp only [FutureContract.outcome, recurringContract] at observed
  rw [recurring_inspection_exact source one, ← samePosition, recurring_inspection_exact target two] at observed
  exact Option.some.inj observed

def RecurringPair.admission {source : RecurringCursor} (pair : RecurringPair source) :
    RecurringAdmission source (.compare pair.first.position pair.second.position) :=
  ⟨⟨⟨pair.first, rfl⟩, pair.firstSignal, pair.firstArrival⟩,
    ⟨⟨pair.second, rfl⟩, pair.secondSignal, pair.secondArrival⟩, pair.distinct⟩

theorem recurring_pair_request_enabled {source : RecurringCursor} (pair : RecurringPair source) :
    recurringEnabled source (.compare pair.first.position pair.second.position) = true := by
  unfold recurringEnabled
  cases decideRecurringAdmission source (.compare pair.first.position pair.second.position) with
  | inl _ => rfl
  | inr impossible => exact False.elim (impossible pair.admission)

theorem recurring_pair_response_length {source : RecurringCursor} (pair : RecurringPair source) :
    StrongPerimetralTurning.History.length
      (performRecurringRequest source (.compare pair.first.position pair.second.position)).history = 1 := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source (.compare pair.first.position pair.second.position) with
  | inl admitted => rfl
  | inr impossible => exact False.elim (impossible pair.admission)

theorem recurring_pair_response_output {source : RecurringCursor} (pair : RecurringPair source) :
    (performRecurringRequest source (.compare pair.first.position pair.second.position)).event =
      .compared (recurringDifference source.values pair.first pair.second) := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source (.compare pair.first.position pair.second.position) with
  | inl admitted =>
    change RecurringEvent.compared admitted.pair.gap = _
    have one := reference_position_injective admitted.first.reading.ref pair.first admitted.first.reading.exactPosition
    have two := reference_position_injective admitted.second.reading.ref pair.second admitted.second.reading.exactPosition
    exact congrArg RecurringEvent.compared (admitted.pair.gap_exact.trans
      ((congrArg (fun first => recurringDifference source.values first admitted.second.reading.ref) one).trans
        (congrArg (recurringDifference source.values pair.first) two)))
  | inr impossible => exact False.elim (impossible pair.admission)

/-- The controller logs each request only after its shared response. There
is no precomputed future cursor or second execution to generate a schedule. -/
structure RecurringRepetition (source : RecurringCursor) where
  cursor : RecurringCursor
  history : RecurringHistory source cursor
  requests : List RecurringRequest
  report : Outcome RecurringEvent Unit

def repeatRecurringPair {source : RecurringCursor} (pair : RecurringPair source) :
    Nat → RecurringRepetition source
  | 0 => ⟨source, .root, [], .stop ()⟩
  | count + 1 =>
      let request := RecurringRequest.compare pair.first.position pair.second.position
      let head := performRecurringRequest source request
      let suffix := repeatRecurringPair (pair.transport head.history) count
      ⟨suffix.cursor, StrongPerimetralTurning.History.append head.history suffix.history,
        request :: suffix.requests, .step () head.allowed head.event suffix.report⟩
termination_by structural count => count

theorem recurring_repetition_all_futures {source : RecurringCursor} (pair : RecurringPair source) (count : Nat) :
    (repeatRecurringPair pair count).report =
      recurringContract.outcome source (repeatRecurringPair pair count).requests := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih =>
    change Outcome.step () _ _ _ = Outcome.step () _ _ _
    rw [recurring_request_allowed_exact, recurring_request_event_exact]
    apply congrArg (Outcome.step () _ _)
    exact (ih _).trans (congrArg (fun state => recurringContract.outcome state _)
      (recurring_request_next_exact source _))

theorem recurring_repetition_length {source : RecurringCursor} (pair : RecurringPair source) (count : Nat) :
    StrongPerimetralTurning.History.length (repeatRecurringPair pair count).history = count := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih =>
    change StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _) = _
    exact (StrongPerimetralTurning.History.length_append _ _).trans
      ((congrArg (fun head => head + StrongPerimetralTurning.History.length
        (repeatRecurringPair (pair.transport
          (performRecurringRequest source (.compare pair.first.position pair.second.position)).history) count).history)
        (recurring_pair_response_length pair)).trans ((congrArg (Nat.add 1) (ih _)).trans (Nat.add_comm 1 count)))

theorem recurring_repetition_requests_length {source : RecurringCursor} (pair : RecurringPair source) (count : Nat) :
    (repeatRecurringPair pair count).requests.length = count := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ (ih _)

theorem recurring_repetition_preserves_sources {source : RecurringCursor} (pair : RecurringPair source) (count : Nat) :
    (recurringHistoryTransport (repeatRecurringPair pair count).history).references pair.first ≠
      (recurringHistoryTransport (repeatRecurringPair pair count).history).references pair.second :=
  fun same => pair.distinct ((recurringHistoryTransport (repeatRecurringPair pair count).history).injective _ _ same)

def RecurringRequestedExecution.transportUsed {source} (run : RecurringRequestedExecution source)
    {one two : Occurrence source.kinds} (edge : RecurringUsed source.formation one two) :
    RecurringUsed run.cursor.formation ⟨one.1, (recurringHistoryTransport run.history).references one.2⟩
      ⟨two.1, (recurringHistoryTransport run.history).references two.2⟩ := recurringHistoryUsed run.history edge

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.resolveRecurringArrivalAt
#print axioms RelationalPerimeter.Relativity.Production.decideRecurringComparison
#print axioms RelationalPerimeter.Relativity.Production.decideRecurringAdmission
#print axioms RelationalPerimeter.Relativity.Production.recurringAdmissionOfEnabled
#print axioms RelationalPerimeter.Relativity.Production.recurring_refusal_refutes
#print axioms RelationalPerimeter.Relativity.Production.recurringContract
#print axioms RelationalPerimeter.Relativity.Production.recurring_same_arrival_refused
#print axioms RelationalPerimeter.Relativity.Production.performRecurringAdmitted
#print axioms RelationalPerimeter.Relativity.Production.performRecurringRequest
#print axioms RelationalPerimeter.Relativity.Production.recurring_request_next_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_request_event_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_request_allowed_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_refusal_is_unchanged
#print axioms RelationalPerimeter.Relativity.Production.recurring_inspection_response
#print axioms RelationalPerimeter.Relativity.Production.recurring_response_length_bound
#print axioms RelationalPerimeter.Relativity.Production.runRecurringRequests
#print axioms RelationalPerimeter.Relativity.Production.recurring_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_final_cursor_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_history_length_bound
#print axioms RelationalPerimeter.Relativity.Production.RecurringRequestedExecution.continue
#print axioms RelationalPerimeter.Relativity.Production.RecurringRequestedExecution.continuedHistory
#print axioms RelationalPerimeter.Relativity.Production.recurring_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_requests_preserve_reads
#print axioms RelationalPerimeter.Relativity.Production.recurring_requests_preserve_distinction
#print axioms RelationalPerimeter.Relativity.Production.recurring_futures_preserve_readout
#print axioms RelationalPerimeter.Relativity.Production.RecurringPair.admission
#print axioms RelationalPerimeter.Relativity.Production.recurring_pair_request_enabled
#print axioms RelationalPerimeter.Relativity.Production.recurring_pair_response_length
#print axioms RelationalPerimeter.Relativity.Production.recurring_pair_response_output
#print axioms RelationalPerimeter.Relativity.Production.repeatRecurringPair
#print axioms RelationalPerimeter.Relativity.Production.recurring_repetition_all_futures
#print axioms RelationalPerimeter.Relativity.Production.recurring_repetition_length
#print axioms RelationalPerimeter.Relativity.Production.recurring_repetition_requests_length
#print axioms RelationalPerimeter.Relativity.Production.recurring_repetition_preserves_sources
#print axioms RelationalPerimeter.Relativity.Production.RecurringRequestedExecution.transportUsed
/- AXIOM_AUDIT_END -/
