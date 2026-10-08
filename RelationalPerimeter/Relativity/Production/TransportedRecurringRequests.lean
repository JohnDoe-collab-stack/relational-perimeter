import RelationalPerimeter.Relativity.Production.RecurringPresentation
import RelationalPerimeter.Relativity.Production.RecurringFutures

/-!
# All recurring requests through the current constituted presentation

Positive receptions, all local admissions and exact refusals return through
the occurrence transport. A paired head executes once in each presentation;
its cached outputs build both events, histories and the next raccord before
the suffix runs. Address translation follows that current raccord, not a
frozen initial permutation. No physical grouping or geometry is claimed.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

theorem Arrived.find_exact {context} {values : Values Value context}
    {past : Formed (context := context) values} {reading signal} (arrival : Arrived past reading signal) :
    findArrival past reading = some ⟨signal, arrival⟩ := by
  induction arrival with
  | received past signal => rfl
  | inherited role old ih => change (findArrival _ _).map _ = _; rw [ih]; rfl

theorem InstrumentArrived.find_exact {context} {values : Values Value context}
    {past : InstrumentFormation (context := context) values} {reading signal}
    (arrival : InstrumentArrived past reading signal) : findInstrumentArrival past reading = some ⟨signal, arrival⟩ := by
  induction arrival with
  | priorComparison role old => change (findArrival _ _).map _ = _; rw [old.find_exact]; rfl
  | received past signal => rfl
  | inherited role old ih => change (findInstrumentArrival _ _).map _ = _; rw [ih]; rfl

theorem RecurringArrival.find_exact {context} {values : Values Value context}
    {past : RecurringFormation values} {reading signal} (arrival : RecurringArrival past reading signal) :
    findRecurringArrival past reading = some ⟨signal, arrival⟩ := by
  induction arrival with
  | fromCursor old => change (findArrival _ _).map _ = _; rw [old.find_exact]; rfl
  | fromInstrument old => change (findInstrumentArrival _ _).map _ = _; rw [old.find_exact]; rfl
  | received past signal => rfl
  | throughSignal role old ih => change (findRecurringArrival _ _).map _ = _; rw [ih]; rfl
  | throughComparison role old ih => change (findRecurringArrival _ _).map _ = _; rw [ih]; rfl

theorem RecurringArrivalAt.unique {source address} (one two : RecurringArrivalAt source address) : one = two := by
  cases one with
  | mk first firstSignal firstArrival =>
    cases two with
    | mk second secondSignal secondArrival =>
      cases ReferenceAt.unique first second
      have same := Option.some.inj (firstArrival.find_exact.symm.trans secondArrival.find_exact)
      exact congrArg (fun found => RecurringArrivalAt.mk first found.1 found.2) same

theorem RecurringAdmission.unique (source : RecurringCursor) (request : RecurringRequest)
    (one two : RecurringAdmission source request) : one = two := by
  cases request with
  | «local» request =>
    cases request with
    | emit _ _ => exact Prod.ext (one.1.unique two.1) (one.2.unique two.2)
    | relay _ _ => exact Prod.ext (one.1.unique two.1) (one.2.unique two.2)
    | receive _ => exact ReferenceAt.unique one two
    | inspect _ _ => exact ReferenceAt.unique one two
  | compare _ _ =>
    cases one with
    | mk first second distinct =>
      cases two with
      | mk otherFirst otherSecond otherDistinct =>
        cases first.unique otherFirst
        cases second.unique otherSecond
        rfl

def RecurringRequest.rename (mapping : Nat → Nat) : RecurringRequest → RecurringRequest
  | .local request => .local (request.rename mapping)
  | .compare first second => .compare (mapping first) (mapping second)

theorem RecurringRequest.rename_returns (forward backward : Nat → Nat)
    (returned : ∀ address, backward (forward address) = address) (request : RecurringRequest) :
    (request.rename forward).rename backward = request := by
  cases request with
  | «local» request => exact congrArg RecurringRequest.local (request.rename_returns forward backward returned)
  | compare first second =>
    change RecurringRequest.compare (backward (forward first)) (backward (forward second)) = _
    rw [returned first, returned second]

def RecurringArrivalAt.rename {source target} (raccord : AddressedRecurringRaccord source target)
    {address} (arrival : RecurringArrivalAt source address) :
    RecurringArrivalAt target (raccord.addresses.forward address) :=
  ⟨ReferenceAt.transport raccord.addresses arrival.reading, raccord.constitution.references.forward arrival.signal,
    raccord.constitution.forwardArrival arrival.arrival⟩

def RecurringAdmission.rename {source target} (raccord : AddressedRecurringRaccord source target) :
    (request : RecurringRequest) → RecurringAdmission source request →
      RecurringAdmission target (request.rename raccord.addresses.forward)
  | .local (.emit _ _), admitted => ⟨ReferenceAt.transport raccord.addresses admitted.1, ReferenceAt.transport raccord.addresses admitted.2⟩
  | .local (.relay _ _), admitted => ⟨ReferenceAt.transport raccord.addresses admitted.1, ReferenceAt.transport raccord.addresses admitted.2⟩
  | .local (.receive _), admitted => ReferenceAt.transport raccord.addresses admitted
  | .local (.inspect _ _), admitted => ReferenceAt.transport raccord.addresses admitted
  | .compare _ _, admitted =>
    ⟨admitted.first.rename raccord, admitted.second.rename raccord, fun same => admitted.distinct
      ((raccord.constitution.references.forwardBackward admitted.first.reading.ref).symm.trans
        ((congrArg raccord.constitution.references.backward same).trans
          (raccord.constitution.references.forwardBackward admitted.second.reading.ref)))⟩

def RecurringAdmission.returned {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) (admitted : RecurringAdmission target (request.rename raccord.addresses.forward)) :
    RecurringAdmission source request :=
  (request.rename_returns _ _ raccord.addresses.forwardBackward) ▸
    RecurringAdmission.rename raccord.reverse _ admitted

theorem recurring_transported_admission_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) :
    recurringEnabled target (request.rename raccord.addresses.forward) = recurringEnabled source request := by
  unfold recurringEnabled
  cases decideRecurringAdmission source request with
  | inl admitted =>
    cases decideRecurringAdmission target (request.rename raccord.addresses.forward) with
    | inl _ => rfl
    | inr impossible => exact False.elim (impossible (RecurringAdmission.rename raccord request admitted))
  | inr impossible =>
    cases decideRecurringAdmission target (request.rename raccord.addresses.forward) with
    | inl admitted => exact False.elim (impossible (RecurringAdmission.returned raccord request admitted))
    | inr _ => rfl

theorem recurring_perform_of_admitted (source : RecurringCursor) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) :
    performRecurringRequest source request = performRecurringAdmitted source request admitted := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source request with
  | inl found => rw [RecurringAdmission.unique source request found admitted]
  | inr impossible => exact False.elim (impossible admitted)

theorem recurring_perform_of_refused (source : RecurringCursor) (request : RecurringRequest)
    (impossible : RecurringAdmission source request → False) :
    performRecurringRequest source request = ⟨source, .local .refused, false, .root⟩ := by
  unfold performRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted => exact False.elim (impossible admitted)
  | inr _ => rfl

structure PairedRecurringResponse (source target : RecurringCursor) where
  first : RecurringResponse source
  second : RecurringResponse target
  raccord : AddressedRecurringRaccord first.cursor second.cursor
  eventExact : second.event = first.event
  allowedExact : second.allowed = first.allowed

def pairedRecurringAction {source target} (raccord : AddressedRecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (one : RecurringProduction source action)
    (two : RecurringProduction target (action.rename raccord.constitution))
    (event : Value kind → RecurringEvent) : PairedRecurringResponse source target :=
  ⟨⟨one.successor, event one.determination.1, true, recurringProductionHistory one⟩,
    ⟨two.successor, event two.determination.1, true, recurringProductionHistory two⟩,
    raccord.afterProduction one two, congrArg event (recurring_paired_outputs_exact raccord.constitution one two), rfl⟩

def pairedRecurringAdmitted {source target} (raccord : AddressedRecurringRaccord source target) :
    (request : RecurringRequest) → RecurringAdmission source request → PairedRecurringResponse source target
  | .local (.emit _ _), admitted =>
    let action := RecurringAction.signal (.emit admitted.1.ref admitted.2.ref)
    let one := performRecurring source action
    let two := performRecurring target (action.rename raccord.constitution)
    pairedRecurringAction raccord one two (fun value => .local (.emitted value))
  | .local (.relay _ _), admitted =>
    let action := RecurringAction.signal (.relay admitted.1.ref admitted.2.ref)
    let one := performRecurring source action
    let two := performRecurring target (action.rename raccord.constitution)
    pairedRecurringAction raccord one two (fun value => .local (.relayed value))
  | .local (.receive _), admitted =>
    let action := RecurringAction.signal (.receive admitted.ref)
    let one := performRecurring source action
    let two := performRecurring target (action.rename raccord.constitution)
    pairedRecurringAction raccord one two (fun value => .local (.received value))
  | .local (.inspect kind _), admitted =>
    ⟨⟨source, .local (.inspected (localReadout kind (source.read admitted.ref))), true, .root⟩,
      ⟨target, .local (.inspected (localReadout kind (target.read (raccord.constitution.references.forward admitted.ref)))), true, .root⟩,
      raccord, congrArg (fun value => RecurringEvent.local (.inspected (localReadout kind value)))
        (raccord.constitution.reads admitted.ref), rfl⟩
  | .compare _ _, admitted =>
    let action := RecurringAction.compare admitted.pair
    let one := performRecurring source action
    let two := performRecurring target (action.rename raccord.constitution)
    pairedRecurringAction raccord one two RecurringEvent.compared

theorem pairedRecurringAdmitted_source_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) (admitted : RecurringAdmission source request) :
    (pairedRecurringAdmitted raccord request admitted).first = performRecurringAdmitted source request admitted := by
  cases request with
  | «local» request => cases request <;> rfl
  | compare _ _ => rfl

theorem pairedRecurringAdmitted_target_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) (admitted : RecurringAdmission source request) :
    (pairedRecurringAdmitted raccord request admitted).second =
      performRecurringAdmitted target (request.rename raccord.addresses.forward)
        (RecurringAdmission.rename raccord request admitted) := by
  cases request with
  | «local» request => cases request <;> rfl
  | compare _ _ => rfl

def pairedRecurringRequest {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) : PairedRecurringResponse source target :=
  match decideRecurringAdmission source request with
  | .inl admitted => pairedRecurringAdmitted raccord request admitted
  | .inr _ => ⟨⟨source, .local .refused, false, .root⟩,
      ⟨target, .local .refused, false, .root⟩, raccord, rfl, rfl⟩

theorem pairedRecurringRequest_source_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) : (pairedRecurringRequest raccord request).first = performRecurringRequest source request := by
  unfold pairedRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted =>
    exact (pairedRecurringAdmitted_source_exact raccord request admitted).trans
      (recurring_perform_of_admitted source request admitted).symm
  | inr impossible => exact (recurring_perform_of_refused source request impossible).symm

theorem pairedRecurringRequest_target_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) : (pairedRecurringRequest raccord request).second =
      performRecurringRequest target (request.rename raccord.addresses.forward) := by
  unfold pairedRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted =>
    exact (pairedRecurringAdmitted_target_exact raccord request admitted).trans
      (recurring_perform_of_admitted target _ (RecurringAdmission.rename raccord request admitted)).symm
  | inr impossible =>
    exact (recurring_perform_of_refused target _
      (fun admitted => impossible (RecurringAdmission.returned raccord request admitted))).symm

def prefixRecurringRequest {source} (head : RecurringResponse source)
    (suffix : RecurringRequestedExecution head.cursor) : RecurringRequestedExecution source :=
  ⟨suffix.cursor, StrongPerimetralTurning.History.append head.history suffix.history,
    .step () head.allowed head.event suffix.report⟩

structure CorrespondingRecurringRequests (source target : RecurringCursor) where
  first : RecurringRequestedExecution source
  second : RecurringRequestedExecution target
  translated : List RecurringRequest
  raccord : AddressedRecurringRaccord first.cursor second.cursor
  reportExact : second.report = first.report

def runCorrespondingRecurring {source target} (raccord : AddressedRecurringRaccord source target) :
    List RecurringRequest → CorrespondingRecurringRequests source target
  | [] => ⟨⟨source, .root, .stop ()⟩, ⟨target, .root, .stop ()⟩, [], raccord, rfl⟩
  | request :: rest =>
    let head := pairedRecurringRequest raccord request
    let suffix := runCorrespondingRecurring head.raccord rest
    ⟨prefixRecurringRequest head.first suffix.first, prefixRecurringRequest head.second suffix.second,
      request.rename raccord.addresses.forward :: suffix.translated, suffix.raccord, by
        change Outcome.step () head.second.allowed head.second.event suffix.second.report =
          Outcome.step () head.first.allowed head.first.event suffix.first.report
        rw [head.allowedExact, head.eventExact, suffix.reportExact]⟩
termination_by structural requests => requests

theorem correspondingRecurring_source_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) :
    (runCorrespondingRecurring raccord requests).first = runRecurringRequests source requests := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := pairedRecurringRequest raccord request
    exact (congrArg (prefixRecurringRequest head.first) (ih head.raccord)).trans (by
      change prefixRecurringRequest (pairedRecurringRequest raccord request).first
        (runRecurringRequests (pairedRecurringRequest raccord request).first.cursor rest) = _
      rw [pairedRecurringRequest_source_exact]; rfl)

theorem correspondingRecurring_target_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) :
    (runCorrespondingRecurring raccord requests).second =
      runRecurringRequests target (runCorrespondingRecurring raccord requests).translated := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := pairedRecurringRequest raccord request
    let suffix := runCorrespondingRecurring head.raccord rest
    exact (congrArg (prefixRecurringRequest head.second) (ih head.raccord)).trans
      (congrArg (fun response : RecurringResponse target =>
        prefixRecurringRequest response (runRecurringRequests response.cursor suffix.translated))
        (pairedRecurringRequest_target_exact raccord request))

theorem recurring_transported_all_futures {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) :
    recurringContract.outcome target (runCorrespondingRecurring raccord requests).translated =
      recurringContract.outcome source requests := by
  have same := (runCorrespondingRecurring raccord requests).reportExact
  rw [correspondingRecurring_source_exact, correspondingRecurring_target_exact,
    recurring_all_futures_exact, recurring_all_futures_exact] at same
  exact same

theorem recurring_translated_length {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) : (runCorrespondingRecurring raccord requests).translated.length = requests.length := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih => exact congrArg Nat.succ (ih (pairedRecurringRequest raccord request).raccord)

def CorrespondingRecurringRequests.continue {source target} (run : CorrespondingRecurringRequests source target)
    (requests : List RecurringRequest) : CorrespondingRecurringRequests run.first.cursor run.second.cursor :=
  runCorrespondingRecurring run.raccord requests

def CorrespondingRecurringRequests.firstContinuedHistory {source target}
    (run : CorrespondingRecurringRequests source target)
    (suffix : CorrespondingRecurringRequests run.first.cursor run.second.cursor) :
    RecurringHistory source suffix.first.cursor :=
  StrongPerimetralTurning.History.append run.first.history suffix.first.history

def CorrespondingRecurringRequests.secondContinuedHistory {source target}
    (run : CorrespondingRecurringRequests source target)
    (suffix : CorrespondingRecurringRequests run.first.cursor run.second.cursor) :
    RecurringHistory target suffix.second.cursor :=
  StrongPerimetralTurning.History.append run.second.history suffix.second.history

theorem recurring_continued_history_uses_cached_suffix {source target}
    (run : CorrespondingRecurringRequests source target)
    (suffix : CorrespondingRecurringRequests run.first.cursor run.second.cursor) :
    run.firstContinuedHistory suffix = StrongPerimetralTurning.History.append run.first.history suffix.first.history ∧
      run.secondContinuedHistory suffix = StrongPerimetralTurning.History.append run.second.history suffix.second.history :=
  ⟨rfl, rfl⟩

theorem recurring_corresponding_continuation_exact {source target}
    (run : CorrespondingRecurringRequests source target) (requests : List RecurringRequest) :
    (run.continue requests).first = runRecurringRequests run.first.cursor requests ∧
      (run.continue requests).second = runRecurringRequests run.second.cursor (run.continue requests).translated :=
  ⟨correspondingRecurring_source_exact run.raccord requests, correspondingRecurring_target_exact run.raccord requests⟩

/-- Counts produced steps, not evaluation work or physical time. -/
def recurringAdmittedStepCount : RecurringRequest → Nat
  | .local (.emit _ _) => 1
  | .local (.relay _ _) => 1
  | .local (.receive _) => 1
  | .local (.inspect _ _) => 0
  | .compare _ _ => 1

theorem recurring_admitted_history_length (source : RecurringCursor) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) :
    StrongPerimetralTurning.History.length (performRecurringAdmitted source request admitted).history =
      recurringAdmittedStepCount request := by
  cases request with
  | «local» request => cases request <;> rfl
  | compare _ _ => rfl

theorem paired_admitted_recurring_history_lengths {source target}
    (raccord : AddressedRecurringRaccord source target) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) :
    StrongPerimetralTurning.History.length (pairedRecurringAdmitted raccord request admitted).second.history =
      StrongPerimetralTurning.History.length (pairedRecurringAdmitted raccord request admitted).first.history := by
  apply Eq.trans (congrArg (fun response : RecurringResponse target =>
    StrongPerimetralTurning.History.length response.history)
    (pairedRecurringAdmitted_target_exact raccord request admitted))
  apply Eq.trans _ (congrArg (fun response : RecurringResponse source =>
    StrongPerimetralTurning.History.length response.history)
    (pairedRecurringAdmitted_source_exact raccord request admitted)).symm
  have lengthRename :
      recurringAdmittedStepCount (request.rename raccord.addresses.forward) = recurringAdmittedStepCount request := by
    cases request with
    | «local» request => cases request <;> rfl
    | compare _ _ => rfl
  exact (recurring_admitted_history_length target _ (RecurringAdmission.rename raccord request admitted)).trans
    (lengthRename.trans (recurring_admitted_history_length source request admitted).symm)

theorem paired_recurring_history_lengths {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) :
    StrongPerimetralTurning.History.length (pairedRecurringRequest raccord request).second.history =
      StrongPerimetralTurning.History.length (pairedRecurringRequest raccord request).first.history := by
  unfold pairedRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted => exact paired_admitted_recurring_history_lengths raccord request admitted
  | inr _ => rfl

theorem corresponding_recurring_history_lengths {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) :
    StrongPerimetralTurning.History.length (runCorrespondingRecurring raccord requests).second.history =
      StrongPerimetralTurning.History.length (runCorrespondingRecurring raccord requests).first.history := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := pairedRecurringRequest raccord request
    let suffix := runCorrespondingRecurring head.raccord rest
    change StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _) =
      StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _)
    exact (StrongPerimetralTurning.History.length_append head.second.history suffix.second.history).trans
      ((congrArg (fun length => length + StrongPerimetralTurning.History.length suffix.second.history)
        (paired_recurring_history_lengths raccord request)).trans
        ((congrArg (Nat.add (StrongPerimetralTurning.History.length head.first.history)) (ih head.raccord)).trans
          (StrongPerimetralTurning.History.length_append head.first.history suffix.first.history).symm))

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Arrived.find_exact
#print axioms RelationalPerimeter.Relativity.Production.InstrumentArrived.find_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrival.find_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrivalAt.unique
#print axioms RelationalPerimeter.Relativity.Production.RecurringAdmission.unique
#print axioms RelationalPerimeter.Relativity.Production.RecurringRequest.rename
#print axioms RelationalPerimeter.Relativity.Production.RecurringRequest.rename_returns
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrivalAt.rename
#print axioms RelationalPerimeter.Relativity.Production.RecurringAdmission.rename
#print axioms RelationalPerimeter.Relativity.Production.RecurringAdmission.returned
#print axioms RelationalPerimeter.Relativity.Production.recurring_transported_admission_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_perform_of_admitted
#print axioms RelationalPerimeter.Relativity.Production.recurring_perform_of_refused
#print axioms RelationalPerimeter.Relativity.Production.PairedRecurringResponse
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringAction
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringAdmitted
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringAdmitted_source_exact
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringAdmitted_target_exact
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringRequest
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringRequest_source_exact
#print axioms RelationalPerimeter.Relativity.Production.pairedRecurringRequest_target_exact
#print axioms RelationalPerimeter.Relativity.Production.prefixRecurringRequest
#print axioms RelationalPerimeter.Relativity.Production.CorrespondingRecurringRequests
#print axioms RelationalPerimeter.Relativity.Production.runCorrespondingRecurring
#print axioms RelationalPerimeter.Relativity.Production.correspondingRecurring_source_exact
#print axioms RelationalPerimeter.Relativity.Production.correspondingRecurring_target_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_transported_all_futures
#print axioms RelationalPerimeter.Relativity.Production.recurring_translated_length
#print axioms RelationalPerimeter.Relativity.Production.CorrespondingRecurringRequests.continue
#print axioms RelationalPerimeter.Relativity.Production.CorrespondingRecurringRequests.firstContinuedHistory
#print axioms RelationalPerimeter.Relativity.Production.CorrespondingRecurringRequests.secondContinuedHistory
#print axioms RelationalPerimeter.Relativity.Production.recurring_continued_history_uses_cached_suffix
#print axioms RelationalPerimeter.Relativity.Production.recurring_corresponding_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.recurringAdmittedStepCount
#print axioms RelationalPerimeter.Relativity.Production.recurring_admitted_history_length
#print axioms RelationalPerimeter.Relativity.Production.paired_admitted_recurring_history_lengths
#print axioms RelationalPerimeter.Relativity.Production.paired_recurring_history_lengths
#print axioms RelationalPerimeter.Relativity.Production.corresponding_recurring_history_lengths
/- AXIOM_AUDIT_END -/
