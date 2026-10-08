import RelationalPerimeter.Relativity.Production.AddressTransport
import RelationalPerimeter.Relativity.Production.TransportedContinuations
import RelationalPerimeter.Relativity.Production.RequestedExecution

/-!
# The complete local request contract through an independent exchange

The current occurrence transport determines addresses before each request.
An admitted action produces once in each presentation. Those same results
form the events, histories and next raccord. Inspection and refusal keep the
current raccord. Arbitrary finite interleavings are covered; no future tail
is used to decide or produce the head. The law remains the declared local
signal law, not a reconstruction of relativistic geometry.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

structure AddressedRaccord (source target : Cursor) where
  constitution : ConstitutedRaccord source target
  addresses : AddressTransport constitution.reading.references

def AddressedRaccord.reverse {source target} (raccord : AddressedRaccord source target) :
    AddressedRaccord target source := ⟨raccord.constitution.reverse, raccord.addresses.reverse⟩

def independentPairAddressed {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (original : IndependentPairProduction source first second)
    (reversed : IndependentPairProduction source second first) :
    AddressedRaccord original.cursor reversed.cursor :=
  ⟨independentPairConstitution original reversed, swapAddresses source.kinds firstKind secondKind⟩

def AddressedRaccord.afterProduction {source target} (raccord : AddressedRaccord source target)
    {kind} {instruction : Instruction source.kinds kind}
    (first : Production source instruction)
    (second : Production target (instruction.rename raccord.constitution.reading.references.forward)) :
    AddressedRaccord first.successor second.successor := by
  cases first with
  | mk firstDetermination firstSuccessor firstExact =>
    cases firstExact
    cases second with
    | mk secondDetermination secondSuccessor secondExact =>
      cases secondExact
      exact ⟨raccord.constitution.afterProduction ⟨firstDetermination, _, rfl⟩
        ⟨secondDetermination, _, rfl⟩, raccord.addresses.extend kind⟩

structure PairedLocalResponse (source target : Cursor) where
  first : LocalResponse source
  second : LocalResponse target
  raccord : AddressedRaccord first.cursor second.cursor
  eventExact : second.event = first.event
  allowedExact : second.allowed = first.allowed

def pairedActionResponse {source target} (raccord : AddressedRaccord source target)
    {kind} {instruction : Instruction source.kinds kind}
    (first : Production source instruction)
    (second : Production target (instruction.rename raccord.constitution.reading.references.forward))
    (event : Value kind → LocalEvent) : PairedLocalResponse source target :=
  ⟨⟨first.successor, event first.determination.1, true, cachedProductionHistory first⟩,
    ⟨second.successor, event second.determination.1, true, cachedProductionHistory second⟩,
    raccord.afterProduction first second,
    congrArg event (paired_outputs_exact raccord.constitution.reading first second), rfl⟩

def pairedAdmitted {source target} (raccord : AddressedRaccord source target) :
    (request : LocalRequest) → LocalAdmission source request → PairedLocalResponse source target
  | .emit _ _, admitted =>
    let instruction : Instruction source.kinds .signal := .emit admitted.1.ref admitted.2.ref
    let first := perform source instruction
    let second := perform target (instruction.rename raccord.constitution.reading.references.forward)
    pairedActionResponse raccord first second LocalEvent.emitted
  | .relay _ _, admitted =>
    let instruction : Instruction source.kinds .signal := .relay admitted.1.ref admitted.2.ref
    let first := perform source instruction
    let second := perform target (instruction.rename raccord.constitution.reading.references.forward)
    pairedActionResponse raccord first second LocalEvent.relayed
  | .receive _, admitted =>
    let instruction : Instruction source.kinds .reading := .receive admitted.ref
    let first := perform source instruction
    let second := perform target (instruction.rename raccord.constitution.reading.references.forward)
    pairedActionResponse raccord first second LocalEvent.received
  | .inspect kind _, admitted =>
    ⟨⟨source, .inspected (localReadout kind (source.read admitted.ref)), true, .root⟩,
      ⟨target, .inspected (localReadout kind
        (target.read (raccord.constitution.reading.references.forward admitted.ref))), true, .root⟩,
      raccord, congrArg (fun value => LocalEvent.inspected (localReadout kind value))
        (raccord.constitution.reading.reads admitted.ref), rfl⟩

theorem pairedAdmitted_source_exact {source target} (raccord : AddressedRaccord source target)
    (request : LocalRequest) (admitted : LocalAdmission source request) :
    (pairedAdmitted raccord request admitted).first = performAdmitted source request admitted := by
  cases request <;> rfl

theorem pairedAdmitted_target_exact {source target} (raccord : AddressedRaccord source target)
    (request : LocalRequest) (admitted : LocalAdmission source request) :
    (pairedAdmitted raccord request admitted).second =
      performAdmitted target (request.rename raccord.addresses.forward)
        (LocalAdmission.transport raccord.addresses request admitted) := by
  cases request <;> rfl

theorem performRequest_of_admitted (source : Cursor) (request : LocalRequest)
    (admitted : LocalAdmission source request) :
    performRequest source request = performAdmitted source request admitted := by
  unfold performRequest
  cases decideAdmission source request with
  | inl found => rw [LocalAdmission.unique source request found admitted]
  | inr impossible => exact False.elim (impossible admitted)

theorem performRequest_of_refused (source : Cursor) (request : LocalRequest)
    (impossible : LocalAdmission source request → False) :
    performRequest source request = ⟨source, .refused, false, .root⟩ := by
  unfold performRequest
  cases decideAdmission source request with
  | inl admitted => exact False.elim (impossible admitted)
  | inr _ => rfl

def pairedRequest {source target} (raccord : AddressedRaccord source target)
    (request : LocalRequest) : PairedLocalResponse source target :=
  match decideAdmission source request with
  | .inl admitted => pairedAdmitted raccord request admitted
  | .inr _ => ⟨⟨source, .refused, false, .root⟩,
      ⟨target, .refused, false, .root⟩, raccord, rfl, rfl⟩

theorem pairedRequest_source_exact {source target} (raccord : AddressedRaccord source target)
    (request : LocalRequest) : (pairedRequest raccord request).first = performRequest source request := by
  unfold pairedRequest
  cases decision : decideAdmission source request with
  | inl admitted =>
    exact (pairedAdmitted_source_exact raccord request admitted).trans
      (performRequest_of_admitted source request admitted).symm
  | inr impossible => exact (performRequest_of_refused source request impossible).symm

theorem pairedRequest_target_exact {source target} (raccord : AddressedRaccord source target)
    (request : LocalRequest) :
    (pairedRequest raccord request).second =
      performRequest target (request.rename raccord.addresses.forward) := by
  unfold pairedRequest
  cases decideAdmission source request with
  | inl admitted =>
    exact (pairedAdmitted_target_exact raccord request admitted).trans
      (performRequest_of_admitted target _ (LocalAdmission.transport raccord.addresses request admitted)).symm
  | inr impossible =>
    exact (performRequest_of_refused target _
      (fun admitted => impossible (LocalAdmission.returned raccord.addresses request admitted))).symm

def prefixRequest {source} (head : LocalResponse source)
    (suffix : RequestedExecution head.cursor) : RequestedExecution source :=
  ⟨suffix.cursor, StrongPerimetralTurning.History.append head.history suffix.history,
    .step () head.allowed head.event suffix.report⟩

structure CorrespondingRequests (source target : Cursor) where
  first : RequestedExecution source
  second : RequestedExecution target
  translated : List LocalRequest
  raccord : AddressedRaccord first.cursor second.cursor
  reportExact : second.report = first.report

def runCorrespondingRequests {source target} (raccord : AddressedRaccord source target) :
    List LocalRequest → CorrespondingRequests source target
  | [] => ⟨⟨source, .root, .stop ()⟩, ⟨target, .root, .stop ()⟩, [], raccord, rfl⟩
  | request :: rest =>
    let head := pairedRequest raccord request
    let suffix := runCorrespondingRequests head.raccord rest
    ⟨prefixRequest head.first suffix.first, prefixRequest head.second suffix.second,
      request.rename raccord.addresses.forward :: suffix.translated, suffix.raccord, by
        change Outcome.step () head.second.allowed head.second.event suffix.second.report =
          Outcome.step () head.first.allowed head.first.event suffix.first.report
        rw [head.allowedExact, head.eventExact, suffix.reportExact]⟩
termination_by structural requests => requests

theorem correspondingRequests_source_exact {source target} (raccord : AddressedRaccord source target)
    (requests : List LocalRequest) :
    (runCorrespondingRequests raccord requests).first = runRequests source requests := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := pairedRequest raccord request
    exact (congrArg (prefixRequest head.first) (ih head.raccord)).trans (by
      change prefixRequest (pairedRequest raccord request).first
        (runRequests (pairedRequest raccord request).first.cursor rest) = _
      rw [pairedRequest_source_exact]
      rfl)

theorem correspondingRequests_target_exact {source target} (raccord : AddressedRaccord source target)
    (requests : List LocalRequest) :
    (runCorrespondingRequests raccord requests).second =
      runRequests target (runCorrespondingRequests raccord requests).translated := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := pairedRequest raccord request
    let suffix := runCorrespondingRequests head.raccord rest
    exact (congrArg (prefixRequest head.second) (ih head.raccord)).trans
      (congrArg (fun response : LocalResponse target =>
        prefixRequest response (runRequests response.cursor suffix.translated))
        (pairedRequest_target_exact raccord request))

theorem transported_all_futures_exact {source target} (raccord : AddressedRaccord source target)
    (requests : List LocalRequest) :
    localContract.outcome target (runCorrespondingRequests raccord requests).translated =
      localContract.outcome source requests := by
  have same := (runCorrespondingRequests raccord requests).reportExact
  rw [correspondingRequests_source_exact, correspondingRequests_target_exact,
    requests_all_futures_exact, requests_all_futures_exact] at same
  exact same

theorem translated_length_exact {source target} (raccord : AddressedRaccord source target)
    (requests : List LocalRequest) :
    (runCorrespondingRequests raccord requests).translated.length = requests.length := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih => exact congrArg Nat.succ (ih (pairedRequest raccord request).raccord)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.AddressedRaccord
#print axioms RelationalPerimeter.Relativity.Production.AddressedRaccord.reverse
#print axioms RelationalPerimeter.Relativity.Production.independentPairAddressed
#print axioms RelationalPerimeter.Relativity.Production.AddressedRaccord.afterProduction
#print axioms RelationalPerimeter.Relativity.Production.PairedLocalResponse
#print axioms RelationalPerimeter.Relativity.Production.pairedActionResponse
#print axioms RelationalPerimeter.Relativity.Production.pairedAdmitted
#print axioms RelationalPerimeter.Relativity.Production.pairedAdmitted_source_exact
#print axioms RelationalPerimeter.Relativity.Production.pairedAdmitted_target_exact
#print axioms RelationalPerimeter.Relativity.Production.performRequest_of_admitted
#print axioms RelationalPerimeter.Relativity.Production.performRequest_of_refused
#print axioms RelationalPerimeter.Relativity.Production.pairedRequest
#print axioms RelationalPerimeter.Relativity.Production.pairedRequest_source_exact
#print axioms RelationalPerimeter.Relativity.Production.pairedRequest_target_exact
#print axioms RelationalPerimeter.Relativity.Production.prefixRequest
#print axioms RelationalPerimeter.Relativity.Production.CorrespondingRequests
#print axioms RelationalPerimeter.Relativity.Production.runCorrespondingRequests
#print axioms RelationalPerimeter.Relativity.Production.correspondingRequests_source_exact
#print axioms RelationalPerimeter.Relativity.Production.correspondingRequests_target_exact
#print axioms RelationalPerimeter.Relativity.Production.transported_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.translated_length_exact
/- AXIOM_AUDIT_END -/
