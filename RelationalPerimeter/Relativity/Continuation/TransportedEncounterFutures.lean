import RelationalPerimeter.Relativity.Continuation.EncounterFutures
import RelationalPerimeter.Relativity.Production.CouplingDescriptions

/-!
# Entire coupling futures through evolving exact state descriptions

Signal actions, deliveries, coupling, inspections and refusals all follow the
present raccord. Occupied arrivals and the instrument are carried as well as
resource addresses. Each admitted source action executes once; its cached
role and output form the other presentation and both successors. Translation
continues from that new raccord, never from a frozen address permutation.
This closes the declared local contract, not a physical propagation network.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Continuation.Encounter
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def Request.rename (mapping : Nat → Nat) : Request → Request
  | .local request => .local (request.rename mapping)
  | .deliver port signal => .deliver port (mapping signal)
  | .encounter => .encounter

theorem Request.rename_returns (forward backward : Nat → Nat)
    (returned : ∀ address, backward (forward address) = address) (request : Request) :
    (request.rename forward).rename backward = request := by
  cases request with
  | «local» request => exact congrArg Request.local (request.rename_returns _ _ returned)
  | deliver port signal => exact congrArg (Request.deliver port) (returned signal)
  | encounter => rfl

theorem vacant_unique {source} {phase : Phase source} {port} (one two : Vacant phase port) : one = two := by
  cases one <;> cases two <;> rfl

theorem encounter_admission_unique {source} (one two : EncounterAdmission source) : one = two := by
  have phases := one.ready.symm.trans two.ready
  have same : one.pair = two.pair := by injection phases
  cases one with
  | mk pair ready => cases two with
    | mk other otherReady => cases same; rfl

theorem admission_unique (source : State) (request : Request) (one two : Admission source request) : one = two := by
  cases request with
  | «local» request => exact RecurringAdmission.unique source.cursor (.local request) one two
  | deliver port signal => exact Prod.ext (ReferenceAt.unique one.1 two.1) (vacant_unique one.2 two.2)
  | encounter => exact encounter_admission_unique one two

def Admission.rename {source target} (raccord : StateRaccord source target) :
    (request : Request) → Admission source request → Admission target (request.rename raccord.resources.addresses.forward)
  | .local request, admitted => RecurringAdmission.rename raccord.resources (.local request) admitted
  | .deliver _ _, admitted =>
    ⟨ReferenceAt.transport raccord.resources.addresses admitted.1,
      admitted.2.rename raccord.resources.constitution raccord.phaseExact⟩
  | .encounter, admitted => EncounterAdmission.rename raccord admitted

def Admission.returned {source target} (raccord : StateRaccord source target) (request : Request)
    (admitted : Admission target (request.rename raccord.resources.addresses.forward)) : Admission source request :=
  (request.rename_returns _ _ raccord.resources.addresses.forwardBackward) ▸ Admission.rename raccord.reverse _ admitted

theorem transported_admission_exact {source target} (raccord : StateRaccord source target) (request : Request) :
    enabled target (request.rename raccord.resources.addresses.forward) = enabled source request := by
  unfold enabled
  cases decide source request with
  | inl admitted => cases decide target (request.rename raccord.resources.addresses.forward) with
    | inl _ => rfl
    | inr no => exact False.elim (no (Admission.rename raccord request admitted))
  | inr no => cases decide target (request.rename raccord.resources.addresses.forward) with
    | inl admitted => exact False.elim (no (Admission.returned raccord request admitted))
    | inr _ => rfl

theorem admitted_response_exact (source : State) (request : Request) (admitted : Admission source request) :
    respond source request = respondAdmitted source request admitted := by
  unfold respond
  cases decide source request with
  | inl other => rw [admission_unique source request other admitted]
  | inr no => exact False.elim (no admitted)

def transportSignal {source target} (raccord : StateRaccord source target)
    {kind} {instruction : Instruction source.cursor.kinds kind} (one : SignalProduction source instruction) :
    SignalProduction target (instruction.rename raccord.resources.constitution.references.forward) :=
  ⟨transportRecurringProduction raccord.resources.constitution one.head⟩

def transportDelivery {source target} (raccord : StateRaccord source target) {port signal vacant}
    (one : DeliveryProduction source port signal vacant) :
    DeliveryProduction target port (raccord.resources.constitution.references.forward signal)
      (vacant.rename raccord.resources.constitution raccord.phaseExact) :=
  ⟨transportRecurringProduction raccord.resources.constitution one.head⟩

def transportEncounter {source target} (raccord : StateRaccord source target) {admitted}
    (one : EncounterProduction source admitted) : EncounterProduction target (admitted.rename raccord) :=
  ⟨transportRecurringProduction raccord.resources.constitution one.head⟩

theorem transported_signal_exact {source target} (raccord : StateRaccord source target)
    {kind} {instruction : Instruction source.cursor.kinds kind} (one : SignalProduction source instruction) :
    transportSignal raccord one = performSignal target (instruction.rename raccord.resources.constitution.references.forward) :=
  congrArg SignalProduction.mk (transported_production_exact raccord.resources.constitution one.head)

theorem transported_delivery_exact {source target} (raccord : StateRaccord source target) {port signal vacant}
    (one : DeliveryProduction source port signal vacant) : transportDelivery raccord one =
      performDelivery target port (raccord.resources.constitution.references.forward signal)
        (vacant.rename raccord.resources.constitution raccord.phaseExact) :=
  congrArg DeliveryProduction.mk (transported_production_exact raccord.resources.constitution one.head)

theorem transported_encounter_exact {source target} (raccord : StateRaccord source target) {admitted}
    (one : EncounterProduction source admitted) :
    transportEncounter raccord one = performEncounter target (admitted.rename raccord) := by
  with_unfolding_all
    exact congrArg EncounterProduction.mk (transported_production_exact raccord.resources.constitution one.head)

structure PairedResponse (source target : State) where
  first : Response source
  second : Response target
  raccord : StateRaccord first.state second.state
  eventExact : second.event = first.event
  allowedExact : second.allowed = first.allowed

def pairedSignal {source target} (raccord : StateRaccord source target)
    {kind} {instruction : Instruction source.cursor.kinds kind} (one : SignalProduction source instruction)
    (event : Value kind → Event) : PairedResponse source target :=
  let two := transportSignal raccord one
  ⟨⟨one.next, event one.head.determination.1, true, .extend .root (.signal one)⟩,
    ⟨two.next, event two.head.determination.1, true, .extend .root (.signal two)⟩,
    raccord.afterSignal one two, rfl, rfl⟩

def pairedDelivery {source target} (raccord : StateRaccord source target) {port signal vacant}
    (one : DeliveryProduction source port signal vacant) : PairedResponse source target :=
  let two := transportDelivery raccord one
  ⟨⟨one.next, .delivered port one.head.determination.1, true, .extend .root (.delivered one)⟩,
    ⟨two.next, .delivered port two.head.determination.1, true, .extend .root (.delivered two)⟩,
    raccord.afterDelivery one two, rfl, rfl⟩

def pairedEncounter {source target} (raccord : StateRaccord source target) {admitted}
    (one : EncounterProduction source admitted) : PairedResponse source target :=
  let two := transportEncounter raccord one
  ⟨⟨one.next, .encountered one.head.determination.1, true, .extend .root (.encountered one)⟩,
    ⟨two.next, .encountered two.head.determination.1, true, .extend .root (.encountered two)⟩,
    raccord.afterEncounter one two, rfl, rfl⟩

def sharedCouplingAdmitted {source target} (raccord : StateRaccord source target) :
    (request : Request) → Admission source request → PairedResponse source target
  | .local (.emit _ _), admitted =>
    pairedSignal raccord (performSignal source (.emit admitted.1.ref admitted.2.ref)) (fun value => .local (.emitted value))
  | .local (.relay _ _), admitted =>
    pairedSignal raccord (performSignal source (.relay admitted.1.ref admitted.2.ref)) (fun value => .local (.relayed value))
  | .local (.receive _), admitted =>
    pairedSignal raccord (performSignal source (.receive admitted.ref)) (fun value => .local (.received value))
  | .local (.inspect kind _), admitted =>
    ⟨⟨source, .local (.inspected (localReadout kind (source.cursor.read admitted.ref))), true, .root⟩,
      ⟨target, .local (.inspected (localReadout kind (target.cursor.read (raccord.resources.constitution.references.forward admitted.ref)))), true, .root⟩,
      raccord, congrArg (fun value => Event.local (.inspected (localReadout kind value)))
        (raccord.resources.constitution.reads admitted.ref), rfl⟩
  | .deliver port _, admitted => pairedDelivery raccord (performDelivery source port admitted.1.ref admitted.2)
  | .encounter, admitted => pairedEncounter raccord (performEncounter source admitted)

theorem shared_admitted_source_exact {source target} (raccord : StateRaccord source target)
    (request : Request) (admitted : Admission source request) :
    (sharedCouplingAdmitted raccord request admitted).first = respondAdmitted source request admitted := by
  cases request with
  | «local» request => cases request <;> rfl
  | deliver port signal => rfl
  | encounter => rfl

theorem shared_admitted_target_exact {source target} (raccord : StateRaccord source target)
    (request : Request) (admitted : Admission source request) :
    (sharedCouplingAdmitted raccord request admitted).second =
      respondAdmitted target (request.rename raccord.resources.addresses.forward) (Admission.rename raccord request admitted) := by
  cases request with
  | «local» request => cases request with
    | emit _ _ => dsimp only [sharedCouplingAdmitted, pairedSignal, respondAdmitted, Admission.rename, Request.rename, LocalRequest.rename]; rw [transported_signal_exact]; rfl
    | relay _ _ => dsimp only [sharedCouplingAdmitted, pairedSignal, respondAdmitted, Admission.rename, Request.rename, LocalRequest.rename]; rw [transported_signal_exact]; rfl
    | receive _ => dsimp only [sharedCouplingAdmitted, pairedSignal, respondAdmitted, Admission.rename, Request.rename, LocalRequest.rename]; rw [transported_signal_exact]; rfl
    | inspect _ _ => rfl
  | deliver port signal =>
    dsimp only [sharedCouplingAdmitted, pairedDelivery, respondAdmitted, Admission.rename, Request.rename]
    rw [transported_delivery_exact]; rfl
  | encounter =>
    change EncounterAdmission source at admitted
    dsimp only [sharedCouplingAdmitted, pairedEncounter, respondAdmitted, Admission.rename, Request.rename]
    with_unfolding_all
      rw [transported_encounter_exact]

def sharedCouplingRequest {source target} (raccord : StateRaccord source target) (request : Request) :
    PairedResponse source target :=
  match decide source request with
  | .inl admitted => sharedCouplingAdmitted raccord request admitted
  | .inr _ => ⟨⟨source, .local .refused, false, .root⟩,
      ⟨target, .local .refused, false, .root⟩, raccord, rfl, rfl⟩

theorem shared_request_source_exact {source target} (raccord : StateRaccord source target) (request : Request) :
    (sharedCouplingRequest raccord request).first = respond source request := by
  unfold sharedCouplingRequest respond
  cases decide source request with
  | inl admitted => exact shared_admitted_source_exact raccord request admitted
  | inr _ => rfl

theorem shared_request_target_exact {source target} (raccord : StateRaccord source target) (request : Request) :
    (sharedCouplingRequest raccord request).second = respond target (request.rename raccord.resources.addresses.forward) := by
  unfold sharedCouplingRequest
  cases chosen : decide source request with
  | inl admitted =>
    exact (shared_admitted_target_exact raccord request admitted).trans
      (admitted_response_exact target _ (Admission.rename raccord request admitted)).symm
  | inr no =>
    unfold respond
    cases decide target (request.rename raccord.resources.addresses.forward) with
    | inl admitted => exact False.elim (no (Admission.returned raccord request admitted))
    | inr _ => rfl

def prefixResponse {source} (head : Response source) (suffix : Execution head.state) : Execution source :=
  ⟨suffix.state, StrongPerimetralTurning.History.append head.history suffix.history,
    .step () head.allowed head.event suffix.report⟩

structure CorrespondingCouplingRequests (source target : State) where
  first : Execution source
  second : Execution target
  translated : List Request
  raccord : StateRaccord first.state second.state
  reportExact : second.report = first.report

def runSharedCoupling {source target} (raccord : StateRaccord source target) :
    List Request → CorrespondingCouplingRequests source target
  | [] => ⟨⟨source, .root, .stop ()⟩, ⟨target, .root, .stop ()⟩, [], raccord, rfl⟩
  | request :: rest =>
    let head := sharedCouplingRequest raccord request
    let suffix := runSharedCoupling head.raccord rest
    ⟨prefixResponse head.first suffix.first, prefixResponse head.second suffix.second,
      request.rename raccord.resources.addresses.forward :: suffix.translated, suffix.raccord, by
        change Outcome.step () head.second.allowed head.second.event suffix.second.report =
          Outcome.step () head.first.allowed head.first.event suffix.first.report
        rw [head.allowedExact, head.eventExact, suffix.reportExact]⟩
termination_by structural requests => requests

theorem shared_run_source_exact {source target} (raccord : StateRaccord source target) (requests : List Request) :
    (runSharedCoupling raccord requests).first = run source requests := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := sharedCouplingRequest raccord request
    exact (congrArg (prefixResponse head.first) (ih head.raccord)).trans (by
      change prefixResponse (sharedCouplingRequest raccord request).first
        (run (sharedCouplingRequest raccord request).first.state rest) = _
      rw [shared_request_source_exact]; rfl)

theorem shared_run_target_exact {source target} (raccord : StateRaccord source target) (requests : List Request) :
    (runSharedCoupling raccord requests).second = run target (runSharedCoupling raccord requests).translated := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := sharedCouplingRequest raccord request
    let suffix := runSharedCoupling head.raccord rest
    exact (congrArg (prefixResponse head.second) (ih head.raccord)).trans
      (congrArg (fun response : Response target => prefixResponse response (run response.state suffix.translated))
        (shared_request_target_exact raccord request))

theorem transported_all_futures {source target} (raccord : StateRaccord source target) (requests : List Request) :
    contract.outcome target (runSharedCoupling raccord requests).translated = contract.outcome source requests := by
  have same := (runSharedCoupling raccord requests).reportExact
  rw [shared_run_source_exact, shared_run_target_exact, all_futures_exact, all_futures_exact] at same
  exact same

theorem translated_length {source target} (raccord : StateRaccord source target) (requests : List Request) :
    (runSharedCoupling raccord requests).translated.length = requests.length := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih => exact congrArg Nat.succ (ih (sharedCouplingRequest raccord request).raccord)

def CorrespondingCouplingRequests.continue {source target} (prior : CorrespondingCouplingRequests source target)
    (requests : List Request) : CorrespondingCouplingRequests prior.first.state prior.second.state :=
  runSharedCoupling prior.raccord requests

theorem continued_full_contract_exact {source target} (prior : CorrespondingCouplingRequests source target)
    (requests : List Request) :
    contract.outcome prior.second.state (prior.continue requests).translated =
      contract.outcome prior.first.state requests := transported_all_futures prior.raccord requests

end RelationalPerimeter.Relativity.Continuation.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Request.rename_returns
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.admission_unique
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Admission.rename
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.Admission.returned
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transported_admission_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transportSignal
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transportDelivery
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transportEncounter
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transported_signal_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transported_delivery_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transported_encounter_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.sharedCouplingAdmitted
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.shared_request_source_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.shared_request_target_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.runSharedCoupling
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.shared_run_source_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.shared_run_target_exact
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.transported_all_futures
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.translated_length
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.continued_full_contract_exact
/- AXIOM_AUDIT_END -/
