import RelationalPerimeter.Relativity.Production.DiscoveredExchange
import RelationalPerimeter.Relativity.Production.TransportedRecurringRequests

/-!
# One productive continuation, with its exact other presentation

The source executes each admitted action once. The other presentation is built
by transporting that same cached output and its positive role, not by calling
the action again. Both presentations retain their occurrences and histories.
The discovered raccord is consumed before the continuation. Full agreement is
with the unchanged recurring contract, including every refusal and finite
interleaving. This is not a quotient of memory or a final physical contract.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def Produces.transportRole {source target : List Kind}
    (references : {kind : Kind} → Ref source kind → Ref target kind)
    {sourceValues : Values Value source} {targetValues : Values Value target}
    (reads : ∀ {kind} (ref : Ref source kind), read targetValues (references ref) = read sourceValues ref)
    {kind} {instruction : Instruction source kind} {output : Value kind}
    (role : Produces sourceValues instruction output) :
    Produces targetValues (instruction.rename references) output := by
  cases role with
  | emitted reading payload =>
    exact ((congrArg (fun value => SignalRecord.emit value (read targetValues (references payload))) (reads reading)).trans
      (congrArg (SignalRecord.emit (read sourceValues reading)) (reads payload))) ▸
      Produces.emitted (references reading) (references payload)
  | relayed signal calibration =>
    exact ((congrArg (fun value => SignalRecord.relay value (read targetValues (references calibration))) (reads signal)).trans
      (congrArg (SignalRecord.relay (read sourceValues signal)) (reads calibration))) ▸
      Produces.relayed (references signal) (references calibration)
  | received signal =>
    exact (congrArg SignalRecord.reading (reads signal)) ▸ Produces.received (references signal)

theorem RecurringComputed.output_exact {context} {values : Values Value context}
    {first second : Ref context .reading} {output : Rational}
    (role : RecurringComputed values first second output) :
    recurringDifference values first second = output := by
  cases role
  rfl

def RecurringProduces.transportRole {source target : RecurringCursor}
    (raccord : RecurringRaccord source target) {kind} {action : RecurringAction source kind}
    {output : Value kind} (role : RecurringProduces source action output) :
    RecurringProduces target (action.rename raccord) output := by
  cases action with
  | signal instruction =>
    cases role with
    | signal localRole => exact .signal (localRole.transportRole raccord.references.forward raccord.reads)
  | compare pair =>
    cases role with
    | compared computation =>
      have same : recurringDifference target.values (raccord.references.forward pair.first)
          (raccord.references.forward pair.second) = recurringDifference source.values pair.first pair.second :=
        (congrArg (fun value => Rational.sub value (target.read (raccord.references.forward pair.first)))
          (raccord.reads pair.second)).trans
          (congrArg (Rational.sub (source.read pair.second)) (raccord.reads pair.first))
      exact RecurringProduces.compared
        ((same.trans computation.output_exact) ▸ RecurringComputed.computed)

def transportRecurringDetermination {source target} (raccord : RecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (determination : RecurringDetermination source action) :
    RecurringDetermination target (action.rename raccord) :=
  ⟨determination.1, determination.2.transportRole raccord⟩

theorem transported_output_is_the_stored_output {source target} (raccord : RecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (determination : RecurringDetermination source action) :
    (transportRecurringDetermination raccord determination).1 = determination.1 := rfl

def transportRecurringProduction {source target} (raccord : RecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (head : RecurringProduction source action) :
    RecurringProduction target (action.rename raccord) :=
  let determination := transportRecurringDetermination raccord head.determination
  ⟨determination, target.extend determination, rfl⟩

theorem recurring_determination_unique (source : RecurringCursor) {kind}
    (action : RecurringAction source kind) (one two : RecurringDetermination source action) : one = two := by
  cases action with
  | signal instruction =>
    cases one with
    | mk oneValue oneRole =>
      cases oneRole with
      | signal oneRole =>
        cases oneRole <;> cases two with
        | mk twoValue twoRole => cases twoRole with | signal twoRole => cases twoRole; rfl
  | compare pair =>
    cases one with
    | mk oneValue oneRole =>
      cases oneRole with
      | compared oneRole =>
        cases oneRole
        cases two with
        | mk twoValue twoRole => cases twoRole with | compared twoRole => cases twoRole; rfl

theorem transported_production_exact {source target} (raccord : RecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (head : RecurringProduction source action) :
    transportRecurringProduction raccord head = performRecurring target (action.rename raccord) :=
  congrArg (fun determination => RecurringProduction.mk determination (target.extend determination) rfl)
    (recurring_determination_unique target _ (transportRecurringDetermination raccord head.determination)
      (executeRecurring target (action.rename raccord)))

def sharedRecurringAdmitted {source target} (raccord : AddressedRecurringRaccord source target) :
    (request : RecurringRequest) → RecurringAdmission source request → PairedRecurringResponse source target
  | .local (.emit _ _), admitted =>
    let head := performRecurring source (.signal (.emit admitted.1.ref admitted.2.ref))
    let transported := transportRecurringProduction raccord.constitution head
    pairedRecurringAction raccord head transported (fun value => .local (.emitted value))
  | .local (.relay _ _), admitted =>
    let head := performRecurring source (.signal (.relay admitted.1.ref admitted.2.ref))
    let transported := transportRecurringProduction raccord.constitution head
    pairedRecurringAction raccord head transported (fun value => .local (.relayed value))
  | .local (.receive _), admitted =>
    let head := performRecurring source (.signal (.receive admitted.ref))
    let transported := transportRecurringProduction raccord.constitution head
    pairedRecurringAction raccord head transported (fun value => .local (.received value))
  | .local (.inspect kind _), admitted =>
    ⟨⟨source, .local (.inspected (localReadout kind (source.read admitted.ref))), true, .root⟩,
      ⟨target, .local (.inspected (localReadout kind (target.read (raccord.constitution.references.forward admitted.ref)))), true, .root⟩,
      raccord, congrArg (fun value => RecurringEvent.local (.inspected (localReadout kind value)))
        (raccord.constitution.reads admitted.ref), rfl⟩
  | .compare _ _, admitted =>
    let head := performRecurring source (.compare admitted.pair)
    let transported := transportRecurringProduction raccord.constitution head
    pairedRecurringAction raccord head transported RecurringEvent.compared

theorem shared_admitted_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) (admitted : RecurringAdmission source request) :
    sharedRecurringAdmitted raccord request admitted = pairedRecurringAdmitted raccord request admitted := by
  cases request with
  | «local» request =>
    cases request with
    | emit _ _ => dsimp only [sharedRecurringAdmitted, pairedRecurringAdmitted, RecurringAdmission, RecurringLocalAdmission]; rw [transported_production_exact]
    | relay _ _ => dsimp only [sharedRecurringAdmitted, pairedRecurringAdmitted, RecurringAdmission, RecurringLocalAdmission]; rw [transported_production_exact]
    | receive _ => dsimp only [sharedRecurringAdmitted, pairedRecurringAdmitted, RecurringAdmission, RecurringLocalAdmission]; rw [transported_production_exact]
    | inspect _ _ => rfl
  | compare _ _ => dsimp only [sharedRecurringAdmitted, pairedRecurringAdmitted, RecurringAdmission]; rw [transported_production_exact]

def sharedRecurringRequest {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) : PairedRecurringResponse source target :=
  match decideRecurringAdmission source request with
  | .inl admitted => sharedRecurringAdmitted raccord request admitted
  | .inr _ => ⟨⟨source, .local .refused, false, .root⟩,
      ⟨target, .local .refused, false, .root⟩, raccord, rfl, rfl⟩

theorem shared_request_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (request : RecurringRequest) : sharedRecurringRequest raccord request = pairedRecurringRequest raccord request := by
  unfold sharedRecurringRequest pairedRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted => exact shared_admitted_exact raccord request admitted
  | inr _ => rfl

def prefixSharedRecurring {source target} (translatedRequest : RecurringRequest)
    (head : PairedRecurringResponse source target)
    (suffix : CorrespondingRecurringRequests head.first.cursor head.second.cursor) :
    CorrespondingRecurringRequests source target :=
  ⟨prefixRecurringRequest head.first suffix.first, prefixRecurringRequest head.second suffix.second,
    translatedRequest :: suffix.translated, suffix.raccord, by
      change ConstitutiveSearch.ContinuationSignatures.Outcome.step () head.second.allowed head.second.event suffix.second.report =
        ConstitutiveSearch.ContinuationSignatures.Outcome.step () head.first.allowed head.first.event suffix.first.report
      rw [head.allowedExact, head.eventExact, suffix.reportExact]⟩

def runSharedRecurring {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) : CorrespondingRecurringRequests source target :=
  match requests with
  | [] => ⟨⟨source, .root, .stop ()⟩, ⟨target, .root, .stop ()⟩, [], raccord, rfl⟩
  | request :: rest =>
    let head := sharedRecurringRequest raccord request
    let suffix := runSharedRecurring head.raccord rest
    prefixSharedRecurring (request.rename raccord.addresses.forward) head suffix
termination_by structural requests

theorem shared_run_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) : runSharedRecurring raccord requests = runCorrespondingRecurring raccord requests := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let translated := request.rename raccord.addresses.forward
    exact (congrArg (fun head : PairedRecurringResponse source target =>
      prefixSharedRecurring translated head (runSharedRecurring head.raccord rest))
      (shared_request_exact raccord request)).trans
      (congrArg (prefixSharedRecurring translated (pairedRecurringRequest raccord request))
        (ih (pairedRecurringRequest raccord request).raccord))

theorem shared_recurring_all_futures {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) :
    recurringContract.outcome target (runSharedRecurring raccord requests).translated =
      recurringContract.outcome source requests := by
  rw [shared_run_exact]
  exact recurring_transported_all_futures raccord requests

theorem shared_recurring_runners_exact {source target} (raccord : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) :
    (runSharedRecurring raccord requests).first = runRecurringRequests source requests ∧
      (runSharedRecurring raccord requests).second =
        runRecurringRequests target (runSharedRecurring raccord requests).translated := by
  rw [shared_run_exact]
  exact ⟨correspondingRecurring_source_exact raccord requests, correspondingRecurring_target_exact raccord requests⟩

def CorrespondingRecurringRequests.continueShared {source target}
    (prior : CorrespondingRecurringRequests source target) (requests : List RecurringRequest) :
    CorrespondingRecurringRequests prior.first.cursor prior.second.cursor := runSharedRecurring prior.raccord requests

theorem shared_continuation_exact {source target} (prior : CorrespondingRecurringRequests source target)
    (requests : List RecurringRequest) :
    (prior.continueShared requests).first = runRecurringRequests prior.first.cursor requests ∧
      (prior.continueShared requests).second =
        runRecurringRequests prior.second.cursor (prior.continueShared requests).translated :=
  shared_recurring_runners_exact prior.raccord requests

def DiscoveredStoredExchange.continue {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    {pair : StoredPairProduction source first second} (found : DiscoveredStoredExchange pair)
    (requests : List RecurringRequest) :
    CorrespondingRecurringRequests (.fromCursor pair.cursor) (.fromCursor found.exchanged.cursor) :=
  runSharedRecurring found.raccord requests

def searchExchangeAndContinue {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) (requests : List RecurringRequest) :
    PSum ((found : DiscoveredStoredExchange pair) ×'
      CorrespondingRecurringRequests (.fromCursor pair.cursor) (.fromCursor found.exchanged.cursor))
      (InputPort second (Ref.here : Ref (firstKind :: source.kinds) firstKind) ×
        RecurringRequestedExecution (.fromCursor pair.cursor)) :=
  match searchStoredExchange pair with
  | .inl found => .inl ⟨found, found.continue requests⟩
  | .inr fresh => .inr ⟨fresh, runRecurringRequests (.fromCursor pair.cursor) requests⟩

theorem discovered_exchange_all_futures {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    {pair : StoredPairProduction source first second} (found : DiscoveredStoredExchange pair)
    (requests : List RecurringRequest) :
    recurringContract.outcome (.fromCursor found.exchanged.cursor) (found.continue requests).translated =
      recurringContract.outcome (.fromCursor pair.cursor) requests := shared_recurring_all_futures found.raccord requests

theorem search_continuation_source_exact {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) (requests : List RecurringRequest) :
    (match searchExchangeAndContinue pair requests with
      | .inl accepted => accepted.2.first
      | .inr refused => refused.2) = runRecurringRequests (.fromCursor pair.cursor) requests := by
  unfold searchExchangeAndContinue
  cases searchStoredExchange pair with
  | inl found => exact (shared_recurring_runners_exact found.raccord requests).1
  | inr _ => rfl

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.RecurringComputed.output_exact
#print axioms RelationalPerimeter.Relativity.Production.Produces.transportRole
#print axioms RelationalPerimeter.Relativity.Production.RecurringProduces.transportRole
#print axioms RelationalPerimeter.Relativity.Production.transportRecurringDetermination
#print axioms RelationalPerimeter.Relativity.Production.transported_output_is_the_stored_output
#print axioms RelationalPerimeter.Relativity.Production.transportRecurringProduction
#print axioms RelationalPerimeter.Relativity.Production.recurring_determination_unique
#print axioms RelationalPerimeter.Relativity.Production.transported_production_exact
#print axioms RelationalPerimeter.Relativity.Production.sharedRecurringAdmitted
#print axioms RelationalPerimeter.Relativity.Production.shared_admitted_exact
#print axioms RelationalPerimeter.Relativity.Production.sharedRecurringRequest
#print axioms RelationalPerimeter.Relativity.Production.shared_request_exact
#print axioms RelationalPerimeter.Relativity.Production.prefixSharedRecurring
#print axioms RelationalPerimeter.Relativity.Production.runSharedRecurring
#print axioms RelationalPerimeter.Relativity.Production.shared_run_exact
#print axioms RelationalPerimeter.Relativity.Production.shared_recurring_all_futures
#print axioms RelationalPerimeter.Relativity.Production.shared_recurring_runners_exact
#print axioms RelationalPerimeter.Relativity.Production.CorrespondingRecurringRequests.continueShared
#print axioms RelationalPerimeter.Relativity.Production.shared_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.DiscoveredStoredExchange.continue
#print axioms RelationalPerimeter.Relativity.Production.searchExchangeAndContinue
#print axioms RelationalPerimeter.Relativity.Production.discovered_exchange_all_futures
#print axioms RelationalPerimeter.Relativity.Production.search_continuation_source_exact
/- AXIOM_AUDIT_END -/
