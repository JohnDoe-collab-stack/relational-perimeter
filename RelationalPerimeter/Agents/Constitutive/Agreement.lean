import RelationalPerimeter.Agents.Constitutive.Execution
import RelationalPerimeter.Constitution.Grouping.ContinuationContract

/-! The rich interpreter reads its constituted history, not the runtime
projection. Transition, event, observation and admission laws are separate. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent
open SAT Resources EndogenousDecomposition Grouping

def sourceStep {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : Source master × LiveContinuation.Event :=
  (⟨source.requirement, source.profile, .step source.history⟩,
    LiveContinuation.sourceEvent source.cursor)

def sourceRunSteps {input : Nat} {master : UnifiedMaster.Instance input} :
    Nat → Source master → Source master × List LiveContinuation.Event
  | 0, source => (source, [])
  | count + 1, source =>
      let head := sourceStep source
      let rest := sourceRunSteps count head.1
      (rest.1, head.2 :: rest.2)

theorem sourceStep_exact {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) :
    (project (sourceStep source).1, (sourceStep source).2) = step (project source) := rfl

theorem sourceRunSteps_exact {input : Nat} {master : UnifiedMaster.Instance input}
    (count : Nat) (source : Source master) :
    (project (sourceRunSteps count source).1, (sourceRunSteps count source).2) =
      runSteps count (project source) := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih =>
      change (project (sourceRunSteps count (sourceStep source).1).1,
        (sourceStep source).2 :: (sourceRunSteps count (sourceStep source).1).2) = _
      have exactTail := ih (sourceStep source).1
      exact congrArg (fun result : Memory × List LiveContinuation.Event =>
        (result.1, (sourceStep source).2 :: result.2)) exactTail

/-- The rich operation retains its actual material reading and decision. Its
result is eliminated from those objects; it is not a runtime result annotated
afterwards with an unrelated historical certificate. -/
inductive RichOperation {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : Request → Type 3 where
  | advance (count : Nat) : RichOperation source (.advance count)
  | inspect (handle : Nat) (var : Var) (reading : MaterialReading source.history.realization)
      (decision : Decision source.requirement reading.values handle var none)
      (decisionExact : decision = decideReply source.requirement reading.values handle var none) :
      RichOperation source (.inspect handle var)
  | propose (handle : Nat) (var : Var) (value : Bool)
      (reading : MaterialReading source.history.realization)
      (decision : Decision source.requirement reading.values handle var (some value))
      (decisionExact : decision = decideReply source.requirement reading.values handle var (some value)) :
      RichOperation source (.propose handle var value)
  | outside (handle : Nat) (var : Var) (absent : source.requirement.permission var = none) :
      RichOperation source (.obtain handle var)
  | obtain (handle : Nat) (var : Var) (permission : Ref source.requirement.realizedScope var)
      (initial : MaterialReading source.history.realization)
      (reading : MaterialReading (sourceRunSteps (needed initial.values.length handle) source).1.history.realization)
      (decision : Decision (sourceRunSteps (needed initial.values.length handle) source).1.requirement
        reading.values handle var none)
      (decisionExact : decision = decideReply
        (sourceRunSteps (needed initial.values.length handle) source).1.requirement reading.values handle var none) :
      RichOperation source (.obtain handle var)

def RichOperation.result {input : Nat} {master : UnifiedMaster.Instance input}
    {source : Source master} {request : Request} : RichOperation source request → Source master × Event
  | .advance count => let produced := sourceRunSteps count source
                      (produced.1, ⟨produced.2, .advanced count⟩)
  | .inspect _ _ _ decision _ => (source, ⟨[], decision.message⟩)
  | .propose _ _ _ _ decision _ => (source, ⟨[], decision.message⟩)
  | .outside handle var _ => (source, ⟨[], .refused handle var .outsideScope⟩)
  | .obtain handle _ _ initial _ decision _ =>
      let produced := sourceRunSteps (needed initial.values.length handle) source
      (produced.1, ⟨produced.2, decision.message⟩)

def sourceProduced {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) : (request : Request) → RichOperation source request
  | .advance count => .advance count
  | .inspect handle var =>
      let reading := source.history.realization.materialReading
      .inspect handle var reading (decideReply source.requirement reading.values handle var none) rfl
  | .propose handle var value =>
      let reading := source.history.realization.materialReading
      .propose handle var value reading (decideReply source.requirement reading.values handle var (some value)) rfl
  | .obtain handle var => match permitted : source.requirement.permission var with
      | none => .outside handle var permitted
      | some permission =>
          let initial := source.history.realization.materialReading
          let produced := sourceRunSteps (needed initial.values.length handle) source
          let reading := produced.1.history.realization.materialReading
          .obtain handle var permission initial reading
            (decideReply produced.1.requirement reading.values handle var none) rfl

def sourcePerform {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) : Source master × Event :=
  (sourceProduced source request).result

theorem sourcePerform_obtain {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (handle : Nat) (var : Var) :
    sourcePerform source (.obtain handle var) =
      match source.requirement.permission var with
      | none => (source, ⟨[], .refused handle var .outsideScope⟩)
      | some _ =>
          let produced := sourceRunSteps (needed source.history.realization.materialRegister.length handle) source
          (produced.1, ⟨produced.2,
            (decideReply produced.1.requirement produced.1.history.realization.materialRegister handle var none).message⟩) := by
  dsimp only [sourcePerform, sourceProduced]
  split
  · rename_i absent
    change (source, Event.mk [] (.refused handle var .outsideScope)) = _
    rw [absent]
  · rename_i permission present
    change ((sourceRunSteps (needed source.history.realization.materialRegister.length handle) source).1,
      Event.mk (sourceRunSteps (needed source.history.realization.materialRegister.length handle) source).2
        (decideReply (sourceRunSteps (needed source.history.realization.materialRegister.length handle) source).1.requirement
          (sourceRunSteps (needed source.history.realization.materialRegister.length handle) source).1.history.realization.materialRegister handle var none).message) = _
    rw [present]

theorem sourcePerform_exact {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Source master) (request : Request) :
    (project (sourcePerform source request).1, (sourcePerform source request).2) =
      executeInput (project source) request := by
  rw [executeInput_exact]
  cases request with
  | advance count =>
      exact congrArg (fun result : Memory × List LiveContinuation.Event =>
        (result.1, Event.mk result.2 (.advanced count))) (sourceRunSteps_exact count source)
  | inspect handle var =>
      change (project source, Event.mk []
        (decideReply source.requirement source.history.realization.materialRegister handle var none).message) = _
      rw [source.history.realization.materialRegister_exact]
      rfl
  | propose handle var value =>
      change (project source, Event.mk []
        (decideReply source.requirement source.history.realization.materialRegister handle var (some value)).message) = _
      rw [source.history.realization.materialRegister_exact]
      rfl
  | obtain handle var =>
      rw [perform_obtain, sourcePerform_obtain]
      dsimp only [project]
      cases permitted : source.requirement.permission var with
      | none => rfl
      | some permission =>
          rw [source.history.realization.materialRegister_exact, RegisterRealization.materialRegister_exact]
          exact congrArg (fun result : Memory × List LiveContinuation.Event =>
            (result.1, Event.mk result.2
              (decideReply result.1.requirement result.1.register handle var none).message))
            (sourceRunSteps_exact (needed source.history.targets.length handle) source)

def table (register : List AnswerTarget) (scope : List Var) : List (Nat × Var × Bool) :=
  let rec rows (handle : Nat) : List AnswerTarget → List (Nat × Var × Bool)
    | [] => []
    | target :: rest => scope.map (fun var => (handle, var, target.read var)) ++ rows (handle + 1) rest
  rows 0 register

def Admission (requirement : Requirement) (register : List AnswerTarget) : Request → Type 3
  | .advance _ => ULift.{3} Unit
  | .inspect handle var => ULift.{3} (Σ value, Authorization requirement register handle var value)
  | .obtain _ var => ULift.{3} (Ref requirement.realizedScope var)
  | .propose handle var value => ULift.{3} (Authorization requirement register handle var value)

/-- The rich permission is in the received scope, before its realization.
Its target comes from the constituted history, not a projected responder. -/
structure RichAuthorization (requirement : Requirement) {register : List AnswerTarget}
    {cursor : MasterResources.Cursor} (realization : RegisterRealization register cursor)
    (handle : Nat) (var : Var) (value : Bool) : Type 3 where
  permission : Ref requirement.scope var
  occurrence : Located register
  occurrenceExact : resolveHandle register handle = some occurrence
  valueExact : value = (realization.support.read (realization.reference occurrence.2)).read var

def RichAuthorization.realize {req register cursor handle var value}
    {realization : RegisterRealization register cursor}
    (witness : RichAuthorization req realization handle var value) : Authorization req register handle var value :=
  ⟨req.scope_exact.symm ▸ witness.permission, witness.occurrence, witness.occurrenceExact,
    witness.valueExact.trans (congrArg (fun target => target.read var) (realization.reads witness.occurrence.2))⟩

def Authorization.received {req register cursor handle var value}
    (realization : RegisterRealization register cursor)
    (witness : Authorization req register handle var value) : RichAuthorization req realization handle var value :=
  ⟨req.scope_exact ▸ witness.permission, witness.occurrence, witness.occurrenceExact,
    witness.valueExact.trans (congrArg (fun target => target.read var) (realization.reads witness.occurrence.2)).symm⟩

theorem reference_transport_return {α : Type} {a b : α} (same : a = b)
    (family : α → Type) (witness : family a) :
    same.symm ▸ (same ▸ witness) = witness := by
  cases same
  rfl

theorem RichAuthorization.return_received {req register cursor handle var value}
    {realization : RegisterRealization register cursor}
    (witness : RichAuthorization req realization handle var value) :
    witness.realize.received realization = witness := by
  cases witness with
  | mk permission occurrence occurrenceExact valueExact =>
      unfold RichAuthorization.realize Authorization.received
      rw [reference_transport_return req.scope_exact.symm (fun scope => Ref scope var) permission]

theorem Authorization.return_realized {req register cursor handle var value}
    (realization : RegisterRealization register cursor)
    (witness : Authorization req register handle var value) :
    (witness.received realization).realize = witness := by
  cases witness with
  | mk permission occurrence occurrenceExact valueExact =>
      unfold RichAuthorization.realize Authorization.received
      rw [reference_transport_return req.scope_exact (fun scope => Ref scope var) permission]

def RichAdmission (requirement : Requirement) {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (realization : RegisterRealization register cursor) : Request → Type 3
  | .advance _ => ULift.{3} Unit
  | .inspect handle var => ULift.{3} (Σ value, RichAuthorization requirement realization handle var value)
  | .obtain _ var => ULift.{3} (Ref requirement.scope var)
  | .propose handle var value => ULift.{3} (RichAuthorization requirement realization handle var value)

def realizeAdmission (req : Requirement) {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (realization : RegisterRealization register cursor) :
    (request : Request) → RichAdmission req realization request → Admission req register request
  | .advance _, witness => witness
  | .inspect _ _, witness => ⟨⟨witness.down.1, witness.down.2.realize⟩⟩
  | .obtain _ _, witness => ⟨req.scope_exact.symm ▸ witness.down⟩
  | .propose _ _ _, witness => ⟨witness.down.realize⟩

def receivedAdmission (req : Requirement) {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (realization : RegisterRealization register cursor) :
    (request : Request) → Admission req register request → RichAdmission req realization request
  | .advance _, witness => witness
  | .inspect _ _, witness => ⟨⟨witness.down.1, witness.down.2.received realization⟩⟩
  | .obtain _ _, witness => ⟨req.scope_exact ▸ witness.down⟩
  | .propose _ _ _, witness => ⟨witness.down.received realization⟩

theorem admission_received_return (req : Requirement) {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (realization : RegisterRealization register cursor)
    (request : Request) (witness : RichAdmission req realization request) :
    receivedAdmission req realization request (realizeAdmission req realization request witness) = witness := by
  cases request with
  | advance count => rfl
  | inspect handle var =>
      cases witness with
      | up pair =>
          cases pair with
          | mk value authorization =>
              exact congrArg (fun a => ULift.up (Sigma.mk value a)) authorization.return_received
  | obtain handle var =>
      cases witness with
      | up permission =>
          exact congrArg ULift.up
            (reference_transport_return req.scope_exact.symm (fun scope => Ref scope var) permission)
  | propose handle var value =>
      cases witness with
      | up authorization => exact congrArg ULift.up authorization.return_received

theorem admission_realized_return (req : Requirement) {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (realization : RegisterRealization register cursor)
    (request : Request) (witness : Admission req register request) :
    realizeAdmission req realization request (receivedAdmission req realization request witness) = witness := by
  cases request with
  | advance count => rfl
  | inspect handle var =>
      cases witness with
      | up pair =>
          cases pair with
          | mk value authorization =>
              exact congrArg (fun a => ULift.up (Sigma.mk value a)) (authorization.return_realized realization)
  | obtain handle var =>
      cases witness with
      | up permission =>
          exact congrArg ULift.up
            (reference_transport_return req.scope_exact (fun scope => Ref scope var) permission)
  | propose handle var value =>
      cases witness with
      | up authorization => exact congrArg ULift.up (authorization.return_realized realization)

def bridge {input : Nat} (master : UnifiedMaster.Instance input) :
    Continuation.Exact (Source master) Memory Request Event (List (Nat × Var × Bool)) where
  project := project
  sourceNext := fun source request => (sourcePerform source request).1
  reducedNext := fun memory request => (executeInput memory request).1
  sourceAllow := fun source => RichAdmission source.requirement source.history.realization
  reducedAllow := fun memory => Admission memory.requirement memory.register
  toReduced := fun source => realizeAdmission source.requirement source.history.realization
  toSource := fun source => receivedAdmission source.requirement source.history.realization
  sourceEvent := fun source request => (sourcePerform source request).2
  reducedEvent := fun memory request => (executeInput memory request).2
  sourceRead := fun source => table source.history.realization.materialRegister source.requirement.scope
  reducedRead := fun memory => table memory.register memory.requirement.realizedScope
  nextLaw := fun source request => congrArg Prod.fst (sourcePerform_exact source request)
  eventLaw := fun source request => congrArg Prod.snd (sourcePerform_exact source request)
  readLaw := fun source =>
    (congrArg (fun register => table register source.requirement.scope)
      source.history.realization.materialRegister_exact).trans
        (congrArg (table source.history.targets) source.requirement.scope_exact.symm)

theorem permission_present (requirement : Requirement) (var : Var)
    (witness : Ref requirement.realizedScope var) :
    ∃ permission, requirement.permission var = some permission := by
  cases present : requirement.permission var with
  | none => exact False.elim (resolvePermission_none requirement.realizedScope var present witness)
  | some permission => exact ⟨permission, rfl⟩

theorem authorized_read {requirement : Requirement} {register : List AnswerTarget}
    {handle : Nat} {var : Var} {value : Bool}
    (witness : Authorization requirement register handle var value) :
    readRegister register handle var = some value := by
  unfold readRegister
  rw [witness.occurrenceExact]
  exact congrArg some witness.valueExact.symm

theorem admitted_inspection_returns (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (value : Bool)
    (witness : Authorization requirement register handle var value) :
    (decideReply requirement register handle var none).message = .answer handle var value := by
  generalize decideReply requirement register handle var none = decision
  cases decision with
  | authorized actual authorization candidate =>
      exact congrArg (Message.answer handle var)
        (Option.some.inj ((authorized_read authorization).symm.trans (authorized_read witness)))
  | outside absent =>
      exact False.elim (resolvePermission_none _ _ absent witness.permission)
  | missing permission absent =>
      cases (absent.symm.trans witness.occurrenceExact)
  | incorrect permission occurrence located value proposed different => cases proposed

theorem correct_candidate_returns (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (value : Bool)
    (witness : Authorization requirement register handle var value) :
    (decideReply requirement register handle var (some value)).message = .answer handle var value := by
  generalize decideReply requirement register handle var (some value) = decision
  cases decision with
  | authorized actual authorization candidate =>
      exact congrArg (Message.answer handle var)
        (Option.some.inj ((authorized_read authorization).symm.trans (authorized_read witness)))
  | outside absent => exact False.elim (resolvePermission_none _ _ absent witness.permission)
  | missing permission absent =>
      cases (absent.symm.trans witness.occurrenceExact)
  | incorrect permission occurrence located proposed proposedExact different =>
      have sameOccurrence := Option.some.inj (witness.occurrenceExact.symm.trans located)
      have sameValue := Option.some.inj proposedExact
      exact False.elim (different (sameValue.symm.trans
        (witness.valueExact.trans (congrArg (fun entry : Located register => entry.1.read var) sameOccurrence))))

theorem incorrect_candidate_refused (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (occurrence : Located register)
    (permission : Ref requirement.realizedScope var)
    (located : resolveHandle register handle = some occurrence) (value : Bool)
    (different : value ≠ occurrence.1.read var) :
    (decideReply requirement register handle var (some value)).message =
      .refused handle var .incorrectValue := by
  generalize decideReply requirement register handle var (some value) = decision
  cases decision with
  | authorized actual authorization candidate =>
      have sameOccurrence := Option.some.inj (authorization.occurrenceExact.symm.trans located)
      cases candidate with
      | inl absent => cases absent
      | inr same =>
          exact False.elim (different ((Option.some.inj same).trans
            (authorization.valueExact.trans (congrArg (fun entry : Located register => entry.1.read var) sameOccurrence))))
  | outside absent => exact False.elim (resolvePermission_none _ _ absent permission)
  | missing permission absent => cases (absent.symm.trans located)
  | incorrect permission occurrence located value proposed different => rfl

theorem candidate_authorization_exact (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (value : Bool) :
    Nonempty (Authorization requirement register handle var value) ↔
      (decideReply requirement register handle var (some value)).message = .answer handle var value := by
  constructor
  · intro admitted
    cases admitted with
    | intro witness => exact correct_candidate_returns requirement register handle var value witness
  · intro published
    generalize decideReply requirement register handle var (some value) = decision at published
    cases decision with
    | authorized actual authorization candidate =>
        cases candidate with
        | inl impossible => cases impossible
        | inr same =>
            cases Option.some.inj same
            exact ⟨authorization⟩
    | outside absent => cases published
    | missing permission absent => cases published
    | incorrect permission occurrence located proposed proposedExact different => cases published

def resolvePresent (register : List AnswerTarget) (handle : Nat)
    (present : (resolveHandle register handle).isSome = true) :
    {occurrence : Located register // resolveHandle register handle = some occurrence} :=
  match found : resolveHandle register handle with
  | some occurrence => ⟨occurrence, rfl⟩
  | none => False.elim (Bool.noConfusion (found ▸ present))

def obtainedAuthorization (memory : Memory) (handle : Nat) (var : Var)
    (permission : Ref memory.requirement.realizedScope var) :
    Σ value, Authorization
      (runSteps (needed memory.register.length handle) memory).1.requirement
      (runSteps (needed memory.register.length handle) memory).1.register handle var value :=
  let found := resolvePresent _ handle (obtained_handle_present memory handle)
  ⟨found.val.1.read var,
    ⟨(runSteps_requirement _ memory).symm ▸ permission, found.val, found.property, rfl⟩⟩

theorem obtain_produces_and_returns (memory : Memory) (handle : Nat) (var : Var)
    (permission : Ref memory.requirement.realizedScope var) :
    (executeInput memory (.obtain handle var)).2.message =
      .answer handle var (obtainedAuthorization memory handle var permission).1 := by
  rw [executeInput_exact]
  obtain ⟨permit, present⟩ := permission_present memory.requirement var permission
  dsimp only [perform, performCertified]
  split
  · rename_i absent
    cases (absent.symm.trans present)
  ·
      exact admitted_inspection_returns _ _ _ _ _ (obtainedAuthorization memory handle var permission).2

theorem obtain_register_exact (memory : Memory) (handle var : Nat)
    (permission : Ref memory.requirement.realizedScope var)
    (missing : memory.register.length ≤ handle) :
    (executeInput memory (.obtain handle var)).1.register.length = handle + 1 := by
  rw [executeInput_exact, perform_obtain]
  cases present : memory.requirement.permission var with
  | none => exact False.elim (resolvePermission_none _ _ present permission)
  | some allowed => exact obtained_register_exact memory handle missing

theorem obtain_work_exact (memory : Memory) (handle var : Nat)
    (permission : Ref memory.requirement.realizedScope var) :
    (executeInput memory (.obtain handle var)).2.productions.length = needed memory.register.length handle := by
  rw [executeInput_exact, perform_obtain]
  cases present : memory.requirement.permission var with
  | none => exact False.elim (resolvePermission_none _ _ present permission)
  | some allowed => exact runSteps_event_count _ _

theorem refusal_preserves_memory (memory : Memory) (request : Request)
    (handle var : Nat) (reason : Refusal)
    (refused : (executeInput memory request).2.message = .refused handle var reason) :
    (executeInput memory request).1 = memory := by
  cases request with
  | advance count =>
      change Message.advanced count = .refused handle var reason at refused
      cases refused
  | inspect _ _ => rfl
  | propose _ _ _ => rfl
  | obtain requested requestedVar =>
      cases present : memory.requirement.permission requestedVar with
      | none => rw [executeInput_exact, perform_obtain, present]
      | some permission =>
          have answered := obtain_produces_and_returns memory requested requestedVar permission
          cases answered.symm.trans refused

theorem executeInput_requirement (memory : Memory) (request : Request) :
    (executeInput memory request).1.requirement = memory.requirement := by
  rw [executeInput_exact]
  cases request with
  | advance count => exact runSteps_requirement count memory
  | inspect handle var => rfl
  | propose handle var value => rfl
  | obtain handle var =>
      dsimp only [perform, performCertified]
      split
      · rfl
      · exact runSteps_requirement _ memory

theorem executed_step_register_exact (memory : Memory) :
    (step memory).1.register = memory.register ++ [resumedTarget (LiveContinuation.produce memory.live)] := rfl

theorem head_uses_current_resources (memory : Memory) (request : Request) :
    executeInput memory request =
      (interactionProducer.operation (memory, ULift.up request, PUnit.unit)).1 := rfl

theorem head_production_entire_exact (memory : Memory) (request : Request) :
    executeProducedInput memory request =
      interactionProducer.operation (memory, ULift.up request, PUnit.unit) := rfl

theorem head_horizon_independent (memory : Memory) (request : Request) (one two : List Request) :
    (executeRequests memory (request :: one)).2.head? =
      (executeRequests memory (request :: two)).2.head? := rfl

theorem cached_obtain_runs_no_stage (memory : Memory) (handle : Nat) (var : Var)
    (within : handle < memory.register.length) :
    (executeInput memory (.obtain handle var)).2.productions = [] := by
  rw [executeInput_exact, perform_obtain]
  split
  · rfl
  · rw [needed_zero _ _ within]; rfl

theorem executeInput_register_monotone (memory : Memory) (request : Request) :
    memory.register.length ≤ (executeInput memory request).1.register.length := by
  rw [executeInput_exact]
  cases request with
  | advance count =>
      change memory.register.length ≤ (runSteps count memory).1.register.length
      rw [runSteps_length]
      exact Nat.le_add_right _ _
  | inspect handle var => exact Nat.le_refl _
  | propose handle var value => exact Nat.le_refl _
  | obtain handle var =>
      rw [perform_obtain]
      split
      · exact Nat.le_refl _
      · change memory.register.length ≤ (runSteps _ memory).1.register.length
        rw [runSteps_length]
        exact Nat.le_add_right _ _

theorem executeInput_old_read (memory : Memory) (request : Request) (handle : Nat) (var : Var)
    (within : handle < memory.register.length) :
    readRegister (executeInput memory request).1.register handle var = readRegister memory.register handle var := by
  rw [executeInput_exact]
  cases request with
  | advance count => exact runSteps_old_read count memory handle var within
  | inspect requested requestedVar => rfl
  | propose requested requestedVar value => rfl
  | obtain requested requestedVar =>
      rw [perform_obtain]
      split
      · rfl
      · exact runSteps_old_read _ memory handle var within

theorem authorized_target_accepted {requirement : Requirement} {register : List AnswerTarget}
    {handle : Nat} {var : Var} {value : Bool}
    (authorization : Authorization requirement register handle var value) :
    GeneratedStructuralBranchAccept authorization.occurrence.1.context
      authorization.occurrence.1.continuation := authorization.occurrence.1.accepted

/-- The criterion required of an actual reply, independent of the responder.
Acceptance is a conclusion about the authorized occurrence, not a premise
supplied by its caller. -/
def ReplyCriterion (requirement : Requirement) (register : List AnswerTarget) : Message → Prop
  | .answer handle var value => ∃ authorization : Authorization requirement register handle var value,
      GeneratedStructuralBranchAccept authorization.occurrence.1.context authorization.occurrence.1.continuation
  | .advanced _ => True
  | .refused _ _ _ => True

theorem ResponseEvidence.criterion {requirement : Requirement} {register : List AnswerTarget}
    {handle : Nat} {var : Var} {candidate : Option Bool} {message : Message}
    (evidence : ResponseEvidence requirement register handle var candidate message) :
    ReplyCriterion requirement register message := by
  cases evidence with
  | answer value authorization _ => exact ⟨authorization, authorized_target_accepted authorization⟩
  | outside _ => exact True.intro
  | missing _ _ => exact True.intro
  | incorrect _ _ _ _ _ _ => exact True.intro

def RequestCriterion (memory : Memory) : Request → Memory × Event → Prop
  | .advance _, _ => True
  | .inspect _ _, result => ReplyCriterion memory.requirement memory.register result.2.message
  | .propose _ _ _, result => ReplyCriterion memory.requirement memory.register result.2.message
  | .obtain _ _, result => ReplyCriterion result.1.requirement result.1.register result.2.message

theorem RequestEvidence.criterion {memory : Memory} {request : Request} {result : Memory × Event}
    (evidence : RequestEvidence memory request result) : RequestCriterion memory request result := by
  cases request with
  | advance _ => exact True.intro
  | inspect _ _ => exact ResponseEvidence.criterion evidence
  | propose _ _ _ => exact ResponseEvidence.criterion evidence
  | obtain _ _ => exact ResponseEvidence.criterion evidence

theorem executed_reply_criterion (memory : Memory) (request : Request) :
    RequestCriterion memory request (executeInput memory request) := (executedEvidence memory request).criterion

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.sourceStep
#print axioms ConstitutiveSearch.Agent.sourceRunSteps_exact
#print axioms ConstitutiveSearch.Agent.sourcePerform
#print axioms ConstitutiveSearch.Agent.RichOperation
#print axioms ConstitutiveSearch.Agent.RichOperation.result
#print axioms ConstitutiveSearch.Agent.sourceProduced
#print axioms ConstitutiveSearch.Agent.sourcePerform_obtain
#print axioms ConstitutiveSearch.Agent.sourcePerform_exact
#print axioms ConstitutiveSearch.Agent.table
#print axioms ConstitutiveSearch.Agent.Admission
#print axioms ConstitutiveSearch.Agent.RichAuthorization.realize
#print axioms ConstitutiveSearch.Agent.Authorization.received
#print axioms ConstitutiveSearch.Agent.reference_transport_return
#print axioms ConstitutiveSearch.Agent.RichAuthorization.return_received
#print axioms ConstitutiveSearch.Agent.Authorization.return_realized
#print axioms ConstitutiveSearch.Agent.RichAdmission
#print axioms ConstitutiveSearch.Agent.realizeAdmission
#print axioms ConstitutiveSearch.Agent.receivedAdmission
#print axioms ConstitutiveSearch.Agent.admission_received_return
#print axioms ConstitutiveSearch.Agent.admission_realized_return
#print axioms ConstitutiveSearch.Agent.bridge
#print axioms ConstitutiveSearch.Agent.permission_present
#print axioms ConstitutiveSearch.Agent.authorized_read
#print axioms ConstitutiveSearch.Agent.admitted_inspection_returns
#print axioms ConstitutiveSearch.Agent.correct_candidate_returns
#print axioms ConstitutiveSearch.Agent.incorrect_candidate_refused
#print axioms ConstitutiveSearch.Agent.candidate_authorization_exact
#print axioms ConstitutiveSearch.Agent.resolvePresent
#print axioms ConstitutiveSearch.Agent.obtainedAuthorization
#print axioms ConstitutiveSearch.Agent.obtain_produces_and_returns
#print axioms ConstitutiveSearch.Agent.obtain_register_exact
#print axioms ConstitutiveSearch.Agent.obtain_work_exact
#print axioms ConstitutiveSearch.Agent.refusal_preserves_memory
#print axioms ConstitutiveSearch.Agent.ResponseEvidence
#print axioms ConstitutiveSearch.Agent.Decision.evidence
#print axioms ConstitutiveSearch.Agent.RequestEvidence
#print axioms ConstitutiveSearch.Agent.executedEvidence
#print axioms ConstitutiveSearch.Agent.executeInput_requirement
#print axioms ConstitutiveSearch.Agent.executed_step_register_exact
#print axioms ConstitutiveSearch.Agent.head_uses_current_resources
#print axioms ConstitutiveSearch.Agent.head_production_entire_exact
#print axioms ConstitutiveSearch.Agent.head_horizon_independent
#print axioms ConstitutiveSearch.Agent.cached_obtain_runs_no_stage
#print axioms ConstitutiveSearch.Agent.executeInput_register_monotone
#print axioms ConstitutiveSearch.Agent.executeInput_old_read
#print axioms ConstitutiveSearch.Agent.authorized_target_accepted
#print axioms ConstitutiveSearch.Agent.ReplyCriterion
#print axioms ConstitutiveSearch.Agent.ResponseEvidence.criterion
#print axioms ConstitutiveSearch.Agent.RequestCriterion
#print axioms ConstitutiveSearch.Agent.RequestEvidence.criterion
#print axioms ConstitutiveSearch.Agent.executed_reply_criterion
/- AXIOM_AUDIT_END -/
