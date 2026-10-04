import RelationalPerimeter.Agents.Constitutive.State

/-! One current request, one shared execution, positive response authorization.
The worker receives no future-request tail. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent
open SAT Resources EndogenousDecomposition

structure Authorization (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (value : Bool) : Type 3 where
  permission : Ref requirement.realizedScope var
  occurrence : Located register
  occurrenceExact : resolveHandle register handle = some occurrence
  valueExact : value = occurrence.1.read var

inductive Decision (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (candidate : Option Bool) : Type 3 where
  | authorized (value : Bool) (witness : Authorization requirement register handle var value)
      (candidateExact : candidate = none ∨ candidate = some value)
  | outside (absent : requirement.permission var = none)
  | missing (permission : Ref requirement.realizedScope var)
      (absent : resolveHandle register handle = none)
  | incorrect (permission : Ref requirement.realizedScope var) (occurrence : Located register)
      (located : resolveHandle register handle = some occurrence) (value : Bool)
      (proposed : candidate = some value) (different : value ≠ occurrence.1.read var)

def decideReply (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (candidate : Option Bool) : Decision requirement register handle var candidate :=
  match permitted : requirement.permission var with
  | none => .outside permitted
  | some permission =>
    match located : resolveHandle register handle with
    | none => .missing permission located
    | some occurrence =>
      match candidate with
      | none => .authorized (occurrence.1.read var) ⟨permission, occurrence, located, rfl⟩ (.inl rfl)
      | some value =>
        if same : value = occurrence.1.read var then
          .authorized value ⟨permission, occurrence, located, same⟩ (.inr rfl)
        else .incorrect permission occurrence located value rfl same

inductive Message where
  | advanced (steps : Nat)
  | answer (handle : Nat) (var : Var) (value : Bool)
  | refused (handle : Nat) (var : Var) (reason : Refusal)
  deriving Repr

def Decision.message {requirement : Requirement} {register : List AnswerTarget}
    {handle : Nat} {var : Var} {candidate : Option Bool} :
    Decision requirement register handle var candidate → Message
  | .authorized value _ _ => .answer handle var value
  | .outside _ => .refused handle var .outsideScope
  | .missing _ _ => .refused handle var .missingHandle
  | .incorrect _ _ _ _ _ _ => .refused handle var .incorrectValue

structure Event : Type 3 where
  productions : List LiveContinuation.Event
  message : Message

/-- The response specification is independent of the responder: it refers
to scope membership, an actual occurrence, its value, or a proved refusal. -/
inductive ResponseEvidence (requirement : Requirement) (register : List AnswerTarget)
    (handle : Nat) (var : Var) (candidate : Option Bool) : Message → Type 3 where
  | answer (value : Bool) (witness : Authorization requirement register handle var value)
      (candidateExact : candidate = none ∨ candidate = some value) :
      ResponseEvidence requirement register handle var candidate (.answer handle var value)
  | outside (absent : requirement.permission var = none) :
      ResponseEvidence requirement register handle var candidate (.refused handle var .outsideScope)
  | missing (permission : Ref requirement.realizedScope var)
      (absent : resolveHandle register handle = none) :
      ResponseEvidence requirement register handle var candidate (.refused handle var .missingHandle)
  | incorrect (permission : Ref requirement.realizedScope var) (occurrence : Located register)
      (located : resolveHandle register handle = some occurrence) (value : Bool)
      (proposed : candidate = some value) (different : value ≠ occurrence.1.read var) :
      ResponseEvidence requirement register handle var candidate (.refused handle var .incorrectValue)

def Decision.evidence {requirement : Requirement} {register : List AnswerTarget}
    {handle : Nat} {var : Var} {candidate : Option Bool}
    (decision : Decision requirement register handle var candidate) :
    ResponseEvidence requirement register handle var candidate decision.message :=
  match decision with
  | .authorized value witness exact => .answer value witness exact
  | .outside absent => .outside absent
  | .missing permission absent => .missing permission absent
  | .incorrect permission occurrence located value proposed different =>
      .incorrect permission occurrence located value proposed different

def RequestEvidence (memory : Memory) : (request : Request) → (Memory × Event) → Type 3
  | .advance count, result => ULift.{3} (PLift (result.2.message = .advanced count))
  | .inspect handle var, result =>
      ResponseEvidence memory.requirement memory.register handle var none result.2.message
  | .propose handle var value, result =>
      ResponseEvidence memory.requirement memory.register handle var (some value) result.2.message
  | .obtain handle var, result =>
      ResponseEvidence result.1.requirement result.1.register handle var none result.2.message

def step (memory : Memory) : Memory × LiveContinuation.Event :=
  let production := LiveContinuation.produce memory.live
  (⟨memory.requirement, production.next, memory.register ++ [resumedTarget production]⟩,
    ⟨memory.live, production⟩)

def runSteps : Nat → Memory → Memory × List LiveContinuation.Event
  | 0, memory => (memory, [])
  | count + 1, memory =>
      let head := step memory
      let tail := runSteps count head.1
      (tail.1, head.2 :: tail.2)

def needed (registerSize handle : Nat) : Nat := handle + 1 - registerSize

def performCertified (memory : Memory) :
    (request : Request) → (result : Memory × Event) × RequestEvidence memory request result
  | .advance count =>
      let produced := runSteps count memory
      ⟨(produced.1, ⟨produced.2, .advanced count⟩), ⟨⟨rfl⟩⟩⟩
  | .inspect handle var =>
      let decision := decideReply memory.requirement memory.register handle var none
      ⟨(memory, ⟨[], decision.message⟩), decision.evidence⟩
  | .propose handle var value =>
      let decision := decideReply memory.requirement memory.register handle var (some value)
      ⟨(memory, ⟨[], decision.message⟩), decision.evidence⟩
  | .obtain handle var =>
      match permitted : memory.requirement.permission var with
      | none => ⟨(memory, ⟨[], .refused handle var .outsideScope⟩), .outside permitted⟩
      | some _ =>
          let produced := runSteps (needed memory.register.length handle) memory
          let decision := decideReply produced.1.requirement produced.1.register handle var none
          ⟨(produced.1, ⟨produced.2, decision.message⟩), decision.evidence⟩

def perform (memory : Memory) (request : Request) : Memory × Event :=
  (performCertified memory request).1

theorem perform_obtain (memory : Memory) (handle : Nat) (var : Var) :
    perform memory (.obtain handle var) =
      match memory.requirement.permission var with
      | none => (memory, ⟨[], .refused handle var .outsideScope⟩)
      | some _ =>
          let produced := runSteps (needed memory.register.length handle) memory
          (produced.1, ⟨produced.2,
            (decideReply produced.1.requirement produced.1.register handle var none).message⟩) := by
  dsimp only [perform, performCertified, RequestEvidence]
  split
  · rename_i absent
    change (memory, Event.mk [] (.refused handle var .outsideScope)) = _
    rw [absent]
  · rename_i permission present
    change ((runSteps (needed memory.register.length handle) memory).1,
      Event.mk (runSteps (needed memory.register.length handle) memory).2
        (decideReply (runSteps (needed memory.register.length handle) memory).1.requirement
          (runSteps (needed memory.register.length handle) memory).1.register handle var none).message) = _
    rw [present]

/- The current checkpoint is received as a retained resource. Its scientific
origin is closed by Agreement, not asserted by the given constructor below.
The new result, unlike the checkpoint, is formed by this actual producer. -/
inductive InteractionKind : Type 3 where
  | memory
  | request
  | result (memory : Memory) (request : Request)

def InteractionValue : InteractionKind → Type 3
  | .memory => Memory
  | .request => ULift.{3} Request
  | .result memory request => (result : Memory × Event) × RequestEvidence memory request result

def interactionProducer : Producer InteractionValue [.request, .memory] where
  inputKinds := [.memory, .request]
  inputs := .cons (.prior .here) (.cons .here .nil)
  outputKind := fun args => .result args.1 args.2.1.down
  operation := fun args => performCertified args.1 args.2.1.down

def executeProducedInput (memory : Memory) (request : Request) :
    (result : Memory × Event) × RequestEvidence memory request result :=
  let retained := Support.given (Value := InteractionValue) (context := [.request, .memory])
    (⟨request⟩, memory, PUnit.unit)
  let produced := retained.extend interactionProducer
  produced.read .here

def executeInput (memory : Memory) (request : Request) : Memory × Event :=
  (executeProducedInput memory request).1

def executedEvidence (memory : Memory) (request : Request) :
    RequestEvidence memory request (executeInput memory request) :=
  (executeProducedInput memory request).2

theorem executeInput_exact (memory : Memory) (request : Request) :
    executeInput memory request = perform memory request := rfl

def executeRequests : Memory → List Request → Memory × List Event
  | memory, [] => (memory, [])
  | memory, request :: future =>
      let produced := executeInput memory request
      let rest := executeRequests produced.1 future
      (rest.1, produced.2 :: rest.2)

theorem length_append (one two : List AnswerTarget) :
    (one ++ two).length = one.length + two.length := by
  induction one with
  | nil => exact (Nat.zero_add _).symm
  | cons head tail ih =>
      change (tail ++ two).length + 1 = (tail.length + 1) + two.length
      rw [ih, Nat.add_right_comm]

theorem register_grows_by_one (memory : Memory) :
    (step memory).1.register.length = memory.register.length + 1 :=
  length_append _ _

theorem runSteps_length (count : Nat) (memory : Memory) :
    (runSteps count memory).1.register.length = memory.register.length + count := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih =>
      change (runSteps count (step memory).1).1.register.length = _
      rw [ih, register_grows_by_one, Nat.add_right_comm, Nat.add_assoc]

theorem runSteps_requirement (count : Nat) (memory : Memory) :
    (runSteps count memory).1.requirement = memory.requirement := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih => exact ih (step memory).1

theorem runSteps_event_count (count : Nat) (memory : Memory) :
    (runSteps count memory).2.length = count := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ (ih (step memory).1)

theorem runSteps_old_read (count : Nat) (memory : Memory) (handle : Nat) (var : Var)
    (within : handle < memory.register.length) :
    readRegister (runSteps count memory).1.register handle var = readRegister memory.register handle var := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih =>
      have extended : handle < (step memory).1.register.length := by
        rw [register_grows_by_one]
        exact Nat.lt_trans within (Nat.lt_succ_self _)
      exact (ih (step memory).1 extended).trans
        (readRegister_append _ _ _ _ within)

theorem needed_reaches : ∀ (size handle : Nat), handle < size + needed size handle
  | 0, handle => by
      change handle < 0 + (handle + 1)
      rw [Nat.zero_add]
      exact Nat.lt_succ_self _
  | size + 1, 0 => by
      unfold needed
      rw [Nat.succ_sub_succ, Nat.zero_sub]
      exact Nat.zero_lt_succ _
  | size + 1, handle + 1 => by
      unfold needed
      rw [Nat.succ_sub_succ, Nat.succ_add]
      exact Nat.succ_lt_succ (needed_reaches size handle)

theorem obtained_handle_present (memory : Memory) (handle : Nat) :
    (resolveHandle (runSteps (needed memory.register.length handle) memory).1.register handle).isSome = true := by
  apply resolveHandle_present
  rw [runSteps_length]
  exact needed_reaches _ _

theorem needed_zero : ∀ size handle, handle < size → needed size handle = 0
  | 0, _, impossible => False.elim (Nat.not_lt_zero _ impossible)
  | size + 1, 0, _ => by unfold needed; rw [Nat.succ_sub_succ, Nat.zero_sub]
  | size + 1, handle + 1, within => by
      unfold needed
      rw [Nat.succ_sub_succ]
      exact needed_zero size handle (Nat.lt_of_succ_lt_succ within)

theorem needed_exact : ∀ (size handle : Nat), size ≤ handle →
    size + needed size handle = handle + 1
  | 0, handle, _ => Nat.zero_add (handle + 1)
  | size + 1, 0, impossible => False.elim (Nat.not_succ_le_zero _ impossible)
  | size + 1, handle + 1, missing => by
      change (size + 1) + ((handle + 1 + 1) - (size + 1)) = (handle + 1) + 1
      exact (congrArg (fun value => (size + 1) + value)
        (Nat.succ_sub_succ (handle + 1) size)).trans
          ((Nat.succ_add size ((handle + 1) - size)).trans
            (congrArg Nat.succ (needed_exact size handle (Nat.le_of_succ_le_succ missing))))

theorem obtained_register_exact (memory : Memory) (handle : Nat)
    (missing : memory.register.length ≤ handle) :
    (runSteps (needed memory.register.length handle) memory).1.register.length = handle + 1 :=
  (runSteps_length _ _).trans (needed_exact _ _ missing)

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Authorization
#print axioms ConstitutiveSearch.Agent.decideReply
#print axioms ConstitutiveSearch.Agent.step
#print axioms ConstitutiveSearch.Agent.runSteps
#print axioms ConstitutiveSearch.Agent.perform
#print axioms ConstitutiveSearch.Agent.performCertified
#print axioms ConstitutiveSearch.Agent.perform_obtain
#print axioms ConstitutiveSearch.Agent.ResponseEvidence
#print axioms ConstitutiveSearch.Agent.Decision.evidence
#print axioms ConstitutiveSearch.Agent.RequestEvidence
#print axioms ConstitutiveSearch.Agent.executeProducedInput
#print axioms ConstitutiveSearch.Agent.executedEvidence
#print axioms ConstitutiveSearch.Agent.interactionProducer
#print axioms ConstitutiveSearch.Agent.executeInput
#print axioms ConstitutiveSearch.Agent.executeInput_exact
#print axioms ConstitutiveSearch.Agent.executeRequests
#print axioms ConstitutiveSearch.Agent.register_grows_by_one
#print axioms ConstitutiveSearch.Agent.runSteps_length
#print axioms ConstitutiveSearch.Agent.runSteps_requirement
#print axioms ConstitutiveSearch.Agent.runSteps_event_count
#print axioms ConstitutiveSearch.Agent.needed_zero
#print axioms ConstitutiveSearch.Agent.needed_exact
#print axioms ConstitutiveSearch.Agent.obtained_register_exact
#print axioms ConstitutiveSearch.Agent.runSteps_old_read
#print axioms ConstitutiveSearch.Agent.needed_reaches
#print axioms ConstitutiveSearch.Agent.obtained_handle_present
/- AXIOM_AUDIT_END -/
