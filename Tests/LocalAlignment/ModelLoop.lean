import RelationalPerimeter.Agents.Constitutive.PublicInstance

/-! Experimental composition: an arbitrary adaptive proposer uses the existing constructive
executor. Resetting the proposer's context does not reset the contract or the
constituted memory. Every accepted proposal consumes the actual shared producer;
an undecodable proposal has no machine effect. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local
open SAT Resources EndogenousDecomposition

structure Observation where
  scope : List Var
  available : Nat

def observe (memory : Memory) : Observation :=
  ⟨memory.requirement.realizedScope, memory.register.length⟩

structure Policy (Context : Type) where
  choose : Context → String → Observation → Context × Option Request
  reset : Context → Context

structure Signal where
  input : String
  forget : Bool

structure State (Context : Type) : Type 3 where
  memory : Memory
  context : Context

def resetContext {Context : Type} (policy : Policy Context) (state : State Context) : State Context :=
  ⟨state.memory, policy.reset state.context⟩

def selection {Context : Type} (policy : Policy Context) (state : State Context)
    (signal : Signal) : Context × Option Request :=
  policy.choose (if signal.forget then policy.reset state.context else state.context)
    signal.input (observe state.memory)

inductive DispatchEvidence (memory : Memory) :
    Option Request → (Memory × Option Event) → Type 3 where
  | rejected : DispatchEvidence memory none (memory, none)
  | executed (request : Request) (result : Memory × Event)
      (evidence : RequestEvidence memory request result) :
      DispatchEvidence memory (some request) (result.1, some result.2)

def dispatchCertified (memory : Memory) : (proposal : Option Request) →
    (result : Memory × Option Event) × DispatchEvidence memory proposal result
  | none => ⟨(memory, none), .rejected⟩
  | some request =>
      let produced := executeProducedInput memory request
      ⟨(produced.1.1, some produced.1.2), .executed request produced.1 produced.2⟩

def dispatch (memory : Memory) (proposal : Option Request) : Memory × Option Event :=
  (dispatchCertified memory proposal).1

structure Turn : Type 3 where
  proposal : Option Request
  event : Option Event

def takeTurn {Context : Type} (policy : Policy Context) (state : State Context)
    (signal : Signal) : State Context × Turn :=
  let chosen := selection policy state signal
  let produced := dispatchCertified state.memory chosen.2
  (⟨produced.1.1, chosen.1⟩, ⟨chosen.2, produced.1.2⟩)

def run {Context : Type} (policy : Policy Context) :
    State Context → List Signal → State Context × List Turn
  | state, [] => (state, [])
  | state, signal :: rest =>
      let head := takeTurn policy state signal
      let tail := run policy head.1 rest
      (tail.1, head.2 :: tail.2)

/-- The evidence is indexed by the actual successive selections and memories,
including the rejection path. It is not supplied by the proposer. -/
inductive CertifiedRun {Context : Type} (policy : Policy Context) :
    State Context → List Signal → Type 3 where
  | nil (state : State Context) : CertifiedRun policy state []
  | cons (state : State Context) (signal : Signal) (rest : List Signal)
      (evidence : DispatchEvidence state.memory (selection policy state signal).2
        (dispatch state.memory (selection policy state signal).2))
      (tail : CertifiedRun policy (takeTurn policy state signal).1 rest) :
      CertifiedRun policy state (signal :: rest)

def certifyRun {Context : Type} (policy : Policy Context) :
    (state : State Context) → (signals : List Signal) → CertifiedRun policy state signals
  | state, [] => .nil state
  | state, signal :: rest =>
      .cons state signal rest (dispatchCertified state.memory (selection policy state signal).2).2
        (certifyRun policy (takeTurn policy state signal).1 rest)

theorem rejected_no_effect (memory : Memory) : dispatch memory none = (memory, none) := rfl

theorem accepted_entire_producer (memory : Memory) (request : Request) :
    dispatchCertified memory (some request) =
      let produced := interactionProducer.operation (memory, ULift.up request, PUnit.unit)
      ⟨(produced.1.1, some produced.1.2), .executed request produced.1 produced.2⟩ := rfl

theorem dispatch_requirement (memory : Memory) (proposal : Option Request) :
    (dispatch memory proposal).1.requirement = memory.requirement := by
  cases proposal with
  | none => rfl
  | some request => exact executeInput_requirement memory request

theorem dispatch_monotone (memory : Memory) (proposal : Option Request) :
    memory.register.length ≤ (dispatch memory proposal).1.register.length := by
  cases proposal with
  | none => exact Nat.le_refl _
  | some request => exact executeInput_register_monotone memory request

theorem dispatch_old_read (memory : Memory) (proposal : Option Request) (handle var : Nat)
    (within : handle < memory.register.length) :
    readRegister (dispatch memory proposal).1.register handle var = readRegister memory.register handle var := by
  cases proposal with
  | none => rfl
  | some request => exact executeInput_old_read memory request handle var within

theorem reset_preserves_machine {Context : Type} (policy : Policy Context) (state : State Context) :
    (resetContext policy state).memory = state.memory := rfl

theorem turn_requirement {Context : Type} (policy : Policy Context) (state : State Context)
    (signal : Signal) :
    (takeTurn policy state signal).1.memory.requirement = state.memory.requirement :=
  dispatch_requirement state.memory (selection policy state signal).2

theorem all_adaptive_requirements {Context : Type} (policy : Policy Context)
    (state : State Context) (signals : List Signal) :
    (run policy state signals).1.memory.requirement = state.memory.requirement := by
  induction signals generalizing state with
  | nil => rfl
  | cons signal rest ih => exact (ih (takeTurn policy state signal).1).trans (turn_requirement policy state signal)

theorem all_adaptive_old_reads {Context : Type} (policy : Policy Context)
    (state : State Context) (signals : List Signal) (handle var : Nat)
    (within : handle < state.memory.register.length) :
    readRegister (run policy state signals).1.memory.register handle var =
      readRegister state.memory.register handle var := by
  induction signals generalizing state with
  | nil => rfl
  | cons signal rest ih =>
      have continued : handle < (takeTurn policy state signal).1.memory.register.length :=
        Nat.lt_of_lt_of_le within (dispatch_monotone state.memory (selection policy state signal).2)
      exact (ih (takeTurn policy state signal).1 continued).trans
        (dispatch_old_read state.memory (selection policy state signal).2 handle var within)

/-- Positive completion of a permitted obtain, even when the target must be
produced. No honesty or competence assumption on a proposing model is used. -/
theorem permitted_obtain_answer (memory : Memory) (handle var : Nat)
    (permission : Ref memory.requirement.realizedScope var) :
    (dispatch memory (some (.obtain handle var))).2 =
      some ⟨(executeInput memory (.obtain handle var)).2.productions,
        .answer handle var (obtainedAuthorization memory handle var permission).1⟩ := by
  change some (executeInput memory (.obtain handle var)).2 = _
  exact congrArg some (congrArg (Event.mk (executeInput memory (.obtain handle var)).2.productions)
    (obtain_produces_and_returns memory handle var permission))

def initialized {Context : Type} {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles)
    (context : Context) : State Context := ⟨start master requirement profile, context⟩

theorem forgotten_profiles_same_adaptive_run {Context : Type} {input : Nat}
    (master : UnifiedMaster.Instance input) (requirement : Requirement)
    (left right : RoleOccurrenceProfile master.roles) (context : Context)
    (policy : Policy Context) (signals : List Signal) :
    run policy (initialized master requirement left context) signals =
      run policy (initialized master requirement right context) signals :=
  congrArg (fun memory => run policy (State.mk memory context) signals)
    (initial_memories_equal master requirement left right)

/-- Fixed model context does not reintroduce the profile forgotten by the
constitutive normalization. An external archive is not part of this state. -/
theorem initial_profile_not_recoverable_combined {Context : Type} {input : Nat}
    (master : UnifiedMaster.Instance input) (requirement : Requirement) (context : Context) :
    ¬ (∃ recover : State Context → RoleOccurrenceProfile master.roles,
      ∀ profile, recover (initialized master requirement profile context) = profile) := by
  intro alleged
  obtain ⟨recover, correct⟩ := alleged
  exact initial_profile_not_recoverable master requirement
    ⟨fun memory => recover ⟨memory, context⟩, correct⟩

end ConstitutiveSearch.Agent.Local
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.observe
#print axioms ConstitutiveSearch.Agent.Local.resetContext
#print axioms ConstitutiveSearch.Agent.Local.selection
#print axioms ConstitutiveSearch.Agent.Local.DispatchEvidence
#print axioms ConstitutiveSearch.Agent.Local.dispatchCertified
#print axioms ConstitutiveSearch.Agent.Local.dispatch
#print axioms ConstitutiveSearch.Agent.Local.takeTurn
#print axioms ConstitutiveSearch.Agent.Local.run
#print axioms ConstitutiveSearch.Agent.Local.CertifiedRun
#print axioms ConstitutiveSearch.Agent.Local.certifyRun
#print axioms ConstitutiveSearch.Agent.Local.rejected_no_effect
#print axioms ConstitutiveSearch.Agent.Local.accepted_entire_producer
#print axioms ConstitutiveSearch.Agent.Local.dispatch_requirement
#print axioms ConstitutiveSearch.Agent.Local.dispatch_monotone
#print axioms ConstitutiveSearch.Agent.Local.dispatch_old_read
#print axioms ConstitutiveSearch.Agent.Local.reset_preserves_machine
#print axioms ConstitutiveSearch.Agent.Local.turn_requirement
#print axioms ConstitutiveSearch.Agent.Local.all_adaptive_requirements
#print axioms ConstitutiveSearch.Agent.Local.all_adaptive_old_reads
#print axioms ConstitutiveSearch.Agent.Local.permitted_obtain_answer
#print axioms ConstitutiveSearch.Agent.Local.initialized
#print axioms ConstitutiveSearch.Agent.Local.forgotten_profiles_same_adaptive_run
#print axioms ConstitutiveSearch.Agent.Local.initial_profile_not_recoverable_combined
/- AXIOM_AUDIT_END -/
