import RelationalPerimeter.Agents.Constitutive.Persistence
import RelationalPerimeter.Constitution.Continuation.Minimality

/-! Signatures for the full existing agent contract at a fixed master and
received requirement. Sources retain their constituted histories in the
specification only. The signature counts executed productions; the runtime
agent and all its requests, events, refusals and rights are unchanged. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.ContinuationSignatures.ReachableAgent
open EndogenousDecomposition

def steps {input : Nat} {master : UnifiedMaster.Instance input}
    {profile : RoleOccurrenceProfile master.roles} : Agent.History master profile → Nat
  | .initial => 0
  | .step past => steps past + 1

theorem histories_same {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement)
    {left right : RoleOccurrenceProfile master.roles}
    (first : Agent.History master left) (second : Agent.History master right)
    (same : steps first = steps second) :
    first.cursor = second.cursor ∧ first.targets = second.targets := by
  induction first generalizing right with
  | initial =>
      cases second with
      | initial =>
          exact ⟨rfl, congrArg Agent.Memory.register
            (Agent.initial_memories_equal master requirement left right)⟩
      | step past => cases same
  | step past ih =>
      cases second with
      | initial => cases same
      | step other =>
          obtain ⟨cursor, targets⟩ := ih other (Nat.succ.inj same)
          exact ⟨congrArg MasterResources.Cursor.next cursor,
            (congrArg (fun xs => xs ++ [Agent.resumedTarget
              (LiveContinuation.sourceProduction past.cursor)]) targets).trans
              (congrArg (fun c => other.targets ++ [Agent.resumedTarget
                (LiveContinuation.sourceProduction c)]) cursor)⟩

def Reachable {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) :=
  { source : Agent.Source master // source.requirement = requirement }

def signature {input : Nat} {master : UnifiedMaster.Instance input}
    {requirement : Agent.Requirement} (source : Reachable master requirement) : Nat :=
  steps source.1.history

theorem memory_same {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (left right : Reachable master requirement)
    (same : signature left = signature right) : Agent.project left.1 = Agent.project right.1 := by
  obtain ⟨cursor, targets⟩ := histories_same master requirement left.1.history right.1.history same
  change Agent.Memory.mk left.1.requirement (LiveContinuation.project left.1.history.cursor) _ =
    Agent.Memory.mk right.1.requirement (LiveContinuation.project right.1.history.cursor) _
  rw [left.2, right.2, cursor, targets]

theorem targets_length {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement)
    {profile : RoleOccurrenceProfile master.roles} (history : Agent.History master profile) :
    history.targets.length = resolutionLength input + steps history := by
  induction history with
  | initial => exact Agent.start_register_length master requirement profile
  | step past ih =>
      change (past.targets ++ [_]).length = _
      rw [Agent.length_append, ih]
      exact Nat.add_assoc _ _ _

theorem length_append {α : Type} (first second : List α) :
    (first ++ second).length = first.length + second.length := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons _ rest ih =>
      change (rest ++ second).length + 1 = (rest.length + 1) + second.length
      rw [ih, Nat.add_right_comm]

theorem length_map {α β : Type} (f : α → β) (items : List α) :
    (items.map f).length = items.length := by
  induction items with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem cancel_prefix (base left right : Nat) (same : base + left = base + right) :
    left = right := by
  induction base with
  | zero => exact (Nat.zero_add left).symm.trans (same.trans (Nat.zero_add right))
  | succ base ih =>
      exact ih (Nat.succ.inj ((Nat.succ_add base left).symm.trans
        (same.trans (Nat.succ_add base right))))

theorem table_length (register : List Agent.AnswerTarget) (scope : List SAT.Var) :
    (Agent.table register scope).length = register.length * scope.length := by
  unfold Agent.table
  suffices all : ∀ handle, (Agent.table.rows scope handle register).length = register.length * scope.length from all 0
  intro handle
  induction register generalizing handle with
  | nil => exact (Nat.zero_mul _).symm
  | cons head rest ih =>
      change (scope.map (fun var => (handle, var, head.read var)) ++ _).length = _
      rw [length_append, length_map, ih]
      exact (Nat.add_comm _ _).trans (Nat.succ_mul rest.length scope.length).symm

theorem steps_of_read_same {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (left right : Reachable master requirement)
    (same : (Agent.bridge master).sourceRead left.1 = (Agent.bridge master).sourceRead right.1) :
    signature left = signature right := by
  have lengths := congrArg List.length same
  change (Agent.table left.1.history.realization.materialRegister left.1.requirement.scope).length =
    (Agent.table right.1.history.realization.materialRegister right.1.requirement.scope).length at lengths
  rw [left.1.history.realization.materialRegister_exact,
    right.1.history.realization.materialRegister_exact, left.2, right.2,
    table_length, table_length, targets_length master requirement,
    targets_length master requirement] at lengths
  have positive : 0 < requirement.scope.length := by
    cases scopeExact : requirement.scope with
    | nil => exact False.elim (requirement.nonempty scopeExact)
    | cons _ _ => exact Nat.zero_lt_succ _
  exact cancel_prefix _ _ _ (Nat.eq_of_mul_eq_mul_right positive lengths)

def decideAdmission (memory : Agent.Memory) :
    (request : Agent.Request) → PSum (Agent.Admission memory.requirement memory.register request)
      (Agent.Admission memory.requirement memory.register request → False)
  | .advance _ => .inl ⟨()⟩
  | .obtain _ var =>
      match present : memory.requirement.permission var with
      | some permission => .inl ⟨permission⟩
      | none => .inr (fun witness => Agent.resolvePermission_none _ _ present witness.down)
  | .inspect handle var =>
      match Agent.decideReply memory.requirement memory.register handle var none with
      | .authorized value witness _ => .inl ⟨⟨value, witness⟩⟩
      | .outside absent => .inr (fun witness =>
          Agent.resolvePermission_none _ _ absent witness.down.2.permission)
      | .missing _ absent => .inr (fun witness => by
          have impossible := absent.symm.trans witness.down.2.occurrenceExact
          cases impossible)
      | .incorrect _ _ _ _ proposed _ => nomatch proposed
  | .propose handle var value =>
      match Agent.decideReply memory.requirement memory.register handle var (some value) with
      | .authorized actual witness exact =>
          let same : value = actual := by
            cases exact with
            | inl impossible => cases impossible
            | inr equal => exact Option.some.inj equal
          .inl ⟨same.symm ▸ witness⟩
      | .outside absent => .inr (fun witness =>
          Agent.resolvePermission_none _ _ absent witness.down.permission)
      | .missing _ absent => .inr (fun witness => by
          have impossible := absent.symm.trans witness.down.occurrenceExact
          cases impossible)
      | .incorrect _ occurrence located actual proposed different => .inr (fun witness => by
          have values : value = actual := Option.some.inj proposed
          have occurrences := Option.some.inj (witness.down.occurrenceExact.symm.trans located)
          exact different (values.symm.trans (witness.down.valueExact.trans
            (congrArg (fun item => item.1.read var) occurrences))))

def runtimeContract : FutureContract Agent.Memory (ULift.{3} Agent.Request)
    Agent.Event (ULift.{3} (List (Nat × SAT.Var × Bool))) where
  next := fun memory request => (Agent.executeInput memory request.down).1
  event := fun memory request => (Agent.executeInput memory request.down).2
  read := fun memory => ⟨Agent.table memory.register memory.requirement.realizedScope⟩
  Allow := fun memory request => Agent.Admission memory.requirement memory.register request.down
  decision := fun memory request => decideAdmission memory request.down

theorem source_requirement {input : Nat} {master : UnifiedMaster.Instance input}
    (source : Agent.Source master) (request : Agent.Request) :
    (Agent.sourcePerform source request).1.requirement = source.requirement :=
  (congrArg (fun result : Agent.Memory × Agent.Event => result.1.requirement)
    (Agent.sourcePerform_exact source request)).trans (Agent.executeInput_requirement _ _)

def next {input : Nat} {master : UnifiedMaster.Instance input} {requirement : Agent.Requirement}
    (source : Reachable master requirement) (request : ULift.{3} Agent.Request) :
    Reachable master requirement :=
  ⟨(Agent.sourcePerform source.1 request.down).1,
    (source_requirement source.1 request.down).trans source.2⟩

def contract {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    FutureContract (Reachable master requirement) (ULift.{3} Agent.Request)
      Agent.Event (ULift.{3} (List (Nat × SAT.Var × Bool))) where
  next := next
  event := fun source request => (Agent.sourcePerform source.1 request.down).2
  read := fun source => ⟨(Agent.bridge master).sourceRead source.1⟩
  Allow := fun source request => Agent.RichAdmission source.1.requirement
    source.1.history.realization request.down
  decision := fun source request =>
    match decideAdmission (Agent.project source.1) request.down with
    | .inl witness => .inl (Agent.receivedAdmission _ _ _ witness)
    | .inr impossible => .inr (fun witness =>
        impossible (Agent.realizeAdmission _ _ _ witness))

def realization {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    ExactRealization (contract master requirement) Agent.Memory where
  reduced := runtimeContract
  project := fun source => Agent.project source.1
  forward := fun source request => Agent.realizeAdmission source.1.requirement
    source.1.history.realization request.down
  backward := fun source request => Agent.receivedAdmission source.1.requirement
    source.1.history.realization request.down
  backward_forward := fun source request witness =>
    Agent.admission_received_return source.1.requirement source.1.history.realization request.down witness
  forward_backward := fun source request witness =>
    Agent.admission_realized_return source.1.requirement source.1.history.realization request.down witness
  next_exact := fun source request => congrArg Prod.fst (Agent.sourcePerform_exact source.1 request.down)
  event_exact := fun source request => congrArg Prod.snd (Agent.sourcePerform_exact source.1 request.down)
  read_exact := fun source => congrArg ULift.up ((Agent.bridge master).readLaw source.1)

theorem signature_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (left right : Reachable master requirement) :
    signature left = signature right ↔ FutureEquivalent (contract master requirement) left right :=
  ⟨fun same => (realization master requirement).equal_memory_same_futures
      (memory_same master requirement left right same),
    fun same => steps_of_read_same master requirement left right (congrArg ULift.down same.read)⟩

def basis {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    FiniteFutureBasis (contract master requirement) where
  tests := [[]]
  complete := fun left right agreement =>
    (signature_exact master requirement left right).mp
      (steps_of_read_same master requirement left right
        (congrArg (fun result => result.read.down) (agreement [] (.head _))))

def separator {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement)
    (left right : Reachable master requirement) (different : signature left ≠ signature right) :
    FutureSeparator (contract master requirement) left right :=
  ⟨[], fun same => different (steps_of_read_same master requirement left right
    (congrArg (fun result => result.read.down) same))⟩

theorem necessary_distinctions {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) {Memory : Type 3}
    (other : ExactRealization (contract master requirement) Memory)
    {left right : Reachable master requirement} (same : other.project left = other.project right) :
    signature left = signature right :=
  (signature_exact master requirement left right).mpr (other.equal_memory_same_futures same)

theorem run_steps_count {input : Nat} {master : UnifiedMaster.Instance input}
    (count : Nat) (source : Agent.Source master) :
    steps (Agent.sourceRunSteps count source).1.history = steps source.history + count := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih =>
      change steps (Agent.sourceRunSteps count (Agent.sourceStep source).1).1.history = _
      exact (ih _).trans (Nat.add_right_comm _ 1 count)

def update (input : Nat) (requirement : Agent.Requirement) (current : Nat) : Agent.Request → Nat
  | .advance count => current + count
  | .inspect _ _ => current
  | .propose _ _ _ => current
  | .obtain handle var => match requirement.permission var with
      | none => current
      | some _ => current + Agent.needed (resolutionLength input + current) handle

theorem update_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : Reachable master requirement) (request : Agent.Request) :
    signature (next source ⟨request⟩) = update input requirement (signature source) request := by
  obtain ⟨⟨actual, profile, history⟩, same⟩ := source
  cases same
  cases request with
  | advance count => exact run_steps_count count ⟨actual, profile, history⟩
  | inspect _ _ => rfl
  | propose _ _ _ => rfl
  | obtain handle var =>
      change steps (Agent.sourcePerform (Agent.Source.mk actual profile history) (.obtain handle var)).1.history = _
      rw [Agent.sourcePerform_obtain]
      dsimp only [update]
      cases allowed : actual.permission var with
      | none => rfl
      | some permission =>
          dsimp only
          rw [history.realization.materialRegister_exact, targets_length master actual]
          exact run_steps_count _ ⟨actual, profile, history⟩

def dynamics {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    Nat → List Agent.Request → Nat
  | count, [] => count
  | count, head :: tail => dynamics master requirement (update input requirement count head) tail

theorem dynamics_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : Reachable master requirement) (requests : List Agent.Request) :
    signature (Grouping.Continuation.run next source (requests.map ULift.up)) =
      dynamics master requirement (signature source) requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
      exact (ih (next source ⟨request⟩)).trans
        (congrArg (fun count => dynamics master requirement count rest)
          (update_exact master requirement source request))

def memorySignature (input : Nat) (memory : Agent.Memory) : Nat :=
  memory.register.length - resolutionLength input

theorem subtract_base (base value : Nat) : base + value - base = value := by
  induction base with
  | zero => exact congrArg (fun n => n - 0) (Nat.zero_add value)
  | succ base ih =>
      exact (congrArg (fun n => n - (base + 1)) (Nat.succ_add base value)).trans
        ((Nat.succ_sub_succ_eq_sub _ _).trans ih)

theorem memorySignature_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : Reachable master requirement) :
    memorySignature input (Agent.project source.1) = signature source :=
  (congrArg (fun count => count - resolutionLength input)
    (targets_length master requirement source.1.history)).trans (subtract_base _ _)

/-- Data comes from the actual executed result, not a rich-history callback. -/
def executeSignedInput (input : Nat) (memory : Agent.Memory) (request : Agent.Request) :
    Agent.Memory × Agent.Event × Nat :=
  let produced := Agent.executeProducedInput memory request
  (produced.1.1, produced.1.2, memorySignature input produced.1.1)

theorem executeSignedInput_erases (input : Nat) (memory : Agent.Memory) (request : Agent.Request) :
    ((executeSignedInput input memory request).1, (executeSignedInput input memory request).2.1) =
      Agent.executeInput memory request := rfl

theorem executeSignedInput_signature {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : Reachable master requirement) (request : Agent.Request) :
    (executeSignedInput input (Agent.project source.1) request).2.2 =
      update input requirement (signature source) request :=
  ((congrArg (memorySignature input)
    (congrArg Prod.fst (Agent.sourcePerform_exact source.1 request)).symm).trans
      (memorySignature_exact master requirement (next source ⟨request⟩))).trans
        (update_exact master requirement source request)

def historyAt {input : Nat} (master : UnifiedMaster.Instance input)
    (profile : RoleOccurrenceProfile master.roles) : Nat → Agent.History master profile
  | 0 => .initial
  | count + 1 => .step (historyAt master profile count)

theorem historyAt_count {input : Nat} (master : UnifiedMaster.Instance input)
    (profile : RoleOccurrenceProfile master.roles) (count : Nat) :
    steps (historyAt master profile count) = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ ih

def coveredSource {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (count : Nat) : Reachable master requirement :=
  ⟨⟨requirement, master.distinctPair.left, historyAt master master.distinctPair.left count⟩, rfl⟩

theorem every_signature_reachable {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (count : Nat) :
    signature (coveredSource master requirement count) = count := historyAt_count _ _ _

theorem source_run_requirement {input : Nat} {master : UnifiedMaster.Instance input}
    (count : Nat) (source : Agent.Source master) :
    (Agent.sourceRunSteps count source).1.requirement = source.requirement := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih => exact ih (Agent.sourceStep source).1

/-- Canonical realization reconstructed by the real runtime engine. It does
not store any source profile or rich history in its count state. Its rebuilding
work is real and must not be advertised as a constant-cost response. -/
def canonicalMemory {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (count : Nat) : Agent.Memory :=
  (Agent.runSteps count (Agent.start master requirement master.distinctPair.left)).1

theorem memory_canonical {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : Reachable master requirement) :
    Agent.project source.1 = canonicalMemory master requirement (signature source) := by
  let origin := Agent.sourceStart master requirement master.distinctPair.left
  let canonical : Reachable master requirement :=
    ⟨(Agent.sourceRunSteps (signature source) origin).1,
      source_run_requirement (signature source) origin⟩
  have count : signature canonical = signature source :=
    (run_steps_count (signature source) origin).trans (Nat.zero_add _)
  exact (memory_same master requirement source canonical count.symm).trans
    (congrArg Prod.fst (Agent.sourceRunSteps_exact (signature source) origin))

def move {α : Type 3} {family : α → Type 3} {a b : α}
    (same : a = b) (witness : family a) : family b := same ▸ witness

theorem move_return {α : Type 3} {family : α → Type 3} {a b : α}
    (same : a = b) (witness : family a) :
    move same.symm (move same witness) = witness := by
  cases same
  rfl

def countContract {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    FutureContract (ULift.{3} Nat) (ULift.{3} Agent.Request)
      Agent.Event (ULift.{3} (List (Nat × SAT.Var × Bool))) where
  next := fun count request => ⟨update input requirement count.down request.down⟩
  event := fun count request => runtimeContract.event (canonicalMemory master requirement count.down) request
  read := fun count => runtimeContract.read (canonicalMemory master requirement count.down)
  Allow := fun count request => runtimeContract.Allow (canonicalMemory master requirement count.down) request
  decision := fun count request => runtimeContract.decision (canonicalMemory master requirement count.down) request

def countRealization {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    ExactRealization (contract master requirement) (ULift.{3} Nat) where
  reduced := countContract master requirement
  project := fun source => ⟨signature source⟩
  forward := fun source request witness =>
    move (family := fun memory => runtimeContract.Allow memory request)
      (memory_canonical master requirement source)
      ((realization master requirement).forward source request witness)
  backward := fun source request witness =>
    (realization master requirement).backward source request
      (move (family := fun memory => runtimeContract.Allow memory request)
        (memory_canonical master requirement source).symm witness)
  backward_forward := fun source request witness =>
    (congrArg ((realization master requirement).backward source request)
      (move_return (family := fun memory => runtimeContract.Allow memory request)
        (memory_canonical master requirement source)
        ((realization master requirement).forward source request witness))).trans
      ((realization master requirement).backward_forward source request witness)
  forward_backward := fun source request witness =>
    (congrArg (move (family := fun memory => runtimeContract.Allow memory request)
        (memory_canonical master requirement source))
      ((realization master requirement).forward_backward source request
        (move (family := fun memory => runtimeContract.Allow memory request)
          (memory_canonical master requirement source).symm witness))).trans
      (move_return (family := fun memory => runtimeContract.Allow memory request)
        (memory_canonical master requirement source).symm witness)
  next_exact := fun source request => congrArg ULift.up (update_exact master requirement source request.down)
  event_exact := fun source request =>
    ((realization master requirement).event_exact source request).trans
      (congrArg (fun memory => runtimeContract.event memory request)
        (memory_canonical master requirement source))
  read_exact := fun source =>
    ((realization master requirement).read_exact source).trans
      (congrArg runtimeContract.read (memory_canonical master requirement source))

def countCoverage {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    PositiveCoverage (countRealization master requirement) where
  representative := fun count => ⟨coveredSource master requirement count.down,
    congrArg ULift.up (every_signature_reachable master requirement count.down)⟩

def recoverCount {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement)
    {Memory : Type 3} (other : ExactRealization (contract master requirement) Memory)
    (coverage : PositiveCoverage other) (memory : Memory) : Nat :=
  signature (coverage.representative memory).1

theorem recoverCount_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) {Memory : Type 3}
    (other : ExactRealization (contract master requirement) Memory) (coverage : PositiveCoverage other)
    (source : Reachable master requirement) :
    recoverCount master requirement other coverage (other.project source) = signature source :=
  necessary_distinctions master requirement other (coverage.representative (other.project source)).2

theorem no_singleton_realization {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) :
    ExactRealization (contract master requirement) (ULift.{3} Unit) → False := by
  intro other
  let first := coveredSource master requirement 0
  let second := coveredSource master requirement 1
  have sameMemory : other.project first = other.project second := by
    cases other.project first with
    | up value => cases value; cases other.project second with
      | up value => cases value; rfl
  have countSame := necessary_distinctions master requirement other sameMemory
  have impossible : 0 = 1 :=
    (every_signature_reachable master requirement 0).symm.trans
      (countSame.trans (every_signature_reachable master requirement 1))
  cases impossible

structure Certificate {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) where
  private mk ::
  exact : ∀ left right : Reachable master requirement,
    signature left = signature right ↔ FutureEquivalent (contract master requirement) left right
  realization : ExactRealization (contract master requirement) (ULift.{3} Nat)
  realizationExact : realization = countRealization master requirement
  coverage : PositiveCoverage realization
  updates : ∀ (source : Reachable master requirement) request, signature (next source ⟨request⟩) =
    update input requirement (signature source) request
  productionExact : ∀ (source : Reachable master requirement) request,
    (executeSignedInput input (Agent.project source.1) request).2.2 =
      update input requirement (signature source) request
  necessary : ∀ {Memory : Type 3} (other : ExactRealization (contract master requirement) Memory)
    {left right}, other.project left = other.project right → signature left = signature right

def certify {input : Nat} (master : UnifiedMaster.Instance input) (requirement : Agent.Requirement) :
    Certificate master requirement :=
  ⟨signature_exact master requirement, countRealization master requirement, rfl,
    countCoverage master requirement, update_exact master requirement,
    executeSignedInput_signature master requirement, necessary_distinctions master requirement⟩

def receivedSingleton (var : SAT.Var) : Agent.Requirement :=
  (Agent.receive [var]).get (Agent.receive_nonempty var [])

def publicCertificate (input : Nat) (var : SAT.Var) :
    Certificate (UnifiedMaster.publicInstance input) (receivedSingleton var) :=
  certify (UnifiedMaster.publicInstance input) (receivedSingleton var)

end ConstitutiveSearch.ContinuationSignatures.ReachableAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.steps
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.histories_same
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.memory_same
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.targets_length
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.table_length
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.steps_of_read_same
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.length_append
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.length_map
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.cancel_prefix
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.decideAdmission
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.runtimeContract
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.source_requirement
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.next
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.contract
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.realization
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.signature_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.basis
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.separator
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.necessary_distinctions
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.run_steps_count
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.update
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.update_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.dynamics
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.dynamics_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.memorySignature
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.subtract_base
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.memorySignature_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.executeSignedInput
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.executeSignedInput_erases
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.executeSignedInput_signature
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.historyAt
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.historyAt_count
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.coveredSource
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.every_signature_reachable
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.source_run_requirement
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.canonicalMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.memory_canonical
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.move
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.move_return
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.countContract
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.countRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.countCoverage
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.recoverCount
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.recoverCount_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.no_singleton_realization
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.Certificate
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.certify
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.receivedSingleton
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableAgent.publicCertificate
/- AXIOM_AUDIT_END -/
