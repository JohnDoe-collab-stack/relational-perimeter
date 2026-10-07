import RelationalPerimeter.Agents.Constitutive.Execution
import RelationalPerimeter.Constitution.Continuation.Minimality

/-!
An isolated connected-channel prototype, not a replacement for the agent.
The received channel authorizes one variable. Runtime memory retains the real
live engine and a materialized bit. Old targets remain on the specification
side only. The future contract permits sample and one actual discovery step;
it does not promise arbitrary historical handle/variable inspection.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.DirectMachine
open SAT Resources EndogenousDecomposition ContinuationSignatures

/-- A connection is authorized once, before its repeated use. -/
structure Channel where
  requirement : Agent.Requirement
  query : Var
  permission : Ref requirement.realizedScope query

def connect (requirement : Agent.Requirement) (query : Var) : Option Channel :=
  (requirement.permission query).map (fun permission => ⟨requirement, query, permission⟩)

def singletonChannel (query : Var) : Channel :=
  let requirement := (Agent.receive [query]).get (Agent.receive_nonempty query [])
  ⟨requirement, query, by change Ref [query] query; exact .here⟩

/-- The retained port has no callback, target, profile, or trace field. -/
structure Wire where
  private mk ::
  bit : Bool

def Wire.read (wire : Wire) : Bool := wire.bit

def Wire.fromTarget (channel : Channel) (target : Agent.AnswerTarget) : Wire :=
  ⟨target.read channel.query⟩

def producedWire (channel : Channel) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) : Wire :=
  ⟨production.built.stage.application.output.1 channel.query⟩

theorem producedWire_exact (channel : Channel) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    (producedWire channel production).read = (Agent.resumedTarget production).read channel.query := rfl

structure Memory : Type 3 where
  live : LiveContinuation.Memory
  wire : Wire

/-- Keep the live engine observations of the existing continuation contract. -/
def Memory.view (memory : Memory) : (Nat × List Var × Nat) × Bool :=
  (LiveContinuation.read memory.live, memory.wire.read)

inductive Request where
  | tick
  | sample

inductive Event where
  | produced (value : Bool)
  | sampled (value : Bool)

/-- One shared production supplies both the next engine and the connected bit. -/
def emit (channel : Channel) (live : LiveContinuation.Memory) : Memory × Event :=
  let production := LiveContinuation.produce live
  let wire := producedWire channel production
  (⟨production.next, wire⟩, .produced wire.read)

def perform (channel : Channel) (memory : Memory) : Request → Memory × Event
  | .tick => emit channel memory.live
  | .sample => (memory, .sampled memory.wire.read)

def execute (channel : Channel) : Memory → List Request → Memory × List Event
  | memory, [] => (memory, [])
  | memory, request :: rest =>
      let head := perform channel memory request
      let tail := execute channel head.1 rest
      (tail.1, head.2 :: tail.2)

/-- Rich specification only. No Source is stored in runtime Memory. -/
structure Source : Type 3 where
  live : LiveContinuation.Memory
  target : Agent.AnswerTarget

def project (channel : Channel) (source : Source) : Memory :=
  ⟨source.live, Wire.fromTarget channel source.target⟩

def sourceEmit (live : LiveContinuation.Memory) : Source :=
  let production := LiveContinuation.produce live
  ⟨production.next, Agent.resumedTarget production⟩

def sourcePerform (channel : Channel) (source : Source) : Request → Source × Event
  | .tick =>
      let next := sourceEmit source.live
      (next, .produced (next.target.read channel.query))
  | .sample => (source, .sampled (source.target.read channel.query))

theorem transition_exact (channel : Channel) (source : Source) (request : Request) :
    project channel (sourcePerform channel source request).1 =
      (perform channel (project channel source) request).1 := by
  cases request <;> rfl

theorem event_exact (channel : Channel) (source : Source) (request : Request) :
    (sourcePerform channel source request).2 =
      (perform channel (project channel source) request).2 := by
  cases request <;> rfl

def sourceExecute (channel : Channel) : Source → List Request → Source × List Event
  | source, [] => (source, [])
  | source, request :: rest =>
      let head := sourcePerform channel source request
      let tail := sourceExecute channel head.1 rest
      (tail.1, head.2 :: tail.2)

/-- The fused runtime loop, not merely its single-step specification. -/
theorem execute_exact (channel : Channel) (source : Source) (requests : List Request) :
    (project channel (sourceExecute channel source requests).1,
      (sourceExecute channel source requests).2) =
      execute channel (project channel source) requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
      let head := sourcePerform channel source request
      have next := ih head.1
      change (project channel (sourceExecute channel head.1 rest).1,
        head.2 :: (sourceExecute channel head.1 rest).2) = _
      have whole := congrArg (fun result : Memory × List Event =>
        (result.1, head.2 :: result.2)) next
      exact whole.trans (by
        rw [event_exact channel source request, transition_exact channel source request]
        rfl)

def sourceContract (channel : Channel) :
    FutureContract Source (ULift.{3} Request) Event ((Nat × List Var × Nat) × Bool) where
  next source request := (sourcePerform channel source request.down).1
  event source request := (sourcePerform channel source request.down).2
  read source := (LiveContinuation.read source.live, source.target.read channel.query)
  Allow _ _ := ULift.{3} Unit
  decision _ _ := .inl ⟨()⟩

def runtimeContract (channel : Channel) :
    FutureContract Memory (ULift.{3} Request) Event ((Nat × List Var × Nat) × Bool) where
  next memory request := (perform channel memory request.down).1
  event memory request := (perform channel memory request.down).2
  read := Memory.view
  Allow _ _ := ULift.{3} Unit
  decision _ _ := .inl ⟨()⟩

def realization (channel : Channel) : ExactRealization (sourceContract channel) Memory where
  reduced := runtimeContract channel
  project := project channel
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact source request := transition_exact channel source request.down
  event_exact source request := event_exact channel source request.down
  read_exact _ := rfl

theorem all_futures_exact (channel : Channel) (source : Source)
    (requests : List (ULift.{3} Request)) :
    (sourceContract channel).outcome source requests =
      (runtimeContract channel).outcome (project channel source) requests :=
  (realization channel).outcome_exact source requests

theorem different_bits_cannot_merge (channel : Channel) {left right : Source}
    (different : left.target.read channel.query ≠ right.target.read channel.query)
    {Other : Type 3} (other : ExactRealization (sourceContract channel) Other) :
    other.project left ≠ other.project right := by
  intro same
  exact different (congrArg Prod.snd (other.equal_memory_same_futures same).read)

theorem different_engine_views_cannot_merge (channel : Channel) {left right : Source}
    (different : LiveContinuation.read left.live ≠ LiveContinuation.read right.live)
    {Other : Type 3} (other : ExactRealization (sourceContract channel) Other) :
    other.project left ≠ other.project right := by
  intro same
  exact different (congrArg Prod.fst (other.equal_memory_same_futures same).read)

theorem same_live_and_bit_same_futures (channel : Channel) (left right : Source)
    (live : left.live = right.live)
    (bit : left.target.read channel.query = right.target.read channel.query) :
    FutureEquivalent (sourceContract channel) left right := by
  apply (realization channel).equal_memory_same_futures
  change Memory.mk left.live (Wire.mk _) = Memory.mk right.live (Wire.mk _)
  rw [live, bit]

theorem sample_keeps_state (channel : Channel) (memory : Memory) :
    (perform channel memory .sample).1 = memory := rfl

theorem tick_matches_agent_engine (channel : Channel) (memory : Memory) :
    (perform channel memory .tick).1.live =
      (Agent.step ⟨channel.requirement, memory.live, []⟩).1.live := rfl

theorem tick_matches_agent_reply (channel : Channel) (memory : Memory) :
    Agent.readRegister (Agent.step ⟨channel.requirement, memory.live, []⟩).1.register
      0 channel.query = some (perform channel memory .tick).1.wire.read := rfl

theorem emitted_target_accepted (live : LiveContinuation.Memory) :
    GeneratedStructuralBranchAccept (sourceEmit live).target.context
      (sourceEmit live).target.continuation := (sourceEmit live).target.accepted

def boot (channel : Channel) (live : LiveContinuation.Memory) : Memory × Event := emit channel live

theorem boot_exact (channel : Channel) (live : LiveContinuation.Memory) :
    (boot channel live).1 = project channel (sourceEmit live) := rfl

/-- No replay from a count: initialization reads the master's actual live cursor. -/
def bootMaster {input : Nat} (channel : Channel) (master : UnifiedMaster.Instance input) :
    Memory × Event := boot channel (LiveContinuation.project master.cursor)

end ConstitutiveSearch.DirectMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.DirectMachine.connect
#print axioms ConstitutiveSearch.DirectMachine.singletonChannel
#print axioms ConstitutiveSearch.DirectMachine.Wire.read
#print axioms ConstitutiveSearch.DirectMachine.producedWire
#print axioms ConstitutiveSearch.DirectMachine.producedWire_exact
#print axioms ConstitutiveSearch.DirectMachine.emit
#print axioms ConstitutiveSearch.DirectMachine.perform
#print axioms ConstitutiveSearch.DirectMachine.execute
#print axioms ConstitutiveSearch.DirectMachine.Memory.view
#print axioms ConstitutiveSearch.DirectMachine.sourceExecute
#print axioms ConstitutiveSearch.DirectMachine.execute_exact
#print axioms ConstitutiveSearch.DirectMachine.realization
#print axioms ConstitutiveSearch.DirectMachine.all_futures_exact
#print axioms ConstitutiveSearch.DirectMachine.different_bits_cannot_merge
#print axioms ConstitutiveSearch.DirectMachine.different_engine_views_cannot_merge
#print axioms ConstitutiveSearch.DirectMachine.same_live_and_bit_same_futures
#print axioms ConstitutiveSearch.DirectMachine.sample_keeps_state
#print axioms ConstitutiveSearch.DirectMachine.tick_matches_agent_engine
#print axioms ConstitutiveSearch.DirectMachine.tick_matches_agent_reply
#print axioms ConstitutiveSearch.DirectMachine.emitted_target_accepted
#print axioms ConstitutiveSearch.DirectMachine.boot_exact
#print axioms ConstitutiveSearch.DirectMachine.bootMaster
/- AXIOM_AUDIT_END -/
