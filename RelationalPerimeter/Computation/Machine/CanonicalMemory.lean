import RelationalPerimeter.Computation.Machine.CausalDistinctions

/-! Executable removal of redundant bank shapes under the UNCHANGED contract.
The live engine is retained, not declared globally minimal. The advance orbit
from CausalDistinctions is never added to this runtime. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine
open EndogenousDecomposition ContinuationSignatures ConnectedFabric

def normalizeBank (bank : Bank) : Bank :=
  route (bank.read .transformed) (bank.read .retained)

def BankNormal (bank : Bank) : Prop := normalizeBank bank = bank

theorem normalized_reads (bank : Bank) (inlet : Inlet) :
    (normalizeBank bank).read inlet = bank.read inlet := by
  cases inlet with
  | transformed => exact route_reads_transformed _ _
  | retained => exact route_reads_retained _ _

theorem normal_route (left right : Signals) : BankNormal (route left right) := by
  unfold BankNormal normalizeBank
  rw [route_reads_transformed, route_reads_retained]

theorem normalize_bank_exact_iff (one two : Bank) :
    normalizeBank one = normalizeBank two ↔
      one.read .transformed = two.read .transformed ∧
      one.read .retained = two.read .retained := by
  constructor
  · intro same
    constructor
    · exact (normalized_reads one .transformed).symm.trans
        ((congrArg (fun bank => bank.read .transformed) same).trans (normalized_reads two .transformed))
    · exact (normalized_reads one .retained).symm.trans
        ((congrArg (fun bank => bank.read .retained) same).trans (normalized_reads two .retained))
  · intro reads
    unfold normalizeBank
    rw [reads.1, reads.2]

def normalizeMemory (memory : Memory) : Memory :=
  ⟨memory.live, memory.gates, normalizeBank memory.bank⟩

theorem normalized_view (memory : Memory) : (normalizeMemory memory).view = memory.view := by
  change (LiveContinuation.read memory.live, (normalizeBank memory.bank).read .transformed,
      (normalizeBank memory.bank).read .retained) =
    (LiveContinuation.read memory.live, memory.bank.read .transformed, memory.bank.read .retained)
  rw [normalized_reads, normalized_reads]

theorem normalized_memory_normal (memory : Memory) : BankNormal (normalizeMemory memory).bank :=
  normal_route _ _

theorem normalize_perform (scope : Scope) (memory : Memory) (request : Request) :
    normalizeMemory (perform scope memory request).1 =
      (perform scope (normalizeMemory memory) request).1 := by
  cases request with
  | advance =>
      change normalizeMemory (install scope (LiveContinuation.produce memory.live)) = _
      have normal : normalizeBank (install scope (LiveContinuation.produce memory.live)).bank =
          (install scope (LiveContinuation.produce memory.live)).bank := normal_route _ _
      change Memory.mk _ _ (normalizeBank _) = Memory.mk _ _ _
      rw [normal]
      rfl
  | sample _ => rfl
  | pulse left right =>
      dsimp only [perform, pulse]
      split
      · change Memory.mk _ _ (normalizeBank (route _ _)) = Memory.mk _ _ (route _ _)
        rw [normal_route]
        rfl
      · rfl

theorem normalize_event (scope : Scope) (memory : Memory) (request : Request) :
    (perform scope memory request).2 = (perform scope (normalizeMemory memory) request).2 := by
  cases request with
  | advance => rfl
  | sample inlet => exact congrArg Event.sampled (normalized_reads memory.bank inlet).symm
  | pulse left right =>
      dsimp only [perform, pulse]
      split <;> rfl

theorem perform_normal (scope : Scope) (memory : Memory) (request : Request)
    (normal : BankNormal memory.bank) : BankNormal (perform scope memory request).1.bank := by
  cases request with
  | advance => exact normal_route _ _
  | sample _ => exact normal
  | pulse left right =>
      dsimp only [perform, pulse]
      split
      · exact normal_route _ _
      · exact normal

/-- Proof erased at runtime: no extra future archive or normalizing pass per pulse. -/
abbrev ReducedMemory := { memory : Memory // BankNormal memory.bank }

def reduceMemory (memory : Memory) : ReducedMemory :=
  ⟨normalizeMemory memory, normalized_memory_normal memory⟩

def reducedPerform (scope : Scope) (memory : ReducedMemory) (request : Request) :
    ReducedMemory × Event :=
  let result := perform scope memory.val request
  (⟨result.1, perform_normal scope memory.val request memory.property⟩, result.2)

def reducedContract (scope : Scope) :
    FutureContract ReducedMemory (ULift.{3} Request) Event View where
  next memory request := (reducedPerform scope memory request.down).1
  event memory request := (reducedPerform scope memory request.down).2
  read memory := memory.val.view
  Allow _ request := Admitted scope request.down
  decision _ request := admission scope request.down

def bankReduction (scope : Scope) : ExactRealization (runtimeContract scope) ReducedMemory where
  reduced := reducedContract scope
  project := reduceMemory
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact memory request := Subtype.ext (normalize_perform scope memory request.down)
  event_exact memory request := normalize_event scope memory request.down
  read_exact memory := (normalized_view memory).symm

theorem reduced_all_futures (scope : Scope) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests =
      (reducedContract scope).outcome (reduceMemory memory) requests :=
  (bankReduction scope).outcome_exact memory requests

theorem reduced_futures_still_match_source (scope : Scope) (frame : Frame)
    (requests : List (ULift.{3} Request)) :
    (sourceContract scope).outcome frame requests =
      (reducedContract scope).outcome (reduceMemory (project scope frame)) requests :=
  (all_futures_exact scope frame requests).trans (reduced_all_futures scope _ requests)

theorem normalized_coherent (scope : Scope) (memory : Memory)
    (coherent : Coherent scope memory) : Coherent scope (normalizeMemory memory) := by
  refine ⟨coherent.1, ?_, ?_⟩
  · exact (congrArg List.length (normalized_reads memory.bank .transformed)).trans coherent.2.1
  · exact (congrArg List.length (normalized_reads memory.bank .retained)).trans coherent.2.2

/-- Complete minimality of the configured part, CONDITIONAL on identical live engines.
This condition is not a substitute for reducing arbitrary live search states. -/
theorem fixed_live_reduction_exact_iff (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (live : one.live = two.live) :
    reduceMemory one = reduceMemory two ↔ FutureEquivalent (runtimeContract scope) one two := by
  constructor
  · exact (bankReduction scope).equal_memory_same_futures
  · intro future
    have gates := futures_determine_connections scope first second future
    have reads := future.read
    have bank := (normalize_bank_exact_iff one.bank two.bank).mpr
      ⟨congrArg (fun view : View => view.2.1) reads,
        congrArg (fun view : View => view.2.2) reads⟩
    apply Subtype.ext
    change Memory.mk one.live one.gates (normalizeBank one.bank) =
      Memory.mk two.live two.gates (normalizeBank two.bank)
    rw [live, gates, bank]

theorem redundant_bank_shape_removed (live : LiveContinuation.Memory) (gates : List Gate)
    (signals : Signals) :
    reduceMemory ⟨live, gates, .separate signals signals⟩ =
      reduceMemory ⟨live, gates, .shared signals⟩ := by
  apply Subtype.ext
  rfl

theorem repeated_path_no_second_normalization (scope : Scope) (memory : ReducedMemory)
    (request : Request) :
    ((reducedPerform scope memory request).1.val, (reducedPerform scope memory request).2) =
      perform scope memory.val request := rfl

end ConstitutiveSearch.ReconfigurableMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.normalize_bank_exact_iff
#print axioms ConstitutiveSearch.ReconfigurableMachine.normalize_perform
#print axioms ConstitutiveSearch.ReconfigurableMachine.perform_normal
#print axioms ConstitutiveSearch.ReconfigurableMachine.reducedPerform
#print axioms ConstitutiveSearch.ReconfigurableMachine.bankReduction
#print axioms ConstitutiveSearch.ReconfigurableMachine.reduced_all_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.reduced_futures_still_match_source
#print axioms ConstitutiveSearch.ReconfigurableMachine.normalized_coherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.fixed_live_reduction_exact_iff
#print axioms ConstitutiveSearch.ReconfigurableMachine.redundant_bank_shape_removed
#print axioms ConstitutiveSearch.ReconfigurableMachine.repeated_path_no_second_normalization
/- AXIOM_AUDIT_END -/
