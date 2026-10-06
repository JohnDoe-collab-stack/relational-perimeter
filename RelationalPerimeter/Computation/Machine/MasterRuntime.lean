import RelationalPerimeter.Computation.Machine.ConstitutiveLiveExecution
import RelationalPerimeter.Computation.Machine.FrontierCircuit
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.UnifiedPublicCertificate

/-! One runtime receives the existing master's live state and constituted SAT
contexts. An advance makes one live production; its discovered selector drives
opening and frontier search. The retained SAT frontier is the next problem
state, and the returned program configures the routing used by later packets.
The older rich memory is a specification, never a second runtime call.

The SAT frontier is kept because later search reads its residual formula and
history. The previous minimality theorem concerns the core's own contract, not
minimality of this enlarged state. No historical reader is silently removed. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.MasterMachine
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures

structure Routing where
  sourceWidth : Nat
  targetWidth : Nat
  circuit : FrontierCircuit

def Routing.apply (routing : Routing) (slot : Nat) (bits : Signals) : Option (Nat × Signals) :=
  if slot < routing.sourceWidth then
    let output := routing.circuit.fire ⟨slot, bits⟩
    some (output.slot, output.bits)
  else none

structure ProblemMemory (formula : Cnf) where
  frontier : VariableMaster.States formula
  routing : Routing
  routed : Option (Nat × Signals)

def initialProblem (formula : Cnf) (source : VariableMaster.States formula) : ProblemMemory formula :=
  ⟨source, ⟨source.length, source.length, .identity⟩, none⟩

/-- A scope-specific production, with no supplied partition or expected width. -/
structure ScopedProblemProduction (scope : Scope) (formula : Cnf) (selected : Var)
    (source : VariableMaster.States formula) where
  private mk ::
  opening : VariableMaster.Opening formula source
  openingExact : opening = VariableMaster.openFrontier formula selected source
  reduction : VariableMaster.Reduction formula selected opening
  reductionExact : reduction = normalizeGeneratedStructuralFrontierByFlip formula selected opening.frontier
  configured : FrontierCircuit
  configuredExact : configured = lowerFrontier scope selected reduction.code

def produceProblem (scope : Scope) (formula : Cnf) (selected : Var)
    (source : VariableMaster.States formula) : ScopedProblemProduction scope formula selected source :=
  let opening := VariableMaster.openFrontier formula selected source
  let reduction := normalizeGeneratedStructuralFrontierByFlip formula selected opening.frontier
  ⟨opening, rfl, reduction, rfl, lowerFrontier scope selected reduction.code, rfl⟩

def ScopedProblemProduction.next {scope : Scope} {formula : Cnf} {selected : Var}
    {source : VariableMaster.States formula} (production : ScopedProblemProduction scope formula selected source) :
    ProblemMemory formula :=
  ⟨production.reduction.retained,
    ⟨production.opening.frontier.length, production.reduction.retained.length, production.configured⟩,
    none⟩

def ScopedProblemProduction.preservation {scope : Scope} {formula : Cnf} {selected : Var}
    {source : VariableMaster.States formula} (production : ScopedProblemProduction scope formula selected source) :
    AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source production.next.frontier :=
  production.opening.preservation.trans production.reduction.preservation

theorem ScopedProblemProduction.circuit_exact {scope : Scope} {formula : Cnf} {selected : Var}
    {source : VariableMaster.States formula} (production : ScopedProblemProduction scope formula selected source)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) production.opening.frontier) :
    production.configured.fire (senseFrontier scope continuation) =
      senseFrontier scope (production.reduction.preservation.forward.map continuation) := by
  rw [production.configuredExact]
  exact lowerFrontier_exact scope selected production.reduction.code continuation

/-- The installed routing returns precisely the transported continuation's
readings, not merely a program with the same measured width. -/
theorem ScopedProblemProduction.route_exact {scope : Scope} {formula : Cnf} {selected : Var}
    {source : VariableMaster.States formula} (production : ScopedProblemProduction scope formula selected source)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) production.opening.frontier) :
    production.next.routing.apply (senseFrontier scope continuation).slot
      (senseFrontier scope continuation).bits =
      some ((senseFrontier scope (production.reduction.preservation.forward.map continuation)).slot,
        (senseFrontier scope (production.reduction.preservation.forward.map continuation)).bits) := by
  unfold Routing.apply
  change (if (senseFrontier scope continuation).slot < production.opening.frontier.length then
    let output := production.configured.fire (senseFrontier scope continuation)
    some (output.slot, output.bits) else none) = _
  rw [if_pos (senseFrontier_slot_lt scope continuation), production.circuit_exact]

structure Memory (scope : Scope) (formula : Cnf) : Type 3 where
  core : ReconfigurableMachine.LiveReduction.Runtime scope
  problem : ProblemMemory formula

structure RichMemory (formula : Cnf) : Type 3 where
  core : ReconfigurableMachine.Memory
  problem : ProblemMemory formula

def project (scope : Scope) {formula : Cnf} (source : RichMemory formula) : Memory scope formula :=
  ⟨ReconfigurableMachine.LiveReduction.projectMemory scope source.core, source.problem⟩

def fromMaster {input : Nat} (scope : Scope) (master : UnifiedMaster.Instance input)
    (formula : Cnf) (source : VariableMaster.States formula) : RichMemory formula :=
  let live := LiveContinuation.project master.cursor
  ⟨⟨live, [], .shared (sense scope live.assignment.assignment)⟩, initialProblem formula source⟩

/-- Initialization calls the existing public master exactly once. -/
def receive (input : Nat) (scope : Scope) (formula : Cnf) (source : VariableMaster.States formula) :
    Memory scope formula :=
  let master := UnifiedMaster.publicInstance input
  project scope (fromMaster scope master formula source)

def advance {scope : Scope} {formula : Cnf} (memory : Memory scope formula) : Memory scope formula :=
  let coreProduction := ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce memory.core.live
  let problemProduction := produceProblem scope formula coreProduction.action.selected memory.problem.frontier
  ⟨(ReconfigurableMachine.LiveReduction.ConstitutiveExecution.installProduced coreProduction).1, problemProduction.next⟩

def richAdvance (scope : Scope) {formula : Cnf} (memory : RichMemory formula) : RichMemory formula :=
  let coreProduction := LiveContinuation.produce memory.core.live
  let problemProduction := produceProblem scope formula coreProduction.built.stage.discovery.var memory.problem.frontier
  ⟨ReconfigurableMachine.install scope coreProduction, problemProduction.next⟩

theorem selected_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce (ReconfigurableMachine.LiveReduction.projectLive scope live)).action.selected =
      (LiveContinuation.produce live).built.stage.discovery.var := by
  rw [ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce_exact]
  exact congrArg (fun discovery => discovery.var) (ReconfigurableMachine.LiveReduction.action_matches_source live)

theorem memory_ext {scope : Scope} {formula : Cnf} (one two : Memory scope formula)
    (core : one.core = two.core) (problem : one.problem = two.problem) : one = two := by
  cases one; cases two; cases core; cases problem; rfl

theorem advance_exact (scope : Scope) {formula : Cnf} (memory : RichMemory formula) :
    advance (project scope memory) = project scope (richAdvance scope memory) := by
  apply memory_ext
  · exact (congrArg Prod.fst (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.advance_exact (ReconfigurableMachine.LiveReduction.projectLive scope memory.core.live))).trans
      (ReconfigurableMachine.LiveReduction.advance_project scope memory.core.live)
  · change (produceProblem scope formula
      (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce (ReconfigurableMachine.LiveReduction.projectLive scope memory.core.live)).action.selected
      memory.problem.frontier).next = _
    rw [selected_exact]
    rfl

theorem advance_core_exact {scope : Scope} {formula : Cnf} (memory : Memory scope formula) :
    (advance memory).core = (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.advance memory.core.live).1 := rfl

theorem advance_frontier_is_produced {scope : Scope} {formula : Cnf} (memory : Memory scope formula) :
    (advance memory).problem.frontier =
      (produceProblem scope formula (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce memory.core.live).action.selected
        memory.problem.frontier).reduction.retained := rfl

theorem advance_preserves_SAT {scope : Scope} {formula : Cnf} (memory : Memory scope formula) :
    FrontierViable (generatedStructuralBranchSystem formula) memory.problem.frontier ↔
      FrontierViable (generatedStructuralBranchSystem formula) (advance memory).problem.frontier :=
  (produceProblem scope formula (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce memory.core.live).action.selected
    memory.problem.frontier).preservation.viable_iff

end ConstitutiveSearch.MasterMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.MasterMachine.Routing.apply
#print axioms ConstitutiveSearch.MasterMachine.produceProblem
#print axioms ConstitutiveSearch.MasterMachine.ScopedProblemProduction.preservation
#print axioms ConstitutiveSearch.MasterMachine.ScopedProblemProduction.circuit_exact
#print axioms ConstitutiveSearch.MasterMachine.ScopedProblemProduction.route_exact
#print axioms ConstitutiveSearch.MasterMachine.receive
#print axioms ConstitutiveSearch.MasterMachine.advance
#print axioms ConstitutiveSearch.MasterMachine.advance_exact
#print axioms ConstitutiveSearch.MasterMachine.advance_core_exact
#print axioms ConstitutiveSearch.MasterMachine.advance_frontier_is_produced
#print axioms ConstitutiveSearch.MasterMachine.advance_preserves_SAT
/- AXIOM_AUDIT_END -/
