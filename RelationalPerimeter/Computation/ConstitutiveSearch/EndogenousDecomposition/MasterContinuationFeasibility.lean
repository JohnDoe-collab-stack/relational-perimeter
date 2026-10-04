import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution

/-!
# Feasibility of irreversible forgetting on the public canonical domain

The domain consists of actual prefixes of the public executor, not arbitrary
counterfactual states. Depth and provenance are used by the next discovery.
This module imposes recovery of the complete depth and provenance list. Under
that stronger contract the input and prefix length are reconstructible, hence
so is the entire canonical prefix. It does not establish that every sufficient
future interface must recover that list. It also says nothing about recovery
of the distinct profile inputs of executed normalization. Those are a different
domain from canonical chronological prefixes.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition
namespace MasterContinuation
set_option maxHeartbeats 2000000
open MasterResources
universe u v

def publicInitialCursor (input : Nat) : Cursor :=
  initialCursor
    (initialThreadedConstitutiveStateFromInitialization (initializeConstitutiveHistory input))
    (initialOperationalPrefix input)
    (initialThreadedConstitutiveStateFromInitialization_fresh (initializeConstitutiveHistory input))

def advance : Nat → Cursor → Cursor
  | 0, cursor => cursor
  | count + 1, cursor => advance count cursor.next

theorem execute_final_cursor (count : Nat) (cursor : Cursor) :
    (MasterResources.execute count cursor).2 = advance count cursor := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact ih cursor.next

theorem advance_depth (count : Nat) (cursor : Cursor) :
    (advance count cursor).depth = cursor.depth + count := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    change (advance count cursor.next).depth = _
    exact (ih cursor.next).trans (Nat.add_right_comm cursor.depth 1 count)

theorem next_provenance_length (cursor : Cursor) :
    cursor.next.state.provenance.length = cursor.state.provenance.length + 1 := by
  exact congrArg List.length cursor.head.run.nextRun.provenanceFromExecution

theorem advance_provenance_length (count : Nat) (cursor : Cursor) :
    (advance count cursor).state.provenance.length = cursor.state.provenance.length + count := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    change (advance count cursor.next).state.provenance.length = _
    rw [ih cursor.next, next_provenance_length]
    exact Nat.add_right_comm _ 1 count

/-- Only prefixes within the actual public horizon are admitted here. -/
structure PublicPrefix where
  input : Nat
  elapsed : Nat
  withinHorizon : elapsed ≤ resolutionLength input

def PublicPrefix.cursor (prefixRun : PublicPrefix) : Cursor :=
  advance prefixRun.elapsed (publicInitialCursor prefixRun.input)

def PublicPrefix.execution (prefixRun : PublicPrefix) :=
  (MasterResources.execute prefixRun.elapsed (publicInitialCursor prefixRun.input)).1

theorem prefix_depth (prefixRun : PublicPrefix) :
    prefixRun.cursor.depth = prefixRun.input + prefixRun.elapsed :=
  advance_depth _ _

theorem prefix_provenance_length (prefixRun : PublicPrefix) :
    prefixRun.cursor.state.provenance.length = prefixRun.elapsed :=
  (advance_provenance_length _ _).trans (Nat.zero_add _)

/-- Strong raw-read contract. The engine uses provenance, but requiring the
whole original list to be reconstructible is stronger than preservation of a
particular consumer's result. No necessity theorem for this contract is claimed. -/
structure PreservesDiscoveryReads (Memory : Type u) (project : PublicPrefix → Memory) where
  depth : Memory → Nat
  provenance : Memory → List SAT.Var
  depthExact : ∀ p, depth (project p) = p.cursor.depth
  provenanceExact : ∀ p, provenance (project p) = p.cursor.state.provenance

def PreservesDiscoveryReads.coordinates {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) (memory : Memory) : Nat × Nat :=
  (contract.depth memory - (contract.provenance memory).length,
    (contract.provenance memory).length)

theorem subtract_added (start count : Nat) : (start + count) - count = start := by
  induction count with
  | zero => rfl
  | succ count ih => exact (Nat.succ_sub_succ _ _).trans ih

theorem coordinates_exact {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) (p : PublicPrefix) :
    contract.coordinates (project p) = (p.input, p.elapsed) := by
  unfold PreservesDiscoveryReads.coordinates
  rw [contract.depthExact, contract.provenanceExact, prefix_provenance_length, prefix_depth]
  exact Prod.ext (subtract_added _ _) rfl

/-- Off the image, the coordinate pair need not describe an admitted prefix.
The executable decoder checks the public horizon rather than assuming it. -/
def PublicPrefix.ofCoordinates (coordinates : Nat × Nat) : Option PublicPrefix :=
  if within : coordinates.2 ≤ resolutionLength coordinates.1 then
    some ⟨coordinates.1, coordinates.2, within⟩
  else none

theorem coordinates_decode (p : PublicPrefix) :
    PublicPrefix.ofCoordinates (p.input, p.elapsed) = some p := by
  unfold PublicPrefix.ofCoordinates
  rw [dif_pos p.withinHorizon]

/-- This decoder reads only the contract's retained memory, not a hidden prefix. -/
def PreservesDiscoveryReads.decode {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) (memory : Memory) : Option PublicPrefix :=
  PublicPrefix.ofCoordinates (contract.coordinates memory)

theorem decode_exact {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) (p : PublicPrefix) :
    contract.decode (project p) = some p := by
  unfold PreservesDiscoveryReads.decode
  rw [coordinates_exact contract p]
  exact coordinates_decode p

def PreservesDiscoveryReads.recoverRead {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) {Readout : Type v}
    (historicalRead : PublicPrefix → Readout) (memory : Memory) : Option Readout :=
  (contract.decode memory).map historicalRead

theorem recoverRead_exact {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) {Readout : Type v}
    (historicalRead : PublicPrefix → Readout) (p : PublicPrefix) :
    contract.recoverRead historicalRead (project p) = some (historicalRead p) := by
  unfold PreservesDiscoveryReads.recoverRead
  rw [decode_exact contract p]
  rfl

theorem projection_injective {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) (p q : PublicPrefix)
    (same : project p = project q) : p = q := by
  have coordinates := (coordinates_exact contract p).symm.trans
    ((congrArg contract.coordinates same).trans (coordinates_exact contract q))
  have inputs := congrArg Prod.fst coordinates
  have elapsed := congrArg Prod.snd coordinates
  cases p
  cases q
  cases inputs
  cases elapsed
  rfl

theorem no_historical_separator {Memory : Type u} {project : PublicPrefix → Memory}
    (contract : PreservesDiscoveryReads Memory project) {Readout : Type v}
    (historicalRead : PublicPrefix → Readout) (p q : PublicPrefix)
    (same : project p = project q) : historicalRead p = historicalRead q :=
  congrArg historicalRead (projection_injective contract p q same)

end MasterContinuation
end ConstitutiveSearch.EndogenousDecomposition
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.publicInitialCursor
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.advance
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.execute_final_cursor
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.advance_depth
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.next_provenance_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.advance_provenance_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PublicPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PublicPrefix.cursor
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PublicPrefix.execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.prefix_depth
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.prefix_provenance_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PreservesDiscoveryReads
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.subtract_added
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.coordinates_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PublicPrefix.ofCoordinates
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.coordinates_decode
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PreservesDiscoveryReads.decode
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.decode_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.PreservesDiscoveryReads.recoverRead
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.recoverRead_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.projection_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterContinuation.no_historical_separator
/- AXIOM_AUDIT_END -/
