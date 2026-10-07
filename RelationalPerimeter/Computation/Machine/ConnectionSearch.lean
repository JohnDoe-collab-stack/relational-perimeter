import RelationalPerimeter.Computation.Machine.Fabric

/-! Discovery can fail. Failure leaves independent inlet buffers; it is not
a permission to merge them. This generic connector uses the existing finder,
not a Boolean success label supplied separately. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ConnectedFabric
open SAT

structure FoundConnection (scope : Scope) {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) where
  private mk ::
  relation : GeneratedStructuralFlipAtRelation selected source target
  gates : List Gate
  gatesExact : gates = configure scope selected

def findConnection (scope : Scope) {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) :
    Option (FoundConnection scope selected source target) :=
  ((generatedStructuralFlipAtSearch root selected).find source target).map
    (fun relation => ⟨relation, configure scope selected, rfl⟩)

theorem FoundConnection.total_action (scope : Scope) {root : Cnf} {selected : Var}
    {source target : GeneratedStructuralBranchContext root}
    (found : FoundConnection scope selected source target)
    (continuation : GeneratedStructuralBranchContinuation source) :
    fire found.gates (sense scope continuation.1) =
      sense scope (found.relation.mapContinuation continuation).1 := by
  rw [found.gatesExact]
  exact configure_exact scope selected continuation.1

def FoundConnection.accepted (scope : Scope) {root : Cnf} {selected : Var}
    {source target : GeneratedStructuralBranchContext root}
    (found : FoundConnection scope selected source target)
    (continuation : GeneratedStructuralBranchContinuation source)
    (accepted : GeneratedStructuralBranchAccept source continuation) :
    { result : GeneratedStructuralBranchContinuation target // GeneratedStructuralBranchAccept target result } :=
  ⟨found.relation.mapContinuation continuation, found.relation.mapContinuation_accept continuation accepted⟩

/-- The rich finder runs only at configuration. No context is stored in gates. -/
def attemptBank (scope : Scope) {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) (left right : Signals) : Bank :=
  match findConnection scope selected source target with
  | none => .separate left right
  | some found => drive found.gates left right

theorem failed_search_cannot_merge (scope : Scope) {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) (left right : Signals)
    (failed : (generatedStructuralFlipAtSearch root selected).find source target = none) :
    attemptBank scope selected source target left right = .separate left right := by
  dsimp only [attemptBank, findConnection]
  rw [failed]
  rfl

theorem failed_search_width_two (scope : Scope) {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) (left right : Signals)
    (failed : (generatedStructuralFlipAtSearch root selected).find source target = none) :
    (attemptBank scope selected source target left right).cells = 2 :=
  congrArg Bank.cells (failed_search_cannot_merge scope selected source target left right failed)

end ConstitutiveSearch.ConnectedFabric
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConnectedFabric.findConnection
#print axioms ConstitutiveSearch.ConnectedFabric.FoundConnection.total_action
#print axioms ConstitutiveSearch.ConnectedFabric.FoundConnection.accepted
#print axioms ConstitutiveSearch.ConnectedFabric.attemptBank
#print axioms ConstitutiveSearch.ConnectedFabric.failed_search_cannot_merge
#print axioms ConstitutiveSearch.ConnectedFabric.failed_search_width_two
/- AXIOM_AUDIT_END -/
