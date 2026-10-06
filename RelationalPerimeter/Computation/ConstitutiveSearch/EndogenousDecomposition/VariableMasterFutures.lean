import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterInstance
import RelationalPerimeter.Constitution.Continuation.Composition

/-!
# A fixed future contract for the actually produced continuation

The contract permits arbitrary finite repeated reads of variable 10 after the
normalizer's action. It does not permit restarting the SAT search, or reading
the original assignment. This is one explicit contract for both incoming
histories, not a claim of minimality for every future runtime interaction.
-/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures
open SAT Example ContinuationSignatures

def assignmentOf : {states : States formula} →
    FrontierContinuation (generatedStructuralBranchSystem formula) states → Assignment
  | [], impossible => nomatch impossible
  | _ :: _, .head continuation => continuation.1
  | _ :: _, .tail tail => assignmentOf tail

theorem actual_opening (previous : Bool) :
    (step origin formula (incoming previous)).opening.frontier =
      [child previous false, child previous true] := by
  rw [(step origin formula (incoming previous)).openingExact,
    (step origin formula (incoming previous)).resourcesExact, selected_exact, opened_exact]

structure Source where
  previous : Bool
  continuation : FrontierContinuation (generatedStructuralBranchSystem formula)
    [child previous false, child previous true]
  accepted : FrontierAccept (generatedStructuralBranchSystem formula) _ continuation

def source (previous choice : Bool) : Source :=
  match choice with
  | false => ⟨previous, .head (continuation previous false), each_child_accepted previous false⟩
  | true => ⟨previous, .tail (.head (continuation previous true)), each_child_accepted previous true⟩

/-- Read the result of the real reduction action, not a branch label. -/
def readProduced (source : Source) : Bool :=
  let production := step origin formula (incoming source.previous)
  let opened := (actual_opening source.previous).symm ▸ source.continuation
  assignmentOf (production.reduction.preservation.forward.map opened) 10

def contract := readOnlyContract readProduced
def basis := readOnlyBasis readProduced
def realization := readOnlyRealization readProduced

theorem grouped_read : readProduced (source true false) = readProduced (source true true) := rfl

theorem unresolved_left_read : readProduced (source false false) = false := rfl
theorem unresolved_right_read : readProduced (source false true) = true := rfl

theorem grouped_all_futures : FutureEquivalent contract (source true false) (source true true) :=
  readOnly_futures readProduced grouped_read

theorem original_sources_distinct (previous : Bool) : source previous false ≠ source previous true := by
  intro same
  have readSame := congrArg (fun state => assignmentOf state.continuation 10) same
  change false = true at readSame
  cases readSame

/-- Complete behavioural quotient for this fixed contract, on every Source. -/
theorem exact_future_fibres (left right : Source) :
    realization.project left = realization.project right ↔ FutureEquivalent contract left right := by
  dsimp only [realization, readOnlyRealization]
  constructor
  · intro same
    exact readOnly_futures (left := left) (right := right) readProduced same
  · intro same
    have direct : contract.read left = contract.read right :=
      @FutureEquivalent.read Source (ULift Unit) (ULift Unit) Bool contract left right same
    dsimp only [contract, readOnlyContract] at direct
    exact direct

def covers_read_values : (value : Bool) → {state : Source // realization.project state = value}
  | false => ⟨source false false, unresolved_left_read⟩
  | true => ⟨source false true, unresolved_right_read⟩

theorem unresolved_distinction :
    producedSignature basis (source false false) ≠ producedSignature basis (source false true) := by
  intro same
  have readSame := (signature_sound basis same).read
  change readProduced (source false false) = readProduced (source false true) at readSame
  rw [unresolved_left_read, unresolved_right_read] at readSame
  cases readSame

def unresolved_separator : FutureSeparator contract (source false false) (source false true) :=
  separate basis _ _ unresolved_distinction

/-- Necessity concerns distinguishability, never a prescribed memory encoding. -/
theorem every_exact_realization_distinguishes {Memory : Type}
    (exact : ExactRealization contract Memory) :
    exact.project (source false false) ≠ exact.project (source false true) := by
  intro same
  exact unresolved_distinction (minimal_distinctions basis exact same)

theorem realization_merges_grouped :
    realization.project (source true false) = realization.project (source true true) := grouped_read

end ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.assignmentOf
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.actual_opening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.readProduced
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.grouped_read
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.unresolved_left_read
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.unresolved_right_read
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.grouped_all_futures
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.original_sources_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.exact_future_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.covers_read_values
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.unresolved_distinction
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.unresolved_separator
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.every_exact_realization_distinguishes
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Futures.realization_merges_grouped
/- AXIOM_AUDIT_END -/
