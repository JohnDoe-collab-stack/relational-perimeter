import RelationalPerimeter

namespace ProducedContinuationTests
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Grouping ProducedContinuation

theorem closed_public_contract (input : Nat) : PublicContractCertificate input :=
  publicContractCertificate input

theorem source_distinction_is_real (input : Nat) : publicLeft input ≠ publicRight input :=
  public_distinct input

theorem produced_image_fibres (input : Nat)
    (p q : RoleOccurrenceProfile (publicRoles input)) :
    project (publicProduce input p) = project (publicProduce input q) ↔
      (publicNormalization input).target p = (publicNormalization input).target q :=
  memory_fibres _ _ p q

theorem no_profile_decoder (input : Nat) :
    ¬ (∃ recover : Memory (publicNormalization input) → RoleOccurrenceProfile (publicRoles input),
      ∀ p, recover (project (publicProduce input p)) = p) :=
  (publicContractCertificate input).noSourceDecoder

theorem actual_future_engine (cursor : MasterResources.Cursor) (count : Nat) :
    LiveContinuation.project (MasterResources.execute count cursor).2 =
      LiveContinuation.run count (LiveContinuation.project cursor) := by
  rw [← LiveContinuation.sourceRun_is_resource_execution]
  exact LiveContinuation.run_exact count cursor

theorem all_mixed_requests (input : Nat) (requests : List (Input (publicNormalization input))) :
    Continuation.events sourceNext sourceEvent (publicProduce input (publicLeft input)) requests =
      Continuation.events sourceNext sourceEvent (publicProduce input (publicRight input)) requests :=
  public_all_future_events input requests

def admitted_first_read (input : Nat) :
    allow (publicStart input) (.inspect publicFirstQuery) := publicFirstQuery_admitted input

def admitted_advance (input steps : Nat) :
    allow (publicStart input) (.advance steps) := advance_admission (publicStart input) steps

def admitted_source_advance (input steps : Nat) :
    allow (project (publicProduce input (publicLeft input))) (.advance steps) :=
  source_advance_admission _ steps

def admitted_mixed_requests (input : Nat) :
    Continuation.Admitted next allow (publicStart input)
      [.advance 0, .inspect publicFirstQuery, .advance 1] :=
  .cons (admitted_advance input 0) (.cons (admitted_first_read input)
    (.cons (admitted_advance input 1) (.nil _)))

theorem first_read_is_not_vacuous (input : Nat) :
    ∃ value, readTarget publicFirstQuery (publicStart input).readers = some value :=
  public_first_read_exists input

def actual_first_read := readTarget publicFirstQuery (publicStart 0).readers

#guard actual_first_read.isSome
#guard (publicStart 0).readers.length == 1
#guard (publicStart 0).live.depth == 1

end ProducedContinuationTests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ProducedContinuationTests.closed_public_contract
#print axioms ProducedContinuationTests.source_distinction_is_real
#print axioms ProducedContinuationTests.produced_image_fibres
#print axioms ProducedContinuationTests.no_profile_decoder
#print axioms ProducedContinuationTests.actual_future_engine
#print axioms ProducedContinuationTests.all_mixed_requests
#print axioms ProducedContinuationTests.admitted_first_read
#print axioms ProducedContinuationTests.admitted_advance
#print axioms ProducedContinuationTests.admitted_source_advance
#print axioms ProducedContinuationTests.admitted_mixed_requests
#print axioms ProducedContinuationTests.first_read_is_not_vacuous
#print axioms ProducedContinuationTests.actual_first_read
/- AXIOM_AUDIT_END -/
