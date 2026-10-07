import RelationalPerimeter.Constitution.Continuation.Signature

/-! Unit charges at the declared contract API boundary. A read, admission
decision, event, and transition are four separate primitives. This is not a
bound for their implementations, allocation, or bit arithmetic. Instance-level
refinements must account for these separately before a total-cost claim. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S I : Type u} {E O : Type v}

structure ContractWork where
  reads : Nat
  decisions : Nat
  events : Nat
  transitions : Nat

def ContractWork.zero : ContractWork := ⟨0, 0, 0, 0⟩

def ContractWork.step (tail : ContractWork) : ContractWork :=
  ⟨tail.reads + 1, tail.decisions + 1, tail.events + 1, tail.transitions + 1⟩

def ContractWork.add (left right : ContractWork) : ContractWork :=
  ⟨left.reads + right.reads, left.decisions + right.decisions,
    left.events + right.events, left.transitions + right.transitions⟩

structure MeasuredOutcome (Event Observation : Type v) where
  value : Outcome Event Observation
  work : ContractWork

def measureOutcome (contract : FutureContract S I E O) : S → List I → MeasuredOutcome E O
  | source, [] => ⟨.stop (contract.read source), ⟨1, 0, 0, 0⟩⟩
  | source, input :: rest =>
      let read := contract.read source
      let allowed := contract.enabled source input
      let event := contract.event source input
      let next := contract.next source input
      let tail := measureOutcome contract next rest
      ⟨.step read allowed event tail.value, tail.work.step⟩

theorem measureOutcome_erases (contract : FutureContract S I E O) (source : S) (requests : List I) :
    (measureOutcome contract source requests).value = contract.outcome source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons input rest ih => exact congrArg (Outcome.step _ _ _) (ih _)

theorem measureOutcome_counts (contract : FutureContract S I E O) (source : S) (requests : List I) :
    (measureOutcome contract source requests).work.reads = requests.length + 1 ∧
    (measureOutcome contract source requests).work.decisions = requests.length ∧
    (measureOutcome contract source requests).work.events = requests.length ∧
    (measureOutcome contract source requests).work.transitions = requests.length := by
  induction requests generalizing source with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons input rest ih =>
      have tail := ih (contract.next source input)
      exact ⟨congrArg (fun count => count + 1) tail.1,
        congrArg Nat.succ tail.2.1, congrArg Nat.succ tail.2.2.1,
        congrArg Nat.succ tail.2.2.2⟩

structure MeasuredTests (Event Observation : Type v) where
  value : List (Outcome Event Observation)
  work : ContractWork
  vectorNodes : Nat

def measureTests (contract : FutureContract S I E O) (source : S) :
    List (List I) → MeasuredTests E O
  | [] => ⟨[], .zero, 0⟩
  | requests :: rest =>
      let first := measureOutcome contract source requests
      let tail := measureTests contract source rest
      ⟨first.value :: tail.value, first.work.add tail.work, tail.vectorNodes + 1⟩

theorem measureTests_erases (contract : FutureContract S I E O) (source : S) (tests : List (List I)) :
    (measureTests contract source tests).value = evaluateTests contract tests source := by
  induction tests with
  | nil => rfl
  | cons requests rest ih =>
      change (measureOutcome contract source requests).value :: _ = _ :: _
      rw [measureOutcome_erases]
      exact congrArg (List.cons _) ih

theorem measureTests_vector_nodes (contract : FutureContract S I E O) (source : S) (tests : List (List I)) :
    (measureTests contract source tests).vectorNodes = tests.length := by
  induction tests with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem measuredSignature_erases (basis : FiniteFutureBasis (contract : FutureContract S I E O)) (source : S) :
    (measureTests contract source basis.tests).value = producedSignature basis source :=
  measureTests_erases contract source basis.tests

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.measureOutcome
#print axioms ConstitutiveSearch.ContinuationSignatures.measureOutcome_erases
#print axioms ConstitutiveSearch.ContinuationSignatures.measureOutcome_counts
#print axioms ConstitutiveSearch.ContinuationSignatures.measureTests
#print axioms ConstitutiveSearch.ContinuationSignatures.measureTests_erases
#print axioms ConstitutiveSearch.ContinuationSignatures.measureTests_vector_nodes
#print axioms ConstitutiveSearch.ContinuationSignatures.measuredSignature_erases
/- AXIOM_AUDIT_END -/
