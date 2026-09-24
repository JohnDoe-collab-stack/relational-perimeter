import RelationalPerimeter.Computation.RelationalAction

/-!
# Executed reconstruction with an exact failure prefix

The relation witness is not an input of the run.  It can occur only in the
successful output of the same structural recursion that records every earlier
failed attempt.  The public run also proves that its recorded input is exactly
the list extracted by the reconstruction system.
-/

namespace RelationalPerimeter.Computation

universe uCandidate uRelation

/-- Candidate extraction and one executable relation attempt for a fixed pair. -/
structure ReconstructionSystem
    (system : SearchSystem)
    (Candidate : Type uCandidate)
    (Relation : system.State → system.State → Type uRelation)
    (left right : system.State) where
  extract : List Candidate
  attempt : (candidate : Candidate) → Option (Relation left right)

/-- A candidate together with the result of the attempt that rejected it. -/
structure FailedAttempt
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (reconstruction : ReconstructionSystem
      system Candidate Relation left right) where
  candidate : Candidate
  attempt_eq_none : reconstruction.attempt candidate = none

/--
An executed exploration either exhausts all candidates or records the exact
failed prefix, the selected candidate, the produced relation, its successful
attempt equation, and the suffix that was not executed.
-/
inductive ExecutedReconstruction
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (reconstruction : ReconstructionSystem
      system Candidate Relation left right) : Type (max uCandidate uRelation)
  | exhausted
      (failures : List (FailedAttempt reconstruction)) :
      ExecutedReconstruction reconstruction
  | found
      (failedPrefix : List (FailedAttempt reconstruction))
      (selected : Candidate)
      (relation : Relation left right)
      (selected_exact : reconstruction.attempt selected = some relation)
      (remaining : List Candidate) :
      ExecutedReconstruction reconstruction

namespace ExecutedReconstruction

/-- Complete candidate list supplied to the execution. -/
def suppliedCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right} :
    ExecutedReconstruction reconstruction → List Candidate
  | .exhausted failures => failures.map FailedAttempt.candidate
  | .found failedPrefix selected _relation _selectedExact remaining =>
      failedPrefix.map FailedAttempt.candidate ++ selected :: remaining

/-- Ordered candidates actually submitted to the attempt function. -/
def testedCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right} :
    ExecutedReconstruction reconstruction → List Candidate
  | .exhausted failures => failures.map FailedAttempt.candidate
  | .found failedPrefix selected _relation _selectedExact _remaining =>
      failedPrefix.map FailedAttempt.candidate ++ [selected]

/-- Number of attempts, derived from the emitted trace. -/
def attempts
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (result : ExecutedReconstruction reconstruction) : Nat :=
  result.testedCandidates.length

/-- Number of failed attempts retained by the executed result. -/
def failedAttempts
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right} :
    ExecutedReconstruction reconstruction → Nat
  | .exhausted failures => failures.length
  | .found failedPrefix _selected _relation _selectedExact _remaining =>
      failedPrefix.length

/-- Candidate selected by the executed run, when one was found. -/
def selectedCandidate?
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right} :
    ExecutedReconstruction reconstruction → Option Candidate
  | .exhausted _failures => none
  | .found _failedPrefix selected _relation _selectedExact _remaining =>
      some selected

/-- Relation produced by the executed run, when one was found. -/
def relation?
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right} :
    ExecutedReconstruction reconstruction → Option (Relation left right)
  | .exhausted _failures => none
  | .found _failedPrefix _selected relation _selectedExact _remaining =>
      some relation

/-- Prepend one recorded failure to an already executed suffix. -/
def prependFailure
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (failure : FailedAttempt reconstruction) :
    ExecutedReconstruction reconstruction → ExecutedReconstruction reconstruction
  | .exhausted failures => .exhausted (failure :: failures)
  | .found failedPrefix selected relation selectedExact remaining =>
      .found (failure :: failedPrefix)
        selected relation selectedExact remaining

/-- Prepending a failure prepends exactly one supplied candidate. -/
theorem prependFailure_suppliedCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (failure : FailedAttempt reconstruction)
    (result : ExecutedReconstruction reconstruction) :
    (result.prependFailure failure).suppliedCandidates =
      failure.candidate :: result.suppliedCandidates := by
  cases result <;> rfl

/-- Prepending a failure prepends exactly one tested candidate. -/
theorem prependFailure_testedCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (failure : FailedAttempt reconstruction)
    (result : ExecutedReconstruction reconstruction) :
    (result.prependFailure failure).testedCandidates =
      failure.candidate :: result.testedCandidates := by
  cases result <;> rfl

/-- Prepending a recorded rejection increments the failed-attempt count. -/
theorem prependFailure_failedAttempts
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (failure : FailedAttempt reconstruction)
    (result : ExecutedReconstruction reconstruction) :
    (result.prependFailure failure).failedAttempts =
      result.failedAttempts + 1 := by
  cases result with
  | exhausted failures =>
      change Nat.succ failures.length = failures.length + 1
      exact Nat.succ_eq_add_one failures.length
  | found failedPrefix selected relation selectedExact remaining =>
      change Nat.succ failedPrefix.length = failedPrefix.length + 1
      exact Nat.succ_eq_add_one failedPrefix.length

/-- Prepending a failure leaves a later selected candidate unchanged. -/
theorem prependFailure_selectedCandidate
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (failure : FailedAttempt reconstruction)
    (result : ExecutedReconstruction reconstruction) :
    (result.prependFailure failure).selectedCandidate? =
      result.selectedCandidate? := by
  cases result <;> rfl

/-- Prepending a failure leaves a relation produced later unchanged. -/
theorem prependFailure_relation
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (failure : FailedAttempt reconstruction)
    (result : ExecutedReconstruction reconstruction) :
    (result.prependFailure failure).relation? = result.relation? := by
  cases result <;> rfl

end ExecutedReconstruction

/-- An executed result indexed by the exact candidate list supplied to it. -/
structure CandidateExecution
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (reconstruction : ReconstructionSystem
      system Candidate Relation left right)
    (candidates : List Candidate) where
  result : ExecutedReconstruction reconstruction
  supplied_exact : result.suppliedCandidates = candidates

namespace CandidateExecution

/-- Ordered candidates actually tested by this indexed execution. -/
def testedCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    {candidates : List Candidate}
    (execution : CandidateExecution reconstruction candidates) : List Candidate :=
  execution.result.testedCandidates

/-- Candidate selected by this indexed execution, when successful. -/
def selectedCandidate?
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    {candidates : List Candidate}
    (execution : CandidateExecution reconstruction candidates) : Option Candidate :=
  execution.result.selectedCandidate?

/-- Relation produced by this indexed execution, when successful. -/
def relation?
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    {candidates : List Candidate}
    (execution : CandidateExecution reconstruction candidates) :
    Option (Relation left right) :=
  execution.result.relation?

end CandidateExecution

/--
Explore candidates in order.  Every head is attempted exactly once.  Failure
is recorded before recursion; success stops the run and retains the untouched
suffix.
-/
def exploreCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (reconstruction : ReconstructionSystem
      system Candidate Relation left right) :
    (candidates : List Candidate) → CandidateExecution reconstruction candidates
  | [] =>
      { result := .exhausted []
        supplied_exact := rfl }
  | candidate :: remaining =>
      match attemptResult : reconstruction.attempt candidate with
      | some relation =>
          { result := .found [] candidate relation attemptResult remaining
            supplied_exact := rfl }
      | none =>
          let tail := exploreCandidates reconstruction remaining
          let failure : FailedAttempt reconstruction :=
            { candidate := candidate
              attempt_eq_none := attemptResult }
          { result := tail.result.prependFailure failure
            supplied_exact := by
              rw [ExecutedReconstruction.prependFailure_suppliedCandidates]
              rw [tail.supplied_exact] }

/-- A completed run paired with the exact extraction equation. -/
structure ReconstructionRun
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (reconstruction : ReconstructionSystem
      system Candidate Relation left right) where
  result : ExecutedReconstruction reconstruction
  supplied_exact : result.suppliedCandidates = reconstruction.extract

namespace ReconstructionRun

/-- Ordered candidates actually tested by the run. -/
def testedCandidates
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction) : List Candidate :=
  run.result.testedCandidates

/-- Attempt count derived from the run's tested trace. -/
def attempts
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction) : Nat :=
  run.result.attempts

/-- Failed-attempt count derived from the proof-carrying rejected prefix. -/
def failedAttempts
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction) : Nat :=
  run.result.failedAttempts

/-- Candidate selected by the run, when successful. -/
def selectedCandidate?
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction) : Option Candidate :=
  run.result.selectedCandidate?

/-- Relation produced by the run, when successful. -/
def relation?
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction) : Option (Relation left right) :=
  run.result.relation?

end ReconstructionRun

/-!
## Success view of an executed run

The view below does not accept a second relation beside the executed result.
Its constructor identifies the run result itself with the `found` constructor;
the usable relation is then projected from that constructor.
-/

/-- Proof-relevant view that one exact run ended in its `found` constructor. -/
inductive SuccessfulRun
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction) : Type (max uCandidate uRelation)
  | found
      (failedPrefix : List (FailedAttempt reconstruction))
      (selected : Candidate)
      (relation : Relation left right)
      (selected_exact : reconstruction.attempt selected = some relation)
      (remaining : List Candidate)
      (result_exact :
        run.result = .found failedPrefix selected relation selected_exact remaining) :
      SuccessfulRun run

namespace SuccessfulRun

/-- The relation is data of the witnessed `found` result, not a parallel field. -/
def relation
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    {run : ReconstructionRun reconstruction} :
    SuccessfulRun run → Relation left right
  | .found _failedPrefix _selected relation _selectedExact _remaining _resultExact =>
      relation

/-- The projected relation is exactly the optional relation returned by the run. -/
theorem relation_exact
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    {run : ReconstructionRun reconstruction}
    (success : SuccessfulRun run) :
    run.relation? = some success.relation := by
  cases success with
  | found failedPrefix selected relation selectedExact remaining resultExact =>
      unfold ReconstructionRun.relation?
      rw [resultExact]
      rfl

/--
Construct the success view from an equality already produced for this run.
The exhausted case is eliminated constructively; in the successful case the
relation is identified with the relation stored by the `found` constructor.
-/
def ofRelationExact
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    {reconstruction : ReconstructionSystem
      system Candidate Relation left right}
    (run : ReconstructionRun reconstruction)
    (relation : Relation left right)
    (relationExact : run.relation? = some relation) :
    SuccessfulRun run := by
  cases resultEq : run.result with
  | exhausted failures =>
      unfold ReconstructionRun.relation? at relationExact
      rw [resultEq] at relationExact
      cases relationExact
  | found failedPrefix selected foundRelation selectedExact remaining =>
      unfold ReconstructionRun.relation? at relationExact
      rw [resultEq] at relationExact
      have foundExact : foundRelation = relation := Option.some.inj relationExact
      cases foundExact
      exact .found failedPrefix selected relation selectedExact remaining resultEq

end SuccessfulRun

namespace ReconstructionSystem

/-- Execute extraction and exploration without accepting a relation as input. -/
def run
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (reconstruction : ReconstructionSystem
      system Candidate Relation left right) :
    ReconstructionRun reconstruction :=
  let execution := exploreCandidates reconstruction reconstruction.extract
  { result := execution.result
    supplied_exact := execution.supplied_exact }

end ReconstructionSystem
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.ReconstructionSystem
#print axioms RelationalPerimeter.Computation.FailedAttempt
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.suppliedCandidates
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.testedCandidates
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.attempts
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.failedAttempts
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.selectedCandidate?
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.relation?
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.prependFailure
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.prependFailure_suppliedCandidates
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.prependFailure_testedCandidates
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.prependFailure_failedAttempts
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.prependFailure_selectedCandidate
#print axioms RelationalPerimeter.Computation.ExecutedReconstruction.prependFailure_relation
#print axioms RelationalPerimeter.Computation.CandidateExecution
#print axioms RelationalPerimeter.Computation.CandidateExecution.testedCandidates
#print axioms RelationalPerimeter.Computation.CandidateExecution.selectedCandidate?
#print axioms RelationalPerimeter.Computation.CandidateExecution.relation?
#print axioms RelationalPerimeter.Computation.exploreCandidates
#print axioms RelationalPerimeter.Computation.ReconstructionRun
#print axioms RelationalPerimeter.Computation.ReconstructionRun.testedCandidates
#print axioms RelationalPerimeter.Computation.ReconstructionRun.attempts
#print axioms RelationalPerimeter.Computation.ReconstructionRun.failedAttempts
#print axioms RelationalPerimeter.Computation.ReconstructionRun.selectedCandidate?
#print axioms RelationalPerimeter.Computation.ReconstructionRun.relation?
#print axioms RelationalPerimeter.Computation.SuccessfulRun
#print axioms RelationalPerimeter.Computation.SuccessfulRun.relation
#print axioms RelationalPerimeter.Computation.SuccessfulRun.relation_exact
#print axioms RelationalPerimeter.Computation.SuccessfulRun.ofRelationExact
#print axioms RelationalPerimeter.Computation.ReconstructionSystem.run
/- AXIOM_AUDIT_END -/
