import Tests.LocalAlignment.DocumentaryControlAssignmentApplication
import Tests.LocalAlignment.DocumentaryControlFrontierEvaluation

/-! The preserved maps and their paid executors are formed together. Applications
return the complete original continuation together with the executable reader of
its actual assignment. A reader bound is a received local hypothesis, closed by
the concrete seed; bounds never apply the native map to discover a budget. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

structure Applied {formula : Cnf} (selected : Var)
    {frontier : List (GeneratedStructuralBranchContext formula)}
    (expected : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) (ceiling : Nat) where
  continuation : Actual expected
  reader : Reader (frontierAssignment (formula := formula) (frontier := frontier) continuation.1)
  limited : reader.queryBound selected ≤ ceiling

structure ExecutablePreservation (formula : Cnf) (selected : Var)
    (source target : List (GeneratedStructuralBranchContext formula)) where
  preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target
  forwardCost : Nat → Nat
  backwardCost : Nat → Nat
  forwardReaderBound : Nat → Nat
  backwardReaderBound : Nat → Nat
  forward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) →
    (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) → reader.queryBound selected ≤ budget →
    Code Label (Applied (formula := formula) (frontier := target) selected (preservation.forward.map input) (forwardReaderBound budget))
  backward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) target) →
    (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) → reader.queryBound selected ≤ budget →
    Code Label (Applied (formula := formula) (frontier := source) selected (preservation.backward.map input) (backwardReaderBound budget))
  forward_bounded : ∀ input budget reader limited, Within (forward input budget reader limited) (forwardCost budget)
  backward_bounded : ∀ input budget reader limited, Within (backward input budget reader limited) (backwardCost budget)

abbrev Formed {formula : Cnf} (selected : Var)
    {source target : List (GeneratedStructuralBranchContext formula)}
    (original : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target) :=
  {execution : ExecutablePreservation formula selected source target // execution.preservation = original}

def forwardCode {formula : Cnf} {selected : Var} {source target}
    (execution : ExecutablePreservation formula selected source target)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) :=
  execution.forward input (reader.queryBound selected) reader (Nat.le_refl _)

def forwardBound {formula : Cnf} {selected : Var} {source target}
    (execution : ExecutablePreservation formula selected source target)
    (reader : Reader assignment) := execution.forwardCost (reader.queryBound selected)

theorem forward_bounded {formula : Cnf} {selected : Var} {source target}
    (execution : ExecutablePreservation formula selected source target)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) :
    Within (forwardCode execution input reader) (forwardBound execution reader) :=
  execution.forward_bounded _ _ _ _

def backwardCode {formula : Cnf} {selected : Var} {source target}
    (execution : ExecutablePreservation formula selected source target)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) :=
  execution.backward input (reader.queryBound selected) reader (Nat.le_refl _)

def backwardBound {formula : Cnf} {selected : Var} {source target}
    (execution : ExecutablePreservation formula selected source target)
    (reader : Reader assignment) := execution.backwardCost (reader.queryBound selected)

theorem backward_bounded {formula : Cnf} {selected : Var} {source target}
    (execution : ExecutablePreservation formula selected source target)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) :
    Within (backwardCode execution input reader) (backwardBound execution reader) :=
  execution.backward_bounded _ _ _ _

def identityForward {formula : Cnf} (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (actual : Actual (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := source) selected (actual.1.forward.map input) budget) :=
  .step .transportApplicationCell (fun _ => .step .transportApplicationPacket (fun _ =>
    .done ⟨⟨input, by obtain ⟨_, actualSame⟩ := actual; cases actualSame; rfl⟩, reader, limited⟩))

def identityBackward {formula : Cnf} (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (actual : Actual (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := source) selected (actual.1.backward.map input) budget) :=
  .step .transportApplicationCell (fun _ => .step .transportApplicationPacket (fun _ =>
    .done ⟨⟨input, by obtain ⟨_, actualSame⟩ := actual; cases actualSame; rfl⟩, reader, limited⟩))

theorem identity_forward_bounded {formula : Cnf} (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (actual : Actual (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (identityForward selected source actual input budget reader limited) 2 :=
  within_step _ _ (within_step _ _ (within_done _))

theorem identity_backward_bounded {formula : Cnf} (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (actual : Actual (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (identityBackward selected source actual input budget reader limited) 2 :=
  within_step _ _ (within_step _ _ (within_done _))

def identityCode (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula)) :
    Code Label (Formed selected (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source)) :=
  (ControlFrontierOpening.identityCode (generatedStructuralBranchSystem formula) source).bind (fun actual =>
    .step .executionPayload (fun _ =>
      .step .controlClosure (fun _ =>
        let forward := identityForward selected source actual
        .step .controlClosure (fun _ =>
          let backward := identityBackward selected source actual
          .step .formationResources (fun _ => .done
            ⟨⟨actual.1, fun _ => 2, fun _ => 2, id, id, forward, backward,
              identity_forward_bounded selected source actual, identity_backward_bounded selected source actual⟩,
              actual.2⟩)))))

theorem identity_bounded (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula)) :
    Within (identityCode formula selected source) (3 + 4) := by
  apply within_bind (ControlFrontierOpening.identity_bounded _ _); intro actual
  repeat apply within_step
  exact within_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.Applied
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.ExecutablePreservation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.forwardCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.forwardBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.backwardCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.backwardBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.identityForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.identityBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.identity_forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.identity_backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.identityCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.identity_bounded
/- AXIOM_AUDIT_END -/
