import Tests.LocalAlignment.DocumentaryControlReaderCeiling
import Tests.LocalAlignment.DocumentaryControlFrontierCeilingOriginal
import Tests.LocalAlignment.DocumentaryControlFrontierApplicationSplit
import Tests.LocalAlignment.DocumentaryControlFrontierApplicationAbsorption

/-! Positive local realizations of reader ceilings accompany the same entire
original preservation. An application produces its continuation, its Reader and
the actual ceiling together. Composition passes that received Nat to its second
child; the native metadata functions occur only in types and erased agreement
proofs. Generic leaf wrapping is conditional on the supplied executor. The
documentary constructors below use only the concrete already opened leaves. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 16000000
universe u
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication
structure Applied {formula : Cnf} (selected : Var)
    {frontier : List (GeneratedStructuralBranchContext formula)}
    (expected : FrontierContinuation (generatedStructuralBranchSystem formula) frontier)
    (expectedCeiling : Nat) where
  application : ControlFrontierApplication.Applied (formula := formula)
    (frontier := frontier) selected expected expectedCeiling
  ceiling : Actual expectedCeiling

theorem applied_limited {formula : Cnf} {selected : Var}
    {frontier : List (GeneratedStructuralBranchContext formula)}
    {expected : FrontierContinuation (generatedStructuralBranchSystem formula) frontier}
    {expectedCeiling : Nat} (actual : Applied selected expected expectedCeiling) :
    actual.application.reader.queryBound selected ≤ actual.ceiling.1 := by
  rw [actual.ceiling.2]
  exact actual.application.limited

structure ExecutablePreservation (formula : Cnf) (selected : Var)
    (source target : List (GeneratedStructuralBranchContext formula)) where
  original : ControlFrontierApplication.ExecutablePreservation formula selected source target
  forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound
  backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound
  forward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) →
    (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) →
    reader.queryBound selected ≤ budget →
    Code Label (Applied (formula := formula) (frontier := target) selected
      (original.preservation.forward.map input) (original.forwardReaderBound budget))
  backward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) target) →
    (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) →
    reader.queryBound selected ≤ budget →
    Code Label (Applied (formula := formula) (frontier := source) selected
      (original.preservation.backward.map input) (original.backwardReaderBound budget))
  forward_finite : ∀ input budget reader limited, Finite (forward input budget reader limited)
  backward_finite : ∀ input budget reader limited, Finite (backward input budget reader limited)

abbrev Formed {formula : Cnf} (selected : Var)
    {source target : List (GeneratedStructuralBranchContext formula)}
    (original : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target) :=
  {execution : ExecutablePreservation formula selected source target //
    execution.original.preservation = original}

theorem finite_of_within {Value : Type u} {code : Code Label Value} {bound : Nat}
    (within : Within code bound) : Finite code := by
  obtain ⟨value, labels, trace, _⟩ := within
  exact ⟨value, labels, trace⟩

def attachCeiling {formula : Cnf} {selected : Var}
    {frontier : List (GeneratedStructuralBranchContext formula)}
    {expected : FrontierContinuation (generatedStructuralBranchSystem formula) frontier}
    {transform : Nat → Nat} (realized : ControlReaderCeiling.Realized transform)
    (budget : Nat)
    (application : ControlFrontierApplication.Applied (formula := formula)
      (frontier := frontier) selected expected (transform budget)) :
    Code Label (Applied selected expected (transform budget)) :=
  (ControlReaderCeiling.code realized budget).bind (fun ceiling =>
    .step .executionPayload (fun _ => .done ⟨application, ceiling⟩))

theorem attach_finite {formula : Cnf} {selected : Var}
    {frontier : List (GeneratedStructuralBranchContext formula)}
    {expected : FrontierContinuation (generatedStructuralBranchSystem formula) frontier}
    {transform : Nat → Nat} (realized : ControlReaderCeiling.Realized transform)
    (budget : Nat)
    (application : ControlFrontierApplication.Applied (formula := formula)
      (frontier := frontier) selected expected (transform budget)) :
    Finite (attachCeiling realized budget application) := by
  apply finite_bind (ControlReaderCeiling.finite realized budget)
  intro ceiling
  exact finite_step _ _ (finite_done _)

/- This generic interface does not assert that an arbitrary supplied original
executor has a closed cost. The leaf constructors below close its actual calls
by selecting the concrete identity, swap, absorption and split executors. -/
def leafForward {formula : Cnf} {selected : Var} {source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (realized : ControlReaderCeiling.Realized original.forwardReaderBound)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := target) selected
      (original.preservation.forward.map input) (original.forwardReaderBound budget)) :=
  .step .transportApplicationCell (fun _ =>
    (original.forward input budget reader limited).bind (fun application =>
      attachCeiling realized budget application))

def leafBackward {formula : Cnf} {selected : Var} {source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (realized : ControlReaderCeiling.Realized original.backwardReaderBound)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := source) selected
      (original.preservation.backward.map input) (original.backwardReaderBound budget)) :=
  .step .transportApplicationCell (fun _ =>
    (original.backward input budget reader limited).bind (fun application =>
      attachCeiling realized budget application))

theorem leaf_forward_finite {formula : Cnf} {selected : Var} {source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (realized : ControlReaderCeiling.Realized original.forwardReaderBound)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input))
    (limited : reader.queryBound selected ≤ budget) :
    Finite (leafForward original realized input budget reader limited) := by
  apply finite_step
  apply finite_bind (finite_of_within (original.forward_bounded _ _ _ _))
  intro application
  exact attach_finite realized budget application

theorem leaf_backward_finite {formula : Cnf} {selected : Var} {source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (realized : ControlReaderCeiling.Realized original.backwardReaderBound)
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input))
    (limited : reader.queryBound selected ≤ budget) :
    Finite (leafBackward original realized input budget reader limited) := by
  apply finite_step
  apply finite_bind (finite_of_within (original.backward_bounded _ _ _ _))
  intro application
  exact attach_finite realized budget application

def leafCode {formula : Cnf} {selected : Var} {source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound)
    (backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound) :
    Code Label {execution : ExecutablePreservation formula selected source target // execution.original = original} :=
  .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
    let forward := leafForward original forwardCeiling
    .step .controlClosure (fun _ =>
      let backward := leafBackward original backwardCeiling
      .step .formationResources (fun _ => .done
        ⟨⟨original, forwardCeiling, backwardCeiling, forward, backward,
          leaf_forward_finite original forwardCeiling,
          leaf_backward_finite original backwardCeiling⟩, rfl⟩))))

theorem leaf_finite {formula : Cnf} {selected : Var} {source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound)
    (backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound) :
    Finite (leafCode original forwardCeiling backwardCeiling) := by
  repeat apply finite_step
  exact finite_done _

def returnLeafCode {formula : Cnf} {selected : Var} {source target}
    {preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound)
    (backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound)
    (same : original.preservation = preservation) : Code Label (Formed selected preservation) :=
  (leafCode original forwardCeiling backwardCeiling).bind (fun received =>
    .done ⟨received.1, (congrArg ControlFrontierApplication.ExecutablePreservation.preservation received.2).trans same⟩)

theorem return_leaf_finite {formula : Cnf} {selected : Var} {source target}
    {preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound)
    (backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound)
    (same : original.preservation = preservation) : Finite (returnLeafCode original forwardCeiling backwardCeiling same) := by
  apply finite_bind (leaf_finite _ _ _); intro received
  exact finite_done _

def formedCode {formula : Cnf} {selected : Var} {source target}
    {preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound)
    (backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound)
    (forward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) →
      (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := target)
        selected (original.preservation.forward.map input) (original.forwardReaderBound budget)))
    (backward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) target) →
      (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := source)
        selected (original.preservation.backward.map input) (original.backwardReaderBound budget)))
    (forwardFinite : ∀ input budget reader limited, Finite (forward input budget reader limited))
    (backwardFinite : ∀ input budget reader limited, Finite (backward input budget reader limited))
    (same : original.preservation = preservation) : Code Label (Formed selected preservation) :=
  .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
    let producedForward := forward
    .step .controlClosure (fun _ =>
      let producedBackward := backward
      .step .formationResources (fun _ => .done
        ⟨⟨original, forwardCeiling, backwardCeiling, producedForward, producedBackward,
          forwardFinite, backwardFinite⟩, same⟩))))

theorem formed_finite {formula : Cnf} {selected : Var} {source target}
    {preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source target}
    (original : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (forwardCeiling : ControlReaderCeiling.Realized original.forwardReaderBound)
    (backwardCeiling : ControlReaderCeiling.Realized original.backwardReaderBound)
    (forward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) source) →
      (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := target)
        selected (original.preservation.forward.map input) (original.forwardReaderBound budget)))
    (backward : (input : FrontierContinuation (generatedStructuralBranchSystem formula) target) →
      (budget : Nat) → (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := source)
        selected (original.preservation.backward.map input) (original.backwardReaderBound budget)))
    (forwardFinite : ∀ input budget reader limited, Finite (forward input budget reader limited))
    (backwardFinite : ∀ input budget reader limited, Finite (backward input budget reader limited))
    (same : original.preservation = preservation) :
    Finite (formedCode original forwardCeiling backwardCeiling forward backward forwardFinite backwardFinite same) := by
  repeat apply finite_step
  exact finite_done _

def identityCode (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula)) :
    Code Label (Formed selected
      (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source)) :=
  (ControlFrontierOpening.identityCode (generatedStructuralBranchSystem formula) source).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := ControlFrontierApplication.identityForward selected source actual
      .step .controlClosure (fun _ =>
        let backward := ControlFrontierApplication.identityBackward selected source actual
        .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected source source :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun _ => 2)
            (fun _ => 2)
            (id)
            (id)
            (forward)
            (backward)
            (ControlFrontierApplication.identity_forward_bounded selected source actual)
            (ControlFrontierApplication.identity_backward_bounded selected source actual)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.identity formula selected source actual) := ⟨original, rfl⟩
          returnLeafCode receivedWhole.1 .identity .identity actual.2)))))

theorem identity_finite (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula)) :
    Finite (identityCode formula selected source) := by
  apply finite_bind (finite_of_within (ControlFrontierOpening.identity_bounded _ _))
  intro actual
  repeat apply finite_step
  exact return_leaf_finite _ _ _ _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.Applied
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.applied_limited
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.ExecutablePreservation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.finite_of_within
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.attachCeiling
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.attach_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.leafForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.leafBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.leaf_forward_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.leaf_backward_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.leafCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.leaf_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.returnLeafCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.return_leaf_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.formedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.formed_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.identityCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.identity_finite
/- AXIOM_AUDIT_END -/
