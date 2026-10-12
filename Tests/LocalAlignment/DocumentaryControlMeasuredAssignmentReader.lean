import Tests.LocalAlignment.DocumentaryControlMeasuredComparison
import Tests.LocalAlignment.DocumentaryPortableAssignment

/-! Positive realizations of the actual measured assignment readers. Queries
return the complete original MeasuredValue, including its work metadata. The
recipe is received from retained productions; no historical stage is replayed.
Each recipe cell and each visit query delays its inspection/application until
a paid entry. The cost of forming a global envelope is a separate obligation. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

structure Reader {assignment : Assignment} (reader : MeasuredAssignment assignment) where
  queryCode : (query : Var) → Code Label (Actual (reader query))
  finite : ∀ query, Finite (queryCode query)

def alternatingCode : (query : Var) → Code Label (Actual (readAlternatingAssignment query))
  | 0 => .step .assignmentQueryCell (fun _ => .done ⟨⟨true, rfl, ⟨1, 0⟩⟩, rfl⟩)
  | 1 => .step .assignmentQueryCell (fun _ => .done ⟨⟨true, rfl, ⟨1, 0⟩⟩, rfl⟩)
  | query + 2 => .step .assignmentQueryCell (fun _ =>
      (alternatingCode (query + 1)).bind (fun prior =>
      .step .assignmentQueryReturn (fun _ => .done
        ⟨⟨!prior.1.value, congrArg Bool.not prior.1.valueExact, prior.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := prior; cases actual; rfl⟩)))

theorem alternating_finite : (query : Var) → Finite (alternatingCode query)
  | 0 => finite_step _ _ (finite_done _)
  | 1 => finite_step _ _ (finite_done _)
  | query + 2 => finite_step _ _
      (finite_bind (alternating_finite (query + 1)) (fun _ => finite_step _ _ (finite_done _)))

def alternatingReader : Reader readAlternatingAssignment :=
  ⟨alternatingCode, alternating_finite⟩

@[inline] def visitCode {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (prior : Reader reader) (query : Var) : Code Label (Actual
      ((PortableAssignment.visit ⟨assignment, reader⟩).reader query)) :=
  .step .assignmentQueryCell (fun _ =>
    (prior.queryCode query).bind (fun received =>
      .step .assignmentQueryReturn (fun _ => .done
        ⟨⟨received.1.value, received.1.valueExact, received.1.work.visit⟩,
          by obtain ⟨_, actual⟩ := received; cases actual; rfl⟩)))

theorem visit_finite {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (prior : Reader reader) (query : Var) : Finite (visitCode prior query) := by
  apply finite_step
  apply finite_bind (prior.finite query); intro received
  exact finite_step _ _ (finite_done _)

@[inline] def visitedReader {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (prior : Reader reader) : Reader (PortableAssignment.visit ⟨assignment, reader⟩).reader :=
  ⟨fun query => visitCode prior query, visit_finite prior⟩

@[inline] def flipCode {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (selected : Var) (prior : Reader reader) (query : Var) :
    Code Label (Actual (readFlippedAssignment selected reader query)) :=
  .step .assignmentQueryCell (fun _ =>
    (ControlMeasuredComparison.unaryCode query selected).bind (fun compared =>
      (prior.queryCode query).bind (fun received =>
        (ControlMasterData.workCode compared.1.work received.1.work).bind (fun work =>
          .step .assignmentQueryReturn (fun _ => match found : compared.1.result with
            | .isTrue same => .done
                ⟨⟨!received.1.value, by
                    rw [Assignment.flipAt, if_pos same, received.1.valueExact], work.1.visit⟩,
                  by obtain ⟨_, actual⟩ := work; cases actual
                     obtain ⟨_, actual⟩ := received; cases actual
                     obtain ⟨_, actual⟩ := compared; cases actual
                     rw [readFlippedAssignment, found]⟩
            | .isFalse different => .done
                ⟨⟨received.1.value, by
                    rw [Assignment.flipAt, if_neg different]; exact received.1.valueExact,
                    work.1.visit⟩,
                  by obtain ⟨_, actual⟩ := work; cases actual
                     obtain ⟨_, actual⟩ := received; cases actual
                     obtain ⟨_, actual⟩ := compared; cases actual
                     rw [readFlippedAssignment, found]⟩)))))

theorem flip_finite {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (selected : Var) (prior : Reader reader) (query : Var) : Finite (flipCode selected prior query) := by
  apply finite_step
  apply finite_bind (ControlMeasuredComparison.unary_finite query selected); intro compared
  apply finite_bind (prior.finite query); intro received
  apply finite_bind (ControlMasterData.work_finite _ _); intro work
  apply finite_step; split <;> exact finite_done _

@[inline] def flippedReader {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (selected : Var) (prior : Reader reader) : Reader (readFlippedAssignment selected reader) :=
  ⟨fun query => flipCode selected prior query, flip_finite selected prior⟩

def recipeCode (recipe : PortableAssignment.Code) :
    Code Label (Reader (PortableAssignment.interpret recipe).reader) :=
  .step .controlInspect (fun _ => match recipe with
    | [] => .step .controlClosure (fun _ => .done alternatingReader)
    | .visit :: prior => (recipeCode prior).bind (fun realized =>
        .step .controlClosure (fun _ => .done (visitedReader realized)))
    | .flip selected :: prior => (recipeCode prior).bind (fun realized =>
        .step .controlClosure (fun _ => .done (flippedReader selected realized))))

theorem recipe_finite (recipe : PortableAssignment.Code) : Finite (recipeCode recipe) := by
  induction recipe with
  | nil => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | cons command prior previous =>
    cases command <;> rw [recipeCode] <;> apply finite_step <;>
      apply finite_bind previous <;> intro realized <;>
      exact finite_step _ _ (finite_done _)

/-- At zero business fuel, no recipe cell or received query is entered. -/
theorem recipe_zero (recipe : PortableAssignment.Code) :
    runCtl 0 (recipeCode recipe) = none := by
  cases recipe with
  | nil => rw [recipeCode]; rfl
  | cons command prior => cases command <;> rw [recipeCode] <;> rfl

theorem visit_zero {assignment : Assignment} {reader : MeasuredAssignment assignment}
    (prior : Reader reader) (query : Var) : runCtl 0 (visitCode prior query) = none := rfl

def formedCode {bundle : PortableAssignment.Bundle} (formed : PortableAssignment.Formed bundle) :
    Code Label (Reader bundle.reader) :=
  (recipeCode formed.code).bind (fun realized => .step .executionPayload (fun _ =>
    .done (Eq.rec (motive := fun bundle _ => Reader bundle.reader) realized formed.exact)))

theorem formed_finite {bundle : PortableAssignment.Bundle} (formed : PortableAssignment.Formed bundle) :
    Finite (formedCode formed) := by
  apply finite_bind (recipe_finite formed.code); intro realized
  exact finite_step _ _ (finite_done _)

@[inline] def retarget {left right : Assignment} {first : MeasuredAssignment left}
    {second : MeasuredAssignment right} (sameAssignment : left = right)
    (sameReader : HEq first second) (received : Reader first) : Reader second := by
  cases sameAssignment; cases sameReader; exact received

@[inline] def castReader {left right : Assignment} (first : MeasuredAssignment left)
    (same : left = right) (received : Reader first) :
    Reader (Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment) first same) := by
  cases same; exact received

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.Reader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.alternatingCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.alternating_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.alternatingReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.visitCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.visit_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.visitedReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.flipCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.flip_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.flippedReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.recipeCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.recipe_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.recipe_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.visit_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.formedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.formed_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.retarget
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredAssignmentReader.castReader
/- AXIOM_AUDIT_END -/
