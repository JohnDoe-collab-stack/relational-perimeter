import Tests.LocalAlignment.DocumentaryAssignmentCapture
import Tests.LocalAlignment.DocumentaryControlMeasuredAssignmentReader

/-! Capture the recipe from the actual retained values. Reflection traverses
only the received transport syntax; it never reruns a stage or its transports.
The concrete correctness invariant realizes the entire original measured reader. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture
open Resources EndogenousDecomposition SAT Control ControlBindings ControlMasterData ControlMeasuredAssignmentReader

def reflectCode {root : Cnf} {selected : Var} (label : Var)
    {source target : GeneratedStructuralBranchContext root}
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (prior : PortableAssignment.Code) : Code Label (Actual (PortableAssignment.reflect label program prior)) :=
  .step .controlInspect (fun _ => match program with
    | .identity _ => .step .formationValues (fun _ => .done ⟨.visit :: prior, rfl⟩)
    | .atom _ => .step .formationValues (fun _ => .done ⟨.flip label :: prior, rfl⟩)
    | .compose first second => (reflectCode label first prior).bind (fun middle =>
        (reflectCode label second middle.1).bind (fun finish =>
          .step .formationValues (fun _ => .done ⟨.visit :: finish.1, by
            obtain ⟨_, actual⟩ := finish; cases actual
            obtain ⟨_, actual⟩ := middle; cases actual; rfl⟩))))

theorem reflect_finite {root : Cnf} {selected : Var} (label : Var)
    {source target : GeneratedStructuralBranchContext root}
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (prior : PortableAssignment.Code) : Finite (reflectCode label program prior) := by
  induction program generalizing prior with
  | identity => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | atom => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | compose first second ihFirst ihSecond =>
      apply finite_step
      apply finite_bind (ihFirst prior); intro middle
      apply finite_bind (ihSecond middle.1); intro finish
      exact finite_step _ _ (finite_done _)

def retainedCode : (kinds : List MasterResources.Kind) → (values : Values MasterResources.Value kinds) →
    Code Label (Actual (AssignmentCapture.retained kinds values))
  | [], _ => .step .controlInspect (fun _ => .done ⟨[], rfl⟩)
  | kind :: kinds, values => .step .controlInspect (fun _ =>
      (retainedCode kinds values.2).bind (fun prior => match kind with
        | .head _ _ => (reflectCode values.1.down.stage.discovery.var
            values.1.down.stage.execution.code prior.1).bind (fun finish =>
              .done ⟨finish.1, by
                obtain ⟨_, actual⟩ := finish; cases actual
                obtain ⟨_, actual⟩ := prior; cases actual; rfl⟩)
        | .source _ _ | .prefix _ | .fresh _ | .discovery _ | .application _ | .decomposition _ _ _ =>
            .done ⟨prior.1, by obtain ⟨_, actual⟩ := prior; cases actual; rfl⟩))

theorem retained_finite (kinds : List MasterResources.Kind) (values : Values MasterResources.Value kinds) :
    Finite (retainedCode kinds values) := by
  induction kinds with
  | nil => exact finite_step _ _ (finite_done _)
  | cons kind kinds ih =>
      apply finite_step
      apply finite_bind (ih values.2); intro prior
      cases kind <;> try exact finite_done _
      apply finite_bind (reflect_finite _ _ prior.1); intro finish; exact finite_done _

def cursorCode (before : MasterResources.Cursor) : Code Label (Actual (AssignmentCapture.cursor before)) :=
  retainedCode before.kinds before.support.values

theorem cursor_finite (before : MasterResources.Cursor) : Finite (cursorCode before) :=
  retained_finite before.kinds before.support.values

def readerCode (before : MasterResources.Cursor) (correct : AssignmentCapture.Correct before) :
    Code Label (Reader before.assignment.reader) :=
  (cursorCode before).bind (fun recipe =>
    (recipeCode recipe.1).bind (fun realized => .step .executionPayload (fun _ =>
      have actual : PortableAssignment.interpret recipe.1 = PortableAssignment.sequential before.assignment :=
        (congrArg PortableAssignment.interpret recipe.2).trans correct
      .done (Eq.rec (motive := fun bundle _ => Reader bundle.reader) realized actual))))

theorem reader_finite (before : MasterResources.Cursor) (correct : AssignmentCapture.Correct before) :
    Finite (readerCode before correct) := by
  apply finite_bind (cursor_finite before); intro recipe
  apply finite_bind (recipe_finite recipe.1); intro realized
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.reflectCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.reflect_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.retainedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.retained_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.cursorCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.cursor_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.readerCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentCapture.reader_finite
/- AXIOM_AUDIT_END -/
