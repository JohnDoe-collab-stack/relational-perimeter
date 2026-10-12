import Tests.LocalAlignment.DocumentaryControlFrontierSyntax

/-! A source assignment requires a received executable reader. The concrete
documentary seed closes this interface with constant readers. Flipped readers
consume the prior paid reader, compare the actual query structurally and return
the original bit point by point. No function equality or opaque query is used.
Reader and budget closure formation is separate from invoking either closure;
budget computation remains a bootstrap obligation. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication
open SAT Control ControlBindings ControlMasterData

structure Reader (assignment : Assignment) where
  readCode : (query : Var) → Code Label (Actual (assignment query))
  queryBound : Var → Nat
  bounded : (query : Var) → Within (readCode query) (queryBound query)

def constantReadCode (value : Bool) (query : Var) :
    Code Label (Actual ((fun _ : Var => value) query)) :=
  .step .assignmentQueryCell (fun _ => .done ⟨value, rfl⟩)

theorem constant_read_bounded (value : Bool) (query : Var) :
    Within (constantReadCode value query) 1 :=
  within_step _ _ (within_done _)

def constantReader (value : Bool) : Reader (fun _ => value) :=
  ⟨constantReadCode value, fun _ => 1, constant_read_bounded value⟩

def constantReaderCode (value : Bool) : Code Label (Actual (constantReader value)) :=
  .step .controlClosure (fun _ =>
    let read := constantReadCode value
    .step .controlClosure (fun _ =>
      let bound := fun _ : Var => 1
      .step .formationResources (fun _ =>
        .done ⟨⟨read, bound, constant_read_bounded value⟩, rfl⟩)))

theorem constant_reader_bounded (value : Bool) : Within (constantReaderCode value) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def flipReadCode {assignment : Assignment} (selected : Var) (prior : Reader assignment) (query : Var) :
    Code Label (Actual (Assignment.flipAt selected assignment query)) :=
  .step .assignmentQueryCell (fun _ =>
    (ControlPermission.equalCode query selected).bind (fun checked =>
      (prior.readCode query).bind (fun bit =>
        .step .assignmentQueryReturn (fun _ => match checked with
          | .isTrue same => .done ⟨!bit.1, by rw [Assignment.flipAt, if_pos same, bit.2]⟩
          | .isFalse different => .done ⟨bit.1, by rw [Assignment.flipAt, if_neg different]; exact bit.2⟩))))

def flipQueryBound {assignment : Assignment} (prior : Reader assignment) (query : Var) : Nat :=
  (ControlFrontierSyntax.equalBound query + (prior.queryBound query + 1)) + 1

theorem flip_read_bounded {assignment : Assignment} (selected : Var)
    (prior : Reader assignment) (query : Var) :
    Within (flipReadCode selected prior query) (flipQueryBound prior query) := by
  apply within_step
  apply within_bind (ControlFrontierSyntax.equal_bounded query selected); intro checked
  apply within_bind (prior.bounded query); intro bit
  apply within_step
  cases checked <;> exact within_done _

def flippedReader {assignment : Assignment} (selected : Var) (prior : Reader assignment) :
    Reader (Assignment.flipAt selected assignment) :=
  ⟨flipReadCode selected prior, flipQueryBound prior, flip_read_bounded selected prior⟩

def flipReaderCode {assignment : Assignment} (selected : Var) (prior : Reader assignment) :
    Code Label (Actual (flippedReader selected prior)) :=
  .step .controlClosure (fun _ =>
    let read := flipReadCode selected prior
    .step .controlClosure (fun _ =>
      let bound := flipQueryBound prior
      .step .formationResources (fun _ =>
        .done ⟨⟨read, bound, flip_read_bounded selected prior⟩, rfl⟩)))

theorem flip_reader_bounded {assignment : Assignment} (selected : Var) (prior : Reader assignment) :
    Within (flipReaderCode selected prior) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def flipEnvelope (selected : Var) (budget : Nat) : Nat :=
  (ControlFrontierSyntax.equalBound selected + (budget + 1)) + 1

theorem flip_query_envelope {assignment : Assignment} (selected : Var)
    (prior : Reader assignment) (budget : Nat) (limited : prior.queryBound selected ≤ budget) :
    (flippedReader selected prior).queryBound selected ≤ flipEnvelope selected budget :=
  Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right limited 1) _) 1

end ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.Reader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.constantReadCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.constant_read_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.constantReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.constantReaderCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.constant_reader_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flipReadCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flipQueryBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flip_read_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flippedReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flipReaderCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flip_reader_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flipEnvelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssignmentApplication.flip_query_envelope
/- AXIOM_AUDIT_END -/
