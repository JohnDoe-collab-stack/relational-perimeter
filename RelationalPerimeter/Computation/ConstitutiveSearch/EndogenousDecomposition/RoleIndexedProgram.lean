import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProfiles

/-!
# Program indexed by relational roles and acting on constituted profiles

The program defined here is downstream of the role occurrence profiles.  It
does not define an alternative type or a profile frontier.  One atom is tied,
by a private constructor and an equality, to the relation reconstructed by one
executed role.  Its interpreter is typed by the actual opening occurrence:
the left occurrence consumes a left continuation and applies the reconstructed
relation; the right occurrence consumes a right continuation and retains it.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT

/-- One authoritative atom, inseparable from the relation stored by its role. -/
structure RoleStageAtom
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) where
  private mk ::
  returnedRelation :
    GeneratedStructuralFlipAtRelation run.selected
      (causalOpeningLeft source run.selected run.fresh)
      (causalOpeningRight source run.selected run.fresh)
  returnedRelationExact : returnedRelation = role.reconstructedRelation

/-- Compile the relation actually reconstructed in this role. -/
def compileRoleStageAtom
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) : RoleStageAtom role :=
  { returnedRelation := role.reconstructedRelation
    returnedRelationExact := rfl }

/-- Total action denoted by the atom before any acceptance proof is consulted. -/
def RoleStageAtom.action
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (atom : RoleStageAtom role) :
    GeneratedStructuralBranchContinuation
        (causalOpeningLeft source run.selected run.fresh) →
      GeneratedStructuralBranchContinuation
        (causalOpeningRight source run.selected run.fresh) :=
  atom.returnedRelation.mapContinuation

/-- The compiled action is exactly the relation reconstructed by execution. -/
theorem compileRoleStageAtom_action_exact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) :
    (compileRoleStageAtom role).action continuation =
      role.reconstructedRelation.mapContinuation continuation :=
  rfl

/-- The criterion-preservation proof remains separate from the total action. -/
theorem RoleStageAtom.preservesAccepted
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (atom : RoleStageAtom role)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh))
    (accepted : GeneratedStructuralBranchAccept
      (causalOpeningLeft source run.selected run.fresh) continuation) :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      (atom.action continuation) := by
  unfold RoleStageAtom.action
  rw [atom.returnedRelationExact]
  exact role.reconstructedRelation.mapContinuation_accept continuation accepted

/-- Payload type selected by the actual role occurrence. -/
def RoleOpeningPayload
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleOpeningOccurrence role) : Type :=
  match occurrence.position with
  | .left => GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)
  | .right => GeneratedStructuralBranchContinuation
      (causalOpeningRight source run.selected run.fresh)

/--
Interpret one real occurrence.  The transformed and retained cases cannot be
interchanged without changing the required payload type.
-/
def interpretRoleStageAtom
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (atom : RoleStageAtom role)
    (occurrence : RoleOpeningOccurrence role) :
    RoleOpeningPayload occurrence →
      GeneratedStructuralBranchContinuation
        (causalOpeningRight source run.selected run.fresh) :=
  match occurrence with
  | ⟨.left, _, _⟩ => fun continuation => atom.action continuation
  | ⟨.right, _, _⟩ => fun continuation => continuation

theorem interpretCompiledRoleStage_left
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) :
    interpretRoleStageAtom (compileRoleStageAtom role)
        (roleOpeningOccurrenceAt role .left) continuation =
      role.reconstructedRelation.mapContinuation continuation :=
  rfl

theorem interpretCompiledRoleStage_right
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningRight source run.selected run.fresh)) :
    interpretRoleStageAtom (compileRoleStageAtom role)
        (roleOpeningOccurrenceAt role .right) continuation = continuation :=
  rfl

/-- The transformed action is positively non-identity on the executed source. -/
theorem compiledRoleStage_action_changes_executed_source
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage run) :
    ((compileRoleStageAtom role).action run.sourceContinuation).1 ≠
      run.sourceContinuation.1 := by
  intro same
  have selectedSame := congrArg (fun assignment => assignment run.selected) same
  have outputAssignment :
      ((compileRoleStageAtom role).action run.sourceContinuation).1 =
        Assignment.flipAt run.selected run.sourceContinuation.1 := by
    exact role.reconstructedRelation.mapContinuation_assignment _
  have sourceFalse : run.sourceContinuation.1 run.selected = false :=
    run.sourceContinuation.2.1
  rw [outputAssignment, Assignment.flipAt_selected, sourceFalse] at selectedSame
  exact Bool.noConfusion selectedSame

/-- The compiled left case is the output produced by the same executed stage. -/
theorem interpretCompiledRoleStage_executedOutput
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage run) :
    interpretRoleStageAtom (compileRoleStageAtom role)
        (roleOpeningOccurrenceAt role .left) run.sourceContinuation =
      run.outputContinuation := by
  exact Eq.trans
    (compileRoleStageAtom_action_exact role run.sourceContinuation)
    (Eq.trans
      (congrArg
        (fun relation => relation.mapContinuation run.sourceContinuation)
        role.reconstructedRelationExact)
      run.outputExact.symm)

/-- Dependent program: one atom for every role in the authoritative history. -/
inductive RoleIndexedProgram :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      RoleIndexedProgram
        (RelationalConstitutiveRoleHistory.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      (atom : RoleStageAtom headRole)
      (tailProgram : RoleIndexedProgram tailRoles) :
      RoleIndexedProgram
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)

/-- Compile the role history without constructing any profile or alternative. -/
def compileRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleIndexedProgram roles
  | _, _, _, .nil => .nil
  | _, _, _, .step headRole tailRoles =>
      .step (compileRoleStageAtom headRole) (compileRoleHistory tailRoles)

def RoleIndexedProgram.atomCount :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      RoleIndexedProgram roles → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, _, .step _ tail => tail.atomCount + 1

theorem compileRoleHistory_atomCount_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (compileRoleHistory roles).atomCount = count
  | _, _, _, .nil => rfl
  | _, _, _, .step _ tailRoles => by
      exact congrArg (fun value => value + 1)
        (compileRoleHistory_atomCount_exact tailRoles)

/-- Dependent payloads for an already constituted occurrence profile. -/
def RoleProfilePayload :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (profile : RoleOccurrenceProfile roles) → Type
  | _, _, _, .nil, _ => Unit
  | _, _, _, .step _ tailRoles, profile =>
      RoleOpeningPayload profile.1 × RoleProfilePayload (roles := tailRoles) profile.2

/--
Interpret the complete profile by executing the atom selected at every role.
The homogeneous readout is a list of resulting assignments; the typed local
interpreter is what enforces the distinct transformed and retained cases.
-/
def interpretRoleOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (program : RoleIndexedProgram roles) →
      (profile : RoleOccurrenceProfile roles) →
      RoleProfilePayload profile → List Assignment
  | _, _, _, _, .nil, _, _ => []
  | _, _, _, _, .step atom tailProgram, profile, payload =>
      (interpretRoleStageAtom atom profile.1 payload.1).1 ::
        interpretRoleOccurrenceProfile tailProgram profile.2 payload.2

/-- One program step must evaluate its stored atom and then its typed tail. -/
theorem interpretRoleOccurrenceProfile_step
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    {headRole : RelationalConstitutiveRoleStage head}
    {tailRoles : RelationalConstitutiveRoleHistory tail}
    (atom : RoleStageAtom headRole)
    (tailProgram : RoleIndexedProgram tailRoles)
    (headOccurrence : RoleOpeningOccurrence headRole)
    (tailProfile : RoleOccurrenceProfile tailRoles)
    (headPayload : RoleOpeningPayload headOccurrence)
    (tailPayload : RoleProfilePayload tailProfile) :
    interpretRoleOccurrenceProfile
        (RoleIndexedProgram.step atom tailProgram)
        (headOccurrence, tailProfile) (headPayload, tailPayload) =
      (interpretRoleStageAtom atom headOccurrence headPayload).1 ::
        interpretRoleOccurrenceProfile tailProgram tailProfile tailPayload :=
  rfl

/-- Interpreting a complete profile produces exactly one result per role. -/
theorem interpretRoleOccurrenceProfile_length :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (program : RoleIndexedProgram roles) →
      (profile : RoleOccurrenceProfile roles) →
      (payload : RoleProfilePayload profile) →
      (interpretRoleOccurrenceProfile program profile payload).length = count
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .step _ tailProgram, profile, payload => by
      exact congrArg (fun value => value + 1)
        (interpretRoleOccurrenceProfile_length
          tailProgram profile.2 payload.2)

/-- Canonical accepted payload for every already constituted profile. -/
def canonicalRoleProfilePayload :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      RoleProfilePayload profile
  | _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleOpeningOccurrence headRole ×
        RoleOccurrenceProfile tailRoles at profile
      cases profile with
      | mk headOccurrence tailProfile =>
          cases headOccurrence with
          | mk position occurrenceState formedAt =>
              cases position with
              | left =>
                  exact
                    (headRole.executedInput,
                      canonicalRoleProfilePayload tailRoles tailProfile)
              | right =>
                  exact
                    (headRole.completedOutput,
                      canonicalRoleProfilePayload tailRoles tailProfile)

/-- Executed retained assignment at every role, read from the role history. -/
def completedRoleAssignments :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      RelationalConstitutiveRoleHistory run → List Assignment
  | _, _, _, .nil => []
  | _, _, _, .step headRole tailRoles =>
      headRole.completedOutput.1 :: completedRoleAssignments tailRoles

/--
The compiled program normalizes every accepted profile to the outputs actually
completed by the same role history.  The transformed case uses the atom action;
the retained case is already at that output.
-/
theorem interpretCompiledRoleHistory_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      interpretRoleOccurrenceProfile
          (compileRoleHistory roles) profile
          (canonicalRoleProfilePayload roles profile) =
        completedRoleAssignments roles
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleOpeningOccurrence headRole ×
        RoleOccurrenceProfile tailRoles at profile
      cases profile with
      | mk headOccurrence tailProfile =>
          cases headOccurrence with
          | mk position occurrenceState formedAt =>
              cases position with
              | left =>
                  change
                    ((compileRoleStageAtom headRole).action
                        headRole.executedInput).1 ::
                        interpretRoleOccurrenceProfile
                          (compileRoleHistory tailRoles) tailProfile
                          (canonicalRoleProfilePayload
                            tailRoles tailProfile) =
                      headRole.completedOutput.1 ::
                        completedRoleAssignments tailRoles
                  have headExact :
                      (compileRoleStageAtom headRole).action
                          headRole.executedInput =
                        headRole.completedOutput :=
                    Eq.trans
                      (compileRoleStageAtom_action_exact
                        headRole headRole.executedInput)
                      headRole.actionExact.symm
                  rw [congrArg Subtype.val headExact]
                  exact congrArg (List.cons headRole.completedOutput.1)
                    (interpretCompiledRoleHistory_exact tailRoles tailProfile)
              | right =>
                  change
                    headRole.completedOutput.1 ::
                        interpretRoleOccurrenceProfile
                          (compileRoleHistory tailRoles) tailProfile
                          (canonicalRoleProfilePayload
                            tailRoles tailProfile) =
                      headRole.completedOutput.1 ::
                        completedRoleAssignments tailRoles
                  exact congrArg (List.cons headRole.completedOutput.1)
                    (interpretCompiledRoleHistory_exact tailRoles tailProfile)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStageAtom
#print axioms ConstitutiveSearch.EndogenousDecomposition.compileRoleStageAtom
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStageAtom.action
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStageAtom.preservesAccepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOpeningPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretRoleStageAtom
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretCompiledRoleStage_left
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretCompiledRoleStage_right
#print axioms ConstitutiveSearch.EndogenousDecomposition.compiledRoleStage_action_changes_executed_source
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretCompiledRoleStage_executedOutput
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.compileRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram.atomCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.compileRoleHistory_atomCount_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleProfilePayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretRoleOccurrenceProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretRoleOccurrenceProfile_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretRoleOccurrenceProfile_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.canonicalRoleProfilePayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.completedRoleAssignments
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretCompiledRoleHistory_exact
/- AXIOM_AUDIT_END -/
