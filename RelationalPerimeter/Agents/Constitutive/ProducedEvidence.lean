import RelationalPerimeter.Agents.Constitutive.Requirement
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.UnifiedPublicCertificate

/-! Contextual targets produced by normalization or by a live executed stage.
The register does not retain the initial source-profile choice. -/
set_option genInjectivity false
namespace ConstitutiveSearch.Agent
open SAT Resources EndogenousDecomposition

/- The origin is a dependent, positive witness of the producer, not a tag
attached to an independently supplied acceptable continuation. No constructor
stores the source-profile choice which normalization is allowed to forget. -/
inductive TargetOrigin : (root : Cnf) → (context : GeneratedStructuralBranchContext root) →
    GeneratedStructuralBranchContinuation context → Type 3 where
  | normalized {state : CausalConstitutiveState} {head : CausalConstitutiveStageExecution state}
      {role : RelationalConstitutiveRoleStage head} {atom : RoleStageAtom role}
      (license : ExecutedRoleReductionLicense role atom) :
      TargetOrigin _ (causalOpeningRight state head.selected head.fresh)
        (retainedExecutedRoleOperationalTarget license)
  | resumed {memory : LiveContinuation.Memory} (production : LiveContinuation.Production memory) :
      TargetOrigin _ production.built.stage.schedule.entry.target production.built.stage.application.output

theorem TargetOrigin.accepted {root : Cnf} {context : GeneratedStructuralBranchContext root}
    {continuation : GeneratedStructuralBranchContinuation context}
    (origin : TargetOrigin root context continuation) : GeneratedStructuralBranchAccept context continuation :=
  match origin with
  | .normalized license => license.retainedAccepted
  | .resumed production => production.built.stage.outputAccepted

structure AnswerTarget where
  private mk ::
  root : Cnf
  context : GeneratedStructuralBranchContext root
  continuation : GeneratedStructuralBranchContinuation context
  origin : TargetOrigin root context continuation

theorem AnswerTarget.accepted (target : AnswerTarget) :
    GeneratedStructuralBranchAccept target.context target.continuation := target.origin.accepted

def AnswerTarget.read (target : AnswerTarget) (var : Var) : Bool :=
  target.continuation.1 var

def initialTargets : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (target : ExecutedOperationalTargetProfile reduction) →
    RoleSemantics.TargetAccept reduction target →
    target = retainedExecutedOperationalTargetProfile reduction → List AnswerTarget
  | _, _, _, _, _, .nil, _, _, _ => []
  | _, state, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ head _ _ _ _ _ license rest, target, accepted, exactOutput =>
      ⟨_, causalOpeningRight state head.selected head.fresh,
        target.1, (congrArg Prod.fst exactOutput).symm ▸ TargetOrigin.normalized license⟩ ::
        initialTargets rest target.2 accepted.2 (congrArg Prod.snd exactOutput)

theorem initialTargets_length : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (target : ExecutedOperationalTargetProfile reduction) →
    (accepted : RoleSemantics.TargetAccept reduction target) →
    (exactOutput : target = retainedExecutedOperationalTargetProfile reduction) →
    (initialTargets reduction target accepted exactOutput).length = count
  | _, _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, _, .step _ rest, target, accepted, exactOutput =>
      congrArg Nat.succ (initialTargets_length rest target.2 accepted.2 (congrArg Prod.snd exactOutput))

def resumedTarget {memory : LiveContinuation.Memory}
    (production : LiveContinuation.Production memory) : AnswerTarget :=
  ⟨_, production.built.stage.schedule.entry.target,
    production.built.stage.application.output, .resumed production⟩

theorem resumedTarget_read {memory : LiveContinuation.Memory}
    (production : LiveContinuation.Production memory) (var : Var) :
    (resumedTarget production).read var =
      production.built.stage.application.output.1 var := rfl

abbrev Located (register : List AnswerTarget) := (target : AnswerTarget) × Ref register target

def extendReference {register : List AnswerTarget} (extra : List AnswerTarget) :
    {target : AnswerTarget} → Ref register target → Ref (register ++ extra) target
  | _, .here => .here
  | _, .prior reference => .prior (extendReference extra reference)

theorem extendReference_position {register : List AnswerTarget} (extra : List AnswerTarget)
    {target : AnswerTarget} (reference : Ref register target) :
    (extendReference extra reference).position = reference.position := by
  induction reference with
  | here => rfl
  | prior reference ih => exact congrArg Nat.succ ih

def resolveHandle : (register : List AnswerTarget) → Nat → Option (Located register)
  | [], _ => none
  | target :: _, 0 => some ⟨target, .here⟩
  | _ :: tail, handle + 1 =>
      (resolveHandle tail handle).map (fun occurrence => ⟨occurrence.1, .prior occurrence.2⟩)

def readRegister (register : List AnswerTarget) (handle : Nat) (var : Var) : Option Bool :=
  (resolveHandle register handle).map (fun occurrence => occurrence.1.read var)

theorem resolveHandle_present : ∀ (register : List AnswerTarget) (handle : Nat),
    handle < register.length → (resolveHandle register handle).isSome = true
  | [], _, impossible => False.elim (Nat.not_lt_zero _ impossible)
  | _ :: _, 0, _ => rfl
  | _ :: tail, handle + 1, within => by
      have smaller := resolveHandle_present tail handle (Nat.lt_of_succ_lt_succ within)
      cases found : resolveHandle tail handle with
      | none => rw [found] at smaller; cases smaller
      | some occurrence => rw [resolveHandle, found]; rfl

theorem resolveHandle_absent : ∀ (register : List AnswerTarget) (handle : Nat),
    register.length ≤ handle → resolveHandle register handle = none
  | [], _, _ => rfl
  | _ :: _, 0, impossible => False.elim (Nat.not_succ_le_zero _ impossible)
  | _ :: tail, handle + 1, outside => by
      change Option.map _ (resolveHandle tail handle) = none
      rw [resolveHandle_absent tail handle (Nat.le_of_succ_le_succ outside)]
      rfl

theorem map_comp {A : Type u} {B : Type v} {C : Type w}
    (value : Option A) (first : A → B) (second : B → C) :
    (value.map first).map second = value.map (fun x => second (first x)) := by
  cases value <;> rfl

theorem resolveHandle_transport : ∀ (register extra : List AnswerTarget) (handle : Nat),
    handle < register.length →
      resolveHandle (register ++ extra) handle = (resolveHandle register handle).map
        (fun occurrence => ⟨occurrence.1, extendReference extra occurrence.2⟩)
  | [], _, _, impossible => False.elim (Nat.not_lt_zero _ impossible)
  | _ :: _, _, 0, _ => rfl
  | head :: tail, extra, handle + 1, within => by
      change (resolveHandle (tail ++ extra) handle).map _ =
        ((resolveHandle tail handle).map (fun occurrence =>
          (⟨occurrence.1, Ref.prior occurrence.2⟩ : Located (head :: tail)))).map _
      rw [resolveHandle_transport tail extra handle (Nat.lt_of_succ_lt_succ within), map_comp, map_comp]
      rfl

theorem readRegister_succ (head : AnswerTarget) (tail : List AnswerTarget) (handle : Nat) (var : Var) :
    readRegister (head :: tail) (handle + 1) var = readRegister tail handle var := by
  unfold readRegister
  rw [resolveHandle, map_comp]

theorem readRegister_append : ∀ (register extra : List AnswerTarget) (handle : Nat) (var : Var),
    handle < register.length →
      readRegister (register ++ extra) handle var = readRegister register handle var
  | [], _, _, _, impossible => False.elim (Nat.not_lt_zero _ impossible)
  | _ :: _, _, 0, _, _ => rfl
  | _ :: tail, extra, handle + 1, var, within => by
      change readRegister (_ :: (tail ++ extra)) (handle + 1) var = _
      rw [readRegister_succ, readRegister_succ]
      exact readRegister_append tail extra handle var (Nat.lt_of_succ_lt_succ within)

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.TargetOrigin
#print axioms ConstitutiveSearch.Agent.TargetOrigin.accepted
#print axioms ConstitutiveSearch.Agent.AnswerTarget
#print axioms ConstitutiveSearch.Agent.AnswerTarget.accepted
#print axioms ConstitutiveSearch.Agent.AnswerTarget.read
#print axioms ConstitutiveSearch.Agent.initialTargets
#print axioms ConstitutiveSearch.Agent.initialTargets_length
#print axioms ConstitutiveSearch.Agent.resumedTarget
#print axioms ConstitutiveSearch.Agent.resumedTarget_read
#print axioms ConstitutiveSearch.Agent.extendReference
#print axioms ConstitutiveSearch.Agent.extendReference_position
#print axioms ConstitutiveSearch.Agent.resolveHandle_transport
#print axioms ConstitutiveSearch.Agent.resolveHandle
#print axioms ConstitutiveSearch.Agent.resolveHandle_present
#print axioms ConstitutiveSearch.Agent.resolveHandle_absent
#print axioms ConstitutiveSearch.Agent.map_comp
#print axioms ConstitutiveSearch.Agent.readRegister_succ
#print axioms ConstitutiveSearch.Agent.readRegister_append
/- AXIOM_AUDIT_END -/
