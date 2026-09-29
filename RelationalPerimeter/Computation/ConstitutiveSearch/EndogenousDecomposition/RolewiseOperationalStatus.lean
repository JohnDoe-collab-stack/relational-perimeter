import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleProfileSemantics
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy
import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage

/-!
# Operational status and semantic action on the same constituted profiles

Absence retains both occurrences. Presence carries an actual preserving map.
The finite image is computed on occurrences, not on functional continuations.
Mixed policies are comparisons on one history, not additional SAT executions.
-/
namespace ConstitutiveSearch.EndogenousDecomposition.RoleStatus
open SAT Extensive RelationalExtensive

abbrev Status {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :=
  Option (AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
    (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right))

def target {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run} :
    Status role → RoleConstitutedOccurrence role → RoleConstitutedOccurrence role
  | none, occurrence => occurrence
  | some _, _ => roleConstitutedOccurrenceAt role .right

/-- Complete finite image, constructed before any convergence specialisation. -/
def localRegime {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} (role : RelationalConstitutiveRoleStage run)
    (status : Status role) : ObligationRegime (roleOpeningFiniteCarrier role) :=
  computedTargetImageRegime (roleOpeningFiniteCarrier role)
    (relationallyConstitutedOccurrenceDecEq (generalOpeningStageOfRole role)) (target status)

theorem localFibres {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (status : Status role) (p q : RoleConstitutedOccurrence role) :
    (localRegime role status).carry p = (localRegime role status).carry q ↔
      target status p = target status q :=
  computedTargetImageRegime_carry_eq_iff_target_eq _ _ _ _ _

theorem pendingWidth {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} (role : RelationalConstitutiveRoleStage run) :
    (localRegime role none).frontier.length = 2 := rfl

theorem absorbedWidth {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (transport : AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
      (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right)) :
    (localRegime role (some transport)).frontier.length = 1 := rfl

/-- Data-level action uses the supplied transport only in its absorbed case. -/
def act {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run} :
    (status : Status role) → (o : RoleConstitutedOccurrence role) →
      RoleOpeningPayload o → RoleOpeningPayload (target status o)
  | none, _, c => c
  | some transport, o, c =>
      eliminateRoleConstitutedOccurrence role o
        (motive := fun o => RoleOpeningPayload o →
          RoleOpeningPayload (roleConstitutedOccurrenceAt role .right))
        transport.map (fun c => c) c

/-- The preservation law is separate from the action, and consumes the transport. -/
theorem act_preserves {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (status : Status role) (o : RoleConstitutedOccurrence role) (c : RoleOpeningPayload o) :
    RoleSemantics.LocalAccept o c → RoleSemantics.LocalAccept (target status o) (act status o c) := by
  cases status with
  | none => exact fun accepted => accepted
  | some transport =>
    exact eliminateRoleConstitutedOccurrence role o
      (motive := fun o => ∀ c : RoleOpeningPayload o,
        RoleSemantics.LocalAccept o c →
        RoleSemantics.LocalAccept (target (some transport) o) (act (some transport) o c))
      transport.preservesAccept (fun _ accepted => accepted) c

/-- Each historical role has its own status, retaining its actual typed transport. -/
inductive History : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    RelationalConstitutiveRoleHistory run → Type 2 where
  | nil {state : CausalConstitutiveState} : History (.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {role : RelationalConstitutiveRoleStage head} {roles : RelationalConstitutiveRoleHistory tail}
      (status : Status role) (rest : History roles) : History (.step role roles)

def History.policy : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → History roles → RolewiseObligationPolicy roles
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .step status rest => .step (localRegime _ status) rest.policy

def History.pendingCount : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → History roles → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, _, .step none rest => rest.pendingCount + 1
  | _, _, _, _, .step (some _) rest => rest.pendingCount

def History.selected : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) → RoleOccurrenceProfile roles → RoleOccurrenceProfile roles
  | _, _, _, _, .nil, _ => ()
  | _, _, _, _, .step status rest, p => (target status p.1, rest.selected p.2)

def History.transform : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) → (p : RoleOccurrenceProfile roles) →
    RoleProfilePayload p → RoleProfilePayload (history.selected p)
  | _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, .step status rest, p, c =>
      (act status p.1 c.1, rest.transform p.2 c.2)

theorem History.preserves : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) → (p : RoleOccurrenceProfile roles) → (c : RoleProfilePayload p) →
    RoleSemantics.ProfileAccept p c →
      RoleSemantics.ProfileAccept (history.selected p) (history.transform p c)
  | _, _, _, _, .nil, _, _, _ => True.intro
  | _, _, _, _, .step status rest, p, c, accepted =>
      ⟨act_preserves status p.1 c.1 accepted.1, rest.preserves p.2 c.2 accepted.2⟩

/-- Exact fibres before convergence; pending occurrences must remain distinct. -/
theorem History.fibres : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) → (p q : RoleOccurrenceProfile roles) →
    rolewiseCarry history.policy p = rolewiseCarry history.policy q ↔ history.selected p = history.selected q
  | _, _, _, _, .nil, p, q => by cases p; cases q; exact Iff.rfl
  | _, _, _, _, .step status rest, p, q => by
      constructor
      · intro same
        exact Prod.ext ((localFibres status p.1 q.1).mp (congrArg Prod.fst same))
          ((rest.fibres p.2 q.2).mp (congrArg Prod.snd same))
      · intro same
        exact Prod.ext ((localFibres status p.1 q.1).mpr (congrArg Prod.fst same))
          ((rest.fibres p.2 q.2).mpr (congrArg Prod.snd same))

/-- The exact width follows from local statuses, including every mixed case. -/
theorem History.width : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) →
    (rolewiseObligationFrontier history.policy).length = 2 ^ history.pendingCount
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .step status rest => by
      change (productFrontier (localRegime _ status).frontier
        (rolewiseObligationFrontier rest.policy)).length = _
      rw [productFrontier_length, rest.width]
      cases status with
      | none =>
        rw [pendingWidth]
        exact Eq.trans (Nat.mul_comm _ _) (Nat.pow_succ 2 rest.pendingCount).symm
      | some transport =>
        rw [absorbedWidth, Nat.one_mul]
        rfl

/-- Read the constituted occurrence denoted by each local image value. -/
def History.realize : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) → RolewiseObligation history.policy → RoleOccurrenceProfile roles
  | _, _, _, _, .nil, _ => ()
  | _, _, _, _, .step _ rest, q => (q.1.1, rest.realize q.2)

theorem History.realize_carry : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : History roles) → (p : RoleOccurrenceProfile roles) →
    history.realize (rolewiseCarry history.policy p) = history.selected p
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .step _ rest, p => Prod.ext rfl (rest.realize_carry p.2)

/-- Local status supplied by the actual executed license, not by a Boolean switch. -/
def returnedTransport {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role} (license : ExecutedRoleReductionLicense role atom) :
    AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
      (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right) :=
  { map := atom.action, preservesAccept := license.preservesCriterion }

/-- Actual decisions and their proofs are read from the executed reduction. -/
def executed : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    ExecutedRoleReductionHistory program → History roles
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .step license rest => .step (some (returnedTransport license)) (executed rest)

theorem executed_pendingCount : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) → (executed reduction).pendingCount = 0
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .step _ rest => executed_pendingCount rest

theorem executed_width {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    (rolewiseObligationFrontier (executed reduction).policy).length = 1 := by
  rw [(executed reduction).width, executed_pendingCount]

theorem singletonMember_eq {α : Type} {a b : α} (member : a ∈ [b]) : a = b := by
  cases member with
  | head => rfl
  | tail _ impossible => cases impossible

/-- Equality of executed policy values follows from the local image computation. -/
theorem executed_all_eq : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (p q : RolewiseObligation (executed reduction).policy) → p = q
  | _, _, _, _, _, .nil, p, q => by cases p; cases q; rfl
  | _, _, _, _, _, .step _ rest, p, q => by
      apply Prod.ext
      · apply Subtype.ext
        have pm := p.1.2
        have qm := q.1.2
        change p.1.1 ∈ [_] at pm
        change q.1.1 ∈ [_] at qm
        exact Eq.trans (singletonMember_eq pm) (singletonMember_eq qm).symm
      · exact executed_all_eq rest p.2 q.2

/-- On every input payload, the status action is the actual licensed atom. -/
theorem returnedAct_exact {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role} (license : ExecutedRoleReductionLicense role atom)
    (o : RoleConstitutedOccurrence role) (c : RoleOpeningPayload o) :
    act (some (returnedTransport license)) o c =
      interpretRoleStageAtom atom o (roleConstitutionEvidence role o) c := by
  exact eliminateRoleConstitutedOccurrence role o
    (motive := fun o => ∀ c : RoleOpeningPayload o,
      act (some (returnedTransport license)) o c =
        interpretRoleStageAtom atom o (roleConstitutionEvidence role o) c)
    (fun _ => rfl) (fun _ => rfl) c

/-- Realize the fully absorbed policy payload in the existing target spaces.
This converts target data, never the authoritative source-profile carrier. -/
def executedPayloadOutput : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) → (p : RoleOccurrenceProfile roles) →
    RoleProfilePayload ((executed reduction).selected p) → ExecutedOperationalTargetProfile reduction
  | _, _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, _, .step _ rest, p, c => (c.1, executedPayloadOutput rest p.2 c.2)

/-- Full semantic refinement of the policy, rather than a comparison of widths. -/
theorem executed_action_exact : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (p : RoleOccurrenceProfile roles) → (c : RoleProfilePayload p) →
    executedPayloadOutput reduction p ((executed reduction).transform p c) =
      RoleSemantics.actProfile reduction p c
  | _, _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, _, .step license rest, p, c =>
      Prod.ext (returnedAct_exact license p.1 c.1) (executed_action_exact rest p.2 c.2)

theorem executedPayloadOutput_preserves : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) → (p : RoleOccurrenceProfile roles) →
    (c : RoleProfilePayload ((executed reduction).selected p)) →
    RoleSemantics.ProfileAccept ((executed reduction).selected p) c →
    RoleSemantics.TargetAccept reduction (executedPayloadOutput reduction p c)
  | _, _, _, _, _, .nil, _, _, _ => True.intro
  | _, _, _, _, _, .step _ rest, p, c, accepted =>
      ⟨accepted.1, executedPayloadOutput_preserves rest p.2 c.2 accepted.2⟩

/-- Semantic preservation is obtained directly from the status interpreter. -/
theorem executed_preserves {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (p : RoleOccurrenceProfile roles) (c : RoleProfilePayload p)
    (accepted : RoleSemantics.ProfileAccept p c) :
    RoleSemantics.TargetAccept reduction
      (executedPayloadOutput reduction p ((executed reduction).transform p c)) :=
  executedPayloadOutput_preserves reduction p _ ((executed reduction).preserves p c accepted)

end ConstitutiveSearch.EndogenousDecomposition.RoleStatus

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.returnedAct_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executedPayloadOutput
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executed_action_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executedPayloadOutput_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executed_preserves

#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.singletonMember_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.Status
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.localRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.localFibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.pendingWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.absorbedWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.act
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.act_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.policy
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.pendingCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.transform
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.width
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.realize
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.History.realize_carry
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.returnedTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executed
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executed_pendingCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executed_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.executed_all_eq
/- AXIOM_AUDIT_END -/
