import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoles
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileConstitution

/-!
# Opening occurrences and extensive profiles indexed by relational roles

The local carrier is not a free Boolean label.  A position is realized by an
occurrence carrying the generated structural state formed at that position of
that particular role.  Complete profiles are dependent selections over the
authoritative role history.  Enumeration and width are derived afterwards.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open RelationalExtensive

/-- The two expected positions of one executed binary opening. -/
inductive OpeningRolePosition
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (_role : RelationalConstitutiveRoleStage run) : Type where
  | left
  | right

/-- The generated state occurring at one role position. -/
def OpeningRolePosition.state
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    OpeningRolePosition role →
      GeneratedStructuralBranchContext source.rootFormula
  | .left => causalOpeningLeft source run.selected run.fresh
  | .right => causalOpeningRight source run.selected run.fresh

/--
An opening occurrence carries both its historical position and the generated
structural state that realizes that position.
-/
structure RoleOpeningOccurrence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) where
  position : OpeningRolePosition role
  state : GeneratedStructuralBranchContext source.rootFormula
  formedAt : state = position.state role

/-- Canonical realization of a role position by its generated occurrence. -/
def roleOpeningOccurrenceAt
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    RoleOpeningOccurrence role :=
  { position := position
    state := position.state role
    formedAt := rfl }

/-- Forget only the realized state, retaining the occurrence's position. -/
def roleOpeningOccurrenceToPosition
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleOpeningOccurrence role) :
    OpeningRolePosition role :=
  occurrence.position

theorem openingPosition_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    roleOpeningOccurrenceToPosition
      (roleOpeningOccurrenceAt role position) = position :=
  rfl

theorem openingOccurrence_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleOpeningOccurrence role) :
    roleOpeningOccurrenceAt role
        (roleOpeningOccurrenceToPosition occurrence) =
      occurrence := by
  cases occurrence with
  | mk position state formedAt =>
      cases formedAt
      rfl

/-- Exact reversible realization between positions and occurrences. -/
def openingPositionOccurrenceTransport
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ExactTypeTransport
      (OpeningRolePosition role)
      (RoleOpeningOccurrence role) :=
  { forward := roleOpeningOccurrenceAt role
    backward := roleOpeningOccurrenceToPosition
    forwardBackward := openingPosition_roundTrip role
    backwardForward := openingOccurrence_roundTrip }

/-- Constructive decidable equality of positions. -/
def openingRolePositionDecEq
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    DecidableEq (OpeningRolePosition role)
  | .left, .left => isTrue rfl
  | .left, .right => isFalse (fun impossible => nomatch impossible)
  | .right, .left => isFalse (fun impossible => nomatch impossible)
  | .right, .right => isTrue rfl

/-- The complete local frontier of structural role positions. -/
def openingPositionFrontier
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    List (OpeningRolePosition role) :=
  [.left, .right]

theorem openingPositionFrontier_complete
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    position ∈ openingPositionFrontier role := by
  cases position with
  | left => exact .head _
  | right => exact .tail _ (.head _)

theorem openingPositionFrontier_nodup
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (openingPositionFrontier role).Nodup := by
  exact .cons
    (fun value member same => by
      cases member with
      | head => nomatch same
      | tail _ impossible => cases impossible)
    (.cons (fun _ impossible _ => nomatch impossible) .nil)

/-- Occurrences are equal exactly when their realized positions are equal. -/
theorem roleOpeningOccurrence_eq_of_position_eq
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {left right : RoleOpeningOccurrence role}
    (same : left.position = right.position) :
    left = right := by
  calc
    left = roleOpeningOccurrenceAt role left.position :=
      (openingOccurrence_roundTrip left).symm
    _ = roleOpeningOccurrenceAt role right.position :=
      congrArg (roleOpeningOccurrenceAt role) same
    _ = right := openingOccurrence_roundTrip right

/-- Constructive decidable equality of realized occurrences. -/
def roleOpeningOccurrenceDecEq
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    DecidableEq (RoleOpeningOccurrence role) := by
  intro left right
  match openingRolePositionDecEq role left.position right.position with
  | isTrue same => exact isTrue (roleOpeningOccurrence_eq_of_position_eq same)
  | isFalse different =>
      exact isFalse (fun occurrenceSame =>
        different (congrArg RoleOpeningOccurrence.position occurrenceSame))

/-- Left and right positions are constructively distinct. -/
theorem openingRolePosition_left_ne_right
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (OpeningRolePosition.left : OpeningRolePosition role) ≠
      OpeningRolePosition.right := by
  intro impossible
  nomatch impossible

/-- The two realized opening occurrences are constructively distinct. -/
theorem roleOpeningOccurrence_left_ne_right
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    roleOpeningOccurrenceAt role .left ≠
      roleOpeningOccurrenceAt role .right := by
  intro impossible
  exact openingRolePosition_left_ne_right role
    (congrArg RoleOpeningOccurrence.position impossible)

/-- The two generated states of an opening are distinct as states, not labels. -/
theorem causalOpening_states_distinct
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source) :
    causalOpeningLeft source run.selected run.fresh ≠
      causalOpeningRight source run.selected run.fresh := by
  intro same
  have decisionsSame :=
    congrArg
      (fun state : GeneratedStructuralBranchContext source.rootFormula =>
        state.context.decisions)
      same
  change
    ({ var := run.selected, value := false } : StructuralBranchDecision) ::
        source.operationalState.context.decisions =
      ({ var := run.selected, value := true } : StructuralBranchDecision) ::
        source.operationalState.context.decisions at decisionsSame
  have headsSame := List.cons.inj decisionsSame
  have valuesSame := congrArg StructuralBranchDecision.value headsSame.1
  exact Bool.noConfusion valuesSame

/-- Local occurrence frontier, derived from the position frontier by realization. -/
def openingOccurrenceFrontier
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    List (RoleOpeningOccurrence role) :=
  (openingPositionFrontier role).map (roleOpeningOccurrenceAt role)

theorem openingOccurrenceFrontier_complete
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (occurrence : RoleOpeningOccurrence role) :
    occurrence ∈ openingOccurrenceFrontier role := by
  have member := relational_mem_map (roleOpeningOccurrenceAt role)
    (openingPositionFrontier_complete role occurrence.position)
  exact (openingOccurrence_roundTrip occurrence) ▸ member

theorem openingOccurrenceFrontier_nodup
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (openingOccurrenceFrontier role).Nodup :=
  relational_nodup_map (roleOpeningOccurrenceAt role)
    (fun {_left _right} same => by
      exact congrArg RoleOpeningOccurrence.position same)
    (openingPositionFrontier_nodup role)

/--
One executed role as an exact relational opening.  Positions are independent
from occurrences; the existing position-occurrence transport realizes them,
and formation and provenance are recorded as exact agreements.
-/
def generalOpeningStageOfRole
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    RelationalOpeningStage CausalConstitutiveState source run.next :=
  { Role := RelationalConstitutiveRoleStage run
    Position := OpeningRolePosition role
    Occurrence := RoleOpeningOccurrence role
    Provenance := List Var
    SourceRelation := fun observed candidate =>
      PLift (candidate.searchState = observed)
    FormationRelation := fun candidate occurrence =>
      PLift (candidate = role) ×
        PLift (occurrence.state = occurrence.position.state role)
    TargetRelation := fun candidate observed =>
      PLift (candidate.nextState = observed)
    ProvenanceRelation := fun provenance candidate occurrence =>
      PLift (provenance = source.provenance) ×
        PLift (candidate = role) ×
        PLift (occurrence.state = occurrence.position.state role)
    role := role
    provenance := source.provenance
    sourceWitness := ⟨role.searchStateExact⟩
    targetWitness := ⟨role.nextStateExact⟩
    positionDecEq := openingRolePositionDecEq role
    positionFrontier := openingPositionFrontier role
    positionComplete := openingPositionFrontier_complete role
    positionNodup := openingPositionFrontier_nodup role
    realize := roleOpeningOccurrenceAt role
    classify := roleOpeningOccurrenceToPosition
    realize_classify := openingOccurrence_roundTrip
    classify_realize := openingPosition_roundTrip role
    formationAgreement := fun _ => ⟨⟨rfl⟩, ⟨rfl⟩⟩
    provenanceAgreement := fun _ =>
      ⟨⟨rfl⟩, ⟨⟨rfl⟩, ⟨rfl⟩⟩⟩ }

/-- The general-stage transport is the authoritative occurrence realization. -/
theorem generalOpeningStage_positionOccurrenceTransport_exact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (generalOpeningStageOfRole role).positionOccurrenceTransport =
      openingPositionOccurrenceTransport role :=
  rfl

/-- The general relational history constituted by the authoritative roles. -/
def generalHistoryOfRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      DependentRelationalRoleHistory CausalConstitutiveState state count
  | _, state, _, .nil => .nil state
  | _, _, _, .step headRole tailRoles =>
      .step (generalOpeningStageOfRole headRole)
        (generalHistoryOfRoleHistory tailRoles)

/-- Position profile over an authoritative role history. -/
abbrev RolePositionProfile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Type :=
  RelationalPositionProfile (generalHistoryOfRoleHistory roles)

/--
The sole occurrence-profile carrier of the executed instance.  It is exactly
the profile derived from the role history through the relational realization;
no parallel concrete profile is defined.
-/
abbrev RoleOccurrenceProfile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Type :=
  RelationalOccurrenceProfile (generalHistoryOfRoleHistory roles)

/-- Pointwise realization of a complete position profile. -/
def rolePositionToOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RolePositionProfile roles → RoleOccurrenceProfile roles :=
  fun roles =>
    relationalPositionToOccurrenceProfile (generalHistoryOfRoleHistory roles)

/-- Recover all historical positions from an occurrence profile. -/
def roleOccurrenceToPositionProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles → RolePositionProfile roles :=
  fun roles =>
    relationalOccurrenceToPositionProfile (generalHistoryOfRoleHistory roles)

theorem rolePositionProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RolePositionProfile roles) →
      roleOccurrenceToPositionProfile roles
          (rolePositionToOccurrenceProfile roles profile) =
        profile :=
  fun roles =>
    relationalPositionProfile_roundTrip (generalHistoryOfRoleHistory roles)

theorem roleOccurrenceProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      rolePositionToOccurrenceProfile roles
          (roleOccurrenceToPositionProfile roles profile) =
        profile :=
  fun roles =>
    relationalOccurrenceProfile_roundTrip (generalHistoryOfRoleHistory roles)

/-- Exact transport between position profiles and realized occurrence profiles. -/
def roleProfileTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    ExactTypeTransport
      (RolePositionProfile roles)
      (RoleOccurrenceProfile roles) :=
  relationalProfileTransport (generalHistoryOfRoleHistory roles)

/-- The sole profile frontier, derived from the exact relational history. -/
def roleProfileFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    List (RoleOccurrenceProfile roles) :=
  relationalProfileFrontier (generalHistoryOfRoleHistory roles)

theorem roleProfileFrontier_complete :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      profile ∈ roleProfileFrontier roles :=
  fun roles profile =>
    relationalProfileFrontier_complete
      (generalHistoryOfRoleHistory roles) profile

theorem roleProfileFrontier_nodup :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (roleProfileFrontier roles).Nodup :=
  fun roles =>
    relationalProfileFrontier_nodup (generalHistoryOfRoleHistory roles)

/-- Width is a readout of the role-produced profile frontier. -/
def roleProfileWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Nat :=
  relationalProfileWidth (generalHistoryOfRoleHistory roles)

/-- Every executed role opening has exactly two realized positions. -/
theorem generalRoleHistory_uniformBinary :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      UniformLocalArity (generalHistoryOfRoleHistory roles) 2
  | _, _, _, .nil => True.intro
  | _, _, _, .step _ tailRoles =>
      ⟨rfl, generalRoleHistory_uniformBinary tailRoles⟩

theorem roleProfileWidth_eq_two_pow_count
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    roleProfileWidth roles = 2 ^ count :=
  uniformLocalArity_width
    (generalHistoryOfRoleHistory roles) 2
    (generalRoleHistory_uniformBinary roles)

theorem roleProfileWidth_step
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    roleProfileWidth
        (RelationalConstitutiveRoleHistory.step headRole tailRoles) =
      roleProfileWidth tailRoles * 2 := by
  rw [roleProfileWidth_eq_two_pow_count,
    roleProfileWidth_eq_two_pow_count]
  exact (Nat.pow_succ 2 _).symm

/-- Constructive equality decision for complete occurrence profiles. -/
def roleOccurrenceProfileDecEq :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      DecidableEq (RoleOccurrenceProfile roles) :=
  fun roles =>
    relationalOccurrenceProfileDecEq (generalHistoryOfRoleHistory roles)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.OpeningRolePosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOpeningOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionOccurrenceTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOpening_states_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingOccurrenceFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingOccurrenceFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingOccurrenceFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalOpeningStageOfRole
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalOpeningStage_positionOccurrenceTransport_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistoryOfRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePositionProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOccurrenceProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalRoleHistory_uniformBinary
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_eq_two_pow_count
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleOccurrenceProfileDecEq
/- AXIOM_AUDIT_END -/
