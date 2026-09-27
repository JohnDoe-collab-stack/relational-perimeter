import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoles

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

/-- Complete duplicate-free local occurrence frontier. -/
def openingOccurrenceFrontier
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    List (RoleOpeningOccurrence role) :=
  [roleOpeningOccurrenceAt role .left,
    roleOpeningOccurrenceAt role .right]

theorem openingOccurrenceFrontier_complete
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (occurrence : RoleOpeningOccurrence role) :
    occurrence ∈ openingOccurrenceFrontier role := by
  cases occurrence with
  | mk position state formedAt =>
      cases formedAt
      cases position with
      | left => exact .head _
      | right => exact .tail _ (.head _)

theorem openingOccurrenceFrontier_nodup
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (openingOccurrenceFrontier role).Nodup := by
  exact .cons
    (fun value member same => by
      cases member with
      | head => exact roleOpeningOccurrence_left_ne_right role same
      | tail _ impossible => cases impossible)
    (.cons (fun _ impossible _ => nomatch impossible) .nil)

/-- Position profile over an authoritative role history. -/
def RolePositionProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      RelationalConstitutiveRoleHistory run → Type
  | _, _, _, .nil => Unit
  | _, _, _, .step headRole tailRoles =>
      OpeningRolePosition headRole × RolePositionProfile tailRoles

/-- Occurrence profile over the same authoritative role history. -/
def RoleOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      RelationalConstitutiveRoleHistory run → Type
  | _, _, _, .nil => Unit
  | _, _, _, .step headRole tailRoles =>
      RoleOpeningOccurrence headRole × RoleOccurrenceProfile tailRoles

/-- Pointwise realization of a complete position profile. -/
def rolePositionToOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RolePositionProfile roles → RoleOccurrenceProfile roles
  | _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, .step headRole tailRoles, profile => by
      change OpeningRolePosition headRole × RolePositionProfile tailRoles at profile
      exact
        (roleOpeningOccurrenceAt headRole profile.1,
          rolePositionToOccurrenceProfile tailRoles profile.2)

/-- Recover all historical positions from an occurrence profile. -/
def roleOccurrenceToPositionProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles → RolePositionProfile roles
  | _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleOpeningOccurrence headRole × RoleOccurrenceProfile tailRoles at profile
      exact
        (roleOpeningOccurrenceToPosition profile.1,
          roleOccurrenceToPositionProfile tailRoles profile.2)

theorem rolePositionProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RolePositionProfile roles) →
      roleOccurrenceToPositionProfile roles
          (rolePositionToOccurrenceProfile roles profile) =
        profile
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step headRole tailRoles, profile => by
      change OpeningRolePosition headRole × RolePositionProfile tailRoles at profile
      let head := profile.1
      let tail := profile.2
      change
        (roleOpeningOccurrenceToPosition
            (roleOpeningOccurrenceAt headRole head),
          roleOccurrenceToPositionProfile tailRoles
            (rolePositionToOccurrenceProfile tailRoles tail)) =
          (head, tail)
      rw [openingPosition_roundTrip,
        rolePositionProfile_roundTrip tailRoles tail]

theorem roleOccurrenceProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      rolePositionToOccurrenceProfile roles
          (roleOccurrenceToPositionProfile roles profile) =
        profile
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleOpeningOccurrence headRole × RoleOccurrenceProfile tailRoles at profile
      let head := profile.1
      let tail := profile.2
      change
        (roleOpeningOccurrenceAt headRole
            (roleOpeningOccurrenceToPosition head),
          rolePositionToOccurrenceProfile tailRoles
            (roleOccurrenceToPositionProfile tailRoles tail)) =
          (head, tail)
      rw [openingOccurrence_roundTrip,
        roleOccurrenceProfile_roundTrip tailRoles tail]

/-- Exact transport between position profiles and realized occurrence profiles. -/
def roleProfileTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    ExactTypeTransport
      (RolePositionProfile roles)
      (RoleOccurrenceProfile roles) :=
  { forward := rolePositionToOccurrenceProfile roles
    backward := roleOccurrenceToPositionProfile roles
    forwardBackward := rolePositionProfile_roundTrip roles
    backwardForward := roleOccurrenceProfile_roundTrip roles }

/- Constructive list lemmas local to the profile construction. -/

theorem profile_mem_map {α β : Type} (map : α → β) {value : α} :
    ∀ {values : List α}, value ∈ values → map value ∈ values.map map
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ prior => .tail _ (profile_mem_map map prior)

theorem profile_mem_append_left {α : Type} {value : α} :
    ∀ {left : List α} (right : List α), value ∈ left → value ∈ left ++ right
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ prior =>
      .tail _ (profile_mem_append_left _ prior)

theorem profile_mem_append_right {α : Type} {value : α} :
    ∀ (left : List α) {right : List α}, value ∈ right → value ∈ left ++ right
  | [], _, prior => prior
  | _ :: tail, _, prior => .tail _ (profile_mem_append_right tail prior)

theorem profile_mem_map_preimage {α β : Type} (map : α → β) {target : β} :
    ∀ {values : List α}, target ∈ values.map map →
      ∃ source, source ∈ values ∧ map source = target
  | _ :: _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, .tail _ prior =>
      let ⟨source, sourceMember, sourceExact⟩ :=
        profile_mem_map_preimage map prior
      ⟨source, .tail _ sourceMember, sourceExact⟩

theorem profile_mem_append_cases {α : Type} {value : α} :
    ∀ {left right : List α}, value ∈ left ++ right →
      value ∈ left ∨ value ∈ right
  | [], _, prior => Or.inr prior
  | _ :: _, _, .head _ => Or.inl (.head _)
  | _ :: tail, _, .tail _ prior =>
      match profile_mem_append_cases (left := tail) prior with
      | .inl inTail => .inl (.tail _ inTail)
      | .inr inRight => .inr inRight

theorem profile_nodup_map
    {α β : Type} (map : α → β)
    (injective : Function.Injective map) :
    ∀ {values : List α}, values.Nodup → (values.map map).Nodup
  | [], .nil => .nil
  | _ :: _, .cons headFresh tailNodup =>
      .cons
        (fun _mapped mappedMember same =>
          let ⟨source, sourceMember, sourceExact⟩ :=
            profile_mem_map_preimage map mappedMember
          headFresh source sourceMember
            (injective (Eq.trans same sourceExact.symm)))
        (profile_nodup_map map injective tailNodup)

theorem profile_nodup_append {α : Type} :
    ∀ {left right : List α},
      left.Nodup → right.Nodup →
      (∀ leftValue, leftValue ∈ left →
        ∀ rightValue, rightValue ∈ right → leftValue ≠ rightValue) →
      (left ++ right).Nodup
  | [], _, .nil, rightNodup, _ => rightNodup
  | head :: _, _, .cons headFresh tailNodup, rightNodup, disjoint =>
      .cons
        (fun value valueMember same =>
          match profile_mem_append_cases valueMember with
          | .inl inTail => headFresh value inTail same
          | .inr inRight => disjoint head (.head _) value inRight same)
        (profile_nodup_append tailNodup rightNodup
          (fun leftValue inTail rightValue inRight =>
            disjoint leftValue (.tail _ inTail) rightValue inRight))

theorem profile_length_map {α β : Type} (map : α → β) :
    ∀ values : List α, (values.map map).length = values.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (profile_length_map map tail)

theorem profile_zero_add : ∀ value : Nat, 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (profile_zero_add value)

theorem profile_succ_add (left : Nat) :
    ∀ right : Nat, Nat.succ left + right = Nat.succ (left + right)
  | 0 => rfl
  | right + 1 => congrArg Nat.succ (profile_succ_add left right)

theorem profile_length_append {α : Type} :
    ∀ left right : List α,
      (left ++ right).length = left.length + right.length
  | [], right => (profile_zero_add right.length).symm
  | _ :: tail, right => Eq.trans
      (congrArg Nat.succ (profile_length_append tail right))
      (profile_succ_add tail.length right.length).symm

/-- Complete frontier produced recursively from the role occurrences. -/
def roleProfileFrontier :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      List (RoleOccurrenceProfile roles)
  | _, _, _, .nil => [()]
  | _, _, _, .step headRole tailRoles =>
      (roleProfileFrontier tailRoles).map
          (fun tail => (roleOpeningOccurrenceAt headRole .left, tail)) ++
        (roleProfileFrontier tailRoles).map
          (fun tail => (roleOpeningOccurrenceAt headRole .right, tail))

theorem roleProfileFrontier_complete :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      profile ∈ roleProfileFrontier roles
  | _, _, _, .nil, profile => by cases profile; exact .head _
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleOpeningOccurrence headRole × RoleOccurrenceProfile tailRoles at profile
      rcases profile with ⟨head, tail⟩
      change
        (head, tail) ∈
          (roleProfileFrontier tailRoles).map
              (fun suffix =>
                (roleOpeningOccurrenceAt headRole .left, suffix)) ++
            (roleProfileFrontier tailRoles).map
              (fun suffix =>
                (roleOpeningOccurrenceAt headRole .right, suffix))
      cases positionExact : head.position with
      | left =>
          have headExact :
              head = roleOpeningOccurrenceAt headRole .left := by
            calc
              head = roleOpeningOccurrenceAt headRole head.position :=
                (openingOccurrence_roundTrip head).symm
              _ = roleOpeningOccurrenceAt headRole .left :=
                congrArg (roleOpeningOccurrenceAt headRole) positionExact
          rw [headExact]
          exact profile_mem_append_left _
            (profile_mem_map
              (fun suffix =>
                (roleOpeningOccurrenceAt headRole .left, suffix))
              (roleProfileFrontier_complete tailRoles tail))
      | right =>
          have headExact :
              head = roleOpeningOccurrenceAt headRole .right := by
            calc
              head = roleOpeningOccurrenceAt headRole head.position :=
                (openingOccurrence_roundTrip head).symm
              _ = roleOpeningOccurrenceAt headRole .right :=
                congrArg (roleOpeningOccurrenceAt headRole) positionExact
          rw [headExact]
          exact profile_mem_append_right _
            (profile_mem_map
              (fun suffix =>
                (roleOpeningOccurrenceAt headRole .right, suffix))
              (roleProfileFrontier_complete tailRoles tail))

theorem roleProfileFrontier_nodup :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (roleProfileFrontier roles).Nodup
  | _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, .step headRole tailRoles => by
      have tailNodup := roleProfileFrontier_nodup tailRoles
      have leftNodup := profile_nodup_map
        (fun suffix => (roleOpeningOccurrenceAt headRole .left, suffix))
        (fun {_left _right} same => congrArg Prod.snd same)
        tailNodup
      have rightNodup := profile_nodup_map
        (fun suffix => (roleOpeningOccurrenceAt headRole .right, suffix))
        (fun {_left _right} same => congrArg Prod.snd same)
        tailNodup
      exact profile_nodup_append leftNodup rightNodup
        (fun leftValue leftMember rightValue rightMember same => by
          let ⟨leftTail, _, leftExact⟩ := profile_mem_map_preimage
            (fun suffix =>
              (roleOpeningOccurrenceAt headRole .left, suffix)) leftMember
          let ⟨rightTail, _, rightExact⟩ := profile_mem_map_preimage
            (fun suffix =>
              (roleOpeningOccurrenceAt headRole .right, suffix)) rightMember
          have pairSame :
              (roleOpeningOccurrenceAt headRole .left, leftTail) =
                (roleOpeningOccurrenceAt headRole .right, rightTail) :=
            Eq.trans leftExact (Eq.trans same rightExact.symm)
          exact roleOpeningOccurrence_left_ne_right headRole
            (congrArg Prod.fst pairSame))

/-- Width is a readout of the role-produced profile frontier. -/
def roleProfileWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Nat :=
  (roleProfileFrontier roles).length

theorem roleProfileWidth_step
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    roleProfileWidth
        (RelationalConstitutiveRoleHistory.step headRole tailRoles) =
      roleProfileWidth tailRoles * 2 := by
  change
    ((roleProfileFrontier tailRoles).map
          (fun tail => (roleOpeningOccurrenceAt headRole .left, tail)) ++
        (roleProfileFrontier tailRoles).map
          (fun tail => (roleOpeningOccurrenceAt headRole .right, tail))).length =
      (roleProfileFrontier tailRoles).length * 2
  calc
    ((roleProfileFrontier tailRoles).map
          (fun tail => (roleOpeningOccurrenceAt headRole .left, tail)) ++
        (roleProfileFrontier tailRoles).map
          (fun tail => (roleOpeningOccurrenceAt headRole .right, tail))).length =
        ((roleProfileFrontier tailRoles).map
            (fun tail =>
              (roleOpeningOccurrenceAt headRole .left, tail))).length +
          ((roleProfileFrontier tailRoles).map
            (fun tail =>
              (roleOpeningOccurrenceAt headRole .right, tail))).length :=
      profile_length_append _ _
    _ = (roleProfileFrontier tailRoles).length +
          (roleProfileFrontier tailRoles).length := by
      rw [profile_length_map, profile_length_map]
    _ = (roleProfileFrontier tailRoles).length * 2 :=
      (Nat.mul_two _).symm

theorem roleProfileWidth_eq_two_pow_count :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      roleProfileWidth roles = 2 ^ count
  | _, _, _, .nil => rfl
  | _, _, _, .step headRole tailRoles => by
      rw [roleProfileWidth_step,
        roleProfileWidth_eq_two_pow_count tailRoles]
      exact (Nat.pow_succ 2 _).symm

/-- Constructive equality decision for complete occurrence profiles. -/
def roleOccurrenceProfileDecEq :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      DecidableEq (RoleOccurrenceProfile roles)
  | _, _, _, .nil => fun left right =>
      match left, right with
      | (), () => isTrue rfl
  | _, _, _, .step headRole tailRoles => fun left right =>
      match roleOpeningOccurrenceDecEq headRole left.1 right.1 with
      | isFalse headDifferent =>
          isFalse (fun same => headDifferent (congrArg Prod.fst same))
      | isTrue headSame =>
          match roleOccurrenceProfileDecEq tailRoles left.2 right.2 with
          | isFalse tailDifferent =>
              isFalse (fun same => tailDifferent (congrArg Prod.snd same))
          | isTrue tailSame =>
              isTrue (Prod.ext headSame tailSame)

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
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePositionProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOccurrenceProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_eq_two_pow_count
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleOccurrenceProfileDecEq
/- AXIOM_AUDIT_END -/
