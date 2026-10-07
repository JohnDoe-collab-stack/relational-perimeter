import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseOperationalStatus

/-!
# Constructed comparison policies on one constituted role history

The first requested roles remain separate. Every later role uses its own
executed, acceptance-preserving transport. This is a downstream comparison
policy, not another search execution or a replacement of the public regime.
Neither the source carrier nor the role history is reconstructed here.
-/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum
open Extensive

/-- Structural recursion on the received role history; no source enumeration. -/
def comparison : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → Nat → RoleStatus.History roles
  | _, _, _, .nil, _ => .nil
  | _, _, _, .step role rest, 0 =>
      .step (some (RoleStatus.returnedTransport (executedRoleReductionLicense role)))
        (comparison rest 0)
  | _, _, _, .step _ rest, pending + 1 => .step none (comparison rest pending)

def regime {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (pending : Nat) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  rolewiseObligationRegime (comparison roles pending).policy

theorem pending_exact : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) →
    (pending : Nat) → pending ≤ count → (comparison roles pending).pendingCount = pending
  | _, _, _, .nil, _pending, bound => (Nat.eq_zero_of_le_zero bound).symm
  | _, _, _, .step _ rest, 0, _ => pending_exact rest 0 (Nat.zero_le _)
  | _, _, _, .step _ rest, pending + 1, bound =>
      congrArg Nat.succ (pending_exact rest pending (Nat.le_of_succ_le_succ bound))

theorem width_exact {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (pending : Nat) (bound : pending ≤ count) :
    (regime roles pending).frontier.length = 2 ^ pending :=
  (comparison roles pending).width.trans (congrArg (Nat.pow 2) (pending_exact roles pending bound))

/-- The actual directed maps preserve arbitrary accepted payloads, not just width. -/
theorem preserves {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (pending : Nat)
    (profile : RoleOccurrenceProfile roles) (data : RoleProfilePayload profile)
    (accepted : RoleSemantics.ProfileAccept profile data) :
    RoleSemantics.ProfileAccept ((comparison roles pending).selected profile)
      ((comparison roles pending).transform profile data) :=
  (comparison roles pending).preserves profile data accepted

theorem full_selected : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → (profile : RoleOccurrenceProfile roles) →
    (comparison roles count).selected profile = profile
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step _ rest, profile => Prod.ext rfl (full_selected rest profile.2)

/-- Two positively constructed source profiles, with an actual carry collision. -/
structure Collision {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} (history : RoleStatus.History roles) where
  left : RoleOccurrenceProfile roles
  right : RoleOccurrenceProfile roles
  distinct : left ≠ right
  carriedTogether : rolewiseCarry history.policy left = rolewiseCarry history.policy right

/-- The first absorbed role supplies the differing constituted occurrences. -/
def collision : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) →
    (pending : Nat) → pending < count → Collision (comparison roles pending)
  | _, _, _, .nil, pending, proper => False.elim ((Nat.not_lt_zero pending) proper)
  | _, _, _, .step role rest, 0, _ =>
      { left := (roleConstitutedOccurrenceAt role .left, defaultRoleOccurrenceProfile rest)
        right := (roleConstitutedOccurrenceAt role .right, defaultRoleOccurrenceProfile rest)
        distinct := fun same => openingRolePosition_left_ne_right role
          (congrArg (fun profile : RoleOccurrenceProfile (.step role rest) => profile.1.position) same)
        carriedTogether := Prod.ext
          ((RoleStatus.localFibres
            (some (RoleStatus.returnedTransport (executedRoleReductionLicense role))) _ _).mpr rfl)
          rfl }
  | _, _, _, .step role rest, pending + 1, proper =>
      let tail := collision rest pending (Nat.lt_of_succ_lt_succ proper)
      { left := (roleConstitutedOccurrenceAt role .left, tail.left)
        right := (roleConstitutedOccurrenceAt role .left, tail.right)
        distinct := fun same => tail.distinct (congrArg Prod.snd same)
        carriedTogether := Prod.ext rfl tail.carriedTogether }

theorem not_injective {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (pending : Nat) (proper : pending < count) :
    ¬ Function.Injective (regime roles pending).carry :=
  fun injective => (collision roles pending proper).distinct
    (injective (collision roles pending proper).carriedTogether)

/-- Injectivity is established from source fibres and a positive collision. -/
theorem injective_iff {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (pending : Nat) (bound : pending ≤ count) :
    Function.Injective (regime roles pending).carry ↔ pending = count := by
  constructor
  · intro injective
    cases Nat.lt_or_eq_of_le bound with
    | inl proper => exact False.elim (not_injective roles pending proper injective)
    | inr same => exact same
  · intro same
    cases same
    intro left right carriedSame
    have selectedSame := ((comparison roles count).fibres left right).mp carriedSame
    exact (full_selected roles left).symm.trans (selectedSame.trans (full_selected roles right))

/-- Every allowed exponent is attained on these same constituted source profiles. -/
theorem every_width_attained {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (pending : Nat) (bound : pending ≤ count) :
    ∃ history : RoleStatus.History roles,
      history.pendingCount = pending ∧
      (rolewiseObligationFrontier history.policy).length = 2 ^ pending ∧
      (Function.Injective (rolewiseCarry history.policy) ↔ pending = count) :=
  ⟨comparison roles pending, pending_exact roles pending bound,
    width_exact roles pending bound, injective_iff roles pending bound⟩

theorem pending_le : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → history.pendingCount ≤ count
  | _, _, _, _, .nil => Nat.le_refl 0
  | _, _, _, _, .step none rest => Nat.succ_le_succ (pending_le rest)
  | _, _, _, _, .step (some _) rest => Nat.le_trans (pending_le rest) (Nat.le_succ _)

/-- Exact spectrum of this rolewise status class, not of arbitrary regimes. -/
theorem width_spectrum {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (width : Nat) :
    (∃ history : RoleStatus.History roles,
      (rolewiseObligationFrontier history.policy).length = width) ↔
    ∃ pending, pending ≤ count ∧ width = 2 ^ pending := by
  constructor
  · rintro ⟨history, same⟩
    exact ⟨history.pendingCount, pending_le history, same.symm.trans history.width⟩
  · rintro ⟨pending, bound, same⟩
    exact ⟨comparison roles pending, (width_exact roles pending bound).trans same.symm⟩

/-- A positive-length history supports exponential submaximal width and a collision. -/
theorem positive_history_half_width {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (positive : 0 < count) :
    ∃ output : ObligationRegime (roleProfileFiniteCarrier roles),
      output.frontier.length = 2 ^ (count - 1) ∧ ¬ Function.Injective output.carry := by
  cases count with
  | zero => exact False.elim ((Nat.not_lt_zero 0) positive)
  | succ count =>
      exact ⟨regime roles count, width_exact roles count (Nat.le_succ count),
        not_injective roles count (Nat.lt_succ_self count)⟩

end ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.comparison
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.regime
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.pending_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.width_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.full_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.Collision
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.collision
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.not_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.injective_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.every_width_attained
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.pending_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.width_spectrum
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum.positive_history_half_width
/- AXIOM_AUDIT_END -/
