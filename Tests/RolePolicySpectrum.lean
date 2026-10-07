import RelationalPerimeter

/-! Public-client regressions for policies on the existing master. Requested
statuses are comparisons, not outcomes of an additional discovery run. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RolePolicySpectrumTests
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition Extensive

def same_carrier (input pending : Nat) :
    ObligationRegime (UnifiedMaster.publicInstance input).carrier :=
  UnifiedMaster.PolicySpectrum.regime (UnifiedMaster.publicInstance input) pending

theorem all_allowed_widths {input : Nat} (master : UnifiedMaster.Instance input)
    (pending : Nat) (bound : pending ≤ input + 1) :
    (UnifiedMaster.PolicySpectrum.regime master pending).frontier.length = 2 ^ pending :=
  UnifiedMaster.PolicySpectrum.width master pending bound

theorem full_preservation_iff {input : Nat} (master : UnifiedMaster.Instance input)
    (pending : Nat) (bound : pending ≤ input + 1) :
    Function.Injective (UnifiedMaster.PolicySpectrum.regime master pending).carry ↔
      pending = input + 1 :=
  UnifiedMaster.PolicySpectrum.injective_iff master pending bound

theorem class_applies_directly (input pending : Nat) :
    (UnifiedMaster.PolicySpectrum.regime (UnifiedMaster.publicInstance input) pending).frontier.length =
        2 ^ (input + 1) ↔
      Function.Injective (UnifiedMaster.PolicySpectrum.regime (UnifiedMaster.publicInstance input) pending).carry :=
  RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
    UnifiedMaster.binaryFamily (index := input) ()
    (UnifiedMaster.PolicySpectrum.regime (UnifiedMaster.publicInstance input) pending)

theorem explicit_distinct_sources {input : Nat} (master : UnifiedMaster.Instance input)
    (pending : Nat) (proper : pending < input + 1) :
    (UnifiedMaster.PolicySpectrum.collision master pending proper).left ≠
      (UnifiedMaster.PolicySpectrum.collision master pending proper).right :=
  (UnifiedMaster.PolicySpectrum.collision master pending proper).distinct

theorem explicit_shared_obligation {input : Nat} (master : UnifiedMaster.Instance input)
    (pending : Nat) (proper : pending < input + 1) :
    (UnifiedMaster.PolicySpectrum.regime master pending).carry
        (UnifiedMaster.PolicySpectrum.collision master pending proper).left =
      (UnifiedMaster.PolicySpectrum.regime master pending).carry
        (UnifiedMaster.PolicySpectrum.collision master pending proper).right :=
  (UnifiedMaster.PolicySpectrum.collision master pending proper).carriedTogether

theorem arbitrary_payloads_preserved {input : Nat} (master : UnifiedMaster.Instance input)
    (pending : Nat) (profile : RoleOccurrenceProfile master.roles) (data : RoleProfilePayload profile)
    (accepted : RoleSemantics.ProfileAccept profile data) :
    RoleSemantics.ProfileAccept ((UnifiedMaster.PolicySpectrum.history master pending).selected profile)
      ((UnifiedMaster.PolicySpectrum.history master pending).transform profile data) :=
  UnifiedMaster.PolicySpectrum.preserves master pending profile data accepted

/-- Both sides of the constructed collision have positive accepted payloads. -/
theorem collision_is_viable {input : Nat} (master : UnifiedMaster.Instance input)
    (pending : Nat) (proper : pending < input + 1) :
    RoleSemantics.ProfileAccept (UnifiedMaster.PolicySpectrum.collision master pending proper).left
        (canonicalRoleProfilePayload master.roles (UnifiedMaster.PolicySpectrum.collision master pending proper).left) ∧
      RoleSemantics.ProfileAccept (UnifiedMaster.PolicySpectrum.collision master pending proper).right
        (canonicalRoleProfilePayload master.roles (UnifiedMaster.PolicySpectrum.collision master pending proper).right) :=
  ⟨RoleSemantics.canonicalPayload_accepted master.roles _,
    RoleSemantics.canonicalPayload_accepted master.roles _⟩

theorem obligation_return {input : Nat} (master : UnifiedMaster.Instance input) (pending : Nat)
    (obligation : RolewiseObligation (UnifiedMaster.PolicySpectrum.history master pending).policy) :
    (UnifiedMaster.PolicySpectrum.history master pending).producedOccurrenceTransport.backward
        ((UnifiedMaster.PolicySpectrum.history master pending).producedOccurrenceTransport.forward obligation) =
      obligation :=
  (UnifiedMaster.PolicySpectrum.history master pending).producedOccurrenceTransport.forwardBackward obligation

theorem selected_occurrence_return {input : Nat} (master : UnifiedMaster.Instance input) (pending : Nat)
    (profile : (UnifiedMaster.PolicySpectrum.history master pending).ProducedOccurrence) :
    (UnifiedMaster.PolicySpectrum.history master pending).producedOccurrenceTransport.forward
        ((UnifiedMaster.PolicySpectrum.history master pending).producedOccurrenceTransport.backward profile) =
      profile :=
  (UnifiedMaster.PolicySpectrum.history master pending).producedOccurrenceTransport.backwardForward profile

theorem empty_history_width_and_injectivity {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory 0 state} (roles : RelationalConstitutiveRoleHistory run) :
    (RolePolicySpectrum.regime roles 0).frontier.length = 1 ∧
      Function.Injective (RolePolicySpectrum.regime roles 0).carry :=
  ⟨RolePolicySpectrum.width_exact roles 0 (Nat.le_refl 0),
    (RolePolicySpectrum.injective_iff roles 0 (Nat.le_refl 0)).mpr rfl⟩

theorem uniform_positive_length (count : Nat) (positive : 0 < count) :
    ∃ input : Nat, count = input + 1 ∧
      ∃ output : ObligationRegime (UnifiedMaster.publicInstance input).carrier,
        output.frontier.length = 2 ^ (count - 1) ∧ ¬ Function.Injective output.carry :=
  UnifiedMaster.PolicySpectrum.every_positive_count count positive

theorem submaximal_exponential_not_injective (input : Nat) :
    (UnifiedMaster.PolicySpectrum.regime (UnifiedMaster.publicInstance input) input).frontier.length = 2 ^ input ∧
      ¬ Function.Injective (UnifiedMaster.PolicySpectrum.regime (UnifiedMaster.publicInstance input) input).carry :=
  UnifiedMaster.PolicySpectrum.half_width (UnifiedMaster.publicInstance input)

theorem old_executed_width_unchanged (input : Nat) :
    (UnifiedMaster.publicInstance input).regime.frontier.length = 1 :=
  (UnifiedMaster.publicInstance input).executed_width

/-- Actual finite-image computation, evaluated below on the same three-role master. -/
def computed_widths : List Nat :=
  let master := UnifiedMaster.publicInstance 2
  [ (UnifiedMaster.PolicySpectrum.regime master 3).frontier.length,
    (UnifiedMaster.PolicySpectrum.regime master 2).frontier.length,
    (UnifiedMaster.PolicySpectrum.regime master 1).frontier.length,
    (UnifiedMaster.PolicySpectrum.regime master 0).frontier.length ]

theorem computed_widths_correct : computed_widths = [8, 4, 2, 1] := by
  dsimp only [computed_widths]
  rw [UnifiedMaster.PolicySpectrum.width _ 3 (Nat.le_refl 3),
    UnifiedMaster.PolicySpectrum.width _ 2 (Nat.le_succ 2),
    UnifiedMaster.PolicySpectrum.width _ 1 (by decide),
    UnifiedMaster.PolicySpectrum.width _ 0 (Nat.zero_le 3)]

#eval computed_widths
#guard computed_widths == [8, 4, 2, 1]

end RolePolicySpectrumTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms RolePolicySpectrumTests.same_carrier
#print axioms RolePolicySpectrumTests.all_allowed_widths
#print axioms RolePolicySpectrumTests.full_preservation_iff
#print axioms RolePolicySpectrumTests.class_applies_directly
#print axioms RolePolicySpectrumTests.explicit_distinct_sources
#print axioms RolePolicySpectrumTests.explicit_shared_obligation
#print axioms RolePolicySpectrumTests.arbitrary_payloads_preserved
#print axioms RolePolicySpectrumTests.collision_is_viable
#print axioms RolePolicySpectrumTests.obligation_return
#print axioms RolePolicySpectrumTests.selected_occurrence_return
#print axioms RolePolicySpectrumTests.empty_history_width_and_injectivity
#print axioms RolePolicySpectrumTests.uniform_positive_length
#print axioms RolePolicySpectrumTests.submaximal_exponential_not_injective
#print axioms RolePolicySpectrumTests.old_executed_width_unchanged
#print axioms RolePolicySpectrumTests.computed_widths
#print axioms RolePolicySpectrumTests.computed_widths_correct
/- AXIOM_AUDIT_END -/
