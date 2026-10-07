import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolePolicySpectrum
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.UnifiedPublicCertificate

/-!
# Rolewise comparison spectrum on the existing public master

These policies consume the already-produced roles and their licensed maps.
They do not execute a new search, alter the master's actual regime, or claim
that a search dynamically selected the requested number of separate roles.
The class theorem and these policies use literally the same source carrier.
-/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum
open Extensive

def history {input : Nat} (master : Instance input) (pending : Nat) :
    RoleStatus.History master.roles :=
  RolePolicySpectrum.comparison master.roles pending

def regime {input : Nat} (master : Instance input) (pending : Nat) :
    ObligationRegime master.carrier :=
  RolePolicySpectrum.regime master.roles pending

theorem width {input : Nat} (master : Instance input) (pending : Nat)
    (bound : pending ≤ input + 1) :
    (regime master pending).frontier.length = 2 ^ pending :=
  RolePolicySpectrum.width_exact master.roles pending bound

theorem injective_iff {input : Nat} (master : Instance input) (pending : Nat)
    (bound : pending ≤ input + 1) :
    Function.Injective (regime master pending).carry ↔ pending = input + 1 :=
  RolePolicySpectrum.injective_iff master.roles pending bound

def collision {input : Nat} (master : Instance input) (pending : Nat)
    (proper : pending < input + 1) : RolePolicySpectrum.Collision (history master pending) :=
  RolePolicySpectrum.collision master.roles pending proper

theorem preserves {input : Nat} (master : Instance input) (pending : Nat)
    (profile : RoleOccurrenceProfile master.roles) (data : RoleProfilePayload profile)
    (accepted : RoleSemantics.ProfileAccept profile data) :
    RoleSemantics.ProfileAccept ((history master pending).selected profile)
      ((history master pending).transform profile data) :=
  RolePolicySpectrum.preserves master.roles pending profile data accepted

theorem spectrum {input : Nat} (master : Instance input) (outputWidth : Nat) :
    (∃ status : RoleStatus.History master.roles,
      (rolewiseObligationFrontier status.policy).length = outputWidth) ↔
    ∃ pending, pending ≤ input + 1 ∧ outputWidth = 2 ^ pending :=
  RolePolicySpectrum.width_spectrum master.roles outputWidth

/-- Direct application of the existing class theorem, with no carrier adapter. -/
theorem class_iff_direct (input pending : Nat) :
    (regime (publicInstance input) pending).frontier.length = 2 ^ (input + 1) ↔
      Function.Injective (regime (publicInstance input) pending).carry :=
  class_iff_on_master_carrier input (regime (publicInstance input) pending)

/-- For n = input + 1, this actual comparison regime has width 2^(n-1). -/
theorem half_width {input : Nat} (master : Instance input) :
    (regime master input).frontier.length = 2 ^ input ∧
      ¬ Function.Injective (regime master input).carry :=
  ⟨width master input (Nat.le_succ input),
    RolePolicySpectrum.not_injective master.roles input (Nat.lt_succ_self input)⟩

/-- A closed witness for every positive length, using only the existing master. -/
theorem every_positive_count (count : Nat) (positive : 0 < count) :
    ∃ input : Nat, count = input + 1 ∧
      ∃ output : ObligationRegime (publicInstance input).carrier,
        output.frontier.length = 2 ^ (count - 1) ∧ ¬ Function.Injective output.carry := by
  cases count with
  | zero => exact False.elim ((Nat.not_lt_zero 0) positive)
  | succ input =>
      exact ⟨input, rfl, regime (publicInstance input) input, half_width (publicInstance input)⟩

end ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.history
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.regime
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.width
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.injective_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.collision
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.spectrum
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.class_iff_direct
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.half_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.PolicySpectrum.every_positive_count
/- AXIOM_AUDIT_END -/
