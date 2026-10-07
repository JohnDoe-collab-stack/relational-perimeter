import RelationalPerimeter.Constitution.Grouping.Normalization
import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage

/-!
# Normal targets and certified fragment frontiers

The source enumeration and equality algorithm come from the existing finite
carrier. This module introduces no second finite carrier or obligation regime.
The exhaustive frontier is a validation readout, not the fragment producer.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.Grouping.FiniteImage

def Target (rules : Rules) := {x : rules.State // rules.normal x = x}

def carry (rules : Rules) (x : rules.State) : Target rules :=
  ⟨rules.normal x, rules.normal_idempotent x⟩

theorem carry_fibres (rules : Rules) (x y : rules.State) :
    carry rules x = carry rules y ↔ Nonempty (Chain rules.Step x y) :=
  ⟨fun same => (rules.normal_eq_iff_chain x y).mp (congrArg Subtype.val same),
    fun chain => Subtype.ext ((rules.normal_eq_iff_chain x y).mpr chain)⟩

structure Composed (rules : Rules) where
  frontier : List rules.State
  distinct : frontier.Nodup
  exact : ∀ y, y ∈ frontier ↔ rules.normal y = y

def frontier (rules : Rules) (equality : DecidableEq rules.State)
    (sources : List rules.State) : List rules.State :=
  Extensive.deduplicate equality (sources.map rules.normal)

theorem frontier_exact (rules : Rules) (equality : DecidableEq rules.State)
    (sources : List rules.State) (complete : ∀ x, x ∈ sources) (y : rules.State) :
    y ∈ frontier rules equality sources ↔ rules.normal y = y := by
  constructor
  · intro member
    obtain ⟨x, _, same⟩ := Extensive.mem_map_preimage rules.normal
      ((Extensive.mem_deduplicate_iff equality y _).mp member)
    cases same
    exact rules.normal_idempotent x
  · intro fixed
    exact (Extensive.mem_deduplicate_iff equality y _).mpr
      (fixed ▸ Extensive.mem_map rules.normal (complete y))

theorem composed_width (rules : Rules) (equality : DecidableEq rules.State)
    (sources : List rules.State) (complete : ∀ x, x ∈ sources) (composed : Composed rules) :
    (frontier rules equality sources).length = composed.frontier.length := by
  letI := equality
  apply Nat.le_antisymm
  · exact Extensive.nodup_length_le_of_subset (Extensive.deduplicate_nodup equality _)
      (fun _ member => (composed.exact _).mpr ((frontier_exact rules equality sources complete _).mp member))
  · exact Extensive.nodup_length_le_of_subset composed.distinct
      (fun _ member => (frontier_exact rules equality sources complete _).mpr ((composed.exact _).mp member))

end ConstitutiveSearch.Grouping.FiniteImage
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Grouping.FiniteImage.Target
#print axioms ConstitutiveSearch.Grouping.FiniteImage.carry
#print axioms ConstitutiveSearch.Grouping.FiniteImage.carry_fibres
#print axioms ConstitutiveSearch.Grouping.FiniteImage.Composed
#print axioms ConstitutiveSearch.Grouping.FiniteImage.frontier
#print axioms ConstitutiveSearch.Grouping.FiniteImage.frontier_exact
#print axioms ConstitutiveSearch.Grouping.FiniteImage.composed_width
/- AXIOM_AUDIT_END -/
