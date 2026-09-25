import RelationalPerimeter

/-!
# Public-root import gate

This module is a downstream-style build check.  Its presence in the default
Lake target ensures that the public `RelationalPerimeter` module is registered,
built, and importable rather than merely valid when elaborated as a source file.
-/

namespace RelationalPerimeter.Tests.PublicRootImport

open RelationalPerimeter.Computation.EndogenousOperationalDecomposition
open ConstitutiveSearch.EndogenousDecomposition

def publicEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence

def publicFamily :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family

def publicOperationalStability :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.endogenousOperationalStability

/-- The public root exposes the recursive witness whose steps contain the
discovered absorption and the transmitted-content raccord. -/
def publicCausalOperationalStability (input : Nat) :=
  (endogenousOperationalStability input).causalStability

/-- The public root exposes the explicit counterfactual carrier obtained when
every binary structural alternative is kept independent. -/
theorem publicUnabsorbedWidthIsExponential (input : Nat) :
    (structuralObligationFrontier input).length =
      2 ^ (input + 1) :=
  unabsorbed_structural_width_is_exponential input

theorem publicUnabsorbedObligationsAreDistinct (input : Nat) :
    (structuralObligationFrontier input).Nodup :=
  unabsorbed_structural_obligations_are_distinct input

/-- The causal public certificate strictly separates retained operational
width from the unabsorbed structural carrier. -/
theorem publicCertifiedAbsorptionControlsWidth (input : Nat) :
    (CausalOperationalStability.retainedOperationalObligationFrontier
      (publicCausalOperationalStability input)).length <
      (structuralObligationFrontier input).length :=
  certified_absorption_prevents_exponential_accumulation input

theorem publicCollapseMapsIntoRetained (input : Nat)
    (obligation : StructuralObligation input)
    (member : obligation ∈ structuralObligationFrontier input) :
    collapseOperationalObligation input obligation ∈
      [retainedOperationalObligation input] :=
  collapse_operational_obligation_mem_retained input obligation member

theorem publicRetainedObligationIsStructural (input : Nat) :
    retainedOperationalObligation input ∈ structuralObligationFrontier input :=
  retained_operational_obligation_is_structural input

theorem publicOperationalImageIsExact (input : Nat)
    (target : StructuralObligation input) :
    ((endogenousOperationalStability input).causalStability
        |>.InOperationalImage target) ↔
      target = retainedOperationalObligation input :=
  operational_image_iff_eq_retained input target

theorem publicStructuralObligationsShareOperationalStatus (input : Nat)
    (left right : StructuralObligation input) :
    collapseOperationalObligation input left =
      collapseOperationalObligation input right :=
  all_structural_obligations_share_operational_status input left right

/-- The public root exposes the executable path normalizer, not only the
singleton image or its cardinality. -/
theorem publicCollapseFollowsMaterialNormalization (input : Nat)
    (obligation : StructuralObligation input) :
    (collapseOperationalObligation input obligation).decisions =
      materiallyNormalizedDecisionPath input obligation :=
  collapse_decisions_follow_material_normalization input obligation

theorem publicStructuralObligationsShareMaterialStatus (input : Nat)
    (left right : StructuralObligation input) :
    materiallyNormalizedDecisionPath input left =
      materiallyNormalizedDecisionPath input right :=
  all_structural_obligations_share_material_status input left right

def publicProjectedStabilizationBoundary :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.projectedStabilizationBoundary

theorem publicPermittedProjectionIsNonconstant (input : Nat) :
    ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryProjection
        (ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryConstitution
          input .retained) ≠
      ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryProjection
        (ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryConstitution
          input .reference) :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.permitted_projection_is_nonconstant input

end RelationalPerimeter.Tests.PublicRootImport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicFamily
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicOperationalStability
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicCausalOperationalStability
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicUnabsorbedWidthIsExponential
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicUnabsorbedObligationsAreDistinct
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicCertifiedAbsorptionControlsWidth
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicCollapseMapsIntoRetained
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicRetainedObligationIsStructural
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicOperationalImageIsExact
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicStructuralObligationsShareOperationalStatus
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicCollapseFollowsMaterialNormalization
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicStructuralObligationsShareMaterialStatus
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicProjectedStabilizationBoundary
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicPermittedProjectionIsNonconstant
/- AXIOM_AUDIT_END -/
