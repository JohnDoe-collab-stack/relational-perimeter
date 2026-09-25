import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.OperationalStability

set_option maxHeartbeats 6000000

/-!
# Projected-state boundary for operational stabilization

The authoritative retained constitution and a counterfactual blocked
constitution share one executed origin and the same projectable assignment,
generation and seed.  They differ in whether a complete one-step operational
stabilization witness can be constructed.  This gives constructive
non-factorization results for both witness availability and a deliberately
coarse calculable width readout.  The full witness retains the causal evidence.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- The exact state data retained by the permitted current-state projection. -/
abbrev NextDiscoveryProjectedState (depth : Nat) :=
  SequentialAssignment (depth + 1) ×
    CanonicalStageGeneration (depth + 1) × Nat

/--
A positive stabilization witness contains the executed one-step history, its
dependent role reading and the stability certificate computed from those roles.
-/
structure OperationalStabilizationWitness
    {depth : Nat} (constitution : NextDiscoveryConstitution depth) : Type 2 where
  history :
    ConstitutiveExecutionHistory (count := 1) constitution.packed.state
  roles : ThreadedConstitutiveRoleHistory history
  stability : OperationalStabilityCertificate history roles

def OperationalStabilizationAvailable {depth : Nat}
    (constitution : NextDiscoveryConstitution depth) : Prop :=
  Nonempty (OperationalStabilizationWitness constitution)

/-- The retained state positively constructs its complete stabilization data. -/
def retainedOperationalStabilizationWitness (depth : Nat) :
    OperationalStabilizationWitness
      (nextDiscoveryConstitution depth .retained) := by
  let history := executeConstitutiveExecutionHistory 1
    (retainedNextDiscoveryState depth).state
    (retainedNextDiscoveryState_fresh depth)
  let roles := buildThreadedConstitutiveRoleHistory history
  exact
    { history := history
      roles := roles
      stability := roles.operationalStabilityCertificate }

theorem retained_operationalStabilizationAvailable (depth : Nat) :
    OperationalStabilizationAvailable
      (nextDiscoveryConstitution depth .retained) :=
  ⟨retainedOperationalStabilizationWitness depth⟩

/-- Failed discovery excludes every positive authoritative history and witness. -/
theorem blocked_operationalStabilizationUnavailable (depth : Nat) :
    ¬ OperationalStabilizationAvailable
      (nextDiscoveryConstitution depth .blocked) := by
  intro available
  rcases available with ⟨witness⟩
  exact failedDiscovery_noPositiveHistory _
    (nextDiscovery_blocked_none depth) witness.history

/-- Availability cannot be recovered from the permitted projected state. -/
theorem operationalStabilizationAvailability_not_factors (depth : Nat) :
    ¬ PredicateFactorsThrough
      (nextDiscoveryProjection (depth := depth))
      (OperationalStabilizationAvailable (depth := depth)) := by
  apply predicate_not_factors_of_same_projection _ _
    (nextDiscoveryConstitution depth .blocked)
    (nextDiscoveryConstitution depth .retained)
  · exact (nextDiscovery_projection_equal depth).symm
  · exact blocked_operationalStabilizationUnavailable depth
  · exact retained_operationalStabilizationAvailable depth

/-- No further view computed solely from the projection recovers availability. -/
theorem operationalStabilizationAvailability_not_factors_through_view
    (depth : Nat) {View : Type}
    (view : NextDiscoveryProjectedState depth → View) :
    ¬ PredicateFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (OperationalStabilizationAvailable (depth := depth)) := by
  apply predicate_not_factors_of_same_projection _ _
    (nextDiscoveryConstitution depth .blocked)
    (nextDiscoveryConstitution depth .retained)
  · exact (congrArg view (nextDiscovery_projection_equal depth)).symm
  · exact blocked_operationalStabilizationUnavailable depth
  · exact retained_operationalStabilizationAvailable depth

/-- Coarse width readout computed from the actual typed frontiers of one
successful discovery.  The proof-relevant stabilization evidence remains in
`OperationalStabilizationWitness`; this projection intentionally records only
the local numerical shape. -/
def discoveryWidthProfile {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) : List Nat :=
  let source := [state]
  let opened :=
    [state.child discovery.var false discovery.fresh,
      state.child discovery.var true discovery.fresh]
  let retained := [state.child discovery.var true discovery.fresh]
  [source.length, opened.length, retained.length]

theorem discoveryWidthProfile_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    discoveryWidthProfile discovery = [1, 2, 1] := by
  rfl

/-- `none` records failed discovery; `some` carries its coarse typed-frontier
width readout. -/
def operationalStabilizationProfile {depth : Nat}
    (constitution : NextDiscoveryConstitution depth) : Option (List Nat) :=
  (nextDiscoveryOutcome constitution).map discoveryWidthProfile

theorem retained_operationalStabilizationProfile (depth : Nat) :
    operationalStabilizationProfile
      (nextDiscoveryConstitution depth .retained) = some [1, 2, 1] := by
  unfold operationalStabilizationProfile
  change Option.map discoveryWidthProfile
      ((runThreadedNextDiscovery
        (retainedNextDiscoveryState depth).state).outcome.discovered?) = _
  rw [runThreadedNextDiscovery_discovered_exact _
    (retainedNextDiscoveryState_fresh depth)]
  rw [canonicalStageDiscovery_found]
  rfl

theorem blocked_operationalStabilizationProfile (depth : Nat) :
    operationalStabilizationProfile
      (nextDiscoveryConstitution depth .blocked) = none := by
  unfold operationalStabilizationProfile
  rw [nextDiscovery_blocked_none]
  rfl

theorem operationalStabilizationProfiles_different (depth : Nat) :
    operationalStabilizationProfile
        (nextDiscoveryConstitution depth .retained) ≠
      operationalStabilizationProfile
        (nextDiscoveryConstitution depth .blocked) := by
  rw [retained_operationalStabilizationProfile,
    blocked_operationalStabilizationProfile]
  decide

/-- Even the coarse calculable readout cannot be recovered from the projected
state. -/
theorem operationalStabilizationProfile_not_factors (depth : Nat) :
    ¬ ValueFactorsThrough
      (nextDiscoveryProjection (depth := depth))
      (operationalStabilizationProfile (depth := depth)) := by
  apply value_not_factors_of_same_projection _ _
    (nextDiscoveryConstitution depth .retained)
    (nextDiscoveryConstitution depth .blocked)
  · exact nextDiscovery_projection_equal depth
  · exact operationalStabilizationProfiles_different depth

/-- No further view computed solely from the projection recovers the coarse
readout. -/
theorem operationalStabilizationProfile_not_factors_through_view
    (depth : Nat) {View : Type}
    (view : NextDiscoveryProjectedState depth → View) :
    ¬ ValueFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (operationalStabilizationProfile (depth := depth)) := by
  apply value_not_factors_of_same_projection _ _
    (nextDiscoveryConstitution depth .retained)
    (nextDiscoveryConstitution depth .blocked)
  · exact congrArg view (nextDiscovery_projection_equal depth)
  · exact operationalStabilizationProfiles_different depth

/--
Self-contained boundary certificate.  The blocked constitution is a causal
counterfactual built from the common executed origin; it is not emitted by the
authoritative public run.
-/
structure ProjectedStabilizationBoundaryCertificate (depth : Nat) : Type 2 where
  retainedWitness :
    OperationalStabilizationWitness
      (nextDiscoveryConstitution depth .retained)
  blockedUnavailable :
    ¬ OperationalStabilizationAvailable
      (nextDiscoveryConstitution depth .blocked)
  sharedProjectedState :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) =
      nextDiscoveryProjection (nextDiscoveryConstitution depth .blocked)
  projectedStateNonconstant :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) ≠
      nextDiscoveryProjection (nextDiscoveryConstitution depth .reference)
  retainedProfileExact :
    operationalStabilizationProfile
      (nextDiscoveryConstitution depth .retained) = some [1, 2, 1]
  blockedProfileExact :
    operationalStabilizationProfile
      (nextDiscoveryConstitution depth .blocked) = none
  stabilizationAvailabilityNotProjected :
    ¬ PredicateFactorsThrough
      (nextDiscoveryProjection (depth := depth))
      (OperationalStabilizationAvailable (depth := depth))
  stabilizationProfileNotProjected :
    ¬ ValueFactorsThrough
      (nextDiscoveryProjection (depth := depth))
      (operationalStabilizationProfile (depth := depth))

def projectedStabilizationBoundaryCertificate (depth : Nat) :
    ProjectedStabilizationBoundaryCertificate depth :=
  { retainedWitness := retainedOperationalStabilizationWitness depth
    blockedUnavailable := blocked_operationalStabilizationUnavailable depth
    sharedProjectedState := nextDiscovery_projection_equal depth
    projectedStateNonconstant := nextDiscovery_projection_nonconstant depth
    retainedProfileExact := retained_operationalStabilizationProfile depth
    blockedProfileExact := blocked_operationalStabilizationProfile depth
    stabilizationAvailabilityNotProjected :=
      operationalStabilizationAvailability_not_factors depth
    stabilizationProfileNotProjected :=
      operationalStabilizationProfile_not_factors depth }

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.NextDiscoveryProjectedState
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalStabilizationWitness
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalStabilizationAvailable
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedOperationalStabilizationWitness
#print axioms ConstitutiveSearch.EndogenousDecomposition.retained_operationalStabilizationAvailable
#print axioms ConstitutiveSearch.EndogenousDecomposition.blocked_operationalStabilizationUnavailable
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStabilizationAvailability_not_factors
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStabilizationAvailability_not_factors_through_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoveryWidthProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoveryWidthProfile_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStabilizationProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.retained_operationalStabilizationProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.blocked_operationalStabilizationProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStabilizationProfiles_different
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStabilizationProfile_not_factors
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStabilizationProfile_not_factors_through_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProjectedStabilizationBoundaryCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.projectedStabilizationBoundaryCertificate
/- AXIOM_AUDIT_END -/
