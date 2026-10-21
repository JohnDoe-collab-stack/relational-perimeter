import RelationalPerimeter.Agents.Neural.IncrementalChecker

/-!
# Equivalence of incremental and complete reference verification

Both checkers decide the same exact target and next-input conditions.  The
incremental checker additionally returns the calculated certificate delta.
Equivalence is stated for every serialized delta at the acceptance level and,
on success, identifies the exact checked update returned by both paths.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

def IncrementalUpdateAccepted (update : IncrementalNeuralUpdate) : Prop :=
  Exists fun checked => checkIncrementalUpdate update = .ok checked

def IncrementalUpdateLocalConditions
    (update : IncrementalNeuralUpdate) : Prop :=
  materializeIncrementalTarget update = publicSerializedReconfiguredNetwork ∧
    update.nextInput = publicSubstantiveNext

theorem checkIncrementalUpdate_complete_for_local_conditions
    (update : IncrementalNeuralUpdate) :
    IncrementalUpdateAccepted update ↔
      IncrementalUpdateLocalConditions update := by
  constructor
  · intro accepted
    rcases accepted with ⟨checked, exact⟩
    unfold checkIncrementalUpdate at exact
    split at exact
    · split at exact
      · exact ⟨‹materializeIncrementalTarget update =
            publicSerializedReconfiguredNetwork›,
          ‹update.nextInput = publicSubstantiveNext›⟩
      · cases exact
    · cases exact
  · intro conditions
    rcases conditions with ⟨targetExact, inputExact⟩
    refine ⟨publicIncrementalCheckedUpdate, ?_⟩
    unfold checkIncrementalUpdate
    split
    · split
      · rfl
      · exact False.elim (‹Not (update.nextInput = publicSubstantiveNext)›
          inputExact)
    · exact False.elim
        (‹Not (materializeIncrementalTarget update =
          publicSerializedReconfiguredNetwork)› targetExact)

theorem incrementalAndReferenceLocalConditions_equivalent
    (update : IncrementalNeuralUpdate) :
    IncrementalUpdateLocalConditions update ↔
      ReferenceUpdateLocalConditions update.toFullReferenceUpdate := by
  rfl

/-- For every serialized delta, incremental verification accepts exactly when
complete verification accepts the materialized target. -/
theorem incrementalAndReferenceAcceptance_equivalent
    (update : IncrementalNeuralUpdate) :
    IncrementalUpdateAccepted update ↔
      ReferenceUpdateAccepted update.toFullReferenceUpdate := by
  constructor
  · intro incrementalAccepted
    have incrementalConditions : IncrementalUpdateLocalConditions update :=
      (checkIncrementalUpdate_complete_for_local_conditions update).mp
        incrementalAccepted
    have referenceConditions :
        ReferenceUpdateLocalConditions update.toFullReferenceUpdate :=
      (incrementalAndReferenceLocalConditions_equivalent update).mp
        incrementalConditions
    exact (checkReferenceUpdate_complete_for_local_conditions
      update.toFullReferenceUpdate).mpr referenceConditions
  · intro referenceAccepted
    have referenceConditions :
        ReferenceUpdateLocalConditions update.toFullReferenceUpdate :=
      (checkReferenceUpdate_complete_for_local_conditions
        update.toFullReferenceUpdate).mp referenceAccepted
    have incrementalConditions : IncrementalUpdateLocalConditions update :=
      (incrementalAndReferenceLocalConditions_equivalent update).mpr
        referenceConditions
    exact (checkIncrementalUpdate_complete_for_local_conditions update).mpr
      incrementalConditions

theorem publicIncrementalCoreCheckedUpdate_eq_reference :
    publicIncrementalCoreCheckedUpdate = publicReferenceCheckedUpdate := by
  rfl

/-- Every successful incremental result is the same checked update returned
by a successful full verification of its materialized target. -/
theorem incrementalSuccess_matches_reference
    (update : IncrementalNeuralUpdate)
    (incremental : PublicIncrementalCheckedUpdate)
    (accepted : checkIncrementalUpdate update = .ok incremental) :
    Exists fun complete : CheckedUpdate publicInitialCheckedAgent .reconfigured =>
      checkReferenceUpdate update.toFullReferenceUpdate = .ok complete ∧
        incremental.checked = complete := by
  have incrementalCanonical :=
    checkIncrementalUpdate_sound update incremental accepted
  have incrementalAccepted : IncrementalUpdateAccepted update :=
    ⟨incremental, accepted⟩
  have referenceAccepted :
      ReferenceUpdateAccepted update.toFullReferenceUpdate :=
    (incrementalAndReferenceAcceptance_equivalent update).mp
      incrementalAccepted
  rcases referenceAccepted with ⟨complete, completeAccepted⟩
  have completeCanonical := checkReferenceUpdate_sound
    update.toFullReferenceUpdate complete completeAccepted
  refine ⟨complete, completeAccepted, ?_⟩
  calc
    incremental.checked = publicIncrementalCheckedUpdate.checked :=
      congrArg PublicIncrementalCheckedUpdate.checked incrementalCanonical
    _ = publicIncrementalCoreCheckedUpdate :=
      publicIncrementalCheckedUpdate.checkedExact
    _ = publicReferenceCheckedUpdate :=
      publicIncrementalCoreCheckedUpdate_eq_reference
    _ = complete := completeCanonical.symm

def eraseIncrementalCheckResult :
    Except AlignmentError PublicIncrementalCheckedUpdate ->
      Except AlignmentError
        (CheckedUpdate publicInitialCheckedAgent .reconfigured)
  | .error problem => .error problem
  | .ok checked => .ok checked.checked

/-- On the closed reference delta the two executable checkers return exactly
the same checked update, not merely the same Boolean verdict. -/
theorem publicIncrementalAndReferenceChecks_exact :
    eraseIncrementalCheckResult
        (checkIncrementalUpdate publicIncrementalNeuralUpdate) =
      checkReferenceUpdate publicFullReferenceNeuralUpdate := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalUpdateAccepted
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalUpdateLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.incrementalAndReferenceLocalConditions_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.incrementalAndReferenceAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalCoreCheckedUpdate_eq_reference
#print axioms ConstitutiveSearch.NeuralAgent.incrementalSuccess_matches_reference
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalAndReferenceChecks_exact
/- AXIOM_AUDIT_END -/
