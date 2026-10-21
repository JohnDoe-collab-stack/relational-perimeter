import RelationalPerimeter.Agents.Neural.CheckedState

/-!
# Executable initial and full-reference update checkers

The initial checker decodes the complete received network before accepting the
closed initial certificate.  The full-reference update checker likewise
decodes the complete successor network, checks the exact next requirement,
and returns the `CheckedUpdate` whose successor certificate consumes the
executed reconfiguration.  Neither serialized input contains a proof or a
certificate.

This is deliberately the full reference checker.  Stable cross-version node
identifiers, affected-cone computation, and incremental certificate reuse are
later layers and are not simulated here.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

inductive AlignmentError where
  | malformedArtifact (problem : ArtifactError)
  | unexpectedInitialArtifact
  | unexpectedSuccessorArtifact
  | successorMismatch
  | noAdmittedTransition
  deriving DecidableEq

/-- The serialized update contains only the complete proposed successor and
the next received requirement.  It cannot carry its own certificate. -/
structure FullReferenceNeuralUpdate where
  targetArtifact : SerializedNetwork
  nextInput : PublicRequirementInput

def publicFullReferenceNeuralUpdate : FullReferenceNeuralUpdate :=
  { targetArtifact := publicSerializedReconfiguredNetwork
    nextInput := publicSubstantiveNext }

/-- Executable initial verification for the closed reference contract.  A
well-formed but different artifact is not silently assigned the reference
certificate. -/
def checkInitial (source : SerializedNetwork) :
    Except AlignmentError
      (CheckedAgent publicConstitutiveMetaContract .initial) :=
  match decodeArtifact PublicInitialOperationalContract source with
  | .error problem => .error (.malformedArtifact problem)
  | .ok _decoded =>
      if _exact : source = publicSerializedRequirementNetwork then
        .ok publicInitialCheckedAgent
      else
        .error .unexpectedInitialArtifact

/-- The successor checked agent consumes the complete target artifact, the
exact executed target state, and its state-indexed constitutive certificate. -/
def publicReferenceNextCheckedAgent :
    CheckedAgent publicConstitutiveMetaContract .reconfigured :=
  certifyCheckedAgent PublicContractAdmission.reconfigured
    publicDecodedReconfiguredArtifact publicReferenceUpdatedState
    publicReferenceUpdatedStateCertificate

def publicReferenceCheckedUpdate :
    CheckedUpdate publicInitialCheckedAgent .reconfigured :=
  certifyCheckedUpdate publicReferenceNextCheckedAgent
    publicOperationalTransition
    (PublicExecutedContractStateTransition.execute publicInitialCertifiedState
      publicSubstantiveNext)

/-- Full verification of the reference update.  The complete target program
is decoded again; only then are its exact artifact and successor input matched
to the state certificate produced by the executed reconfiguration. -/
def checkReferenceUpdate (update : FullReferenceNeuralUpdate) :
    Except AlignmentError
      (CheckedUpdate publicInitialCheckedAgent .reconfigured) :=
  match decodeArtifact PublicReconfiguredOperationalContract
      update.targetArtifact with
  | .error problem => .error (.malformedArtifact problem)
  | .ok _decoded =>
      if _artifactExact :
          update.targetArtifact = publicSerializedReconfiguredNetwork then
        match publicRequirementInputEquality update.nextInput
            publicSubstantiveNext with
        | .isTrue _nextExact => .ok publicReferenceCheckedUpdate
        | .isFalse _ => .error .successorMismatch
      else
        .error .unexpectedSuccessorArtifact

theorem checkInitial_accepts_reference :
    checkInitial publicSerializedRequirementNetwork =
      .ok publicInitialCheckedAgent := by
  rfl

theorem checkInitial_rejects_malformed :
    checkInitial mismatchedInputCountNetwork =
      .error (.malformedArtifact .inputCountMismatch) := by
  rfl

theorem checkReferenceUpdate_accepts_reference :
    checkReferenceUpdate publicFullReferenceNeuralUpdate =
      .ok publicReferenceCheckedUpdate := by
  rfl

def publicWrongSuccessorReferenceUpdate : FullReferenceNeuralUpdate :=
  { targetArtifact := publicSerializedReconfiguredNetwork
    nextInput := publicSubstantiveContextualNext }

theorem checkReferenceUpdate_rejects_wrong_successor :
    checkReferenceUpdate publicWrongSuccessorReferenceUpdate =
      .error .successorMismatch := by
  rfl

/-- Any successful initial check returns the exact closed checked agent; no
independently reconstructed certificate can appear in the result. -/
theorem checkInitial_sound
    (source : SerializedNetwork)
    (checked : CheckedAgent publicConstitutiveMetaContract .initial)
    (accepted : checkInitial source = .ok checked) :
    checked = publicInitialCheckedAgent := by
  unfold checkInitial at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
      rfl
    · cases accepted

/-- Any successful full-reference update check returns the precise update
whose transition and successor are consumed by execution. -/
theorem checkReferenceUpdate_sound
    (update : FullReferenceNeuralUpdate)
    (checked : CheckedUpdate publicInitialCheckedAgent .reconfigured)
    (accepted : checkReferenceUpdate update = .ok checked) :
    checked = publicReferenceCheckedUpdate := by
  unfold checkReferenceUpdate at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · split at accepted
      · cases accepted
        rfl
      · cases accepted
    · cases accepted

def ReferenceUpdateAccepted (update : FullReferenceNeuralUpdate) : Prop :=
  Exists fun checked => checkReferenceUpdate update = .ok checked

def ReferenceUpdateLocalConditions
    (update : FullReferenceNeuralUpdate) : Prop :=
  update.targetArtifact = publicSerializedReconfiguredNetwork ∧
    update.nextInput = publicSubstantiveNext

/-- Relative completeness is stated only for the two decidable local
conditions actually implemented by this reference checker. -/
theorem checkReferenceUpdate_complete_for_local_conditions
    (update : FullReferenceNeuralUpdate) :
    ReferenceUpdateAccepted update ↔
      ReferenceUpdateLocalConditions update := by
  constructor
  · intro accepted
    rcases accepted with ⟨checked, exact⟩
    unfold checkReferenceUpdate at exact
    split at exact
    · cases exact
    · split at exact
      · split at exact
        · exact ⟨‹update.targetArtifact =
              publicSerializedReconfiguredNetwork›,
            ‹update.nextInput = publicSubstantiveNext›⟩
        · cases exact
      · cases exact
  · intro conditions
    rcases conditions with ⟨artifactExact, inputExact⟩
    cases update
    cases artifactExact
    cases inputExact
    exact ⟨publicReferenceCheckedUpdate,
      checkReferenceUpdate_accepts_reference⟩

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.AlignmentError
#print axioms ConstitutiveSearch.NeuralAgent.FullReferenceNeuralUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceNextCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.ReferenceUpdateAccepted
#print axioms ConstitutiveSearch.NeuralAgent.ReferenceUpdateLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_complete_for_local_conditions
/- AXIOM_AUDIT_END -/
