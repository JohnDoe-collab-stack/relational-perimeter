import RelationalPerimeter.Agents.Neural.ReferenceChecker

namespace ConstitutiveSearch.NeuralAgent

example : checkPublicInitial publicSerializedInitialConstitutiveArtifact =
    .ok publicInitialCheckSuccess :=
  checkInitial_accepts_reference

example : checkPublicInitial publicMalformedInitialConstitutiveArtifact =
    .error (.artifact (.malformed (.network .inputCountMismatch))) :=
  checkInitial_rejects_malformed

example : checkPublicInitial publicSerializedReconfiguredConstitutiveArtifact =
    .ok publicReconfiguredCheckSuccess :=
  checkInitial_accepts_reconfigured_reference

example : publicInitialCheckSuccess.checkedAgent =
    publicInitialCheckedAgent :=
  publicInitialCheckSuccess_checkedAgent_exact

example : publicReconfiguredCheckSuccess.checkedAgent =
    publicReferenceNextCheckedAgent :=
  publicReconfiguredCheckSuccess_checkedAgent_exact

def locallyUnsupportedInitialArtifact : SerializedConstitutiveArtifact :=
  { publicSerializedInitialConstitutiveArtifact with
    stableNaming :=
      { inputKeys := [11]
        neuronKeys := [12]
        outputKeys := [13] } }

example : checkPublicInitial locallyUnsupportedInitialArtifact =
    .error (.artifact .locallyUnsupported) := by
  rfl

def basisRejectingInterface :
    ExecutableMetaContractInterface publicConstitutiveMetaContract :=
  { publicExecutableMetaContractInterface with
    basisDecision := fun _ => reflectedFalse }

example : checkInitial basisRejectingInterface
      publicSerializedInitialConstitutiveArtifact =
    .error (.state .causalBasis) := by
  rfl

example : checkReferenceUpdate publicFullReferenceNeuralUpdate =
    .ok publicReferenceCheckedUpdate :=
  checkReferenceUpdate_accepts_reference

example : checkReferenceUpdate publicWrongSuccessorReferenceUpdate =
    .error .successorMismatch :=
  checkReferenceUpdate_rejects_wrong_successor

example : ReferenceUpdateAccepted publicFullReferenceNeuralUpdate :=
  (checkReferenceUpdate_complete_for_local_conditions
    publicFullReferenceNeuralUpdate).2 ⟨rfl, rfl, rfl⟩

example :
    (publicFullyRecheckedCertificate
      (publicExecutableStateAcceptance .reconfigured)).fragments =
      PublicExecutableDecodedArtifact.reconfigured.recomputedFragments :=
  publicFullyRecheckedCertificate_fragments_exact _

example : publicReferenceCheckedUpdate.next.state =
    publicReferenceUpdatedState := rfl

example : publicReferenceCheckedUpdate.next.certificate =
    publicReferenceUpdatedStateCertificate := rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.publicExecutableMetaContractInterface
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedCertificate_fragments_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckSuccess_checkedAgent_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCheckedUpdate
/- AXIOM_AUDIT_END -/
