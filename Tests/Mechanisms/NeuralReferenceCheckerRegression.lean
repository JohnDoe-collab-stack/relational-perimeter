import RelationalPerimeter.Agents.Neural.ReferenceChecker

namespace ConstitutiveSearch.NeuralAgent

example : checkInitial publicSerializedRequirementNetwork =
    .ok publicInitialCheckedAgent :=
  checkInitial_accepts_reference

example : checkInitial mismatchedInputCountNetwork =
    .error (.malformedArtifact .inputCountMismatch) :=
  checkInitial_rejects_malformed

example : checkReferenceUpdate publicFullReferenceNeuralUpdate =
    .ok publicReferenceCheckedUpdate :=
  checkReferenceUpdate_accepts_reference

example : checkReferenceUpdate publicWrongSuccessorReferenceUpdate =
    .error .successorMismatch :=
  checkReferenceUpdate_rejects_wrong_successor

example : ReferenceUpdateAccepted publicFullReferenceNeuralUpdate :=
  (checkReferenceUpdate_complete_for_local_conditions
    publicFullReferenceNeuralUpdate).2 ⟨rfl, rfl⟩

example : publicReferenceCheckedUpdate.next.state =
    publicReferenceUpdatedState := rfl

example : publicReferenceCheckedUpdate.next.certificate =
    publicReferenceUpdatedStateCertificate := rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCheckedUpdate
/- AXIOM_AUDIT_END -/
