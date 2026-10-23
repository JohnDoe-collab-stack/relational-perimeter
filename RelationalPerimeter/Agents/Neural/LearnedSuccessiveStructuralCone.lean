import RelationalPerimeter.Agents.Neural.LearnedSuccessiveAffectedCone

/-!
# Successive learned input and neuron cone equations
-/
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent

theorem learnedSuccessiveInput0_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.receivedInput 0)) = false := by rfl
theorem learnedSuccessiveInput1_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.receivedInput 1)) = false := by rfl
theorem learnedSuccessiveInput2_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.receivedInput 2)) = false := by rfl
theorem learnedSuccessiveNeuron110_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 110)) = false := by rfl
theorem learnedSuccessiveNeuron111_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 111)) = false := by rfl
theorem learnedSuccessiveNeuron112_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 112)) = false := by rfl
theorem learnedSuccessiveNeuron113_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 113)) = false := by rfl
theorem learnedSuccessiveNeuron114_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 114)) = false := by rfl
theorem learnedSuccessiveNeuron115_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 115)) = false := by rfl
theorem learnedSuccessiveNeuron116_unaffected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 116)) = false := by rfl
theorem learnedSuccessiveNeuron117_affected :
    affectedConstitutiveNode LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph
      (.artifactNode (.neuron 117)) = true := by rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveInput0_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveInput1_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveInput2_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron110_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron111_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron112_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron113_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron114_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron115_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron116_unaffected
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveNeuron117_affected
/- AXIOM_AUDIT_END -/
