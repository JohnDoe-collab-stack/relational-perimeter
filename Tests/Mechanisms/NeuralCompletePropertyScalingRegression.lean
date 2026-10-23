import RelationalPerimeter.Agents.Neural.CompletePropertyScalingMeasurement

namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism

def regressionScalingState := scalingState 2 .local

def regressionScalingCertificate := scalingStateCertificate 2 .local

example : Nonempty (ScalingRequirementEncodingWitness regressionScalingState) :=
  ⟨regressionScalingCertificate.requirementEncodingWitness⟩

example : Nonempty (ScalingExecutedCausalWitness regressionScalingState) :=
  ⟨regressionScalingCertificate.causalConditionWitness⟩

example : Nonempty (ScalingActionWitness regressionScalingState) :=
  ⟨regressionScalingCertificate.proposalActionWitness⟩

example : Nonempty (ScalingAuthorizationWitness regressionScalingState) :=
  ⟨regressionScalingCertificate.authorizationWitness⟩

example : Nonempty (ScalingEffectWitness regressionScalingState) :=
  ⟨regressionScalingCertificate.effectWitness⟩

example : Nonempty (ScalingHistoricalWitness regressionScalingState) :=
  ⟨regressionScalingCertificate.historicalWitness⟩

example :
    (regressionScalingCertificate.coveredFutureWitness
      (scalingFutureRequests 3)).events.length = 3 := by
  rfl

example : scalingSemanticCertificateChecksum regressionScalingCertificate 3 = 19 := by
  rfl

example :
    ((scalingSystem 2 .local).run scalingInput).activations.read
      (scalingLastNeuron 2) = 0 :=
  scalingLastOutput_original 2 .local

example :
    (executeIntervened (scalingIntervention 2 .local)).read
      (scalingLastNeuron 2) = 1 :=
  scalingLastOutput_intervened 2 .local

example
    (inputs : SizedActivations 1)
    (prior : SizedActivations 3)
    (inputExact : inputs.read publicRequirementPort = 3)
    (priorExact : prior.read (Fin.last 2) = 0) :
    fireNeuron (scalingFinalNeuron 2 .local) inputs prior = 0 :=
  scalingFinalWithoutPrior_zero 2 .local inputs prior inputExact priorExact

example : (scalingFutureRequests 5).length = 5 :=
  scalingFutureRequests_length 5

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.regressionScalingState
#print axioms ConstitutiveSearch.NeuralAgent.Tests.regressionScalingCertificate
#print axioms ConstitutiveSearch.NeuralAgent.scalingSemanticCertificateChecksum
#print axioms ConstitutiveSearch.NeuralAgent.scalingCompleteCost
/- AXIOM_AUDIT_END -/
