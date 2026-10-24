import RelationalPerimeter.Agents.Neural.LearnedSuccessiveLocalCompleteness

/-!
# Canonical reference member of the learned successive domain

The reference member closes the autonomous local conditions for the admitted
successive serialized update. It is evidence for the domain, not an input to
the current-aware runtime checker.
-/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

def learnedReferenceDecodedSuccessiveUpdate :
    DecodedLearnedSuccessiveUpdate learnedExtendedSerializedUpdate :=
  match exact : decodeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate with
  | .error problem => False.elim (by cases exact)
  | .ok decoded => decoded

theorem decodeLearnedSuccessiveUpdate_reference_exact :
    decodeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate =
      .ok learnedReferenceDecodedSuccessiveUpdate := by
  rfl

def learnedReferenceSuccessiveExecutedDependencies :
    LearnedSuccessiveExecutedDependencies learnedExtendedSerializedUpdate where
  decoded := learnedReferenceDecodedSuccessiveUpdate
  decodedExact := decodeLearnedSuccessiveUpdate_reference_exact
  receivedDecision := learnedExtendedTransitionDecision
  transitionAccepted := by rfl
  authorizationConsumed := by rfl
  targetNetworkExact := by rfl

def learnedReferenceSuccessiveStructuralAssembly :
    CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate
      learnedReferenceSuccessiveExecutedDependencies.preCertificateGraph
      (licensedStructuralEntries
        learnedReferenceSuccessiveExecutedDependencies.transportedLicenses)
      learnedReferenceSuccessiveExecutedDependencies.recomputedStructural := by
  exact learnedSuccessiveCalculatedStructuralAssembly

theorem checkLearnedSuccessiveStructuralAssembly_reference_exact :
    checkLearnedSuccessiveStructuralAssembly
        learnedReferenceSuccessiveExecutedDependencies =
      .ok learnedReferenceSuccessiveStructuralAssembly := by
  exact checkLearnedSuccessiveStructuralAssembly_of_calculated
    learnedReferenceSuccessiveExecutedDependencies
    learnedReferenceSuccessiveStructuralAssembly

def learnedReferenceSuccessiveLocalConditions :
    LearnedSuccessiveLocalConditionData learnedExtendedSerializedUpdate where
  executed := learnedReferenceSuccessiveExecutedDependencies
  structuralAssembly := learnedReferenceSuccessiveStructuralAssembly
  structuralAssemblyChecked :=
    checkLearnedSuccessiveStructuralAssembly_reference_exact

def learnedReferenceSuccessiveAnalysis :
    LearnedSuccessiveEngineAnalysis learnedExtendedSerializedUpdate :=
  learnedSuccessiveAnalysisOfLocalConditions
    learnedReferenceSuccessiveLocalConditions

theorem analyzeLearnedSuccessiveUpdate_reference_exact :
    analyzeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate =
      .ok learnedReferenceSuccessiveAnalysis :=
  analyzeLearnedSuccessiveUpdate_of_local_conditions
    learnedExtendedSerializedUpdate learnedReferenceSuccessiveLocalConditions

theorem learnedReferenceSuccessiveAnalysis_exists :
    Exists fun analysis : LearnedSuccessiveEngineAnalysis
        learnedExtendedSerializedUpdate =>
      analyzeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate =
        .ok analysis :=
  ⟨learnedReferenceSuccessiveAnalysis,
    analyzeLearnedSuccessiveUpdate_reference_exact⟩

def LearnedSuccessiveAnalysisAccepted
    (source : LearnedSerializedConstitutiveUpdate) : Prop :=
  match analyzeLearnedSuccessiveUpdate source with
  | .ok _ => True
  | .error _ => False

theorem learnedReferenceSuccessiveAnalysis_accepted :
    LearnedSuccessiveAnalysisAccepted learnedExtendedSerializedUpdate := by
  unfold LearnedSuccessiveAnalysisAccepted
  rw [analyzeLearnedSuccessiveUpdate_reference_exact]
  trivial

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedReferenceSuccessiveExecutedDependencies
#print axioms ConstitutiveSearch.NeuralAgent.learnedReferenceSuccessiveStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedSuccessiveUpdate_reference_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedReferenceSuccessiveAnalysis_accepted
/- AXIOM_AUDIT_END -/
