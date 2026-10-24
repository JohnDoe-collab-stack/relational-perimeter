import RelationalPerimeter.Agents.Neural.LearnedSuccessiveDecodedChecker

/-! # Canonical compatibility entry point for the successive checker -/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

def checkLearnedExtendedSerializedUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError
      (DependentCheckedUpdateResult LearnedAlignedCheckedAgent) :=
  match decodedExact : decodeLearnedSuccessiveUpdate source with
  | .error problem => .error problem
  | .ok decoded =>
      checkDecodedLearnedExtendedSerializedUpdate source decoded decodedExact

/-- Compatibility transport for callers that already possess the exact
canonical predecessor.  The executed dependent runtime does not use this
wrapper: it forwards its received predecessor to the decoded current-aware
checker directly. -/
def checkLearnedExtendedSerializedUpdateAtCurrent
    (current : CheckedAgent learnedConstitutiveMetaContract .aligned)
    (currentExact : current = LearnedAlignedCheckedAgent)
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError (DependentCheckedUpdateResult current) := by
  cases currentExact
  exact checkLearnedExtendedSerializedUpdate source

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedExtendedSerializedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedExtendedSerializedUpdateAtCurrent
/- AXIOM_AUDIT_END -/
