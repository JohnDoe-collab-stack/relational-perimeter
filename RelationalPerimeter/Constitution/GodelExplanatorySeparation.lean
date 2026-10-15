import RelationalPerimeter.Constitution.ArithmeticGodelCorrespondence
import RelationalPerimeter.Constitution.HeytingArithmeticGodelInstance
import RelationalPerimeter.Constitution.HeytingArithmetic.InternalNumeralProofs

/-!
# Explanatory separation around the produced Gödel sentence

The produced diagonal sentence blocks directed semantic completeness at that
exact sentence.  This does not make every true sentence proofless.  The
positive boundary below records an independently checked sentence and derives
its truth and sentence-local completeness from the same proof certificate.

The generic comparison keeps the scopes separate: it proves that such an
anchor differs from the produced diagonal sentence, retains the strict
continuation already constructed by the correspondence, and cannot be used to
recover completeness at the produced sentence.  The HA instance realizes the
anchor with the explicit proof of `0 = 0`.
-/

namespace StrongPerimetralTurning

/-- A positive, checked anchor inside an effective Gödel system.  It contains
no negative conclusion and no completeness premise: both the semantic witness
and the local truth-to-proof map are derived from this exact certificate. -/
structure EffectiveGodelSelectiveBoundary
    (system : EffectivelyPresentedSoundGodelSystem) where
  sentence : system.Sentence
  checkedProof :
    CheckedSentenceProof system.encodeSentence system.proofCheck sentence

namespace EffectiveGodelSelectiveBoundary

/-- Soundness consumes the exact checked proof stored by the boundary. -/
def truth
    {system : EffectivelyPresentedSoundGodelSystem}
    (boundary : EffectiveGodelSelectiveBoundary system) :
    system.Truth boundary.sentence :=
  system.proofSound boundary.checkedProof

/-- At the positively checked anchor, directed semantic completeness is
realized by returning the already constructed proof certificate. -/
def anchorCompleteness
    {system : EffectivelyPresentedSoundGodelSystem}
    (boundary : EffectiveGodelSelectiveBoundary system) :
    DirectedSemanticCompletenessAt system.Truth
      (CheckedSentenceProof system.encodeSentence system.proofCheck)
      boundary.sentence :=
  fun _truth => boundary.checkedProof

/-- A checked anchor cannot be the produced Gödel sentence, since transporting
its exact proof along that equality would contradict the produced witness. -/
theorem anchorDiffersFromProduced
    {system : EffectivelyPresentedSoundGodelSystem}
    (boundary : EffectiveGodelSelectiveBoundary system) :
    boundary.sentence ≠
      ((effectiveGodelPerimetralCorrespondence system).execution.exit.witness).production.sentence := by
  intro equality
  let witness :=
    (effectiveGodelPerimetralCorrespondence system).execution.exit.witness
  exact Empty.elim
    (witness.unprovable
      (Eq.mp
        (congrArg (fun sentence => system.toGodelSyntax.Proof sentence) equality)
        boundary.checkedProof))

/-- The full comparison is a derived output, not a premise stored in the
positive boundary. -/
abbrev SelectiveContrast
    {system : EffectivelyPresentedSoundGodelSystem}
    (boundary : EffectiveGodelSelectiveBoundary system) : Type :=
  DirectedSemanticCompletenessAt system.Truth
      (CheckedSentenceProof system.encodeSentence system.proofCheck)
      boundary.sentence ×
    (ExecutedGodelProducedCompleteness
        (effectiveGodelPerimetralCorrespondence system).execution.exit.witness →
      Empty) ×
    PLift (boundary.sentence ≠
      ((effectiveGodelPerimetralCorrespondence system).execution.exit.witness).production.sentence) ×
    StrictConstitutivePrefix
      (perimeterDeployment
        (executedGodelCircularPresentation
          (effectiveGodelPerimetralCorrespondence system).execution.exit.witness))
      (effectiveGodelPerimetralCorrespondence system).execution.exit.continuation

/-- Package the positive anchor, the produced-sentence obstruction, their
separation, and the already constructed strict continuation without changing
any of their scopes. -/
def selectiveContrast
    {system : EffectivelyPresentedSoundGodelSystem}
    (boundary : EffectiveGodelSelectiveBoundary system) :
    SelectiveContrast boundary :=
  ⟨boundary.anchorCompleteness,
    (effectiveGodelPerimetralCorrespondence system).semanticCompletenessAtProducedSentenceIsImpossible,
    ⟨boundary.anchorDiffersFromProduced⟩,
    (effectiveGodelPerimetralCorrespondence system).continuationIsStrict⟩

/-- A construction of positive anchors cannot imply completeness at the
produced Gödel sentence: applying it to this boundary is rejected by the same
produced witness. -/
def notReducibleToProducedCompleteness
    {system : EffectivelyPresentedSoundGodelSystem}
    (boundary : EffectiveGodelSelectiveBoundary system) :
    (EffectiveGodelSelectiveBoundary system →
      ExecutedGodelProducedCompleteness
        (effectiveGodelPerimetralCorrespondence system).execution.exit.witness) →
      Empty :=
  fun reduction =>
    (effectiveGodelPerimetralCorrespondence system).semanticCompletenessAtProducedSentenceIsImpossible
      (reduction boundary)

end EffectiveGodelSelectiveBoundary

/-- Systems whose checker accepts no sentence cannot manufacture the positive
boundary.  This closes the abstract degenerate regression case without adding
a negative field to the boundary itself. -/
def prooflessSystemRejectsSelectiveBoundary
    (system : EffectivelyPresentedSoundGodelSystem)
    (proofless : (sentence : system.Sentence) →
      CheckedSentenceProof system.encodeSentence system.proofCheck sentence →
        Empty) :
    EffectiveGodelSelectiveBoundary system → Empty :=
  fun boundary => proofless boundary.sentence boundary.checkedProof

end StrongPerimetralTurning

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

/-- The closed HA sentence `0 = 0`, used only as a positive explanatory
anchor and not as a replacement for the produced diagonal sentence. -/
def haReflexiveZeroSentence : Sentence :=
  { raw := (numeralEqualityFormula 0 0 0).raw
    isScoped := (numeralEqualityFormula 0 0 0).isScoped }

/-- An explicit checked HA certificate for the anchor `0 = 0`. -/
def heytingArithmeticReflexiveZeroCheckedProof :
    CheckedSentenceProof Sentence.quote haProofCheck haReflexiveZeroSentence :=
  haCheckedProofOfDerivation (numeralEqualityProof 0 0 0 rfl)

/-- The concrete positive selective boundary in named Heyting arithmetic. -/
def heytingArithmeticGodelSelectiveBoundary :
    EffectiveGodelSelectiveBoundary heytingArithmeticEffectiveGodelSystem :=
  { sentence := haReflexiveZeroSentence
    checkedProof := heytingArithmeticReflexiveZeroCheckedProof }

def heytingArithmeticReflexiveZeroTruth :
    haTruth haReflexiveZeroSentence :=
  heytingArithmeticGodelSelectiveBoundary.truth

def heytingArithmeticReflexiveZeroCompleteness :
    DirectedSemanticCompletenessAt haTruth
      (CheckedSentenceProof Sentence.quote haProofCheck)
      haReflexiveZeroSentence :=
  heytingArithmeticGodelSelectiveBoundary.anchorCompleteness

theorem heytingArithmeticReflexiveZeroDiffersFromProduced :
    haReflexiveZeroSentence ≠
      (heytingArithmeticGodelPerimetralCorrespondence.execution.exit.witness).production.sentence :=
  heytingArithmeticGodelSelectiveBoundary.anchorDiffersFromProduced

def heytingArithmeticSelectiveContrast :
    EffectiveGodelSelectiveBoundary.SelectiveContrast
      heytingArithmeticGodelSelectiveBoundary :=
  heytingArithmeticGodelSelectiveBoundary.selectiveContrast

def heytingArithmeticBoundaryDoesNotReduceToProducedCompleteness :
    (EffectiveGodelSelectiveBoundary heytingArithmeticEffectiveGodelSystem →
      ExecutedGodelProducedCompleteness
        heytingArithmeticGodelPerimetralCorrespondence.execution.exit.witness) →
      Empty :=
  heytingArithmeticGodelSelectiveBoundary.notReducibleToProducedCompleteness

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary.truth
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary.anchorCompleteness
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary.anchorDiffersFromProduced
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary.SelectiveContrast
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary.selectiveContrast
#print axioms StrongPerimetralTurning.EffectiveGodelSelectiveBoundary.notReducibleToProducedCompleteness
#print axioms StrongPerimetralTurning.prooflessSystemRejectsSelectiveBoundary
#print axioms RelationalPerimeter.HeytingArithmetic.haReflexiveZeroSentence
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticReflexiveZeroCheckedProof
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelSelectiveBoundary
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticReflexiveZeroTruth
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticReflexiveZeroCompleteness
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticReflexiveZeroDiffersFromProduced
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSelectiveContrast
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticBoundaryDoesNotReduceToProducedCompleteness
/- AXIOM_AUDIT_END -/
