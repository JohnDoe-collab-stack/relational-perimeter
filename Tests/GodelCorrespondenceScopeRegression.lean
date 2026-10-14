import RelationalPerimeter.Constitution.ArithmeticGodelCorrespondence

/-!
# Scope regression for the abstract Gödel adapter

This test deliberately preserves the smallest countermodel accepted by
`EffectivelyPresentedSoundGodelSystem`.  Its purpose is to prevent that
abstract compatibility interface from being cited as a realization of a
non-trivial arithmetic theory.  The stronger public arithmetic entry point is
`SemanticallyDefinedProofArithmeticTheory`, whose substitution and proof
relation laws are not fields of this countermodel.
-/

namespace RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression

open StrongPerimetralTurning

def abstractDegenerateSystem : EffectivelyPresentedSoundGodelSystem :=
  { UnaryFormula := Unit
    Sentence := Unit
    encodeUnary := fun _ => 0
    decodeUnary := fun _ => some ()
    decodeUnary_encode := fun _ => rfl
    encodeSentence := fun _ => 0
    decodeSentence := fun _ => some ()
    decodeSentence_encode := fun _ => rfl
    substitute := fun _ _ => ()
    diagonalize := fun _ => ()
    proofCheck := fun _ _ => false
    equivalenceCheck := fun _ _ _ => true
    diagonalizeExact := fun _ _ => ⟨0, ⟨rfl⟩⟩
    proofForward := fun _ proof => nomatch proof.2.down
    proofBackward := fun _ proof => nomatch proof.2.down
    Truth := fun _ => Unit
    proofSound := fun proof => nomatch proof.2.down
    equivalenceTruthForward := fun _ truth => truth
    equivalenceTruthBackward := fun _ truth => truth
    unprovabilityFormula := ()
    representsUnprovabilityForward :=
      fun _ _ proof => nomatch proof.2.down
    representsUnprovabilityBackward := fun _ _ => () }

def abstractDegenerateCorrespondence :
    EffectiveGodelPerimetralCorrespondence abstractDegenerateSystem :=
  effectiveGodelPerimetralCorrespondence abstractDegenerateSystem

theorem abstractInterfaceDoesNotImplyAnyProofExists
    (sentence : Unit) :
    CheckedSentenceProof abstractDegenerateSystem.encodeSentence
      abstractDegenerateSystem.proofCheck sentence → False :=
  fun proof => nomatch proof.2.down

theorem abstractDegenerateHistoryStillPinsItsExactExit :
    abstractDegenerateCorrespondence.execution.exit =
      arithmeticCanonicalExecutedGodelRegimeExit
        abstractDegenerateSystem.toGodelSyntax
        abstractDegenerateSystem.unprovabilityFormula
        abstractDegenerateSystem.toGodelInterpretation :=
  abstractDegenerateCorrespondence.execution.arithmeticHistoryPinsExit

end RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateSystem
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateCorrespondence
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractInterfaceDoesNotImplyAnyProofExists
#print axioms RelationalPerimeter.Tests.GodelCorrespondenceScopeRegression.abstractDegenerateHistoryStillPinsItsExactExit
/- AXIOM_AUDIT_END -/
