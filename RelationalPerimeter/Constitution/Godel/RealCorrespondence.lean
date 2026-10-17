import RelationalPerimeter.Constitution.Godel.RelationalCompleteness
import RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gödel perimeter and effective-real correspondence

The same executed Gödel production fixes the presentation and the historical
base of the runtime realization.  A received effective presentation, or an
external effective Cauchy carrier, is realized on that exact perimeter.  The
positive runtime, numerical correspondence, retained finite-limit futures,
and the two Gödel rejections are packaged without deriving numerical values
from the Gödel contradiction.
-/

namespace StrongPerimetralTurning.GodelRealCorrespondence

open GodelRelationalCompleteness
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence

def presentationToGodelRuntime
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (presentation : EffectiveDyadicPresentation) :
    RuntimeReal (godelPerimetralPresentation execution) 1 :=
  presentationToRuntime (godelPerimetralPresentation execution) 1 presentation

def carrierToGodelRuntime
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (real : EffectiveCauchyReal.Carrier) :
    RuntimeReal (godelPerimetralPresentation execution) 1 :=
  presentationToGodelRuntime execution (EffectiveCauchyReal.toPresentation real)

/-- Complete realization of one received numerical presentation at Gödel `H1`. -/
structure PresentationResult
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (presentation : EffectiveDyadicPresentation) where
  godel : GodelRelationalCompleteness.Result execution
    (presentationToGodelRuntime execution presentation).family
  godelExact : godel = GodelRelationalCompleteness.raccord execution
    (presentationToGodelRuntime execution presentation).family
  godelInitialIsRuntimeInitial : godel.initial =
    (presentationToGodelRuntime execution presentation).initial
  godelProducedRealIsRuntimeProduced : godel.producedReal =
    (presentationToGodelRuntime execution presentation).produced
  godelFirstStepIsRuntimeStep : HEq godel.firstStep
    ((presentationToGodelRuntime execution presentation).stepAt 0)
  readoutCorrespondence : EffectiveDyadicPresentation.Equivalent
    (runtimeToPresentation
      (presentationToGodelRuntime execution presentation))
    presentation
  roundtripFutures : LimitFutureEquivalent
    (presentationToRuntime (godelPerimetralPresentation execution) 1
      (runtimeToPresentation
        (presentationToGodelRuntime execution presentation)))
    (presentationToGodelRuntime execution presentation)
  externalCorrespondence : EffectiveCauchyReal.Equivalent
    (EffectiveCauchyReal.fromRuntime
      (presentationToGodelRuntime execution presentation))
    (EffectiveCauchyReal.ofPresentation presentation)
  readoutOrigin : (precision : Nat) ->
    RuntimeReal.ReadoutOrigin
      (presentationToGodelRuntime execution presentation) precision

def realizePresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (presentation : EffectiveDyadicPresentation) :
    PresentationResult execution presentation := by
  let runtime := presentationToGodelRuntime execution presentation
  let godel := GodelRelationalCompleteness.raccord execution runtime.family
  let readoutCorrespondence := presentation_roundtrip_equivalent
    (godelPerimetralPresentation execution) 1 presentation
  have godelInitialIsRuntimeInitial : godel.initial = runtime.initial :=
    godel.initialExact
  have godelProducedRealIsRuntimeProduced :
      godel.producedReal = runtime.produced :=
    godel.producedRealExact.trans runtime.producedExact.symm
  have godelFirstStepIsRuntimeStep :
      HEq godel.firstStep (runtime.stepAt 0) := by
    cases godelInitialIsRuntimeInitial
    exact heq_of_eq
      ((godel.firstStepExact.trans
        (godel.producedRealRuntimeExact
          runtime.initial godel.initialReachable 0)).trans
        (runtime.stepAt_is_perform 0).symm)
  exact
  { godel := godel
    godelExact := rfl
    godelInitialIsRuntimeInitial := godelInitialIsRuntimeInitial
    godelProducedRealIsRuntimeProduced := godelProducedRealIsRuntimeProduced
    godelFirstStepIsRuntimeStep := godelFirstStepIsRuntimeStep
    readoutCorrespondence := readoutCorrespondence
    roundtripFutures :=
      (runtime_roundtrip_readout_equivalent runtime).toLimitFuture
    externalCorrespondence :=
      EffectiveCauchyReal.presentationEquivalentToCarrier readoutCorrespondence
    readoutOrigin := runtime.readoutOrigin }

/-- Complete realization of one external effective Cauchy real at Gödel `H1`. -/
structure CarrierResult
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (real : EffectiveCauchyReal.Carrier) where
  presentationResult : PresentationResult execution
    (EffectiveCauchyReal.toPresentation real)
  externalCorrespondence : EffectiveCauchyReal.Equivalent
    (EffectiveCauchyReal.fromRuntime (carrierToGodelRuntime execution real)) real

def realizeCarrier
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (real : EffectiveCauchyReal.Carrier) : CarrierResult execution real := by
  let presentationResult :=
    realizePresentation execution (EffectiveCauchyReal.toPresentation real)
  exact
  { presentationResult := presentationResult
    externalCorrespondence := EffectiveCauchyReal.Equivalent.trans
      presentationResult.externalCorrespondence
      (EffectiveCauchyReal.carrier_roundtrip_equivalent real) }

end StrongPerimetralTurning.GodelRealCorrespondence

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelRealCorrespondence.presentationToGodelRuntime
#print axioms StrongPerimetralTurning.GodelRealCorrespondence.carrierToGodelRuntime
#print axioms StrongPerimetralTurning.GodelRealCorrespondence.PresentationResult
#print axioms StrongPerimetralTurning.GodelRealCorrespondence.realizePresentation
#print axioms StrongPerimetralTurning.GodelRealCorrespondence.CarrierResult
#print axioms StrongPerimetralTurning.GodelRealCorrespondence.realizeCarrier
/- AXIOM_AUDIT_END -/
