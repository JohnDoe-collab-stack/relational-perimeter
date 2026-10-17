import RelationalPerimeter.Instances.HeytingArithmetic.RealCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Tests.RuntimeRealCorrespondence

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime
open RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence

def zeroCode : SignedDyadicCode :=
  { positive := 0, negative := 0, scale := 0 }

/-- A closed executable presentation used to exercise the whole correspondence. -/
def zeroPresentation : EffectiveDyadicPresentation where
  approximation := fun _precision => zeroCode
  coherent := fun precision _left _right _leftBeyond _rightBeyond =>
    Near.refl precision zeroCode

def zeroRuntime : RuntimeReal heytingArithmeticGodelPresentation 1 :=
  heytingArithmeticPresentationRuntime zeroPresentation

def zeroResult :=
  heytingArithmeticPresentationCorrespondence zeroPresentation

theorem zeroReadoutRoundtripExact (precision : Nat) :
    (runtimeToPresentation zeroRuntime).approximation precision =
      zeroPresentation.approximation precision :=
  presentation_roundtrip_readout_exact
    heytingArithmeticGodelPresentation 1 precision zeroPresentation

/-- Every exposed readout still carries the exact executed step that produced it. -/
def zeroReadoutOrigin (precision : Nat) :
    RuntimeReal.ReadoutOrigin zeroRuntime precision :=
  zeroResult.readoutOrigin precision

theorem zeroGodelFirstStepUsesRuntime :
    HEq zeroResult.godel.firstStep (zeroRuntime.stepAt 0) :=
  zeroResult.godelFirstStepIsRuntimeStep

def zeroRoundtripRuntime : RuntimeReal heytingArithmeticGodelPresentation 1 :=
  presentationToRuntime heytingArithmeticGodelPresentation 1
    (runtimeToPresentation zeroRuntime)

def zeroRoundtripFuture : LimitFutureEquivalent zeroRoundtripRuntime zeroRuntime :=
  zeroResult.roundtripFutures

/-- Numerical equality is recovered from singleton futures, not stored in them. -/
def zeroRoundtripReadoutsFromFutures :
    RuntimeReadoutEquivalent zeroRoundtripRuntime zeroRuntime :=
  zeroRoundtripFuture.toReadouts

def zeroConstantEquivalent :
    EffectiveDyadicPresentation.Equivalent
      (EffectiveDyadicPresentation.constant zeroCode)
      (EffectiveDyadicPresentation.constant zeroCode) :=
  EffectiveDyadicPresentation.constantEquivalent (SameValue.refl zeroCode)

def oneLimitQuery :
    LimitQuery zeroRoundtripFuture.responseThreshold :=
  { accuracy := 3
    leftResponse := zeroRoundtripFuture.responseThreshold 3
    rightResponse := zeroRoundtripFuture.responseThreshold 3
    leftBeyond := PrecisionExtension.refl _
    rightBeyond := PrecisionExtension.refl _ }

def oneLimitFutureTrace :
    PairedLimitTrace zeroRoundtripRuntime zeroRuntime
      zeroRoundtripFuture.responseThreshold
      (queries := [oneLimitQuery])
      (run zeroRoundtripRuntime.family zeroRoundtripRuntime.initial
        (leftLimitRequests zeroRoundtripRuntime.family [oneLimitQuery])).traceEvidence
      (run zeroRuntime.family zeroRuntime.initial
        (rightLimitRequests zeroRuntime.family [oneLimitQuery])).traceEvidence :=
  zeroRoundtripFuture.traces [oneLimitQuery]

theorem oneLimitFutureTerminalDepthExact :
    (run zeroRoundtripRuntime.family zeroRoundtripRuntime.initial
      (leftLimitRequests zeroRoundtripRuntime.family
        [oneLimitQuery])).finalState.journal.absoluteDepth =
    (run zeroRuntime.family zeroRuntime.initial
      (rightLimitRequests zeroRuntime.family
        [oneLimitQuery])).finalState.journal.absoluteDepth :=
  oneLimitFutureTrace.terminalDepthExact

def zeroCarrier : EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation zeroPresentation

def zeroCarrierResult :=
  heytingArithmeticEffectiveCauchyCorrespondence zeroCarrier

def zeroCarrierRoundtrip : EffectiveCauchyReal.Equivalent
    (EffectiveCauchyReal.fromRuntime
      (heytingArithmeticEffectiveCauchyRuntime zeroCarrier))
    zeroCarrier :=
  zeroCarrierResult.externalCorrespondence

/-- The same concrete result retains the Gödel rejection branch. -/
def rejectZeroRuntimeTotalLoop
    (loop : ExecutedGodelTotalLoop
      heytingArithmeticGodelExecution.witness) : Empty :=
  zeroResult.godel.totalLoopRejected loop

end RelationalPerimeter.Tests.RuntimeRealCorrespondence

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroPresentation
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroRuntime
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroResult
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroReadoutRoundtripExact
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroReadoutOrigin
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroGodelFirstStepUsesRuntime
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroRoundtripFuture
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroRoundtripReadoutsFromFutures
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroConstantEquivalent
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.oneLimitFutureTrace
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.oneLimitFutureTerminalDepthExact
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroCarrier
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroCarrierResult
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.zeroCarrierRoundtrip
#print axioms RelationalPerimeter.Tests.RuntimeRealCorrespondence.rejectZeroRuntimeTotalLoop
/- AXIOM_AUDIT_END -/
