import RelationalPerimeter.Constitution.Reals.DyadicCompletionOrderedCharacterization
import Tests.RelationalRealCarrierCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Tests.PresentedDyadicCompletion
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence RelationalRealAddition RelationalRealOrder
open RelationalRealFamilyTransport RelationalRealCarrierCompleteness
open RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion
open CarrierOrderedField DyadicCompletionCharacterization
open RelationalRealCarrierCompleteness

def ownShifted := ownFamily carrierPresentedCore (decayTerm 1)
theorem ownTermExact (n : Nat) : ownShifted.terms n = dyadicCarrier ((decayTerm 1).approximation n) := rfl
theorem ownModuleExact (p : Nat) : ownShifted.modulus p = p + 2 := rfl
def selfShifted := selfConvergence carrierPresentedCore (decayTerm 1)
theorem addSchedule (n : Nat) :
    ((canonicalAdditiveFamily carrierPresentedCore (decayTerm 1) secondZero).terms n).approximation 0 =
      (((decayTerm 1).approximation ((decayTerm 1).modulus (n + 1))).add
        (secondZero.approximation (secondZero.modulus (n + 1)))).raise 0 := rfl
theorem negSchedule (n : Nat) :
    ((canonicalNegativeFamily carrierPresentedCore (decayTerm 1)).terms n).approximation 0 =
      (((decayTerm 1).approximation ((decayTerm 1).modulus n)).neg).raise 0 := rfl
theorem mulSchedule (n : Nat) :
    ((canonicalMultiplicativeFamily carrierPresentedCore (decayTerm 1) secondZero).terms n).approximation 0 =
      (((decayTerm 1).approximation ((decayTerm 1).modulus (n + 1 + 3))).mul
        (secondZero.approximation (secondZero.modulus (n + 1 + 5)))).raise 0 := rfl
theorem canonicalModules (p : Nat) :
    (canonicalAdditiveFamily carrierPresentedCore (decayTerm 1) secondZero).modulus p = p ∧
    (canonicalNegativeFamily carrierPresentedCore (decayTerm 1)).modulus p = p ∧
    (canonicalMultiplicativeFamily carrierPresentedCore (decayTerm 1) secondZero).modulus p = p := ⟨rfl, rfl, rfl⟩
theorem crossedProbes :
    probeAmplitude ((EffectiveCauchyReal.toPresentation (decayTerm 1)).approximation 0) = 5 ∧
    probeAmplitude ((EffectiveCauchyReal.toPresentation secondZero).approximation 0) = 3 := ⟨rfl, rfl⟩
def normalizedTwoLosses (P : CircularPresentation) (d : Nat) := normalizedEquivalentNear (candidateAgreement P d) 2 4 5 (.refl _) ⟨1, rfl⟩
def multiplicationCongruence (P : CircularPresentation) (d : Nat) :=
  mulCarrierCongr (candidateAgreement P d) (candidateAgreement P d).symm
def additiveCanonicalConvergence := carrierAddConvergence firstPerimeter 1 (decayTerm 1) secondZero
def negativeCanonicalConvergence := carrierNegConvergence firstPerimeter 1 (decayTerm 1)
def multiplicativeCanonicalConvergence := carrierMulConvergence firstPerimeter 1 (decayTerm 1) secondZero
def diagonalFamily := diagonalTransportFamily carrierPresentedCore carrierPresentedCore
  ⟨decayFamily.terms, decayFamily.modulus, decayFamily.modulusMonotone, decayFamily.cauchy⟩
theorem diagonalOuter (p : Nat) : diagonalFamily.modulus p = (p + 1) + (p + 2) := rfl
theorem diagonalTerm (n : Nat) : diagonalFamily.terms n = dyadicCarrier
    ((decayFamily.terms n).approximation ((decayFamily.terms n).modulus n)) := rfl

/-- A distinct presented carrier keeps an extra tag; equivalence ignores it.
Its completion is still produced by the actual native carrier completion. -/
def taggedCore : PresentedDyadicStructure where
  Carrier := Bool × EffectiveCauchyReal.Carrier
  approximation x := x.2.approximation
  modulus x := x.2.modulus
  modulusMonotone x := x.2.modulusMonotone
  coherent x := x.2.cauchy
  dyadic code := ⟨false, dyadicCarrier code⟩
  dyadicExact := EffectiveDyadicPresentation.constantApproximationSameValue
  Equivalent x y := EffectiveCauchyReal.Equivalent x.2 y.2
  equivalentRefl x := .refl x.2
  equivalentSymm := EffectiveCauchyReal.Equivalent.symm
  equivalentTrans := EffectiveCauchyReal.Equivalent.trans
  toApprox same := ⟨same.firstThreshold, same.secondThreshold, same.near⟩
  fromApprox same := ⟨same.firstThreshold, same.secondThreshold, same.near⟩
def taggedCompletion (P : CircularPresentation) (d : Nat) :
    RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicCompletion taggedCore where
  complete family :=
    let produced := carrierCompletion P d
      ⟨fun n => (family.terms n).2, family.modulus, family.modulusMonotone, family.cauchy⟩
    { value := ⟨true, produced.limit⟩
      convergence := ⟨produced.convergence.threshold, produced.convergence.converges⟩
      unique := fun other convergence => produced.uniqueness other.2 ⟨convergence.threshold, convergence.near⟩ }
def taggedTarget (P : CircularPresentation) (d : Nat) : PresentedDyadicCompletionObject := ⟨taggedCore, taggedCompletion P d⟩
theorem producedTag (x : EffectiveCauchyReal.Carrier) : (toTarget (taggedTarget firstPerimeter 1) x).1 = true := rfl
def taggedCarrierReturn (x : EffectiveCauchyReal.Carrier) := fromToTarget (taggedTarget firstPerimeter 1) x
def taggedTargetReturn (x : taggedCore.Carrier) := toFromTarget (taggedTarget firstPerimeter 1) x
def noTagIdentity (same : toTarget (taggedTarget firstPerimeter 1)
    (fromTarget taggedCore ⟨false, firstZero⟩) = (⟨false, firstZero⟩ : taggedCore.Carrier)) : Empty := by
  have tags := congrArg Prod.fst same
  change true = false at tags
  cases tags
def taggedForward := comparisonMorphism (carrierCompletionObject firstPerimeter 1) (taggedTarget secondPerimeter 4)
def taggedBackward := reverseMorphism (taggedTarget secondPerimeter 4) firstPerimeter 1
def taggedUnique := comparisonUnique taggedForward
def taggedDyadic := taggedForward.mapDyadic SignedDyadicCode.one
def transportedFamilyLimit := mapProducedLimit taggedForward
  ⟨decayFamily.terms, decayFamily.modulus, decayFamily.modulusMonotone, decayFamily.cauchy⟩

def orderedSource := carrierOrderedCompletion firstPerimeter 1
def orderedTarget := carrierOrderedCompletion secondPerimeter 4
def terminal := relativeOrderedCharacterization firstPerimeter 1 orderedTarget
def additiveTransport := terminal.forwardTransports.add (decayTerm 1) secondZero
def negativeTransport := terminal.forwardTransports.neg (decayTerm 1)
def multiplicativeTransport := terminal.forwardTransports.mul (decayTerm 1) secondZero
def unitOrder := (carrierOrderedData firstPerimeter 1).orderedLaws.unitPositive
def unitDomain : CanonicalCarrierDomain canonicalOneCarrier := .inr unitOrder
def inverseTransport := terminal.forwardTransports.inverse canonicalOneCarrier unitDomain
def densityProduced := produceCarrierDensity firstPerimeter 1 unitOrder
def boundsProduced := produceCarrierNaturalBounds firstPerimeter 1 (decayTerm 1)
def densityTransport := terminal.forwardTransports.density ⟨densityProduced.code, densityProduced.left, densityProduced.right⟩
def boundsTransport := terminal.forwardTransports.bounds
  ⟨boundsProduced.lower, boundsProduced.upper, boundsProduced.lowerOrder, boundsProduced.upperOrder⟩
def completionIndependence := carrierOrderedCompletionIndependent firstPerimeter secondPerimeter 1 4
def terminalProducedLimit := terminal.forwardLimit
  ⟨decayFamily.terms, decayFamily.modulus, decayFamily.modulusMonotone, decayFamily.cauchy⟩

end RelationalPerimeter.Tests.PresentedDyadicCompletion

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.ownShifted
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.ownTermExact
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.ownModuleExact
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.selfShifted
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.addSchedule
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.negSchedule
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.mulSchedule
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.canonicalModules
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.crossedProbes
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.normalizedTwoLosses
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.multiplicationCongruence
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.additiveCanonicalConvergence
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.negativeCanonicalConvergence
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.multiplicativeCanonicalConvergence
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.diagonalFamily
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.diagonalOuter
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.diagonalTerm
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedCore
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedCompletion
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedTarget
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.producedTag
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedCarrierReturn
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedTargetReturn
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.noTagIdentity
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedForward
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedBackward
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedUnique
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.taggedDyadic
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.transportedFamilyLimit
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.orderedSource
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.orderedTarget
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.terminal
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.additiveTransport
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.negativeTransport
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.multiplicativeTransport
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.unitOrder
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.unitDomain
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.inverseTransport
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.densityProduced
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.boundsProduced
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.densityTransport
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.boundsTransport
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.completionIndependence
#print axioms RelationalPerimeter.Tests.PresentedDyadicCompletion.terminalProducedLimit
/- AXIOM_AUDIT_END -/
