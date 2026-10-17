import RelationalPerimeter.Constitution.Reals.RelationalRealInverse
import RelationalPerimeter.Constitution.Reals.RelationalRealMultiplicativeLaws

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Inverse laws consume actual product probes, refinements and the reciprocal
packet owned by the received inverse Step. No numerical inverse is imported. -/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealInverse
open StrongPerimetralTurning HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder
open RelationalRealMultiplication DyadicReciprocal
variable {P : CircularPresentation} {baseDepth : Nat}

/-- Historical unit estimate on one received product Step. The threshold reads
its actual inverse probe; neither source nor reciprocal is re-executed here. -/
def mul_inverse_step {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    {archive : (environment (.mul source (inverse source witness))).Archive} {p response : Nat}
    (step : Step (environment (.mul source (inverse source witness))) archive response)
    (beyond : PrecisionExtension (p + 1 + probeAmplitude step.resource.rightProbe.code) response) :
    Near p step.code SignedDyadicCode.one := by
  dsimp only [environment, inverse, certificate, mulEnvironment, ReciprocalRuntime.inverseEnvironment] at archive step
  let product := step.resource
  let reciprocal := product.right.resource
  let bi := probeAmplitude product.rightProbe.code
  let bs := probeAmplitude product.leftProbe.code
  let j := response + 1 + bs
  let k := ReciprocalDomain.away witness
  have coarseResponse : PrecisionExtension p response :=
    (PrecisionExtension.next p).trans ((PrecisionExtension.first (p + 1) bi).trans beyond)
  have sourceBeyond : PrecisionExtension (p + 1 + bi) (sourcePrecision k j) :=
    beyond.trans ((PrecisionExtension.refine response bs).trans
      ((PrecisionExtension.first j 2).trans (PrecisionExtension.first (j + 2) (k + k))))
  have sourceNear := (coherent source).near (p + 1 + bi) _ _ product.left reciprocal.sourceStep
    (beyond.trans (PrecisionExtension.refine response bi)) sourceBeyond
  have inverseAmplitude : Amplitude bi product.right.code := Amplitude.fromProbe
    ((coherent (inverse source witness)).near 0 _ 0 product.right product.rightProbe
      ⟨_, Nat.zero_add _⟩ (PrecisionExtension.refl 0))
  have sourceAmplitude : Amplitude bs reciprocal.sourceStep.code := Amplitude.fromProbe
    ((coherent source).near 0 _ 0 reciprocal.sourceStep product.leftProbe
      ⟨_, Nat.zero_add _⟩ (PrecisionExtension.refl 0))
  have roundBudget : PrecisionExtension (p + 1 + bs) (roundingPrecision j) :=
    (coarseResponse.succ.add (PrecisionExtension.refl bs)).trans (PrecisionExtension.first j 2)
  have first : Near (p + 1) (product.left.code.mul product.right.code)
      (reciprocal.sourceStep.code.mul reciprocal.result.code) := sourceNear.mulRight inverseAmplitude
  have second := reciprocalUnit reciprocal.nonzero sourceAmplitude reciprocal.result roundBudget
  change Near p product.code SignedDyadicCode.one
  rw [product.readoutExact]
  exact Near.compose first second

def mul_inverse (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    Equivalent (.mul source (inverse source witness)) (one P baseDepth) where
  threshold p := p + 1 + probeAmplitude (readout (inverse source witness) 0)
  near := by
    intro p l r hl hr
    let step := executeReal (.mul source (inverse source witness)) l
    have actualBeyond : PrecisionExtension (p + 1 + probeAmplitude step.resource.rightProbe.code) l := by
      rw [currentReadout (inverse source witness) _ _ step.resource.rightProbe]
      exact hl
    exact Near.ofSameRight (mul_inverse_step step actualBeyond) (constant_readout SignedDyadicCode.one r).symm

def inverse_mul (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    Equivalent (.mul (inverse source witness) source) (one P baseDepth) :=
  (mul_comm _ _).trans (mul_inverse source witness)

def mul_inverse_futures (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    NumericalFutureEquivalent (.mul source (inverse source witness)) (one P baseDepth) :=
  (mul_inverse source witness).toFutures

def inverse_mul_futures (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    NumericalFutureEquivalent (.mul (inverse source witness) source) (one P baseDepth) :=
  (inverse_mul source witness).toFutures

/-- Algebraic uniqueness uses the two executed unit laws, not another division.
No equality of certificates, directions, occurrences or histories is needed. -/
def witness_independent (source : Real P baseDepth)
    (first second : Apartness source (zero P baseDepth)) :
    Equivalent (inverse source first) (inverse source second) :=
  (mul_one _).symm.trans
    ((mul_congr (Equivalent.refl _) (mul_inverse source second).symm).trans
      ((mul_assoc _ _ _).symm.trans
        ((mul_congr (inverse_mul source first) (Equivalent.refl _)).trans (one_mul _))))

def witness_independent_futures (source : Real P baseDepth)
    (first second : Apartness source (zero P baseDepth)) :
    NumericalFutureEquivalent (inverse source first) (inverse source second) :=
  (witness_independent source first second).toFutures

/-- Numerical congruence also follows from the executed units. It does not
transport, identify or reconstruct either witness's historical resources. -/
def inverse_congr {first second : Real P baseDepth} (same : Equivalent first second)
    (fw : Apartness first (zero P baseDepth)) (sw : Apartness second (zero P baseDepth)) :
    Equivalent (inverse first fw) (inverse second sw) :=
  (mul_one _).symm.trans
    ((mul_congr (Equivalent.refl _) (mul_inverse second sw).symm).trans
      ((mul_congr (Equivalent.refl _) (mul_congr same.symm (Equivalent.refl _))).trans
        ((mul_assoc _ _ _).symm.trans
          ((mul_congr (inverse_mul first fw) (Equivalent.refl _)).trans (one_mul _)))))

def inverse_congr_futures {first second : Real P baseDepth} (same : NumericalFutureEquivalent first second)
    (fw : Apartness first (zero P baseDepth)) (sw : Apartness second (zero P baseDepth)) :
    NumericalFutureEquivalent (inverse first fw) (inverse second sw) :=
  (inverse_congr same.toEquivalent fw sw).toFutures

end RelationalPerimeter.Constitution.Reals.RelationalRealInverse

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.mul_inverse_step
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.mul_inverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverse_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.mul_inverse_futures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverse_mul_futures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.witness_independent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.witness_independent_futures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverse_congr
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverse_congr_futures
/- AXIOM_AUDIT_END -/
