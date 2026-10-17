import RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# External effective Cauchy-real carrier

This quotient-free carrier is independent of runtime histories.  It consists
of an executable signed-dyadic sequence, an explicit monotone modulus, and a
positive Cauchy law.  Correspondence with the authoritative runtime is routed
through `EffectiveDyadicPresentation`; it never reconstructs erased runtime
resources from numerical values.
-/

namespace RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal

open StrongPerimetralTurning
open RuntimeCorrespondence

/-- A constructive Cauchy real with an explicit response modulus. -/
structure Carrier where
  approximation : Nat -> SignedDyadicCode
  modulus : Nat -> Nat
  modulusMonotone :
    {coarse fine : Nat} ->
    PrecisionExtension coarse fine ->
      PrecisionExtension (modulus coarse) (modulus fine)
  cauchy :
    (precision leftResponse rightResponse : Nat) ->
    PrecisionExtension (modulus precision) leftResponse ->
    PrecisionExtension (modulus precision) rightResponse ->
      Near precision
        (approximation leftResponse)
        (approximation rightResponse)

/-- Positive equivalence allows the two carriers to have different moduli. -/
structure Equivalent (first second : Carrier) where
  firstThreshold : Nat -> Nat
  secondThreshold : Nat -> Nat
  near :
    (precision firstResponse secondResponse : Nat) ->
    PrecisionExtension (firstThreshold precision) firstResponse ->
    PrecisionExtension (secondThreshold precision) secondResponse ->
      Near precision
        (first.approximation firstResponse)
        (second.approximation secondResponse)

def Equivalent.refl (real : Carrier) : Equivalent real real where
  firstThreshold := real.modulus
  secondThreshold := real.modulus
  near := real.cauchy

def Equivalent.symm
    {first second : Carrier}
    (equivalent : Equivalent first second) : Equivalent second first where
  firstThreshold := equivalent.secondThreshold
  secondThreshold := equivalent.firstThreshold
  near := fun precision firstResponse secondResponse firstBeyond secondBeyond =>
    (equivalent.near precision secondResponse firstResponse
      secondBeyond firstBeyond).symm

private def firstThresholdExtension (first second : Nat) :
    PrecisionExtension first (first + second) where
  extra := second
  exact := rfl

private def secondThresholdExtension (first second : Nat) :
    PrecisionExtension second (first + second) where
  extra := first
  exact := Nat.add_comm second first

def Equivalent.trans
    {first middle last : Carrier}
    (left : Equivalent first middle)
    (right : Equivalent middle last) : Equivalent first last where
  firstThreshold := fun precision => left.firstThreshold (Nat.succ precision)
  secondThreshold := fun precision => right.secondThreshold (Nat.succ precision)
  near := by
    intro precision firstResponse lastResponse firstBeyond lastBeyond
    let leftMiddle := left.secondThreshold (Nat.succ precision)
    let rightMiddle := right.firstThreshold (Nat.succ precision)
    let leftToCombined := firstThresholdExtension leftMiddle rightMiddle
    let rightToCombined := secondThresholdExtension leftMiddle rightMiddle
    have firstNear := left.near
      (Nat.succ precision) firstResponse (leftMiddle + rightMiddle)
      firstBeyond leftToCombined
    have lastNear := right.near
      (Nat.succ precision) (leftMiddle + rightMiddle) lastResponse
      rightToCombined lastBeyond
    exact Near.compose firstNear lastNear

/-! ## Presentation correspondence -/

/-- Diagonalize the carrier through its explicit modulus. -/
def toPresentation (real : Carrier) : EffectiveDyadicPresentation where
  approximation := fun precision => real.approximation (real.modulus precision)
  coherent := by
    intro coarse leftPrecision rightPrecision leftExtension rightExtension
    exact real.cauchy coarse
      (real.modulus leftPrecision) (real.modulus rightPrecision)
      (real.modulusMonotone leftExtension)
      (real.modulusMonotone rightExtension)

/-- Regard an effective presentation as the canonical identity-modulus carrier. -/
def ofPresentation (presentation : EffectiveDyadicPresentation) : Carrier where
  approximation := presentation.approximation
  modulus := fun precision => precision
  modulusMonotone := fun extension => extension
  cauchy := presentation.coherent

theorem presentation_roundtrip_exact
    (presentation : EffectiveDyadicPresentation)
    (precision : Nat) :
    (toPresentation (ofPresentation presentation)).approximation precision =
      presentation.approximation precision :=
  rfl

def carrier_roundtrip_equivalent (real : Carrier) :
    Equivalent (ofPresentation (toPresentation real)) real where
  firstThreshold := fun precision => precision
  secondThreshold := real.modulus
  near := by
    intro precision firstResponse secondResponse firstBeyond secondBeyond
    exact real.cauchy precision
      (real.modulus firstResponse) secondResponse
      (real.modulusMonotone firstBeyond) secondBeyond

def presentationEquivalentToCarrier
    {first second : EffectiveDyadicPresentation}
    (equivalent : EffectiveDyadicPresentation.Equivalent first second) :
    Equivalent (ofPresentation first) (ofPresentation second) where
  firstThreshold := equivalent.responseThreshold
  secondThreshold := equivalent.responseThreshold
  near := equivalent.near

def carrierEquivalentToPresentation
    {first second : EffectiveDyadicPresentation}
    (equivalent : Equivalent
      (ofPresentation first) (ofPresentation second)) :
    EffectiveDyadicPresentation.Equivalent first second where
  responseThreshold := fun precision =>
    equivalent.firstThreshold precision +
      equivalent.secondThreshold precision
  near := by
    intro precision firstResponse secondResponse firstBeyond secondBeyond
    let firstToCombined := firstThresholdExtension
      (equivalent.firstThreshold precision)
      (equivalent.secondThreshold precision)
    let secondToCombined := secondThresholdExtension
      (equivalent.firstThreshold precision)
      (equivalent.secondThreshold precision)
    exact equivalent.near precision firstResponse secondResponse
      (firstToCombined.trans firstBeyond)
      (secondToCombined.trans secondBeyond)

def presentationCarrierCorrespondence
    (first second : EffectiveDyadicPresentation) :
    (EffectiveDyadicPresentation.Equivalent first second ->
      Equivalent (ofPresentation first) (ofPresentation second)) ×
    (Equivalent (ofPresentation first) (ofPresentation second) ->
      EffectiveDyadicPresentation.Equivalent first second) :=
  ⟨presentationEquivalentToCarrier, carrierEquivalentToPresentation⟩

/-! ## Runtime correspondence -/

def fromRuntime
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth) : Carrier :=
  ofPresentation (runtimeToPresentation real)

def toRuntime
    (P : CircularPresentation)
    (baseDepth : Nat)
    (real : Carrier) : RuntimeReal P baseDepth :=
  presentationToRuntime P baseDepth (toPresentation real)

def runtimeEquivalentToCarrier
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : RuntimeReadoutEquivalent first second) :
    Equivalent (fromRuntime first) (fromRuntime second) :=
  presentationEquivalentToCarrier equivalent.toPresentation

def carrierEquivalentToRuntime
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : Equivalent (fromRuntime first) (fromRuntime second)) :
    RuntimeReadoutEquivalent first second :=
  RuntimeReadoutEquivalent.ofPresentation
    (carrierEquivalentToPresentation equivalent)

/-- Runtime readout equivalence is exactly carrier equivalence after readout. -/
def runtimeCarrierCorrespondence
    {P : CircularPresentation}
    {baseDepth : Nat}
    (first second : RuntimeReal P baseDepth) :
    (RuntimeReadoutEquivalent first second ->
      Equivalent (fromRuntime first) (fromRuntime second)) ×
    (Equivalent (fromRuntime first) (fromRuntime second) ->
      RuntimeReadoutEquivalent first second) :=
  ⟨runtimeEquivalentToCarrier, carrierEquivalentToRuntime⟩

def carrier_runtime_roundtrip_equivalent
    (P : CircularPresentation)
    (baseDepth : Nat)
    (real : Carrier) :
    Equivalent (fromRuntime (toRuntime P baseDepth real)) real :=
  Equivalent.trans
    (presentationEquivalentToCarrier
      (RuntimeCorrespondence.presentation_roundtrip_equivalent
        P baseDepth (toPresentation real)))
    (carrier_roundtrip_equivalent real)

end RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.Carrier
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.Equivalent
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.Equivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.toPresentation
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.ofPresentation
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.presentation_roundtrip_exact
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.carrier_roundtrip_equivalent
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.presentationCarrierCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.fromRuntime
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.toRuntime
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.runtimeCarrierCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.carrier_runtime_roundtrip_equivalent
/- AXIOM_AUDIT_END -/
