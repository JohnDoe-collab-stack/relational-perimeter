import RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Carrier completion produced by the native runtime

The input is one family with both its outer modulus and its terms' own
moduli. The native completeness packet is retained before its limit is read
as a carrier. Numerical transport forgets histories, never recovers them.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness
open StrongPerimetralTurning ProducedCompleteness RuntimeCorrespondence HeterogeneousRealRuntime
open RelationalRealAddition RelationalRealFamilyTransport RelationalRealNativeCauchy

variable {P : CircularPresentation} {baseDepth : Nat}

/-- Current owned replies are transported to the received normalized codes.
Only monotonicity, not cofinality, of each inner modulus is needed. -/
def carrierNativeFamily (P : CircularPresentation) (baseDepth : Nat)
    (family : CarrierFamily) : NativeCauchyFamily P baseDepth :=
  NativeCauchyFamily.ofTerms (fun n => ofCarrier P baseDepth (family.terms n))
    family.modulus family.modulusMonotone (by
      intro p n m r s aa ba first second hn hm hr hs
      have leftExact : first.code = (family.terms n).approximation ((family.terms n).modulus r) := by
        rw [currentReadout _ _ _ first]
        exact ofPresentation_readout _ _
      have rightExact : second.code = (family.terms m).approximation ((family.terms m).modulus s) := by
        rw [currentReadout _ _ _ second]
        exact ofPresentation_readout _ _
      exact alignOwnedNear first.code second.code leftExact.symm rightExact.symm
        (family.cauchy p n m ((family.terms n).modulus r) ((family.terms m).modulus s)
          hn hm ((family.terms n).modulusMonotone hr) ((family.terms m).modulusMonotone hs)))

/-- This is the returned numerical family, not an identity of rich families. -/
def carrierReturnedFamily (P : CircularPresentation) (baseDepth : Nat)
    (family : CarrierFamily) : CarrierFamily :=
  readoutCarrierFamily (realizedFamily (carrierNativeFamily P baseDepth family))

theorem returnedNormalizedTermAt (family : CarrierFamily) (n r : Nat) :
    ((normalizeCarrierFamily (carrierReturnedFamily P baseDepth family)).terms n).approximation r =
      ((normalizeCarrierFamily family).terms n).approximation r := by
  change readout (ofCarrier P baseDepth (family.terms n)) r = _
  exact ofPresentation_readout _ _

def originalCarrierLimitToReturned {family : CarrierFamily} {value : EffectiveCauchyReal.Carrier}
    (convergence : CarrierLimit family value) :
    CarrierLimit (carrierReturnedFamily P baseDepth family) value where
  threshold := convergence.threshold
  converges p n r s hn hr hs :=
    LimitGrouping.transportNear (returnedNormalizedTermAt family n r).symm rfl
      (convergence.converges p n r s hn hr hs)

def returnedCarrierLimitToOriginal {family : CarrierFamily} {value : EffectiveCauchyReal.Carrier}
    (convergence : CarrierLimit (carrierReturnedFamily P baseDepth family) value) :
    CarrierLimit family value where
  threshold := convergence.threshold
  converges p n r s hn hr hs :=
    LimitGrouping.transportNear (returnedNormalizedTermAt family n r) rfl
      (convergence.converges p n r s hn hr hs)

/-- A received limit supplies a candidate only; it never supplies the native
producer's output. Both current Steps are consumed by this law. -/
def carrierLimitNativeCandidate (family : CarrierFamily) (value : EffectiveCauchyReal.Carrier)
    (convergence : CarrierLimit family value) :
    NativeCandidate (carrierNativeFamily P baseDepth family) where
  real := ofCarrier P baseDepth value
  threshold := convergence.threshold
  converges := by
    intro p n r s ta a term candidate hn hr hs
    let returned := originalCarrierLimitToReturned (P := P) (baseDepth := baseDepth) convergence
    have near := returned.converges p n r s hn hr hs
    have leftExact : term.code =
        ((normalizeCarrierFamily (carrierReturnedFamily P baseDepth family)).terms n).approximation r :=
      currentReadout _ _ _ term
    have rightExact : candidate.code = (EffectiveCauchyReal.toPresentation value).approximation s := by
      rw [currentReadout _ _ _ candidate]
      exact ofPresentation_readout _ _
    exact LimitGrouping.transportNear leftExact.symm rightExact.symm near

/-- Retain the whole native packet, then project its produced limit. -/
structure CarrierCompletionResult (P : CircularPresentation) (baseDepth : Nat)
    (family : CarrierFamily) where
  native : NativeCompleteness (carrierNativeFamily P baseDepth family)
  limit : EffectiveCauchyReal.Carrier
  limitExact : limit = toCarrier native.limit
  convergence : CarrierLimit family limit
  uniqueness : (other : EffectiveCauchyReal.Carrier) → CarrierLimit family other →
    EffectiveCauchyReal.Equivalent limit other

def nativeCarrierConvergence (family : CarrierFamily)
    (native : NativeCompleteness (carrierNativeFamily P baseDepth family)) :
    CarrierLimit family (toCarrier native.limit) := by
  let returned := preserveCarrierLimit (asExecutedCandidate native.candidate)
  have projected : CarrierLimit (carrierReturnedFamily P baseDepth family)
      (toCarrier native.limit) := by
    rw [native.candidateExact] at returned
    rw [native.limitExact]
    exact returned
  exact returnedCarrierLimitToOriginal projected

def nativeCarrierUniqueness (family : CarrierFamily)
    (native : NativeCompleteness (carrierNativeFamily P baseDepth family))
    (other : EffectiveCauchyReal.Carrier) (convergence : CarrierLimit family other) :
    EffectiveCauchyReal.Equivalent (toCarrier native.limit) other :=
  let candidate := carrierLimitNativeCandidate family other convergence
  let unique := native.uniqueness candidate
  EffectiveCauchyReal.Equivalent.trans
    ((equivalentCarrier native.limit candidate.real).1 unique.1)
    (carrier_roundtrip other)

def carrierCompletion (P : CircularPresentation) (baseDepth : Nat) (family : CarrierFamily) :
    CarrierCompletionResult P baseDepth family :=
  let native := nativeCompleteness (carrierNativeFamily P baseDepth family)
  let limit := toCarrier native.limit
  ⟨native, limit, rfl, nativeCarrierConvergence family native, nativeCarrierUniqueness family native⟩

/-- Uniqueness compares the produced values for the very same input family.
It asserts no equality of the two runtimes, archives or occurrences. -/
def carrierCompletion_perimeterIndependent (P Q : CircularPresentation)
    (baseDepth otherDepth : Nat) (family : CarrierFamily) :
    EffectiveCauchyReal.Equivalent (carrierCompletion P baseDepth family).limit
      (carrierCompletion Q otherDepth family).limit :=
  (carrierCompletion P baseDepth family).uniqueness _
    (carrierCompletion Q otherDepth family).convergence

end RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.carrierNativeFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.carrierReturnedFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.returnedNormalizedTermAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.originalCarrierLimitToReturned
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.returnedCarrierLimitToOriginal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.carrierLimitNativeCandidate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.CarrierCompletionResult
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.nativeCarrierConvergence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.nativeCarrierUniqueness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.carrierCompletion
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness.carrierCompletion_perimeterIndependent
/- AXIOM_AUDIT_END -/
