import RelationalPerimeter.Constitution.Reals.DyadicMultiplication

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Regular dyadic names receive arbitrary approximation functions. Their positive
regularity is numerical; no runtime, carrier, or choice of representatives is
used in this layer.
-/
namespace RelationalPerimeter.Constitution.Reals

theorem regularMaxLeft (a b : Nat) : a ≤ max a b := by
  cases (inferInstance : Decidable (a ≤ b)) with
  | isTrue h =>
    rw [Nat.max_def, if_pos h]
    exact h
  | isFalse h =>
    rw [Nat.max_def, if_neg h]
    exact Nat.le_refl _

theorem regularMaxRight (a b : Nat) : b ≤ max a b := by
  cases (inferInstance : Decidable (a ≤ b)) with
  | isTrue h =>
    rw [Nat.max_def, if_pos h]
    exact Nat.le_refl _
  | isFalse h =>
    rw [Nat.max_def, if_neg h]
    cases Nat.le_total a b with
    | inl bound => exact False.elim (h bound)
    | inr bound => exact bound

structure RegularDyadicName where
  approximation : Nat → SignedDyadicCode
  coherent : (precision leftResponse rightResponse : Nat) →
    PrecisionExtension precision leftResponse → PrecisionExtension precision rightResponse →
    Near precision (approximation leftResponse) (approximation rightResponse)

structure NameEquivalent (first second : RegularDyadicName) where
  responseThreshold : Nat → Nat
  near : (precision leftResponse rightResponse : Nat) →
    PrecisionExtension (responseThreshold precision) leftResponse →
    PrecisionExtension (responseThreshold precision) rightResponse →
    Near precision (first.approximation leftResponse) (second.approximation rightResponse)

namespace NameEquivalent

def refl (name : RegularDyadicName) : NameEquivalent name name :=
  ⟨fun p => p, name.coherent⟩

def symm {first second : RegularDyadicName} (same : NameEquivalent first second) :
    NameEquivalent second first :=
  ⟨same.responseThreshold, fun p r s hr hs => (same.near p s r hs hr).symm⟩

def trans {first middle last : RegularDyadicName}
    (left : NameEquivalent first middle) (right : NameEquivalent middle last) :
    NameEquivalent first last where
  responseThreshold p := max (left.responseThreshold (p + 1)) (right.responseThreshold (p + 1))
  near p r s hr hs :=
    let threshold := max (left.responseThreshold (p + 1)) (right.responseThreshold (p + 1))
    let leftBound := PrecisionExtension.ofLe (regularMaxLeft
      (left.responseThreshold (p + 1)) (right.responseThreshold (p + 1)))
    let rightBound := PrecisionExtension.ofLe (regularMaxRight
      (left.responseThreshold (p + 1)) (right.responseThreshold (p + 1)))
    Near.compose (left.near (p + 1) r threshold (leftBound.trans hr) leftBound)
      (right.near (p + 1) threshold s rightBound (rightBound.trans hs))

def ofPointwiseSame {first second : RegularDyadicName}
    (same : (p : Nat) → SameValue (first.approximation p) (second.approximation p)) :
    NameEquivalent first second where
  responseThreshold p := p
  near p r s hr hs := Near.ofSameRight (first.coherent p r s hr hs) (same s)

end NameEquivalent

namespace RegularDyadicName

def constantName (code : SignedDyadicCode) : RegularDyadicName where
  approximation p := code.raise p
  coherent p r s hr hs :=
    ((SameValue.raiseExact code r).symm.trans (SameValue.raiseExact code s)).toNear p

def constantNameSameValue (code : SignedDyadicCode) (response : Nat) :
    SameValue ((constantName code).approximation response) code :=
  (SameValue.raiseExact code response).symm

def zeroName : RegularDyadicName := constantName SignedDyadicCode.zero
def oneName : RegularDyadicName := constantName SignedDyadicCode.one

def negName (source : RegularDyadicName) : RegularDyadicName where
  approximation p := (source.approximation p).neg
  coherent p r s hr hs := (source.coherent p r s hr hs).neg

def addName (left right : RegularDyadicName) : RegularDyadicName where
  approximation p := (left.approximation (p + 1)).add (right.approximation (p + 1))
  coherent p r s hr hs := Near.add
    (left.coherent (p + 1) (r + 1) (s + 1) hr.succ hs.succ)
    (right.coherent (p + 1) (r + 1) (s + 1) hr.succ hs.succ)

def nameAmplitude (name : RegularDyadicName) (response : Nat) :
    Amplitude (probeAmplitude (name.approximation 0)) (name.approximation response) :=
  Amplitude.fromProbe (name.coherent 0 response 0
    (PrecisionExtension.ofLe (Nat.zero_le _)) (.refl _))

def mulName (left right : RegularDyadicName) : RegularDyadicName where
  approximation p :=
    (left.approximation (p + 1 + probeAmplitude (right.approximation 0))).mul
      (right.approximation (p + 1 + probeAmplitude (left.approximation 0)))
  coherent p r s hr hs := Near.mul
    (left.coherent (p + 1 + probeAmplitude (right.approximation 0)) _ _
      (hr.succ.add (.refl _)) (hs.succ.add (.refl _)))
    (right.coherent (p + 1 + probeAmplitude (left.approximation 0)) _ _
      (hr.succ.add (.refl _)) (hs.succ.add (.refl _)))
    (nameAmplitude right _) (nameAmplitude left _)

def negNameCongr {a b : RegularDyadicName} (same : NameEquivalent a b) :
    NameEquivalent (negName a) (negName b) :=
  ⟨same.responseThreshold, fun p r s hr hs => (same.near p r s hr hs).neg⟩

def addNameCongr {a b c d : RegularDyadicName}
    (first : NameEquivalent a c) (second : NameEquivalent b d) :
    NameEquivalent (addName a b) (addName c d) where
  responseThreshold p := max (first.responseThreshold (p + 1)) (second.responseThreshold (p + 1))
  near p r s hr hs :=
    let firstBound := PrecisionExtension.ofLe (regularMaxLeft
      (first.responseThreshold (p + 1)) (second.responseThreshold (p + 1)))
    let secondBound := PrecisionExtension.ofLe (regularMaxRight
      (first.responseThreshold (p + 1)) (second.responseThreshold (p + 1)))
    Near.add
      (first.near (p + 1) (r + 1) (s + 1)
        ((firstBound.trans hr).trans (.next _)) ((firstBound.trans hs).trans (.next _)))
      (second.near (p + 1) (r + 1) (s + 1)
        ((secondBound.trans hr).trans (.next _)) ((secondBound.trans hs).trans (.next _)))

/-- The two compared products keep their own crossed probe schedules. -/
def mulNameCongr {a b c d : RegularDyadicName}
    (first : NameEquivalent a c) (second : NameEquivalent b d) :
    NameEquivalent (mulName a b) (mulName c d) where
  responseThreshold p := max
    (first.responseThreshold (p + 1 + probeAmplitude (b.approximation 0)))
    (second.responseThreshold (p + 1 + probeAmplitude (c.approximation 0)))
  near p r s hr hs := by
    let leftPrecision := p + 1 + probeAmplitude (b.approximation 0)
    let rightPrecision := p + 1 + probeAmplitude (c.approximation 0)
    let firstBound := PrecisionExtension.ofLe (regularMaxLeft
      (first.responseThreshold leftPrecision) (second.responseThreshold rightPrecision))
    let secondBound := PrecisionExtension.ofLe (regularMaxRight
      (first.responseThreshold leftPrecision) (second.responseThreshold rightPrecision))
    exact Near.mul
      (first.near leftPrecision _ _
        ((firstBound.trans hr).trans (.refine _ _))
        ((firstBound.trans hs).trans (.refine _ _)))
      (second.near rightPrecision _ _
        ((secondBound.trans hr).trans (.refine _ _))
        ((secondBound.trans hs).trans (.refine _ _)))
      (nameAmplitude b _) (nameAmplitude c _)

def addNameComm (a b : RegularDyadicName) :
    NameEquivalent (addName a b) (addName b a) :=
  NameEquivalent.ofPointwiseSame (fun p => SignedDyadicCode.add_comm _ _)

def addNameAssoc (a b c : RegularDyadicName) :
    NameEquivalent (addName (addName a b) c) (addName a (addName b c)) where
  responseThreshold p := p + 2
  near p r s hr hs := by
    let rNext := (PrecisionExtension.next r).trans (PrecisionExtension.next (r + 1))
    let sNext := (PrecisionExtension.next s).trans (PrecisionExtension.next (s + 1))
    exact Near.ofSameRight
      (Near.add (Near.add
        (a.coherent (p + 2) (r + 2) (s + 1) (hr.trans rNext) (hs.trans (.next _)))
        (b.coherent (p + 2) (r + 2) (s + 2) (hr.trans rNext) (hs.trans sNext)))
        (c.coherent (p + 1) (r + 1) (s + 2)
          (((PrecisionExtension.next (p + 1)).trans hr).trans (.next _))
          (((PrecisionExtension.next (p + 1)).trans hs).trans sNext)))
      (SignedDyadicCode.add_assoc _ _ _)

def zeroNameLeft (a : RegularDyadicName) : NameEquivalent (addName zeroName a) a where
  responseThreshold p := p
  near p r s hr hs := Near.ofSameLeft
    ((SameValue.add (constantNameSameValue _ _) (.refl _)).trans (SignedDyadicCode.zero_add _))
    (a.coherent p (r + 1) s (hr.trans (.next _)) hs)

def zeroNameRight (a : RegularDyadicName) : NameEquivalent (addName a zeroName) a where
  responseThreshold p := p
  near p r s hr hs := Near.ofSameLeft
    ((SameValue.add (.refl _) (constantNameSameValue _ _)).trans (SignedDyadicCode.add_zero _))
    (a.coherent p (r + 1) s (hr.trans (.next _)) hs)

def negNameInvolutive (a : RegularDyadicName) : NameEquivalent (negName (negName a)) a :=
  NameEquivalent.ofPointwiseSame (fun p => by
    change SameValue (a.approximation p).neg.neg (a.approximation p)
    rw [SignedDyadicCode.neg_neg_exact]
    exact .refl _)

def addNameInverseLeft (a : RegularDyadicName) : NameEquivalent (addName (negName a) a) zeroName :=
  NameEquivalent.ofPointwiseSame (fun p =>
    (SignedDyadicCode.neg_add _).trans (constantNameSameValue _ p).symm)

def addNameInverseRight (a : RegularDyadicName) : NameEquivalent (addName a (negName a)) zeroName :=
  NameEquivalent.ofPointwiseSame (fun p =>
    (SignedDyadicCode.add_neg _).trans (constantNameSameValue _ p).symm)

def negNameSum (a b : RegularDyadicName) :
    NameEquivalent (negName (addName a b)) (addName (negName a) (negName b)) :=
  NameEquivalent.ofPointwiseSame (fun p => by
    change SameValue ((a.approximation (p + 1)).add (b.approximation (p + 1))).neg _
    rw [SignedDyadicCode.neg_add_exact]
    exact .refl _)

end RegularDyadicName

structure RegularPresentedFamily where
  name : Nat → RegularDyadicName
  modulus : Nat → Nat
  modulusMonotone : {p q : Nat} → PrecisionExtension p q → PrecisionExtension (modulus p) (modulus q)
  cauchy : (p n m r s : Nat) → PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
    PrecisionExtension p r → PrecisionExtension p s →
    Near p ((name n).approximation r) ((name m).approximation s)

namespace RegularDyadicName

def diagonalName (family : RegularPresentedFamily) : RegularDyadicName where
  approximation p := (family.name (family.modulus p)).approximation p
  coherent p r s hr hs := family.cauchy p _ _ r s
    (family.modulusMonotone hr) (family.modulusMonotone hs) hr hs

structure RegularConverges (family : RegularPresentedFamily) (value : RegularDyadicName) where
  threshold : Nat → Nat
  near : (p n r s : Nat) → PrecisionExtension (family.modulus p) n →
    PrecisionExtension p r → PrecisionExtension (threshold p) s →
    Near p ((family.name n).approximation r) (value.approximation s)

structure RegularLimitResult (family : RegularPresentedFamily) where
  value : RegularDyadicName
  convergence : RegularConverges family value
  unique : (other : RegularDyadicName) → RegularConverges family other → NameEquivalent value other

def regularLimitResult (family : RegularPresentedFamily) : RegularLimitResult family where
  value := diagonalName family
  convergence := {
    threshold := fun p => p
    near := fun p n r s hn hr hs =>
      family.cauchy p n (family.modulus s) r s hn (family.modulusMonotone hs) hr hs }
  unique other convergence := {
    responseThreshold := fun p => max (p + 1) (convergence.threshold (p + 1))
    near := fun p r s hr hs =>
      let sourceBound := PrecisionExtension.ofLe (regularMaxLeft (p + 1) (convergence.threshold (p + 1)))
      let targetBound := PrecisionExtension.ofLe (regularMaxRight (p + 1) (convergence.threshold (p + 1)))
      Near.compose
        ((family.cauchy (p + 1) (family.modulus (p + 1)) (family.modulus r) (p + 1) r
          (.refl _) (family.modulusMonotone (sourceBound.trans hr)) (.refl _) (sourceBound.trans hr)).symm)
        (convergence.near (p + 1) (family.modulus (p + 1)) (p + 1) s
          (.refl _) (.refl _) (targetBound.trans hs)) }

end RegularDyadicName
end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.regularMaxLeft
#print axioms RelationalPerimeter.Constitution.Reals.regularMaxRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName
#print axioms RelationalPerimeter.Constitution.Reals.NameEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.NameEquivalent.refl
#print axioms RelationalPerimeter.Constitution.Reals.NameEquivalent.symm
#print axioms RelationalPerimeter.Constitution.Reals.NameEquivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.NameEquivalent.ofPointwiseSame
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.constantName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.constantNameSameValue
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.zeroName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.oneName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.negName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameAmplitude
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.negNameCongr
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addNameCongr
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameCongr
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addNameComm
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addNameAssoc
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.zeroNameLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.zeroNameRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.negNameInvolutive
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addNameInverseLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addNameInverseRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.negNameSum
#print axioms RelationalPerimeter.Constitution.Reals.RegularPresentedFamily
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.diagonalName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.RegularConverges
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.RegularLimitResult
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.regularLimitResult
/- AXIOM_AUDIT_END -/
