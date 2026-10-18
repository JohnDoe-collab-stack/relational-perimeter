import RelationalPerimeter.Constitution.Reals.RegularDyadicName
import RelationalPerimeter.Constitution.Reals.DyadicOrderTransport
import RelationalPerimeter.Constitution.Reals.DyadicDensity

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Constitution.Reals

structure NameOrder (left right : RegularDyadicName) where
  accuracy : Nat
  response : Nat
  beyond : PrecisionExtension (accuracy + 3) response
  separation : StrictSeparation accuracy
    (left.approximation response) (right.approximation response)

def NameApartness (left right : RegularDyadicName) : Type :=
  NameOrder left right ⊕ NameOrder right left

namespace RegularDyadicName
open DyadicReciprocal DyadicDensity

def transportNameOrder {a b c d : RegularDyadicName} (origin : NameOrder a b)
    (left : NameEquivalent a c) (right : NameEquivalent b d) : NameOrder c d := by
  let p := origin.accuracy
  let lr := (p + 3) + left.responseThreshold (p + 3)
  let rr := (p + 3) + right.responseThreshold (p + 3)
  have l1 := a.coherent (p + 3) origin.response lr origin.beyond (.first _ _)
  have l2 := left.near (p + 3) lr lr (.second _ _) (.second _ _)
  have l3 := c.coherent (p + 3) lr (p + 5) (.first _ _) ⟨2, rfl⟩
  have r1 := b.coherent (p + 3) origin.response rr origin.beyond (.first _ _)
  have r2 := right.near (p + 3) rr rr (.second _ _) (.second _ _)
  have r3 := d.coherent (p + 3) rr (p + 5) (.first _ _) ⟨2, rfl⟩
  exact ⟨p + 2, p + 5, .refl _,
    strengthenSeparationThreeLinks origin.separation l1 l2 l3 r1 r2 r3⟩

def transportNameApartness {a b c d : RegularDyadicName} (origin : NameApartness a b)
    (left : NameEquivalent a c) (right : NameEquivalent b d) : NameApartness c d :=
  match origin with
  | .inl order => .inl (transportNameOrder order left right)
  | .inr order => .inr (transportNameOrder order right left)

end RegularDyadicName

namespace NameOrder
open RegularDyadicName

def irreflexive {a : RegularDyadicName} (order : NameOrder a a) : Empty :=
  order.separation.refuteUpper (.ofNear (Near.refl _ _))

def refine {a b : RegularDyadicName} (origin : NameOrder a b)
    (response : Nat) (beyond : PrecisionExtension (origin.accuracy + 5) response) : NameOrder a b := by
  have old : PrecisionExtension (origin.accuracy + 2) origin.response :=
    (PrecisionExtension.next _).trans origin.beyond
  have fine : PrecisionExtension (origin.accuracy + 2) response :=
    (PrecisionExtension.first _ 3).trans beyond
  exact ⟨origin.accuracy + 2, response, beyond,
    strengthenSeparation origin.separation
      (a.coherent _ _ _ old fine) (b.coherent _ _ _ old fine)⟩

def asymmetric {a b : RegularDyadicName} (first : NameOrder a b) (reverse : NameOrder b a) : Empty := by
  let response := (reverse.accuracy + 5) + (first.accuracy + 3)
  let refined := reverse.refine response (.first _ _)
  have fine : PrecisionExtension (first.accuracy + 2) response :=
    (PrecisionExtension.next _).trans (.second _ _)
  have old : PrecisionExtension (first.accuracy + 2) first.response :=
    (PrecisionExtension.next _).trans first.beyond
  have leftNear := a.coherent (first.accuracy + 2) first.response response old fine
  have rightNear := b.coherent (first.accuracy + 2) first.response response old fine
  exact first.separation.refuteUpper (DirectedUpper.compose
    (DirectedUpper.compose (.ofNear rightNear) (refined.separation.forwardUpper (first.accuracy + 2)))
    ((DirectedUpper.ofNear leftNear.symm).weaken (.next _)))

def cotransitive {a c : RegularDyadicName} (origin : NameOrder a c) (middle : RegularDyadicName) :
    NameOrder a middle ⊕ NameOrder middle c := by
  let p := origin.accuracy
  let response := p + 5
  have old : PrecisionExtension (p + 2) origin.response := (PrecisionExtension.next _).trans origin.beyond
  have fine : PrecisionExtension (p + 2) response := .first _ 3
  let leftNear := a.coherent (p + 2) origin.response response old fine
  let rightNear := c.coherent (p + 2) origin.response response old fine
  cases inspectGap (p + 2) (a.approximation response) (middle.approximation response) with
  | inl gap => exact .inl ⟨p + 2, response, .refl _, gap⟩
  | inr upper =>
    cases inspectGap (p + 2) (middle.approximation response) (c.approximation response) with
    | inl gap => exact .inr ⟨p + 2, response, .refl _, gap⟩
    | inr second =>
      exact (origin.separation.refuteUpper (DirectedUpper.compose
        (DirectedUpper.compose (.ofNear rightNear) second)
        (DirectedUpper.compose upper (.ofNear leftNear.symm)))).elim

def transitive {a b c : RegularDyadicName} (first : NameOrder a b) (second : NameOrder b c) : NameOrder a c :=
  match first.cotransitive c with
  | .inl order => order
  | .inr reverse => (second.asymmetric reverse).elim

def refutesEquivalent {a b : RegularDyadicName} (order : NameOrder a b) (same : NameEquivalent a b) : Empty :=
  (transportNameOrder order (.refl a) same.symm).irreflexive

end NameOrder

namespace NameApartness

def symm {a b : RegularDyadicName} : NameApartness a b → NameApartness b a
  | .inl order => .inr order
  | .inr order => .inl order

def irreflexive {a : RegularDyadicName} : NameApartness a a → Empty
  | .inl order => order.irreflexive
  | .inr order => order.irreflexive

def cotransitive {a c : RegularDyadicName} (origin : NameApartness a c) (middle : RegularDyadicName) :
    NameApartness a middle ⊕ NameApartness middle c :=
  match origin with
  | .inl order => match order.cotransitive middle with
    | .inl first => .inl (.inl first)
    | .inr second => .inr (.inl second)
  | .inr order => match order.cotransitive middle with
    | .inl first => .inr (.inr first)
    | .inr second => .inl (.inr second)

end NameApartness

structure NameDensityWitness (a b : RegularDyadicName) where
  code : SignedDyadicCode
  left : NameOrder a (RegularDyadicName.constantName code)
  right : NameOrder (RegularDyadicName.constantName code) b

structure NameNaturalBounds (name : RegularDyadicName) where
  lower : Nat
  upper : Nat
  lowerOrder : NameOrder (RegularDyadicName.constantName (DyadicDensity.negativeNaturalCode lower)) name
  upperOrder : NameOrder name (RegularDyadicName.constantName (DyadicDensity.naturalCode upper))

namespace RegularDyadicName
open DyadicReciprocal DyadicDensity

def nameDensity {a b : RegularDyadicName} (origin : NameOrder a b) : NameDensityWitness a b := by
  let middle := bisect origin.separation
  let p := origin.accuracy
  have fine : PrecisionExtension (p + 3) (p + 6) := .first _ 3
  exact ⟨middle.code,
    ⟨p + 3, p + 6, .refl _, strengthenSeparation middle.leftMargin
      (a.coherent _ _ _ origin.beyond fine)
      ((constantNameSameValue middle.code (p + 6)).symm.toNear _)⟩,
    ⟨p + 3, p + 6, .refl _, strengthenSeparation middle.rightMargin
      ((constantNameSameValue middle.code (p + 6)).symm.toNear _)
      (b.coherent _ _ _ origin.beyond fine)⟩⟩

def nameNaturalBounds (name : RegularDyadicName) : NameNaturalBounds name := by
  let probe := name.approximation 2
  let bounds := naturalBounds probe
  have near := name.coherent 2 2 5 (.refl _) (.first _ 3)
  exact ⟨bounds.lower, bounds.upper,
    ⟨2, 5, .refl _, strengthenSeparation bounds.lowerMargin
      ((constantNameSameValue (negativeNaturalCode bounds.lower) 5).symm.toNear 2) near⟩,
    ⟨2, 5, .refl _, strengthenSeparation bounds.upperMargin near
      ((constantNameSameValue (naturalCode bounds.upper) 5).symm.toNear 2)⟩⟩

def nameReadoutsNear (name : RegularDyadicName) (p r s : Nat)
    (hr : PrecisionExtension p r) (hs : PrecisionExtension p s) :
    Near p (RegularDyadicName.approximation name r) (RegularDyadicName.approximation name s) := name.coherent p r s hr hs

theorem mulNameReadout (a b : RegularDyadicName) (p : Nat) :
    (mulName a b).approximation p =
      (RegularDyadicName.approximation a (p + 1 + probeAmplitude (RegularDyadicName.approximation b 0))).mul
        (RegularDyadicName.approximation b (p + 1 + probeAmplitude (RegularDyadicName.approximation a 0))) := rfl

theorem addNameReadout (a b : RegularDyadicName) (p : Nat) :
    (addName a b).approximation p = (RegularDyadicName.approximation a (p + 1)).add (RegularDyadicName.approximation b (p + 1)) := rfl

theorem negNameReadout (a : RegularDyadicName) (p : Nat) :
    (negName a).approximation p = (RegularDyadicName.approximation a p).neg := rfl

def mulNameSampleNear (left right : RegularDyadicName) (p response l r : Nat)
    (responseBeyond : PrecisionExtension p response)
    (leftBeyond : PrecisionExtension (p + 1 + probeAmplitude (RegularDyadicName.approximation right 0)) l)
    (rightBeyond : PrecisionExtension (p + 1 + probeAmplitude (RegularDyadicName.approximation left 0)) r) :
    Near p (RegularDyadicName.approximation (mulName left right) response) ((RegularDyadicName.approximation left l).mul (RegularDyadicName.approximation right r)) := by
  rw [mulNameReadout]
  exact Near.mul
    (nameReadoutsNear left _ _ _ (responseBeyond.succ.add (PrecisionExtension.refl _)) leftBeyond)
    (nameReadoutsNear right _ _ _ (responseBeyond.succ.add (PrecisionExtension.refl _)) rightBeyond)
    (nameAmplitude right _) (nameAmplitude left _)

def mulNameComm (left right : RegularDyadicName) : NameEquivalent (mulName left right) (mulName right left) :=
  NameEquivalent.ofPointwiseSame (fun p => by
    rw [mulNameReadout, mulNameReadout, SignedDyadicCode.mul_comm_exact]
    exact SameValue.refl _)

def mulNameOneRight (real : RegularDyadicName) : NameEquivalent (mulName real oneName) real where
  responseThreshold := fun p => p
  near := by
    intro p l r hl hr
    rw [mulNameReadout]
    have same : SameValue
        ((RegularDyadicName.approximation real (l + 1 + probeAmplitude (RegularDyadicName.approximation oneName 0))).mul
          (RegularDyadicName.approximation oneName (l + 1 + probeAmplitude (RegularDyadicName.approximation real 0))))
        (RegularDyadicName.approximation real (l + 1 + probeAmplitude (RegularDyadicName.approximation oneName 0))) := by
      apply SameValue.trans (SameValue.mul (SameValue.refl _) (constantNameSameValue SignedDyadicCode.one _))
      rw [SignedDyadicCode.mul_one_exact]
      exact SameValue.refl _
    exact Near.ofSameLeft same (nameReadoutsNear real p _ r (hl.trans (PrecisionExtension.refine l _)) hr)

def mulNameOneLeft (real : RegularDyadicName) : NameEquivalent (mulName oneName real) real :=
  (mulNameComm _ _).trans (mulNameOneRight real)

def mulNameZeroRight (real : RegularDyadicName) : NameEquivalent (mulName real zeroName) zeroName :=
  NameEquivalent.ofPointwiseSame (fun p => by
    rw [mulNameReadout]
    exact ((SameValue.mul (SameValue.refl _) (constantNameSameValue SignedDyadicCode.zero _)).trans
      (SignedDyadicCode.mul_zero _)).trans (constantNameSameValue SignedDyadicCode.zero p).symm)

def mulNameZeroLeft (real : RegularDyadicName) : NameEquivalent (mulName zeroName real) zeroName :=
  (mulNameComm _ _).trans (mulNameZeroRight real)

theorem nameProbeAmplitudeNeg (code : SignedDyadicCode) : probeAmplitude code.neg = probeAmplitude code :=
  congrArg (fun n => n + 1) (Nat.add_comm _ _)

def mulNameNegRight (a b : RegularDyadicName) : NameEquivalent (mulName a (negName b)) (negName (mulName a b)) :=
  NameEquivalent.ofPointwiseSame (fun p => by
    rw [mulNameReadout, negNameReadout (mulName a b) p, mulNameReadout,
      negNameReadout b 0, nameProbeAmplitudeNeg, negNameReadout b,
      SignedDyadicCode.mul_neg_exact]
    exact SameValue.refl _)

def mulNameNegLeft (a b : RegularDyadicName) : NameEquivalent (mulName (negName a) b) (negName (mulName a b)) :=
  (mulNameComm _ _).trans ((mulNameNegRight b a).trans (negNameCongr (mulNameComm b a)))

/-- A finite list of explicit error requirements, not a magic global bound. -/
def nameAssociativityPrecisions (a b c : RegularDyadicName) (p : Nat) : List Nat :=
  let ba := probeAmplitude (RegularDyadicName.approximation a 0)
  let bb := probeAmplitude (RegularDyadicName.approximation b 0)
  let bc := probeAmplitude (RegularDyadicName.approximation c 0)
  let bab := probeAmplitude (RegularDyadicName.approximation (mulName a b) 0)
  let bbc := probeAmplitude (RegularDyadicName.approximation (mulName b c) 0)
  [p + 2, p + 3 + bc, p + 3 + bab, p + 2 + bc,
    (p + 2 + bc) + 1 + bb, (p + 2 + bc) + 1 + ba,
    p + 3 + bbc, p + 3 + ba, p + 2 + ba,
    (p + 2 + ba) + 1 + bc, (p + 2 + ba) + 1 + bb]

def mulNameAssoc (a b c : RegularDyadicName) : NameEquivalent (mulName (mulName a b) c) (mulName a (mulName b c)) where
  responseThreshold p := precisionPool (nameAssociativityPrecisions a b c p)
  near := by
    intro p l r hl hr
    let pool := nameAssociativityPrecisions a b c p
    let k := precisionPool pool
    have h0 : PrecisionMember (p + 2) pool := .here
    have h1 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation c 0)) pool := .there .here
    have h2 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation (mulName a b) 0)) pool := .there (.there .here)
    have h3 : PrecisionMember (p + 2 + probeAmplitude (RegularDyadicName.approximation c 0)) pool := .there (.there (.there .here))
    have h4 : PrecisionMember ((p + 2 + probeAmplitude (RegularDyadicName.approximation c 0)) + 1 + probeAmplitude (RegularDyadicName.approximation b 0)) pool :=
      .there (.there (.there (.there .here)))
    have h5 : PrecisionMember ((p + 2 + probeAmplitude (RegularDyadicName.approximation c 0)) + 1 + probeAmplitude (RegularDyadicName.approximation a 0)) pool :=
      .there (.there (.there (.there (.there .here))))
    have h6 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation (mulName b c) 0)) pool :=
      .there (.there (.there (.there (.there (.there .here)))))
    have h7 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation a 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there .here))))))
    have h8 : PrecisionMember (p + 2 + probeAmplitude (RegularDyadicName.approximation a 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there (.there .here)))))))
    have h9 : PrecisionMember ((p + 2 + probeAmplitude (RegularDyadicName.approximation a 0)) + 1 + probeAmplitude (RegularDyadicName.approximation c 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    have h10 : PrecisionMember ((p + 2 + probeAmplitude (RegularDyadicName.approximation a 0)) + 1 + probeAmplitude (RegularDyadicName.approximation b 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    have outerLeft := mulNameSampleNear (mulName a b) c (p + 2) l k k (h0.extension.trans hl) h1.extension h2.extension
    have innerLeft := (mulNameSampleNear a b (p + 2 + probeAmplitude (RegularDyadicName.approximation c 0)) k k k
      h3.extension h4.extension h5.extension).mulRight (nameAmplitude c k)
    have outerRight := mulNameSampleNear a (mulName b c) (p + 2) r k k (h0.extension.trans hr) h6.extension h7.extension
    have innerRight := (mulNameSampleNear b c (p + 2 + probeAmplitude (RegularDyadicName.approximation a 0)) k k k
      h8.extension h9.extension h10.extension).mulLeft (nameAmplitude a k)
    have left := Near.compose outerLeft innerLeft
    have right := Near.compose outerRight innerRight
    have exact : SameValue (((RegularDyadicName.approximation a k).mul (RegularDyadicName.approximation b k)).mul (RegularDyadicName.approximation c k))
        ((RegularDyadicName.approximation a k).mul ((RegularDyadicName.approximation b k).mul (RegularDyadicName.approximation c k))) := by
      rw [SignedDyadicCode.mul_assoc_exact]
      exact SameValue.refl _
    exact Near.compose (Near.ofSameRight left exact) right.symm

def nameDistributivityPrecisions (a b c : RegularDyadicName) (p : Nat) : List Nat :=
  let ba := probeAmplitude (RegularDyadicName.approximation a 0)
  [p + 2, p + 3 + probeAmplitude (RegularDyadicName.approximation (addName b c) 0), p + 3 + ba,
    (p + 2 + ba) + 1, p + 3 + probeAmplitude (RegularDyadicName.approximation b 0), p + 3 + probeAmplitude (RegularDyadicName.approximation c 0)]

def mulNameDistributeLeft (a b c : RegularDyadicName) : NameEquivalent (mulName a (addName b c)) (addName (mulName a b) (mulName a c)) where
  responseThreshold p := precisionPool (nameDistributivityPrecisions a b c p)
  near := by
    intro p l r hl hr
    let pool := nameDistributivityPrecisions a b c p
    let k := precisionPool pool
    have h0 : PrecisionMember (p + 2) pool := .here
    have h1 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation (addName b c) 0)) pool := .there .here
    have h2 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation a 0)) pool := .there (.there .here)
    have h3 : PrecisionMember ((p + 2 + probeAmplitude (RegularDyadicName.approximation a 0)) + 1) pool := .there (.there (.there .here))
    have h4 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation b 0)) pool := .there (.there (.there (.there .here)))
    have h5 : PrecisionMember (p + 3 + probeAmplitude (RegularDyadicName.approximation c 0)) pool := .there (.there (.there (.there (.there .here))))
    have outer := mulNameSampleNear a (addName b c) (p + 2) l k k (h0.extension.trans hl) h1.extension h2.extension
    have sumNear : Near (p + 2 + probeAmplitude (RegularDyadicName.approximation a 0))
        (RegularDyadicName.approximation (addName b c) k) ((RegularDyadicName.approximation b k).add (RegularDyadicName.approximation c k)) := by
      rw [addNameReadout]
      exact Near.add
        (nameReadoutsNear b _ _ _ (h3.extension.trans (PrecisionExtension.next k)) h3.extension)
        (nameReadoutsNear c _ _ _ (h3.extension.trans (PrecisionExtension.next k)) h3.extension)
    have left := Near.compose outer (sumNear.mulLeft (nameAmplitude a k))
    have right : Near (p + 1) (RegularDyadicName.approximation (addName (mulName a b) (mulName a c)) r)
        (((RegularDyadicName.approximation a k).mul (RegularDyadicName.approximation b k)).add ((RegularDyadicName.approximation a k).mul (RegularDyadicName.approximation c k))) := by
      rw [addNameReadout]
      exact Near.add
        (mulNameSampleNear a b (p + 2) (r + 1) k k
          ((h0.extension.trans hr).trans (PrecisionExtension.next r)) h4.extension h2.extension)
        (mulNameSampleNear a c (p + 2) (r + 1) k k
          ((h0.extension.trans hr).trans (PrecisionExtension.next r)) h5.extension h2.extension)
    exact Near.compose (Near.ofSameRight left (SignedDyadicCode.mul_add _ _ _)) right.symm

def mulNameDistributeRight (a b c : RegularDyadicName) : NameEquivalent (mulName (addName a b) c) (addName (mulName a c) (mulName b c)) :=
  (mulNameComm _ _).trans ((mulNameDistributeLeft c a b).trans (addNameCongr (mulNameComm c a) (mulNameComm c b)))

def unitNamePositive : NameOrder zeroName oneName := by
  have margin : StrictSeparation 1 SignedDyadicCode.zero SignedDyadicCode.one :=
    ⟨⟨1, 1, 1, rfl, rfl⟩, 0, rfl, by decide⟩
  exact ⟨1, 4, .refl _,
    (margin.ofSameRight (constantNameSameValue SignedDyadicCode.one 4).symm).ofSameLeft
      (constantNameSameValue SignedDyadicCode.zero 4)⟩

def translateNameOrderRight {a b : RegularDyadicName} (origin : NameOrder a b) (shift : RegularDyadicName) :
    NameOrder (addName a shift) (addName b shift) := by
  let p := origin.accuracy
  have old : PrecisionExtension (p + 2) origin.response := (PrecisionExtension.next _).trans origin.beyond
  have fine : PrecisionExtension (p + 2) (p + 5 + 1) := .first _ 4
  exact ⟨p + 2, p + 5, .refl _,
    (strengthenSeparation origin.separation
      (a.coherent _ _ _ old fine) (b.coherent _ _ _ old fine)).addRight _⟩

/-- Domain data retain the same away parameter at every source response. -/
structure ReciprocalNameDomain (source : RegularDyadicName) where
  direction : Direction
  away : Nat
  nonzero : (p : Nat) → NonzeroCode direction away (source.approximation (sourcePrecision away p))

def reciprocalName (source : RegularDyadicName) (domain : ReciprocalNameDomain source) : RegularDyadicName where
  approximation p := (computeReciprocal domain.direction
    (source.approximation (sourcePrecision domain.away p)) (roundingPrecision p) (domain.nonzero p).positive).code
  coherent p l r hl hr := reciprocalNear (domain.nonzero l) (domain.nonzero r)
    (computeReciprocal _ _ _ (domain.nonzero l).positive)
    (computeReciprocal _ _ _ (domain.nonzero r).positive)
    (source.coherent (sourcePrecision domain.away p) _ _
      ((hl.succ.succ).add (.refl _)) ((hr.succ.succ).add (.refl _))) hl hr

def inverseSourceBeyond (accuracy p : Nat) :
    PrecisionExtension (accuracy + 3) (sourcePrecision (accuracy + 2) p) :=
  ⟨p + accuracy + 3, by
    change (accuracy + 3) + (p + accuracy + 3) = p + 2 + ((accuracy + 2) + (accuracy + 2))
    conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩

def inverseNameDomain (source : RegularDyadicName) (origin : NameApartness source zeroName) :
    ReciprocalNameDomain source := by
  cases origin with
  | inl order =>
    refine ⟨.negative, order.accuracy + 2, fun p => fromNegativeMargin ?_⟩
    exact strengthenSeparationThreeLinks order.separation
      (source.coherent _ _ _ order.beyond (inverseSourceBeyond order.accuracy p))
      (Near.refl _ _) (Near.refl _ _)
      ((constantNameSameValue SignedDyadicCode.zero order.response).toNear _)
      (Near.refl _ _) (Near.refl _ _)
  | inr order =>
    refine ⟨.positive, order.accuracy + 2, fun p => fromPositiveMargin ?_⟩
    exact strengthenSeparationThreeLinks order.separation
      ((constantNameSameValue SignedDyadicCode.zero order.response).toNear _)
      (Near.refl _ _) (Near.refl _ _)
      (source.coherent _ _ _ order.beyond (inverseSourceBeyond order.accuracy p))
      (Near.refl _ _) (Near.refl _ _)

def inverseName (source : RegularDyadicName) (origin : NameApartness source zeroName) : RegularDyadicName :=
  reciprocalName source (inverseNameDomain source origin)

def reciprocalNameProductNear (source : RegularDyadicName) (domain : ReciprocalNameDomain source)
    (p response : Nat)
    (beyond : PrecisionExtension
      (p + 1 + probeAmplitude ((reciprocalName source domain).approximation 0)) response) :
    Near p ((mulName source (reciprocalName source domain)).approximation response) SignedDyadicCode.one := by
  let reciprocal := reciprocalName source domain
  let bi := probeAmplitude (reciprocal.approximation 0)
  let bs := probeAmplitude (source.approximation 0)
  let j := response + 1 + bs
  let k := domain.away
  let result := computeReciprocal domain.direction
    (source.approximation (sourcePrecision k j)) (roundingPrecision j) (domain.nonzero j).positive
  have coarseResponse : PrecisionExtension p response :=
    (PrecisionExtension.next p).trans ((PrecisionExtension.first (p + 1) bi).trans beyond)
  have sourceBeyond : PrecisionExtension (p + 1 + bi) (sourcePrecision k j) :=
    beyond.trans ((PrecisionExtension.refine response bs).trans
      ((PrecisionExtension.first j 2).trans (PrecisionExtension.first (j + 2) (k + k))))
  have sourceNear := source.coherent (p + 1 + bi) _ _
    (beyond.trans (PrecisionExtension.refine response bi)) sourceBeyond
  have inverseAmplitude := nameAmplitude reciprocal j
  have sourceAmplitude := nameAmplitude source (sourcePrecision k j)
  have roundBudget : PrecisionExtension (p + 1 + bs) (roundingPrecision j) :=
    (coarseResponse.succ.add (PrecisionExtension.refl bs)).trans (PrecisionExtension.first j 2)
  have first : Near (p + 1)
      ((source.approximation (response + 1 + bi)).mul (reciprocal.approximation j))
      ((source.approximation (sourcePrecision k j)).mul result.code) :=
    sourceNear.mulRight inverseAmplitude
  have second := reciprocalUnit (domain.nonzero j) sourceAmplitude result roundBudget
  exact Near.compose first second

def reciprocalNameUnitRight (source : RegularDyadicName) (domain : ReciprocalNameDomain source) :
    NameEquivalent (mulName source (reciprocalName source domain)) oneName where
  responseThreshold p := p + 1 + probeAmplitude ((reciprocalName source domain).approximation 0)
  near p r s hr hs := Near.ofSameRight (reciprocalNameProductNear source domain p r hr)
    (constantNameSameValue SignedDyadicCode.one s).symm

def reciprocalNameUnitLeft (source : RegularDyadicName) (domain : ReciprocalNameDomain source) :
    NameEquivalent (mulName (reciprocalName source domain) source) oneName :=
  (mulNameComm _ _).trans (reciprocalNameUnitRight source domain)

def nameInverseUnique {a b c : RegularDyadicName}
    (rightUnit : NameEquivalent (mulName a b) oneName)
    (leftUnit : NameEquivalent (mulName c a) oneName) : NameEquivalent b c :=
  (mulNameOneLeft b).symm.trans
    ((mulNameCongr leftUnit.symm (.refl b)).trans
      ((mulNameAssoc c a b).trans
        ((mulNameCongr (.refl c) rightUnit).trans (mulNameOneRight c))))

def reciprocalNameCongr {a b : RegularDyadicName} (same : NameEquivalent a b)
    (first : ReciprocalNameDomain a) (second : ReciprocalNameDomain b) :
    NameEquivalent (reciprocalName a first) (reciprocalName b second) :=
  nameInverseUnique (reciprocalNameUnitRight a first)
    ((mulNameCongr (.refl _) same).trans (reciprocalNameUnitLeft b second))

def reciprocalNameWitnessIndependent (source : RegularDyadicName)
    (first second : ReciprocalNameDomain source) :
    NameEquivalent (reciprocalName source first) (reciprocalName source second) :=
  reciprocalNameCongr (.refl source) first second

def inverseNameUnitRight (source : RegularDyadicName) (origin : NameApartness source zeroName) :
    NameEquivalent (mulName source (inverseName source origin)) oneName :=
  reciprocalNameUnitRight source (inverseNameDomain source origin)

def inverseNameUnitLeft (source : RegularDyadicName) (origin : NameApartness source zeroName) :
    NameEquivalent (mulName (inverseName source origin) source) oneName :=
  reciprocalNameUnitLeft source (inverseNameDomain source origin)

def inverseNameCongr {a b : RegularDyadicName} (same : NameEquivalent a b)
    (first : NameApartness a zeroName) (second : NameApartness b zeroName) :
    NameEquivalent (inverseName a first) (inverseName b second) :=
  reciprocalNameCongr same (inverseNameDomain a first) (inverseNameDomain b second)

def inverseNameWitnessIndependent (source : RegularDyadicName) (first second : NameApartness source zeroName) :
    NameEquivalent (inverseName source first) (inverseName source second) :=
  inverseNameCongr (.refl source) first second

def translateNameOrderLeft {a b : RegularDyadicName} (origin : NameOrder a b) (shift : RegularDyadicName) :
    NameOrder (addName shift a) (addName shift b) :=
  transportNameOrder (translateNameOrderRight origin shift) (addNameComm a shift) (addNameComm b shift)

def nameAddCancellation (a shift : RegularDyadicName) :
    NameEquivalent (addName (addName a shift) (negName shift)) a :=
  (addNameAssoc _ _ _).trans
    ((addNameCongr (.refl _) (addNameInverseRight shift)).trans (zeroNameRight a))

def reflectNameTranslationRight {a b shift : RegularDyadicName}
    (origin : NameOrder (addName a shift) (addName b shift)) : NameOrder a b :=
  transportNameOrder (translateNameOrderRight origin (negName shift))
    (nameAddCancellation a shift) (nameAddCancellation b shift)

def namePositiveAt {source : RegularDyadicName} (origin : NameOrder zeroName source)
    (response : Nat) (beyond : PrecisionExtension (origin.accuracy + 3) response) :
    NonzeroCode .positive (origin.accuracy + 2) (source.approximation response) :=
  fromPositiveMargin (strengthenSeparationThreeLinks origin.separation
    ((constantNameSameValue SignedDyadicCode.zero origin.response).toNear _)
    (Near.refl _ _) (Near.refl _ _)
    (source.coherent _ _ _ origin.beyond beyond) (Near.refl _ _) (Near.refl _ _))

def positiveNameProduct {a b : RegularDyadicName} (left : NameOrder zeroName a) (right : NameOrder zeroName b) :
    NameOrder zeroName (mulName a b) := by
  let p := (left.accuracy + 2) + (right.accuracy + 2) + 1
  let response := p + 3
  have leftBeyond : PrecisionExtension (left.accuracy + 3) response := ⟨right.accuracy + 5, by
    change (left.accuracy + 3) + (right.accuracy + 5) =
      (left.accuracy + 2) + (right.accuracy + 2) + 1 + 3
    conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩
  have rightBeyond : PrecisionExtension (right.accuracy + 3) response := ⟨left.accuracy + 5, by
    change (right.accuracy + 3) + (left.accuracy + 5) =
      (left.accuracy + 2) + (right.accuracy + 2) + 1 + 3
    conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩
  let first := namePositiveAt left (response + 1 + probeAmplitude (b.approximation 0))
    (leftBeyond.trans (.refine response _))
  let second := namePositiveAt right (response + 1 + probeAmplitude (a.approximation 0))
    (rightBeyond.trans (.refine response _))
  exact ⟨p, response, .refl _,
    (first.mulPositive second).ofSameLeft (constantNameSameValue SignedDyadicCode.zero response)⟩

def namePositiveDifference {a b : RegularDyadicName} (origin : NameOrder a b) :
    NameOrder zeroName (addName b (negName a)) :=
  transportNameOrder (translateNameOrderRight origin (negName a)) (addNameInverseRight a) (.refl _)

def nameDifferenceProductCancellation (a b c : RegularDyadicName) :
    NameEquivalent (addName (mulName (addName b (negName a)) c) (mulName a c)) (mulName b c) :=
  (addNameCongr (mulNameDistributeRight b (negName a) c) (.refl _)).trans
    ((addNameCongr (addNameCongr (.refl _) (mulNameNegLeft a c)) (.refl _)).trans
      ((addNameAssoc (mulName b c) (negName (mulName a c)) (mulName a c)).trans
        ((addNameCongr (.refl _) (addNameInverseLeft (mulName a c))).trans (zeroNameRight _))))

def multiplyNamePositiveRight {a b c : RegularDyadicName} (origin : NameOrder a b)
    (factor : NameOrder zeroName c) : NameOrder (mulName a c) (mulName b c) :=
  transportNameOrder
    (translateNameOrderRight (positiveNameProduct (namePositiveDifference origin) factor) (mulName a c))
    (zeroNameLeft _) (nameDifferenceProductCancellation a b c)

def multiplyNamePositiveLeft {a b c : RegularDyadicName} (origin : NameOrder a b)
    (factor : NameOrder zeroName c) : NameOrder (mulName c a) (mulName c b) :=
  transportNameOrder (multiplyNamePositiveRight origin factor) (mulNameComm a c) (mulNameComm b c)

end RegularDyadicName

namespace NameOrder
open RegularDyadicName

def unitPositive : NameOrder zeroName oneName := unitNamePositive
def transport {a b c d : RegularDyadicName} := @transportNameOrder a b c d
def translateRight {a b : RegularDyadicName} := @translateNameOrderRight a b
def translateLeft {a b : RegularDyadicName} := @translateNameOrderLeft a b
def reflectTranslationRight {a b shift : RegularDyadicName} := @reflectNameTranslationRight a b shift
def positiveProduct {a b : RegularDyadicName} := @positiveNameProduct a b
def multiplyPositiveRight {a b c : RegularDyadicName} := @multiplyNamePositiveRight a b c
def multiplyPositiveLeft {a b c : RegularDyadicName} := @multiplyNamePositiveLeft a b c

end NameOrder

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder
#print axioms RelationalPerimeter.Constitution.Reals.NameApartness
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.transportNameOrder
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.transportNameApartness
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.irreflexive
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.refine
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.asymmetric
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.cotransitive
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.transitive
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.refutesEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.NameApartness.symm
#print axioms RelationalPerimeter.Constitution.Reals.NameApartness.irreflexive
#print axioms RelationalPerimeter.Constitution.Reals.NameApartness.cotransitive
#print axioms RelationalPerimeter.Constitution.Reals.NameDensityWitness
#print axioms RelationalPerimeter.Constitution.Reals.NameNaturalBounds
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameDensity
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameNaturalBounds
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameReadoutsNear
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameReadout
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.addNameReadout
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.negNameReadout
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameSampleNear
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameComm
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameOneRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameOneLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameZeroRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameZeroLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameProbeAmplitudeNeg
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameNegRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameNegLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameAssociativityPrecisions
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameAssoc
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameDistributivityPrecisions
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameDistributeLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.mulNameDistributeRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.unitNamePositive
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.translateNameOrderRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.ReciprocalNameDomain
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reciprocalName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseSourceBeyond
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseNameDomain
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseName
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reciprocalNameProductNear
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reciprocalNameUnitRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reciprocalNameUnitLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameInverseUnique
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reciprocalNameCongr
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reciprocalNameWitnessIndependent
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseNameUnitRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseNameUnitLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseNameCongr
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.inverseNameWitnessIndependent
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.translateNameOrderLeft
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameAddCancellation
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.reflectNameTranslationRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.namePositiveAt
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.positiveNameProduct
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.namePositiveDifference
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.nameDifferenceProductCancellation
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.multiplyNamePositiveRight
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicName.multiplyNamePositiveLeft
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.unitPositive
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.transport
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.translateRight
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.translateLeft
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.reflectTranslationRight
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.positiveProduct
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.multiplyPositiveRight
#print axioms RelationalPerimeter.Constitution.Reals.NameOrder.multiplyPositiveLeft
/- AXIOM_AUDIT_END -/
