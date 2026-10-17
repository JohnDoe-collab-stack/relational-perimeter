import RelationalPerimeter.Constitution.Reals.RelationalRealAddition

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Numerical laws are downstream of the owned probe/refinement/action chain.
They never identify trees, operand roles, archives or occurrences. -/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealAddition
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime
open RelationalRealMultiplication
variable {P : CircularPresentation} {baseDepth : Nat}

def readoutAmplitude (real : Real P baseDepth) (p : Nat) :
    Amplitude (probeAmplitude (readout real 0)) (readout real p) :=
  Amplitude.fromProbe (readoutsNear real 0 p 0 ⟨p, Nat.zero_add _⟩ (PrecisionExtension.refl 0))

/-- Compare an actual product reply with independently specified sufficiently
fine operand replies. This is a proof about production, not its definition. -/
def mul_sampleNear (left right : Real P baseDepth) (p response l r : Nat)
    (responseBeyond : PrecisionExtension p response)
    (leftBeyond : PrecisionExtension (p + 1 + probeAmplitude (readout right 0)) l)
    (rightBeyond : PrecisionExtension (p + 1 + probeAmplitude (readout left 0)) r) :
    Near p (readout (.mul left right) response) ((readout left l).mul (readout right r)) := by
  rw [mul_readout_exact]
  exact Near.mul
    (readoutsNear left _ _ _ (responseBeyond.succ.add (PrecisionExtension.refl _)) leftBeyond)
    (readoutsNear right _ _ _ (responseBeyond.succ.add (PrecisionExtension.refl _)) rightBeyond)
    (readoutAmplitude right _) (readoutAmplitude left _)

def mul_congr {a b c d : Real P baseDepth} (first : Equivalent a c) (second : Equivalent b d) :
    Equivalent (.mul a b) (.mul c d) where
  threshold p := first.threshold (p + 1 + probeAmplitude (readout b 0)) +
    second.threshold (p + 1 + probeAmplitude (readout c 0))
  near := by
    intro p l r hl hr
    rw [mul_readout_exact, mul_readout_exact]
    let x := first.threshold (p + 1 + probeAmplitude (readout b 0))
    let y := second.threshold (p + 1 + probeAmplitude (readout c 0))
    exact Near.mul
      (first.near _ _ _
        (((PrecisionExtension.first x y).trans hl).trans (PrecisionExtension.refine l _))
        (((PrecisionExtension.first x y).trans hr).trans (PrecisionExtension.refine r _)))
      (second.near _ _ _
        (((PrecisionExtension.second x y).trans hl).trans (PrecisionExtension.refine l _))
        (((PrecisionExtension.second x y).trans hr).trans (PrecisionExtension.refine r _)))
      (readoutAmplitude b _) (readoutAmplitude c _)

def mul_comm (left right : Real P baseDepth) : Equivalent (.mul left right) (.mul right left) :=
  Equivalent.ofExact (fun p => by
    rw [mul_readout_exact, mul_readout_exact, SignedDyadicCode.mul_comm_exact]
    exact SameValue.refl _)

def mul_one (real : Real P baseDepth) : Equivalent (.mul real (one P baseDepth)) real where
  threshold := fun p => p
  near := by
    intro p l r hl hr
    rw [mul_readout_exact]
    have same : SameValue
        ((readout real (l + 1 + probeAmplitude (readout (one P baseDepth) 0))).mul
          (readout (one P baseDepth) (l + 1 + probeAmplitude (readout real 0))))
        (readout real (l + 1 + probeAmplitude (readout (one P baseDepth) 0))) := by
      apply SameValue.trans (SameValue.mul (SameValue.refl _) (constant_readout SignedDyadicCode.one _))
      rw [SignedDyadicCode.mul_one_exact]
      exact SameValue.refl _
    exact Near.ofSameLeft same (readoutsNear real p _ r (hl.trans (PrecisionExtension.refine l _)) hr)

def one_mul (real : Real P baseDepth) : Equivalent (.mul (one P baseDepth) real) real :=
  (mul_comm _ _).trans (mul_one real)

def mul_zero (real : Real P baseDepth) : Equivalent (.mul real (zero P baseDepth)) (zero P baseDepth) :=
  Equivalent.ofExact (fun p => by
    rw [mul_readout_exact]
    exact ((SameValue.mul (SameValue.refl _) (constant_readout SignedDyadicCode.zero _)).trans
      (SignedDyadicCode.mul_zero _)).trans (constant_readout SignedDyadicCode.zero p).symm)

def zero_mul (real : Real P baseDepth) : Equivalent (.mul (zero P baseDepth) real) (zero P baseDepth) :=
  (mul_comm _ _).trans (mul_zero real)

theorem probeAmplitude_neg (code : SignedDyadicCode) : probeAmplitude code.neg = probeAmplitude code :=
  congrArg (fun n => n + 1) (Nat.add_comm _ _)

def mul_neg (a b : Real P baseDepth) : Equivalent (.mul a (.neg b)) (.neg (.mul a b)) :=
  Equivalent.ofExact (fun p => by
    rw [mul_readout_exact, neg_readout_exact (.mul a b) p, mul_readout_exact,
      neg_readout_exact b 0, probeAmplitude_neg, neg_readout_exact b,
      SignedDyadicCode.mul_neg_exact]
    exact SameValue.refl _)

def neg_mul (a b : Real P baseDepth) : Equivalent (.mul (.neg a) b) (.neg (.mul a b)) :=
  (mul_comm _ _).trans ((mul_neg b a).trans (neg_congr (mul_comm b a)))

/-- A finite list of explicit error requirements, not a magic global bound. -/
def associativityPrecisions (a b c : Real P baseDepth) (p : Nat) : List Nat :=
  let ba := probeAmplitude (readout a 0)
  let bb := probeAmplitude (readout b 0)
  let bc := probeAmplitude (readout c 0)
  let bab := probeAmplitude (readout (.mul a b) 0)
  let bbc := probeAmplitude (readout (.mul b c) 0)
  [p + 2, p + 3 + bc, p + 3 + bab, p + 2 + bc,
    (p + 2 + bc) + 1 + bb, (p + 2 + bc) + 1 + ba,
    p + 3 + bbc, p + 3 + ba, p + 2 + ba,
    (p + 2 + ba) + 1 + bc, (p + 2 + ba) + 1 + bb]

def mul_assoc (a b c : Real P baseDepth) : Equivalent (.mul (.mul a b) c) (.mul a (.mul b c)) where
  threshold p := precisionPool (associativityPrecisions a b c p)
  near := by
    intro p l r hl hr
    let pool := associativityPrecisions a b c p
    let k := precisionPool pool
    have h0 : PrecisionMember (p + 2) pool := .here
    have h1 : PrecisionMember (p + 3 + probeAmplitude (readout c 0)) pool := .there .here
    have h2 : PrecisionMember (p + 3 + probeAmplitude (readout (.mul a b) 0)) pool := .there (.there .here)
    have h3 : PrecisionMember (p + 2 + probeAmplitude (readout c 0)) pool := .there (.there (.there .here))
    have h4 : PrecisionMember ((p + 2 + probeAmplitude (readout c 0)) + 1 + probeAmplitude (readout b 0)) pool :=
      .there (.there (.there (.there .here)))
    have h5 : PrecisionMember ((p + 2 + probeAmplitude (readout c 0)) + 1 + probeAmplitude (readout a 0)) pool :=
      .there (.there (.there (.there (.there .here))))
    have h6 : PrecisionMember (p + 3 + probeAmplitude (readout (.mul b c) 0)) pool :=
      .there (.there (.there (.there (.there (.there .here)))))
    have h7 : PrecisionMember (p + 3 + probeAmplitude (readout a 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there .here))))))
    have h8 : PrecisionMember (p + 2 + probeAmplitude (readout a 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there (.there .here)))))))
    have h9 : PrecisionMember ((p + 2 + probeAmplitude (readout a 0)) + 1 + probeAmplitude (readout c 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    have h10 : PrecisionMember ((p + 2 + probeAmplitude (readout a 0)) + 1 + probeAmplitude (readout b 0)) pool :=
      .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    have outerLeft := mul_sampleNear (.mul a b) c (p + 2) l k k (h0.extension.trans hl) h1.extension h2.extension
    have innerLeft := (mul_sampleNear a b (p + 2 + probeAmplitude (readout c 0)) k k k
      h3.extension h4.extension h5.extension).mulRight (readoutAmplitude c k)
    have outerRight := mul_sampleNear a (.mul b c) (p + 2) r k k (h0.extension.trans hr) h6.extension h7.extension
    have innerRight := (mul_sampleNear b c (p + 2 + probeAmplitude (readout a 0)) k k k
      h8.extension h9.extension h10.extension).mulLeft (readoutAmplitude a k)
    have left := Near.compose outerLeft innerLeft
    have right := Near.compose outerRight innerRight
    have exact : SameValue (((readout a k).mul (readout b k)).mul (readout c k))
        ((readout a k).mul ((readout b k).mul (readout c k))) := by
      rw [SignedDyadicCode.mul_assoc_exact]
      exact SameValue.refl _
    exact Near.compose (Near.ofSameRight left exact) right.symm

def distributivityPrecisions (a b c : Real P baseDepth) (p : Nat) : List Nat :=
  let ba := probeAmplitude (readout a 0)
  [p + 2, p + 3 + probeAmplitude (readout (.add b c) 0), p + 3 + ba,
    (p + 2 + ba) + 1, p + 3 + probeAmplitude (readout b 0), p + 3 + probeAmplitude (readout c 0)]

def mul_add (a b c : Real P baseDepth) : Equivalent (.mul a (.add b c)) (.add (.mul a b) (.mul a c)) where
  threshold p := precisionPool (distributivityPrecisions a b c p)
  near := by
    intro p l r hl hr
    let pool := distributivityPrecisions a b c p
    let k := precisionPool pool
    have h0 : PrecisionMember (p + 2) pool := .here
    have h1 : PrecisionMember (p + 3 + probeAmplitude (readout (.add b c) 0)) pool := .there .here
    have h2 : PrecisionMember (p + 3 + probeAmplitude (readout a 0)) pool := .there (.there .here)
    have h3 : PrecisionMember ((p + 2 + probeAmplitude (readout a 0)) + 1) pool := .there (.there (.there .here))
    have h4 : PrecisionMember (p + 3 + probeAmplitude (readout b 0)) pool := .there (.there (.there (.there .here)))
    have h5 : PrecisionMember (p + 3 + probeAmplitude (readout c 0)) pool := .there (.there (.there (.there (.there .here))))
    have outer := mul_sampleNear a (.add b c) (p + 2) l k k (h0.extension.trans hl) h1.extension h2.extension
    have sumNear : Near (p + 2 + probeAmplitude (readout a 0))
        (readout (.add b c) k) ((readout b k).add (readout c k)) := by
      rw [add_readout_exact]
      exact Near.add
        (readoutsNear b _ _ _ (h3.extension.trans (PrecisionExtension.next k)) h3.extension)
        (readoutsNear c _ _ _ (h3.extension.trans (PrecisionExtension.next k)) h3.extension)
    have left := Near.compose outer (sumNear.mulLeft (readoutAmplitude a k))
    have right : Near (p + 1) (readout (.add (.mul a b) (.mul a c)) r)
        (((readout a k).mul (readout b k)).add ((readout a k).mul (readout c k))) := by
      rw [add_readout_exact]
      exact Near.add
        (mul_sampleNear a b (p + 2) (r + 1) k k
          ((h0.extension.trans hr).trans (PrecisionExtension.next r)) h4.extension h2.extension)
        (mul_sampleNear a c (p + 2) (r + 1) k k
          ((h0.extension.trans hr).trans (PrecisionExtension.next r)) h5.extension h2.extension)
    exact Near.compose (Near.ofSameRight left (SignedDyadicCode.mul_add _ _ _)) right.symm

def add_mul (a b c : Real P baseDepth) : Equivalent (.mul (.add a b) c) (.add (.mul a c) (.mul b c)) :=
  (mul_comm _ _).trans ((mul_add c a b).trans (add_congr (mul_comm c a) (mul_comm c b)))

structure MultiplicativeLaws (P : CircularPresentation) (baseDepth : Nat) where
  congruent : {a b c d : Real P baseDepth} → Equivalent a c → Equivalent b d → Equivalent (.mul a b) (.mul c d)
  commutative : (a b : Real P baseDepth) → Equivalent (.mul a b) (.mul b a)
  associative : (a b c : Real P baseDepth) → Equivalent (.mul (.mul a b) c) (.mul a (.mul b c))
  unitRight : (a : Real P baseDepth) → Equivalent (.mul a (one P baseDepth)) a
  unitLeft : (a : Real P baseDepth) → Equivalent (.mul (one P baseDepth) a) a
  zeroRight : (a : Real P baseDepth) → Equivalent (.mul a (zero P baseDepth)) (zero P baseDepth)
  zeroLeft : (a : Real P baseDepth) → Equivalent (.mul (zero P baseDepth) a) (zero P baseDepth)
  distributeLeft : (a b c : Real P baseDepth) → Equivalent (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  distributeRight : (a b c : Real P baseDepth) → Equivalent (.mul (.add a b) c) (.add (.mul a c) (.mul b c))
  negateRight : (a b : Real P baseDepth) → Equivalent (.mul a (.neg b)) (.neg (.mul a b))
  negateLeft : (a b : Real P baseDepth) → Equivalent (.mul (.neg a) b) (.neg (.mul a b))

def multiplicativeLaws (P : CircularPresentation) (baseDepth : Nat) : MultiplicativeLaws P baseDepth :=
  ⟨mul_congr, mul_comm, mul_assoc, mul_one, one_mul, mul_zero, zero_mul, mul_add, add_mul, mul_neg, neg_mul⟩

structure MultiplicativeFutureLaws (P : CircularPresentation) (baseDepth : Nat) where
  congruent : {a b c d : Real P baseDepth} → NumericalFutureEquivalent a c → NumericalFutureEquivalent b d →
    NumericalFutureEquivalent (.mul a b) (.mul c d)
  commutative : (a b : Real P baseDepth) → NumericalFutureEquivalent (.mul a b) (.mul b a)
  associative : (a b c : Real P baseDepth) → NumericalFutureEquivalent (.mul (.mul a b) c) (.mul a (.mul b c))
  unitRight : (a : Real P baseDepth) → NumericalFutureEquivalent (.mul a (one P baseDepth)) a
  unitLeft : (a : Real P baseDepth) → NumericalFutureEquivalent (.mul (one P baseDepth) a) a
  zeroRight : (a : Real P baseDepth) → NumericalFutureEquivalent (.mul a (zero P baseDepth)) (zero P baseDepth)
  zeroLeft : (a : Real P baseDepth) → NumericalFutureEquivalent (.mul (zero P baseDepth) a) (zero P baseDepth)
  distributeLeft : (a b c : Real P baseDepth) → NumericalFutureEquivalent (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  distributeRight : (a b c : Real P baseDepth) → NumericalFutureEquivalent (.mul (.add a b) c) (.add (.mul a c) (.mul b c))
  negateRight : (a b : Real P baseDepth) → NumericalFutureEquivalent (.mul a (.neg b)) (.neg (.mul a b))
  negateLeft : (a b : Real P baseDepth) → NumericalFutureEquivalent (.mul (.neg a) b) (.neg (.mul a b))

def multiplicativeFutureLaws (P : CircularPresentation) (baseDepth : Nat) : MultiplicativeFutureLaws P baseDepth :=
  ⟨fun a b => (mul_congr a.toEquivalent b.toEquivalent).toFutures,
    fun a b => (mul_comm a b).toFutures, fun a b c => (mul_assoc a b c).toFutures,
    fun a => (mul_one a).toFutures, fun a => (one_mul a).toFutures,
    fun a => (mul_zero a).toFutures, fun a => (zero_mul a).toFutures,
    fun a b c => (mul_add a b c).toFutures, fun a b c => (add_mul a b c).toFutures,
    fun a b => (mul_neg a b).toFutures, fun a b => (neg_mul a b).toFutures⟩

def presentationAmplitude (presentation : EffectiveDyadicPresentation) (p : Nat) :
    Amplitude (probeAmplitude (presentation.approximation 0)) (presentation.approximation p) :=
  Amplitude.fromProbe (presentation.coherent 0 p 0 ⟨p, Nat.zero_add _⟩ (PrecisionExtension.refl 0))

/-- A downstream numerical operation; the runtime above never calls this. -/
def mulPresentation (left right : EffectiveDyadicPresentation) : EffectiveDyadicPresentation where
  approximation p := (left.approximation (p + 1 + probeAmplitude (right.approximation 0))).mul
    (right.approximation (p + 1 + probeAmplitude (left.approximation 0)))
  coherent := fun p l r hl hr => Near.mul
    (left.coherent _ _ _ (hl.succ.add (PrecisionExtension.refl _)) (hr.succ.add (PrecisionExtension.refl _)))
    (right.coherent _ _ _ (hl.succ.add (PrecisionExtension.refl _)) (hr.succ.add (PrecisionExtension.refl _)))
    (presentationAmplitude right _) (presentationAmplitude left _)

def toPresentation_mul (left right : Real P baseDepth) :
    EffectiveDyadicPresentation.Equivalent (toPresentation (.mul left right))
      (mulPresentation (toPresentation left) (toPresentation right)) where
  responseThreshold := fun p => p
  near := by
    intro p l r hl hr
    change Near p (readout (.mul left right) l) _
    rw [mul_readout_exact]
    exact (mulPresentation (toPresentation left) (toPresentation right)).coherent p l r hl hr

def realization_mul (left right : EffectiveDyadicPresentation) :
    Equivalent (.mul (ofPresentation P baseDepth left) (ofPresentation P baseDepth right))
      (ofPresentation P baseDepth (mulPresentation left right)) :=
  Equivalent.ofExact (fun p => by
    rw [mul_readout_exact, ofPresentation_readout, ofPresentation_readout,
      ofPresentation_readout, ofPresentation_readout, ofPresentation_readout]
    exact SameValue.refl _)

def mulCarrier (left right : EffectiveCauchyReal.Carrier) : EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation
    (mulPresentation (EffectiveCauchyReal.toPresentation left) (EffectiveCauchyReal.toPresentation right))

def toCarrier_mul (left right : Real P baseDepth) :
    EffectiveCauchyReal.Equivalent (toCarrier (.mul left right)) (mulCarrier (toCarrier left) (toCarrier right)) :=
  EffectiveCauchyReal.presentationEquivalentToCarrier (toPresentation_mul left right)

def realization_carrier_mul (left right : EffectiveCauchyReal.Carrier) :
    Equivalent (.mul (ofCarrier P baseDepth left) (ofCarrier P baseDepth right))
      (ofCarrier P baseDepth (mulCarrier left right)) :=
  realization_mul _ _

end RelationalPerimeter.Constitution.Reals.RelationalRealAddition

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.readoutAmplitude
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_sampleNear
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_congr
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_comm
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_one
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.one_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_zero
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.zero_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.probeAmplitude_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.associativityPrecisions
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_assoc
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.distributivityPrecisions
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.MultiplicativeLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.multiplicativeLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.MultiplicativeFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.multiplicativeFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.presentationAmplitude
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mulPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toPresentation_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.realization_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mulCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toCarrier_mul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.realization_carrier_mul
/- AXIOM_AUDIT_END -/
