import RelationalPerimeter.Constitution.Reals.DyadicArithmetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Constructive signed multiplication and probe-derived amplitude

Bounds concern the signed value at a recorded common scale, never the sum of
the two components of an arbitrary fine, non-normalized representation.
-/

namespace RelationalPerimeter.Constitution.Reals

theorem mulDistributeRight (a b c : Nat) : (a + b) * c = a * c + b * c :=
  (Nat.mul_comm _ _).trans ((Nat.mul_add _ _ _).trans
    ((congrArg (fun x => x + c * b) (Nat.mul_comm c a)).trans
      (congrArg (fun x => a * c + x) (Nat.mul_comm c b))))

theorem mulAssociate (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      calc
        (a * b) * (c + 1) = (a * b) * c + a * b := Nat.mul_succ _ _
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add _ _ _).symm
        _ = a * (b * (c + 1)) := congrArg (Nat.mul a) (Nat.mul_succ _ _).symm

theorem addCongruence {a b c d : Nat} (first : a = b) (second : c = d) : a + c = b + d :=
  (congrArg (fun x => x + c) first).trans (congrArg (fun x => b + x) second)

theorem leCancelLeft {a b c : Nat} (bound : a + b ≤ a + c) : b ≤ c := by
  rw [Nat.add_comm a b, Nat.add_comm a c] at bound
  exact leCancelRight bound

theorem offsetOfLe {a b : Nat} (bound : a ≤ b) : ∃ extra, b = a + extra := by
  induction bound with
  | refl => exact ⟨0, rfl⟩
  | @step b bound ih =>
      obtain ⟨extra, equality⟩ := ih
      exact ⟨extra + 1, congrArg Nat.succ equality⟩

theorem probeSignedBound (x xn y yn tolerance bound extra : Nat)
    (near : x + yn ≤ y + xn + tolerance) (probe : y ≤ bound) :
    x ≤ xn + (bound + extra + tolerance) := by
  calc
    x ≤ x + yn := Nat.le_add_right _ _
    _ ≤ y + xn + tolerance := near
    _ ≤ bound + xn + tolerance := Nat.add_le_add (Nat.add_le_add probe (Nat.le_refl _)) (Nat.le_refl _)
    _ ≤ (bound + extra) + xn + tolerance :=
      Nat.add_le_add (Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_refl _)) (Nat.le_refl _)
    _ = xn + (bound + extra + tolerance) := by
      rw [Nat.add_comm (bound + extra) xn, Nat.add_assoc]

theorem scaleNat_mul_right (a b extra : Nat) :
    scaleNat (a * b) extra = scaleNat a extra * b := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      change scaleNat (a * b) extra + scaleNat (a * b) extra = _
      rw [ih]
      exact (mulDistributeRight _ _ _).symm

theorem scaleNat_mul_left (a b extra : Nat) :
    scaleNat (a * b) extra = a * scaleNat b extra := by
  rw [Nat.mul_comm, scaleNat_mul_right, Nat.mul_comm]

theorem scaleNat_mul_both (a b first second : Nat) :
    scaleNat (a * b) (first + second) = scaleNat a first * scaleNat b second := by
  rw [scaleNat_addSteps, scaleNat_mul_right, scaleNat_mul_left]

theorem scaleNat_eq_mul (value extra : Nat) : scaleNat value extra = value * powerOfTwo extra := by
  have exact := scaleNat_mul_left value 1 extra
  rw [Nat.mul_one] at exact
  exact exact

theorem powerOfTwo_add_mul (first second : Nat) :
    powerOfTwo (first + second) = powerOfTwo first * powerOfTwo second := by
  exact (powerOfTwo_add first second).trans (scaleNat_eq_mul _ _)

theorem scaleNat_extension (value base extra : Nat) :
    scaleNat value base ≤ scaleNat value (base + extra) := by
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem nat_le_powerOfTwo (value : Nat) : value ≤ powerOfTwo value := by
  induction value with
  | zero => exact Nat.zero_le _
  | succ value ih =>
      have positive : 1 ≤ powerOfTwo value := by
        have h := powerOfTwo_extension 0 value
        rw [Nat.zero_add] at h
        exact h
      change value + 1 ≤ powerOfTwo value + powerOfTwo value
      exact Nat.add_le_add ih positive

def PrecisionExtension.ofLe : {coarse fine : Nat} → coarse ≤ fine → PrecisionExtension coarse fine
  | 0, fine, _ => ⟨fine, Nat.zero_add _⟩
  | _ + 1, 0, impossible => nomatch impossible
  | _ + 1, _ + 1, bound => (PrecisionExtension.ofLe (Nat.le_of_succ_le_succ bound)).succ

def PrecisionExtension.refine (precision bound : Nat) : PrecisionExtension precision (precision + 1 + bound) :=
  (PrecisionExtension.next precision).trans (PrecisionExtension.first (precision + 1) bound)

def precisionPool : List Nat → Nat
  | [] => 0
  | first :: rest => first + precisionPool rest

inductive PrecisionMember (precision : Nat) : List Nat → Type
  | here {rest : List Nat} : PrecisionMember precision (precision :: rest)
  | there {first : Nat} {rest : List Nat} : PrecisionMember precision rest → PrecisionMember precision (first :: rest)

def PrecisionMember.extension {precision : Nat} : {pool : List Nat} →
    PrecisionMember precision pool → PrecisionExtension precision (precisionPool pool)
  | _ :: _, .here => PrecisionExtension.first _ _
  | first :: rest, .there member => member.extension.trans (PrecisionExtension.second first (precisionPool rest))

/-- A finite probe determines an integer bound, not a fine-code size bound. -/
def probeAmplitude (probe : SignedDyadicCode) : Nat := probe.positive + probe.negative + 1

structure Amplitude (bound : Nat) (code : SignedDyadicCode) where
  common : Nat
  extra : Nat
  scaleExact : code.scale + extra = common
  positiveBound : liftedPositive code extra ≤ liftedNegative code extra + scaleNat bound common
  negativeBound : liftedNegative code extra ≤ liftedPositive code extra + scaleNat bound common

namespace Amplitude

def fromProbe {code probe : SignedDyadicCode} (near : Near 0 code probe) :
    Amplitude (probeAmplitude probe) code := by
  have hp : liftedPositive probe near.scale.rightExtra ≤ scaleNat probe.positive near.scale.common := by
    rw [← near.scale.rightExact, Nat.add_comm probe.scale near.scale.rightExtra]
    exact scaleNat_extension _ _ _
  have hn : liftedNegative probe near.scale.rightExtra ≤ scaleNat probe.negative near.scale.common := by
    rw [← near.scale.rightExact, Nat.add_comm probe.scale near.scale.rightExtra]
    exact scaleNat_extension _ _ _
  have precision : near.precisionExtra = near.scale.common :=
    (Nat.zero_add _).symm.trans near.precisionExact
  refine ⟨near.scale.common, near.scale.leftExtra, near.scale.leftExact, ?_, ?_⟩
  · have h := near.leftBound
    rw [precision] at h
    change liftedPositive code _ ≤ liftedNegative code _ + scaleNat (probe.positive + probe.negative + 1) _
    rw [scaleNat_additive, scaleNat_additive]
    dsimp only [powerOfTwo] at h
    exact probeSignedBound _ _ _ _ _ _ _ h hp
  · have h := near.rightBound
    rw [precision] at h
    change liftedNegative code _ ≤ liftedPositive code _ + scaleNat (probe.positive + probe.negative + 1) _
    rw [scaleNat_additive, scaleNat_additive]
    dsimp only [powerOfTwo] at h
    rw [Nat.add_comm (liftedPositive probe near.scale.rightExtra)
      (liftedNegative code near.scale.leftExtra),
      Nat.add_comm (liftedPositive code near.scale.leftExtra)
        (liftedNegative probe near.scale.rightExtra)] at h
    have exact := probeSignedBound _ _ _ _ _ _ (scaleNat probe.positive near.scale.common) h hn
    rw [Nat.add_comm (scaleNat probe.negative _) (scaleNat probe.positive _)] at exact
    exact exact

def liftCommon {bound : Nat} {code : SignedDyadicCode}
    (amplitude : Amplitude bound code) (extra : Nat) : Amplitude bound code where
  common := amplitude.common + extra
  extra := amplitude.extra + extra
  scaleExact := (Nat.add_assoc _ _ _).symm.trans (congrArg (fun x => x + extra) amplitude.scaleExact)
  positiveBound := by
    have h := scaleNat_monotone amplitude.positiveBound extra
    rw [scaleNat_additive] at h
    rw [liftedPositive_addSteps, liftedNegative_addSteps, scaleNat_addSteps]
    exact h
  negativeBound := by
    have h := scaleNat_monotone amplitude.negativeBound extra
    rw [scaleNat_additive] at h
    rw [liftedPositive_addSteps, liftedNegative_addSteps, scaleNat_addSteps]
    exact h

end Amplitude

/-- Signed errors multiply by signed amplitudes; cancellation is respected. -/
theorem signedCrossProductBound (a c bp bn tolerance magnitude : Nat)
    (ac : a ≤ c + tolerance) (ca : c ≤ a + tolerance)
    (positive : bp ≤ bn + magnitude) (negative : bn ≤ bp + magnitude) :
    a * bp + c * bn ≤ c * bp + a * bn + tolerance * magnitude := by
  cases Nat.le_total a c with
  | inl h =>
      obtain ⟨difference, equality⟩ := offsetOfLe h
      rw [equality] at ca ⊢
      have small : difference ≤ tolerance := leCancelLeft ca
      have first := Nat.mul_le_mul_left difference negative
      have second := Nat.mul_le_mul_right magnitude small
      rw [Nat.mul_add] at first
      have combined := Nat.le_trans first (Nat.add_le_add (Nat.le_refl _) second)
      calc
        a * bp + (a + difference) * bn = (a * bp + a * bn) + difference * bn := by
          rw [mulDistributeRight, Nat.add_assoc]
        _ ≤ (a * bp + a * bn) + (difference * bp + tolerance * magnitude) :=
          Nat.add_le_add (Nat.le_refl _) combined
        _ = (a + difference) * bp + a * bn + tolerance * magnitude := by
          rw [addPairExchange, ← Nat.add_assoc, ← mulDistributeRight]
  | inr h =>
      obtain ⟨difference, equality⟩ := offsetOfLe h
      rw [equality] at ac ⊢
      have small : difference ≤ tolerance := leCancelLeft ac
      have first := Nat.mul_le_mul_left difference positive
      have second := Nat.mul_le_mul_right magnitude small
      rw [Nat.mul_add] at first
      have combined := Nat.le_trans first (Nat.add_le_add (Nat.le_refl _) second)
      calc
        (c + difference) * bp + c * bn = (c * bp + c * bn) + difference * bp := by
          rw [mulDistributeRight, addSwapMiddle]
        _ ≤ (c * bp + c * bn) + (difference * bn + tolerance * magnitude) :=
          Nat.add_le_add (Nat.le_refl _) combined
        _ = c * bp + (c + difference) * bn + tolerance * magnitude := by
          rw [Nat.add_assoc, ← Nat.add_assoc (c * bn), ← mulDistributeRight, ← Nat.add_assoc]

namespace SignedDyadicCode

def mul (left right : SignedDyadicCode) : SignedDyadicCode :=
  ⟨left.positive * right.positive + left.negative * right.negative,
    left.positive * right.negative + left.negative * right.positive,
    left.scale + right.scale⟩

theorem mul_positive (left right : SignedDyadicCode) (first second : Nat) :
    liftedPositive (left.mul right) (first + second) =
      liftedPositive left first * liftedPositive right second +
        liftedNegative left first * liftedNegative right second := by
  exact (scaleNat_additive _ _ _).trans
    (addCongruence (scaleNat_mul_both _ _ _ _) (scaleNat_mul_both _ _ _ _))

theorem mul_negative (left right : SignedDyadicCode) (first second : Nat) :
    liftedNegative (left.mul right) (first + second) =
      liftedPositive left first * liftedNegative right second +
        liftedNegative left first * liftedPositive right second := by
  exact (scaleNat_additive _ _ _).trans
    (addCongruence (scaleNat_mul_both _ _ _ _) (scaleNat_mul_both _ _ _ _))

theorem extensionality {first second : SignedDyadicCode}
    (hp : first.positive = second.positive) (hn : first.negative = second.negative)
    (hs : first.scale = second.scale) : first = second := by
  cases first; cases second; cases hp; cases hn; cases hs; rfl

theorem mul_comm_exact (left right : SignedDyadicCode) : left.mul right = right.mul left := by
  apply extensionality
  · exact addCongruence (Nat.mul_comm _ _) (Nat.mul_comm _ _)
  · exact (addCongruence (Nat.mul_comm _ _) (Nat.mul_comm _ _)).trans (Nat.add_comm _ _)
  · exact Nat.add_comm _ _

theorem mul_assoc_exact (a b c : SignedDyadicCode) : (a.mul b).mul c = a.mul (b.mul c) := by
  apply extensionality
  · change (a.positive * b.positive + a.negative * b.negative) * c.positive +
      (a.positive * b.negative + a.negative * b.positive) * c.negative =
      a.positive * (b.positive * c.positive + b.negative * c.negative) +
      a.negative * (b.positive * c.negative + b.negative * c.positive)
    rw [mulDistributeRight, mulDistributeRight, Nat.mul_add, Nat.mul_add,
      mulAssociate, mulAssociate, mulAssociate, mulAssociate]
    exact (addPairExchange _ _ _ _).trans (congrArg (Nat.add _) (Nat.add_comm _ _))
  · change (a.positive * b.positive + a.negative * b.negative) * c.negative +
      (a.positive * b.negative + a.negative * b.positive) * c.positive =
      a.positive * (b.positive * c.negative + b.negative * c.positive) +
      a.negative * (b.positive * c.positive + b.negative * c.negative)
    rw [mulDistributeRight, mulDistributeRight, Nat.mul_add, Nat.mul_add,
      mulAssociate, mulAssociate, mulAssociate, mulAssociate]
    exact (addPairExchange _ _ _ _).trans (congrArg (Nat.add _) (Nat.add_comm _ _))
  · exact Nat.add_assoc _ _ _

theorem mul_one_exact (code : SignedDyadicCode) : code.mul one = code := by
  cases code
  rename_i positive negative scale
  change SignedDyadicCode.mk (positive * 1 + negative * 0) (positive * 0 + negative * 1) scale = _
  rw [Nat.mul_one, Nat.mul_zero, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]

def mul_zero (code : SignedDyadicCode) : SameValue (code.mul zero) zero where
  scale := ⟨code.scale, 0, code.scale, rfl, Nat.zero_add _⟩
  exact := by
    change (code.positive * 0 + code.negative * 0) + scaleNat 0 code.scale =
      scaleNat 0 code.scale + (code.positive * 0 + code.negative * 0)
    rw [Nat.mul_zero, Nat.mul_zero, scaleNat_zero]

theorem mul_neg_exact (left right : SignedDyadicCode) :
    left.mul right.neg = (left.mul right).neg := by
  rfl

def mul_add (a b c : SignedDyadicCode) : SameValue (a.mul (b.add c)) ((a.mul b).add (a.mul c)) := by
  have hp : liftedPositive (a.mul (b.add c)) a.scale =
      liftedPositive ((a.mul b).add (a.mul c)) 0 := by
    change liftedPositive (a.mul (b.add c)) (a.scale + 0) = _
    rw [mul_positive, add_positive, add_positive, Nat.add_zero, Nat.add_zero]
    change _ = liftedPositive (a.mul b) (a.scale + c.scale) + liftedPositive (a.mul c) (a.scale + b.scale)
    rw [mul_positive, mul_positive]
    change _ + liftedNegative a a.scale * liftedNegative (b.add c) 0 = _
    rw [add_negative, Nat.add_zero, Nat.add_zero, Nat.mul_add, Nat.mul_add]
    exact addPairExchange _ _ _ _
  have hn : liftedNegative (a.mul (b.add c)) a.scale =
      liftedNegative ((a.mul b).add (a.mul c)) 0 := by
    change liftedNegative (a.mul (b.add c)) (a.scale + 0) = _
    rw [mul_negative, add_negative, add_negative, Nat.add_zero, Nat.add_zero]
    change _ = liftedNegative (a.mul b) (a.scale + c.scale) + liftedNegative (a.mul c) (a.scale + b.scale)
    rw [mul_negative, mul_negative]
    change _ + liftedNegative a a.scale * liftedPositive (b.add c) 0 = _
    rw [add_positive, Nat.add_zero, Nat.add_zero, Nat.mul_add, Nat.mul_add]
    exact addPairExchange _ _ _ _
  refine ⟨⟨(a.scale + b.scale) + (a.scale + c.scale), a.scale, 0, ?_, rfl⟩, ?_⟩
  · change (a.scale + (b.scale + c.scale)) + a.scale = _
    rw [← Nat.add_assoc, addSwapMiddle, Nat.add_assoc]
  · exact addCongruence hp hn.symm

end SignedDyadicCode

theorem addOuterExchange (a b c d : Nat) : (a + b) + (c + d) = (a + d) + (c + b) :=
  (addPairExchange _ _ _ _).trans
    ((congrArg (Nat.add _) (Nat.add_comm b d)).trans (addPairExchange _ _ _ _))

theorem signedProductRegroup (ap an cp cn bp bn : Nat) :
    (ap * bp + an * bn) + (cp * bn + cn * bp) =
      (ap + cn) * bp + (cp + an) * bn := by
  rw [mulDistributeRight, mulDistributeRight]
  exact addOuterExchange _ _ _ _

theorem productToleranceBudget (bound first second : Nat) :
    powerOfTwo first * scaleNat bound second ≤ powerOfTwo (bound + first + second) := by
  rw [scaleNat_eq_mul, ← mulAssociate, Nat.mul_comm (powerOfTwo first) bound]
  have h := Nat.mul_le_mul_right (powerOfTwo first) (nat_le_powerOfTwo bound)
  have result := Nat.mul_le_mul_right (powerOfTwo second) h
  rw [← powerOfTwo_add_mul, ← powerOfTwo_add_mul] at result
  exact result

namespace SameValue

def mulRight {left right : SignedDyadicCode} (same : SameValue left right)
    (code : SignedDyadicCode) : SameValue (left.mul code) (right.mul code) where
  scale := ⟨same.scale.common + code.scale, same.scale.leftExtra,
    same.scale.rightExtra,
    (addSwapMiddle _ _ _).trans (congrArg (fun n => n + code.scale) same.scale.leftExact),
    (addSwapMiddle _ _ _).trans (congrArg (fun n => n + code.scale) same.scale.rightExact)⟩
  exact := by
    change liftedPositive (left.mul code) (same.scale.leftExtra + 0) +
      liftedNegative (right.mul code) (same.scale.rightExtra + 0) = _
    rw [SignedDyadicCode.mul_positive, SignedDyadicCode.mul_negative]
    change _ = liftedPositive (right.mul code) (same.scale.rightExtra + 0) +
      liftedNegative (left.mul code) (same.scale.leftExtra + 0)
    rw [SignedDyadicCode.mul_positive, SignedDyadicCode.mul_negative,
      signedProductRegroup, signedProductRegroup, same.exact]

def mulLeft {left right : SignedDyadicCode} (same : SameValue left right)
    (code : SignedDyadicCode) : SameValue (code.mul left) (code.mul right) := by
  rw [SignedDyadicCode.mul_comm_exact code left, SignedDyadicCode.mul_comm_exact code right]
  exact same.mulRight code

def mul {a b c d : SignedDyadicCode} (left : SameValue a c) (right : SameValue b d) :
    SameValue (a.mul b) (c.mul d) := (left.mulRight b).trans (right.mulLeft c)

end SameValue

namespace Near

def mulRight {precision bound : Nat} {left right code : SignedDyadicCode}
    (near : Near (precision + bound) left right) (amplitude : Amplitude bound code) :
    Near precision (left.mul code) (right.mul code) := by
  refine {
    scale := ⟨near.scale.common + amplitude.common,
      near.scale.leftExtra + amplitude.extra, near.scale.rightExtra + amplitude.extra, ?_, ?_⟩
    precisionExtra := bound + near.precisionExtra + amplitude.common
    precisionExact := ?_
    leftBound := ?_
    rightBound := ?_ }
  · exact (addPairExchange _ _ _ _).trans (addCongruence near.scale.leftExact amplitude.scaleExact)
  · exact (addPairExchange _ _ _ _).trans (addCongruence near.scale.rightExact amplitude.scaleExact)
  · exact ((Nat.add_assoc _ _ _).symm.trans
      (congrArg (fun n => n + amplitude.common) (Nat.add_assoc _ _ _).symm)).trans
        (congrArg (fun n => n + amplitude.common) near.precisionExact)
  · dsimp only
    rw [SignedDyadicCode.mul_positive, SignedDyadicCode.mul_negative,
      SignedDyadicCode.mul_positive, SignedDyadicCode.mul_negative,
      signedProductRegroup, signedProductRegroup]
    exact Nat.le_trans (signedCrossProductBound _ _ _ _ _ _ near.leftBound near.rightBound
      amplitude.positiveBound amplitude.negativeBound)
      (Nat.add_le_add (Nat.le_refl _) (productToleranceBudget _ _ _))
  · dsimp only
    rw [SignedDyadicCode.mul_positive, SignedDyadicCode.mul_negative,
      SignedDyadicCode.mul_positive, SignedDyadicCode.mul_negative,
      signedProductRegroup, signedProductRegroup]
    exact Nat.le_trans (signedCrossProductBound _ _ _ _ _ _ near.rightBound near.leftBound
      amplitude.positiveBound amplitude.negativeBound)
      (Nat.add_le_add (Nat.le_refl _) (productToleranceBudget _ _ _))

def mulLeft {precision bound : Nat} {left right code : SignedDyadicCode}
    (near : Near (precision + bound) left right) (amplitude : Amplitude bound code) :
    Near precision (code.mul left) (code.mul right) := by
  rw [SignedDyadicCode.mul_comm_exact code left, SignedDyadicCode.mul_comm_exact code right]
  exact near.mulRight amplitude

/-- Each factor spends the bound obtained by probing the other factor. -/
def mul {precision leftBound rightBound : Nat} {a b c d : SignedDyadicCode}
    (left : Near (precision + 1 + rightBound) a c)
    (right : Near (precision + 1 + leftBound) b d)
    (bAmplitude : Amplitude rightBound b) (cAmplitude : Amplitude leftBound c) :
    Near precision (a.mul b) (c.mul d) :=
  compose (left.mulRight bAmplitude) (right.mulLeft cAmplitude)

end Near

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.mulDistributeRight
#print axioms RelationalPerimeter.Constitution.Reals.mulAssociate
#print axioms RelationalPerimeter.Constitution.Reals.addCongruence
#print axioms RelationalPerimeter.Constitution.Reals.leCancelLeft
#print axioms RelationalPerimeter.Constitution.Reals.offsetOfLe
#print axioms RelationalPerimeter.Constitution.Reals.probeSignedBound
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_mul_right
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_mul_left
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_mul_both
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_eq_mul
#print axioms RelationalPerimeter.Constitution.Reals.powerOfTwo_add_mul
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_extension
#print axioms RelationalPerimeter.Constitution.Reals.nat_le_powerOfTwo
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.ofLe
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.refine
#print axioms RelationalPerimeter.Constitution.Reals.precisionPool
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionMember
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionMember.extension
#print axioms RelationalPerimeter.Constitution.Reals.probeAmplitude
#print axioms RelationalPerimeter.Constitution.Reals.Amplitude
#print axioms RelationalPerimeter.Constitution.Reals.Amplitude.fromProbe
#print axioms RelationalPerimeter.Constitution.Reals.Amplitude.liftCommon
#print axioms RelationalPerimeter.Constitution.Reals.signedCrossProductBound
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_positive
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_negative
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_comm_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_assoc_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_one_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_zero
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_neg_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.mul_add
#print axioms RelationalPerimeter.Constitution.Reals.addOuterExchange
#print axioms RelationalPerimeter.Constitution.Reals.signedProductRegroup
#print axioms RelationalPerimeter.Constitution.Reals.productToleranceBudget
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.mulRight
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.mulLeft
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.mul
#print axioms RelationalPerimeter.Constitution.Reals.Near.mulRight
#print axioms RelationalPerimeter.Constitution.Reals.Near.mulLeft
#print axioms RelationalPerimeter.Constitution.Reals.Near.mul
/- AXIOM_AUDIT_END -/
