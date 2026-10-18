import RelationalPerimeter.Constitution.Reals.DyadicOrder

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Constitution.Reals

theorem composeSignedBoundMixed
    {xp xn yp yn zp zn firstTolerance secondTolerance : Nat}
    (xy : xp + yn ≤ yp + xn + firstTolerance)
    (yz : yp + zn ≤ zp + yn + secondTolerance) :
    xp + zn ≤ zp + xn + (firstTolerance + secondTolerance) := by
  apply leCancelRight (c := yn)
  calc
    (xp + zn) + yn = (xp + yn) + zn := addSwapMiddle _ _ _
    _ ≤ (yp + xn + firstTolerance) + zn := Nat.add_le_add_right xy _
    _ = (yp + zn) + (xn + firstTolerance) := by
      rw [addSwapMiddle (yp + xn) firstTolerance zn, addSwapMiddle yp xn zn, Nat.add_assoc]
    _ ≤ (zp + yn + secondTolerance) + (xn + firstTolerance) := Nat.add_le_add_right yz _
    _ = (zp + xn + (firstTolerance + secondTolerance)) + yn := by
      conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sixFineOneMiddleBudget (extra : Nat) :
    6 * powerOfTwo extra + powerOfTwo (extra + 1) = powerOfTwo (extra + 3) := by
  conv => lhs; simp only [powerOfTwo_succ, Nat.succ_mul, Nat.zero_mul, Nat.zero_add, Nat.add_assoc]
  conv => rhs; simp only [powerOfTwo_succ, Nat.add_assoc]

namespace DirectedUpper

/-- Align a received bound without modifying its precision or tolerance. -/
def align {p : Nat} {x y : SignedDyadicCode} (upper : DirectedUpper p x y)
    (common : Nat) (extension : PrecisionExtension upper.scale.common common) :
    DirectedUpper p x y :=
  let raised := upper.liftCommon extension.extra
  { scale := ⟨common, raised.scale.leftExtra, raised.scale.rightExtra,
      raised.scale.leftExact.trans extension.exact, raised.scale.rightExact.trans extension.exact⟩
    precisionExtra := raised.precisionExtra
    precisionExact := raised.precisionExact.trans extension.exact
    bound := raised.bound }

/-- All seven bounds are lifted to one pool before their signed numerators
are cancelled. The six fine margins plus the middle margin spend exactly p. -/
def composeThreeOneThree {p : Nat} {a a1 a2 c b b1 b2 d : SignedDyadicCode}
    (right1 : DirectedUpper (p + 3) b b1) (right2 : DirectedUpper (p + 3) b1 b2)
    (right3 : DirectedUpper (p + 3) b2 d) (middle : DirectedUpper (p + 2) d c)
    (left3 : DirectedUpper (p + 3) c a2) (left2 : DirectedUpper (p + 3) a2 a1)
    (left1 : DirectedUpper (p + 3) a1 a) : DirectedUpper p b a := by
  let pool := [right1.scale.common, right2.scale.common, right3.scale.common,
    middle.scale.common, left3.scale.common, left2.scale.common, left1.scale.common]
  have m1 : PrecisionMember right1.scale.common pool := .here
  have m2 : PrecisionMember right2.scale.common pool := .there .here
  have m3 : PrecisionMember right3.scale.common pool := .there (.there .here)
  have m4 : PrecisionMember middle.scale.common pool := .there (.there (.there .here))
  have m5 : PrecisionMember left3.scale.common pool := .there (.there (.there (.there .here)))
  have m6 : PrecisionMember left2.scale.common pool := .there (.there (.there (.there (.there .here))))
  have m7 : PrecisionMember left1.scale.common pool := .there (.there (.there (.there (.there (.there .here)))))
  let r1 := right1.align (precisionPool pool) m1.extension
  let r2 := right2.align (precisionPool pool) m2.extension
  let r3 := right3.align (precisionPool pool) m3.extension
  let mid := middle.align (precisionPool pool) m4.extension
  let l3 := left3.align (precisionPool pool) m5.extension
  let l2 := left2.align (precisionPool pool) m6.extension
  let l1 := left1.align (precisionPool pool) m7.extension
  have e12 : r1.scale.rightExtra = r2.scale.leftExtra := addLeftCancel (r1.scale.rightExact.trans r2.scale.leftExact.symm)
  have e23 : r2.scale.rightExtra = r3.scale.leftExtra := addLeftCancel (r2.scale.rightExact.trans r3.scale.leftExact.symm)
  have e34 : r3.scale.rightExtra = mid.scale.leftExtra := addLeftCancel (r3.scale.rightExact.trans mid.scale.leftExact.symm)
  have e45 : mid.scale.rightExtra = l3.scale.leftExtra := addLeftCancel (mid.scale.rightExact.trans l3.scale.leftExact.symm)
  have e56 : l3.scale.rightExtra = l2.scale.leftExtra := addLeftCancel (l3.scale.rightExact.trans l2.scale.leftExact.symm)
  have e67 : l2.scale.rightExtra = l1.scale.leftExtra := addLeftCancel (l2.scale.rightExact.trans l1.scale.leftExact.symm)
  have t2 : r2.precisionExtra = r1.precisionExtra := addLeftCancel (r2.precisionExact.trans r1.precisionExact.symm)
  have t3 : r3.precisionExtra = r1.precisionExtra := addLeftCancel (r3.precisionExact.trans r1.precisionExact.symm)
  have t5 : l3.precisionExtra = r1.precisionExtra := addLeftCancel (l3.precisionExact.trans r1.precisionExact.symm)
  have t6 : l2.precisionExtra = r1.precisionExtra := addLeftCancel (l2.precisionExact.trans r1.precisionExact.symm)
  have t7 : l1.precisionExtra = r1.precisionExtra := addLeftCancel (l1.precisionExact.trans r1.precisionExact.symm)
  have t4 : mid.precisionExtra = r1.precisionExtra + 1 := by
    apply addLeftCancel (a := p + 2)
    calc
      (p + 2) + mid.precisionExtra = precisionPool pool := mid.precisionExact
      _ = (p + 3) + r1.precisionExtra := r1.precisionExact.symm
      _ = (p + 2) + (r1.precisionExtra + 1) := by
        rw [← Nat.add_assoc, addSwapMiddle (p + 2) r1.precisionExtra 1]
  have h2 := r2.bound
  have h3 := r3.bound
  have h4 := mid.bound
  have h5 := l3.bound
  have h6 := l2.bound
  have h7 := l1.bound
  rw [← e12, t2] at h2
  rw [← e23, t3] at h3
  rw [← e34, t4] at h4
  rw [← e45, t5] at h5
  rw [← e56, t6] at h6
  rw [← e67, t7] at h7
  have combined := composeSignedBoundMixed
    (composeSignedBoundMixed (composeSignedBoundMixed (composeSignedBoundMixed
      (composeSignedBoundMixed (composeSignedBoundMixed r1.bound h2) h3) h4) h5) h6) h7
  have budget : (((((powerOfTwo r1.precisionExtra + powerOfTwo r1.precisionExtra) +
        powerOfTwo r1.precisionExtra) + powerOfTwo (r1.precisionExtra + 1)) +
        powerOfTwo r1.precisionExtra) + powerOfTwo r1.precisionExtra) +
        powerOfTwo r1.precisionExtra = powerOfTwo (r1.precisionExtra + 3) := by
    rw [← sixFineOneMiddleBudget]
    conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    conv => rhs; simp only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [budget] at combined
  exact ⟨⟨precisionPool pool, r1.scale.leftExtra, l1.scale.rightExtra,
    r1.scale.leftExact, l1.scale.rightExact⟩, r1.precisionExtra + 3,
    (Nat.add_assoc p r1.precisionExtra 3).symm.trans
      ((addSwapMiddle p r1.precisionExtra 3).trans r1.precisionExact), combined⟩

end DirectedUpper

def strengthenSeparationThreeLinks {p : Nat} {a a1 a2 c b b1 b2 d : SignedDyadicCode}
    (gap : StrictSeparation p a b)
    (left1 : Near (p + 3) a a1) (left2 : Near (p + 3) a1 a2) (left3 : Near (p + 3) a2 c)
    (right1 : Near (p + 3) b b1) (right2 : Near (p + 3) b1 b2) (right3 : Near (p + 3) b2 d) :
    StrictSeparation (p + 2) c d :=
  match inspectGap (p + 2) c d with
  | .inl result => result
  | .inr upper => (gap.refuteUpper (DirectedUpper.composeThreeOneThree
      (.ofNear right1) (.ofNear right2) (.ofNear right3) upper
      (.ofNear left3.symm) (.ofNear left2.symm) (.ofNear left1.symm))).elim

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.composeSignedBoundMixed
#print axioms RelationalPerimeter.Constitution.Reals.sixFineOneMiddleBudget
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper.align
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper.composeThreeOneThree
#print axioms RelationalPerimeter.Constitution.Reals.strengthenSeparationThreeLinks
/- AXIOM_AUDIT_END -/

