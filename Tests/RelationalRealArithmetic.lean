import RelationalPerimeter.Constitution.Reals.DyadicArithmetic

set_option autoImplicit false

namespace RelationalPerimeter.Tests.RelationalRealArithmetic
open RelationalPerimeter.Constitution.Reals

def half : SignedDyadicCode := ⟨1, 0, 1⟩
def quarter : SignedDyadicCode := ⟨1, 0, 2⟩

theorem unequalScalesExact : half.add quarter = ⟨6, 0, 3⟩ := rfl
theorem zeroExact : SignedDyadicCode.zero.add SignedDyadicCode.zero = SignedDyadicCode.zero := rfl
theorem oneExact : SignedDyadicCode.one.add SignedDyadicCode.one = ⟨2, 0, 0⟩ := rfl
def raisedSum : SameValue ((half.raise 2).add (quarter.raise 3)) (half.add quarter) :=
  SignedDyadicCode.add_raise half quarter 2 3
def successorErrorBudget : Near 5 (half.add quarter) (half.add quarter) :=
  Near.add (Near.refl 6 half) (Near.refl 6 quarter)
def halfError : Near 1 SignedDyadicCode.zero half where
  scale := ⟨1, 1, 0, rfl, rfl⟩
  precisionExtra := 0
  precisionExact := rfl
  leftBound := Nat.zero_le _
  rightBound := Nat.le_refl _
def saturatedErrorBudget : Near 0 (SignedDyadicCode.zero.add SignedDyadicCode.zero) (half.add half) :=
  Near.add halfError halfError
theorem halfErrorIsNonzero : SignedDyadicCode.zero.positive ≠ half.positive := by intro h; cases h
theorem sumErrorReachesOne : half.add half = SignedDyadicCode.one.raise 2 := rfl
def associate : SameValue ((half.add quarter).add half) (half.add (quarter.add half)) :=
  SignedDyadicCode.add_assoc half quarter half

end RelationalPerimeter.Tests.RelationalRealArithmetic

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.half
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.quarter
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.unequalScalesExact
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.zeroExact
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.oneExact
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.raisedSum
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.successorErrorBudget
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.halfError
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.saturatedErrorBudget
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.halfErrorIsNonzero
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.sumErrorReachesOne
#print axioms RelationalPerimeter.Tests.RelationalRealArithmetic.associate
/- AXIOM_AUDIT_END -/
