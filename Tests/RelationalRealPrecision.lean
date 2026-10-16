import RelationalPerimeter.Constitution.Reals.Precision

set_option autoImplicit false

/-!
# Regression checks for relational-real precision

These checks exercise the constructive scale witnesses.  In particular, they
record that a scale change preserves the represented value without identifying
the two source codes.
-/

namespace RelationalPerimeter.Tests.RelationalRealPrecision

open RelationalPerimeter.Constitution.Reals

def baseCode : SignedDyadicCode where
  positive := 3
  negative := 1
  scale := 2

def raisedCode : SignedDyadicCode :=
  baseCode.raise 2

theorem repeatedDoubling_exact : scaleNat 3 2 = 12 := by
  rfl

theorem powerOfTwo_exact : powerOfTwo 4 = 16 := by
  rfl

def scaleChange_preservesValue : SameValue baseCode raisedCode :=
  SameValue.raiseExact baseCode 2

theorem scaleChange_retainsStrictScaleDistinction :
    baseCode.scale < raisedCode.scale := by
  exact Nat.le.step (Nat.le_refl 3)

def coarseToFine : PrecisionExtension 3 5 where
  extra := 2
  exact := rfl

def precisionWeakening_executes : Near 3 baseCode baseCode :=
  Near.weaken coarseToFine (Near.refl 5 baseCode)

def raisedOperand_remainsNear : Near 6 baseCode raisedCode :=
  (Near.refl 6 baseCode).raiseRight 2

def raisedOperand_returnsToSource : Near 6 baseCode baseCode :=
  Near.lowerRight raisedOperand_remainsNear

def composedPrecision_executes : Near 5 baseCode baseCode :=
  Near.compose raisedOperand_remainsNear raisedOperand_remainsNear.symm

def iteratedScaleChange_preservesValue :
    SameValue baseCode (raisedCode.raise 3) :=
  SameValue.trans scaleChange_preservesValue
    (SameValue.raiseExact raisedCode 3)

end RelationalPerimeter.Tests.RelationalRealPrecision

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.baseCode
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.raisedCode
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.repeatedDoubling_exact
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.powerOfTwo_exact
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.scaleChange_preservesValue
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.scaleChange_retainsStrictScaleDistinction
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.coarseToFine
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.precisionWeakening_executes
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.raisedOperand_remainsNear
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.raisedOperand_returnsToSource
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.composedPrecision_executes
#print axioms RelationalPerimeter.Tests.RelationalRealPrecision.iteratedScaleChange_preservesValue
/- AXIOM_AUDIT_END -/
