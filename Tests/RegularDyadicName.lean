import RelationalPerimeter.Constitution.Reals.RegularDyadicName

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Tests.RegularDyadicName
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.RegularDyadicName

/-- Arbitrary received functions remain arbitrary parameters of the tests. -/
def tailName (name : RegularDyadicName) (offset : Nat) : RegularDyadicName where
  approximation p := name.approximation (p + offset)
  coherent p r s hr hs := name.coherent p _ _
    (hr.trans (.first _ _)) (hs.trans (.first _ _))

def tailEquivalent (name : RegularDyadicName) (offset : Nat) : NameEquivalent name (tailName name offset) where
  responseThreshold p := p
  near p r s hr hs := name.coherent p r (s + offset) hr (hs.trans (.first _ _))

def nonidentityFamily (name : RegularDyadicName) : RegularPresentedFamily where
  name n := constantName (name.approximation n)
  modulus p := p + 2
  modulusMonotone h := h.add (.refl _)
  cauchy p n m r s hn hm hr hs := Near.ofSameLeft (constantNameSameValue _ r)
    (Near.ofSameRight (name.coherent p n m
      ((PrecisionExtension.first p 2).trans hn) ((PrecisionExtension.first p 2).trans hm))
      (constantNameSameValue _ s).symm)

def receivedNameCompleted (name : RegularDyadicName) :
    RegularConverges (nonidentityFamily name) (regularLimitResult (nonidentityFamily name)).value :=
  (regularLimitResult _).convergence

def originalIsLimit (name : RegularDyadicName) : RegularConverges (nonidentityFamily name) name where
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (constantNameSameValue _ r)
    (name.coherent p n s ((PrecisionExtension.first p 2).trans hn) hs)

def completedEquivalentOriginal (name : RegularDyadicName) :
    NameEquivalent (regularLimitResult (nonidentityFamily name)).value name :=
  (regularLimitResult _).unique name (originalIsLimit name)

theorem diagonalSchedule (name : RegularDyadicName) (p : Nat) :
    (diagonalName (nonidentityFamily name)).approximation p = (name.approximation (p + 2)).raise p := rfl

theorem transThreshold {a b c : RegularDyadicName} (first : NameEquivalent a b)
    (second : NameEquivalent b c) (p : Nat) :
    (first.trans second).responseThreshold p =
      max (first.responseThreshold (p + 1)) (second.responseThreshold (p + 1)) := rfl

theorem constantSchedule (code : SignedDyadicCode) (p : Nat) :
    (constantName code).approximation p = code.raise p := rfl

theorem multiplicationSchedule (a b : RegularDyadicName) (p : Nat) :
    (mulName a b).approximation p =
      (a.approximation (p + 1 + probeAmplitude (b.approximation 0))).mul
        (b.approximation (p + 1 + probeAmplitude (a.approximation 0))) := rfl

def twoDistinctZeroNames : NameEquivalent zeroName (tailName zeroName 1) := tailEquivalent zeroName 1

theorem distinctZeroReplies : zeroName.approximation 0 ≠ (tailName zeroName 1).approximation 0 := by
  intro equality
  have scales := congrArg SignedDyadicCode.scale equality
  exact Nat.noConfusion scales

end RelationalPerimeter.Tests.RegularDyadicName

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RegularDyadicName.tailName
#print axioms RelationalPerimeter.Tests.RegularDyadicName.tailEquivalent
#print axioms RelationalPerimeter.Tests.RegularDyadicName.nonidentityFamily
#print axioms RelationalPerimeter.Tests.RegularDyadicName.receivedNameCompleted
#print axioms RelationalPerimeter.Tests.RegularDyadicName.originalIsLimit
#print axioms RelationalPerimeter.Tests.RegularDyadicName.completedEquivalentOriginal
#print axioms RelationalPerimeter.Tests.RegularDyadicName.diagonalSchedule
#print axioms RelationalPerimeter.Tests.RegularDyadicName.transThreshold
#print axioms RelationalPerimeter.Tests.RegularDyadicName.constantSchedule
#print axioms RelationalPerimeter.Tests.RegularDyadicName.multiplicationSchedule
#print axioms RelationalPerimeter.Tests.RegularDyadicName.twoDistinctZeroNames
#print axioms RelationalPerimeter.Tests.RegularDyadicName.distinctZeroReplies
/- AXIOM_AUDIT_END -/
