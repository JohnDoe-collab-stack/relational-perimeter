import RelationalPerimeter.Constitution.Reals.SequentialCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Positive equivalence of relational-real presentations

Relational reals are not quotiented by structural equality.  An equivalence
supplies an executable response threshold at every requested precision and a
positive `Near` witness for every pair of responses beyond that threshold.
Transitivity computes a new threshold and spends one precision level through
the constructive triangle law.
-/

namespace RelationalPerimeter.Constitution.Reals
namespace RelationalReal

open StrongPerimetralTurning.GodelGroupingTower

/-- Positive, response-modulated equivalence of two relational reals. -/
structure Equivalent
    {P : StrongPerimetralTurning.CircularPresentation}
    (first second : RelationalReal P) where
  responseThreshold : Nat -> Nat
  near :
    (precision leftResponse rightResponse : Nat) ->
      PrecisionExtension (responseThreshold precision) leftResponse ->
      PrecisionExtension (responseThreshold precision) rightResponse ->
      Near precision
        (first.approximation leftResponse)
        (second.approximation rightResponse)

/-- Every relational real is equivalent to itself by its own coherence law. -/
def Equivalent.refl
    {P : StrongPerimetralTurning.CircularPresentation}
    (real : RelationalReal P) : Equivalent real real where
  responseThreshold := fun precision => precision
  near := fun precision leftResponse rightResponse leftBeyond rightBeyond =>
    real.coherent precision leftResponse rightResponse leftBeyond rightBeyond

/-- Positive equivalence is symmetric without changing its threshold. -/
def Equivalent.symm
    {P : StrongPerimetralTurning.CircularPresentation}
    {first second : RelationalReal P}
    (equivalent : Equivalent first second) : Equivalent second first where
  responseThreshold := equivalent.responseThreshold
  near := fun precision leftResponse rightResponse leftBeyond rightBeyond =>
    (equivalent.near precision rightResponse leftResponse
      rightBeyond leftBeyond).symm

/-- The first threshold embeds constructively in the combined threshold. -/
def firstThresholdExtension (first second : Nat) :
    PrecisionExtension first (first + second) where
  extra := second
  exact := rfl

/-- The second threshold embeds constructively in the combined threshold. -/
def secondThresholdExtension (first second : Nat) :
    PrecisionExtension second (first + second) where
  extra := first
  exact := Nat.add_comm second first

/--
Compose equivalences by calculating a common response threshold at precision
`p+1`, then applying the constructive `Near` triangle law at precision `p`.
-/
def Equivalent.trans
    {P : StrongPerimetralTurning.CircularPresentation}
    {first middle last : RelationalReal P}
    (left : Equivalent first middle)
    (right : Equivalent middle last) : Equivalent first last where
  responseThreshold := fun precision =>
    left.responseThreshold (Nat.succ precision) +
      right.responseThreshold (Nat.succ precision)
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    let leftThreshold := left.responseThreshold (Nat.succ precision)
    let rightThreshold := right.responseThreshold (Nat.succ precision)
    let leftToCombined :=
      firstThresholdExtension leftThreshold rightThreshold
    let rightToCombined :=
      secondThresholdExtension leftThreshold rightThreshold
    have leftNear := left.near
      (Nat.succ precision) leftResponse (leftThreshold + rightThreshold)
      (leftToCombined.trans leftBeyond) leftToCombined
    have rightNear := right.near
      (Nat.succ precision) (leftThreshold + rightThreshold) rightResponse
      rightToCombined (rightToCombined.trans rightBeyond)
    exact Near.compose leftNear rightNear

/-- A constant response remains exactly the dyadic code that generated it. -/
def constantApproximationSameValue
    (P : StrongPerimetralTurning.CircularPresentation)
    (code : SignedDyadicCode)
    (precision : Nat) :
    SameValue (constant P code |>.approximation precision) code :=
  (SameValue.raiseExact code precision).symm

/-- Its executed readout has the same exact dyadic value as the generator. -/
def constantReadoutSameValue
    (P : StrongPerimetralTurning.CircularPresentation)
    (code : SignedDyadicCode)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) :
    SameValue (constant P code |>.executedReadout journal precision) code :=
  constantApproximationSameValue P code precision

/-- Exactly equal dyadic values generate equivalent constant presentations. -/
def constantEquivalent
    (P : StrongPerimetralTurning.CircularPresentation)
    {left right : SignedDyadicCode}
    (same : SameValue left right) :
    Equivalent (constant P left) (constant P right) where
  responseThreshold := fun precision => precision
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    exact
      ((SameValue.raiseExact left leftResponse).symm.trans
        (same.trans (SameValue.raiseExact right rightResponse))).toNear precision

end RelationalReal
end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.Equivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.Equivalent.refl
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.Equivalent.symm
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.firstThresholdExtension
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.secondThresholdExtension
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.Equivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.constantApproximationSameValue
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.constantReadoutSameValue
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.constantEquivalent
/- AXIOM_AUDIT_END -/
