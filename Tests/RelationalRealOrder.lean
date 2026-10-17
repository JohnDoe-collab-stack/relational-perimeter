import Tests.RelationalRealMultiplication
import RelationalPerimeter.Constitution.Reals.RelationalRealOrder

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealOrder
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition
open RelationalPerimeter.Constitution.Reals.RelationalRealOrder
variable (P : CircularPresentation) (baseDepth : Nat)

def unitMargin : StrictSeparation 1 SignedDyadicCode.zero SignedDyadicCode.one :=
  ⟨⟨1, 1, 1, rfl, rfl⟩, 0, rfl, by decide⟩
def finiteTag {p : Nat} {x y : SignedDyadicCode} : FiniteDirection p x y → Nat
  | .forward _ => 0
  | .backward _ => 1
  | .inconclusive _ _ => 2
theorem finiteOrientations : finiteTag (classifyFinite 1 SignedDyadicCode.zero SignedDyadicCode.one) = 0 ∧
    finiteTag (classifyFinite 1 SignedDyadicCode.one SignedDyadicCode.zero) = 1 ∧
    finiteTag (classifyFinite 1 RelationalRealMultiplication.cancelled SignedDyadicCode.zero) = 2 :=
  ⟨by decide, by decide, by decide⟩

def unitAttempt := compareCurrent (zero P baseDepth) (one P baseDepth)
  (environment (zero P baseDepth)).initialArchive (environment (one P baseDepth)).initialArchive 3

def unitPositive : Positive (one P baseDepth) := by
  have left : SameValue (unitAttempt P baseDepth).pair.left.code SignedDyadicCode.zero := by
    rw [currentReadout (zero P baseDepth) _ _ (unitAttempt P baseDepth).pair.left]
    exact constant_readout _ _
  have right : SameValue (unitAttempt P baseDepth).pair.right.code SignedDyadicCode.one := by
    rw [currentReadout (one P baseDepth) _ _ (unitAttempt P baseDepth).pair.right]
    exact constant_readout _ _
  exact (unitAttempt P baseDepth).forward (strengthenSeparation unitMargin (left.symm.toNear 3) (right.symm.toNear 3))

def sumMargin : StrictSeparation 3 (⟨3, 0, 2⟩ : SignedDyadicCode) SignedDyadicCode.one :=
  ⟨⟨3, 1, 3, rfl, rfl⟩, 0, rfl, by decide⟩
def sumAttempt := compareCurrent (RelationalRealRuntime.sum P baseDepth) (one P baseDepth)
  (environment (RelationalRealRuntime.sum P baseDepth)).initialArchive (environment (one P baseDepth)).initialArchive 5
def sumContinued := continueComparison (sumAttempt P baseDepth) 5

def sumLessOne : StrictOrder (RelationalRealRuntime.sum P baseDepth) (one P baseDepth) := by
  have left : SameValue (sumContinued P baseDepth).pair.left.code ⟨3, 0, 2⟩ := by
    rw [currentReadout (RelationalRealRuntime.sum P baseDepth) _ _ (sumContinued P baseDepth).pair.left]
    exact RelationalRealRuntime.sumHasExpectedValue P baseDepth _
  have right : SameValue (sumContinued P baseDepth).pair.right.code SignedDyadicCode.one := by
    rw [currentReadout (one P baseDepth) _ _ (sumContinued P baseDepth).pair.right]
    exact constant_readout _ _
  exact (sumContinued P baseDepth).forward (strengthenSeparation sumMargin (left.symm.toNear 5) (right.symm.toNear 5))

theorem continuationUsesCurrent : (sumContinued P baseDepth).pair.left =
    executeAt (RelationalRealRuntime.sum P baseDepth) (sumAttempt P baseDepth).pair.left.next 8 := rfl
theorem nonemptyHistory : (sumAttempt P baseDepth).pair.left.next.retained.length = 1 ∧
    (sumContinued P baseDepth).pair.left.next.retained.length = 2 := ⟨rfl, rfl⟩
theorem journalCurrent : (sumContinued P baseDepth).pair.left.next.journal.absoluteDepth = baseDepth + 12 := by
  change (sumContinued P baseDepth).pair.left.resource.action.completedJournal.absoluteDepth = _
  rw [(sumContinued P baseDepth).pair.left.resource.action.completed_absoluteDepth]
  change (sumAttempt P baseDepth).pair.left.resource.action.completedJournal.absoluteDepth + 6 = _
  rw [(sumAttempt P baseDepth).pair.left.resource.action.completed_absoluteDepth]
  exact Nat.add_assoc baseDepth 6 6

def aliased := compareCurrent (RelationalRealRuntime.sum P baseDepth) (RelationalRealRuntime.sum P baseDepth)
  (sumAttempt P baseDepth).pair.left.next (sumContinued P baseDepth).pair.left.next 2
theorem aliasHasTwoCurrentRoles : (aliased P baseDepth).pair.left =
    executeAt (RelationalRealRuntime.sum P baseDepth) (sumAttempt P baseDepth).pair.left.next 5 ∧
    (aliased P baseDepth).pair.right = executeAt (RelationalRealRuntime.sum P baseDepth)
      (sumContinued P baseDepth).pair.left.next 5 := ⟨rfl, rfl⟩
theorem aliasInconclusive : (aliased P baseDepth).apartness? = none :=
  (aliased P baseDepth).noneOfEquivalent (Equivalent.refl _)

def cancelled : Real P baseDepth := .leaf (constantRuntime P baseDepth RelationalRealMultiplication.cancelled)
def cancelledEquivalent : Equivalent (cancelled P baseDepth) (zero P baseDepth) := Equivalent.ofExact (by
  intro p
  exact ((constant_readout RelationalRealMultiplication.cancelled p).trans
    RelationalRealMultiplication.cancelledSameZero).trans (constant_readout SignedDyadicCode.zero p).symm)
def cancelledAttempt := compareCurrent (cancelled P baseDepth) (zero P baseDepth)
  (environment (cancelled P baseDepth)).initialArchive (environment (zero P baseDepth)).initialArchive 2
theorem cancellationInconclusive : (cancelledAttempt P baseDepth).apartness? = none :=
  (cancelledAttempt P baseDepth).noneOfEquivalent (cancelledEquivalent P baseDepth)

def refined := refineHistorical (sumLessOne P baseDepth) ((sumLessOne P baseDepth).accuracy + 5) (PrecisionExtension.refl _)
theorem refinementOwnsOrigin : (refined P baseDepth).originOwned = sumLessOne P baseDepth :=
  (refined P baseDepth).originExact
theorem refinementUsesSuccessors : (refined P baseDepth).pair.left = executeAt (RelationalRealRuntime.sum P baseDepth)
    (sumLessOne P baseDepth).pair.left.next ((sumLessOne P baseDepth).accuracy + 5) := rfl
def refinedMargin := (refined P baseDepth).separation
def transported := transportOrder (sumLessOne P baseDepth) (Equivalent.refl _) (Equivalent.refl _)
  (sumContinued P baseDepth).pair.left.next (sumContinued P baseDepth).pair.right.next
def futureTransported := transportOrderFutures (sumLessOne P baseDepth) (Equivalent.refl _).toFutures (Equivalent.refl _).toFutures
  (sumContinued P baseDepth).pair.left.next (sumContinued P baseDepth).pair.right.next
theorem receivedTargetArchives : (transported P baseDepth).target.left = executeAt (RelationalRealRuntime.sum P baseDepth)
    (sumContinued P baseDepth).pair.left.next (precisionPool (transportPrecisions (sumLessOne P baseDepth) (Equivalent.refl _) (Equivalent.refl _))) := rfl
def transportedOrder := (transported P baseDepth).order
def transportedApartness := transportApartness (.forward (sumLessOne P baseDepth)) (Equivalent.refl _) (Equivalent.refl _)
  (sumContinued P baseDepth).pair.left.next (sumContinued P baseDepth).pair.right.next

def cotrans := cotransition (sumLessOne P baseDepth) (RelationalRealRuntime.sum P baseDepth)
  (sumContinued P baseDepth).pair.left.next (sumAttempt P baseDepth).pair.left.next (sumContinued P baseDepth).pair.right.next
theorem middleIsOwnedOnce : (cotrans P baseDepth).triple.leftMiddle.right = executeAt (RelationalRealRuntime.sum P baseDepth)
    (sumAttempt P baseDepth).pair.left.next ((sumLessOne P baseDepth).accuracy + 5) := rfl
def cotransOrders := (cotrans P baseDepth).orders
def apartCotrans := Apartness.cotransitive (.backward (sumLessOne P baseDepth)) (zero P baseDepth)
  (sumContinued P baseDepth).pair.right.next (environment (zero P baseDepth)).initialArchive (sumContinued P baseDepth).pair.left.next
def noSelf {a : Real P baseDepth} (witness : Apartness a a) : Empty := witness.irreflexive
def noReverse (reverse : StrictOrder (one P baseDepth) (RelationalRealRuntime.sum P baseDepth)) : Empty :=
  (sumLessOne P baseDepth).asymmetric reverse
def noEquivalent (same : Equivalent (RelationalRealRuntime.sum P baseDepth) (one P baseDepth)) : Empty :=
  (sumLessOne P baseDepth).refutesEquivalent same
def transitive {a b c : Real P baseDepth} (first : StrictOrder a b) (second : StrictOrder b c) : StrictOrder a c := first.transitive second
def signAttempt := signCurrent (one P baseDepth) (unitAttempt P baseDepth).pair.left.next (unitAttempt P baseDepth).pair.right.next 3
def signResult := (signAttempt P baseDepth).sign?
def noBothSigns (negative : Negative (one P baseDepth)) : Empty := signsExclusive (unitPositive P baseDepth) negative
def positiveSumMargin : StrictSeparation 1 SignedDyadicCode.zero (⟨3, 0, 2⟩ : SignedDyadicCode) :=
  ⟨⟨2, 2, 0, rfl, rfl⟩, 1, rfl, by decide⟩
def negativeAttempt := compareCurrent (.neg (RelationalRealRuntime.sum P baseDepth)) (zero P baseDepth)
  (executeReal (.neg (RelationalRealRuntime.sum P baseDepth)) 0).next (unitAttempt P baseDepth).pair.left.next 3
def negativeWitness : Negative (.neg (RelationalRealRuntime.sum P baseDepth)) := by
  have left : SameValue (negativeAttempt P baseDepth).pair.left.code (SignedDyadicCode.neg ⟨3, 0, 2⟩) := by
    rw [currentReadout (.neg (RelationalRealRuntime.sum P baseDepth)) _ _ (negativeAttempt P baseDepth).pair.left,
      neg_readout_exact]
    exact (RelationalRealRuntime.sumHasExpectedValue P baseDepth _).neg
  have right : SameValue (negativeAttempt P baseDepth).pair.right.code SignedDyadicCode.zero := by
    rw [currentReadout (zero P baseDepth) _ _ (negativeAttempt P baseDepth).pair.right]
    exact constant_readout _ _
  exact (negativeAttempt P baseDepth).forward
    (strengthenSeparation positiveSumMargin.negReverse (left.symm.toNear 3) (right.symm.toNear 3))
def transportedAcrossPrograms := transportOrder (sumLessOne P baseDepth)
  (RelationalRealAddition.neg_neg (RelationalRealRuntime.sum P baseDepth)).symm
  (RelationalRealAddition.add_zero (one P baseDepth)).symm
  (executeReal (.neg (.neg (RelationalRealRuntime.sum P baseDepth))) 1).next
  (executeReal (.add (one P baseDepth) (zero P baseDepth)) 1).next
def negated := negateOrder (sumLessOne P baseDepth)
  (executeReal (.neg (one P baseDepth)) 0).next (executeReal (.neg (RelationalRealRuntime.sum P baseDepth)) 0).next
def reversedNegation := (negated P baseDepth).order
def projectedPresentation := (sumLessOne P baseDepth).toPresentation
def reflectedPresentation := reflectPresentationOrder (projectedPresentation P baseDepth)
  (sumContinued P baseDepth).pair.left.next (sumContinued P baseDepth).pair.right.next
def projectedCarrier := (sumLessOne P baseDepth).toCarrier
def reflectedCarrier := reflectCarrierOrder (projectedCarrier P baseDepth)
  (sumContinued P baseDepth).pair.left.next (sumContinued P baseDepth).pair.right.next
def apartPresentation := (Apartness.forward (sumLessOne P baseDepth)).toPresentation
def apartCarrier := (Apartness.backward (sumLessOne P baseDepth)).toCarrier
def reflectedApartCarrier := reflectCarrierApartness (apartCarrier P baseDepth)
  (sumContinued P baseDepth).pair.right.next (sumContinued P baseDepth).pair.left.next

end RelationalPerimeter.Tests.RelationalRealOrder

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.unitMargin
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.finiteTag
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.finiteOrientations
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.unitAttempt
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.unitPositive
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.sumMargin
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.sumAttempt
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.sumContinued
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.sumLessOne
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.continuationUsesCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.nonemptyHistory
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.journalCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.aliased
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.aliasHasTwoCurrentRoles
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.aliasInconclusive
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.cancelled
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.cancelledEquivalent
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.cancelledAttempt
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.cancellationInconclusive
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.refined
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.refinementOwnsOrigin
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.refinementUsesSuccessors
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.refinedMargin
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.transported
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.futureTransported
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.receivedTargetArchives
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.transportedOrder
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.transportedApartness
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.cotrans
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.middleIsOwnedOnce
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.cotransOrders
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.apartCotrans
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.noSelf
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.noReverse
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.noEquivalent
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.transitive
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.signAttempt
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.signResult
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.noBothSigns
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.positiveSumMargin
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.negativeAttempt
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.negativeWitness
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.transportedAcrossPrograms
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.negated
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.reversedNegation
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.projectedPresentation
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.reflectedPresentation
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.projectedCarrier
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.reflectedCarrier
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.apartPresentation
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.apartCarrier
#print axioms RelationalPerimeter.Tests.RelationalRealOrder.reflectedApartCarrier
/- AXIOM_AUDIT_END -/
