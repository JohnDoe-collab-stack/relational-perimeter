import Tests.RelationalRealInverse
import RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealOrderedField
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder
open RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField
variable (P : CircularPresentation) (depth : Nat)

def origin := RelationalRealOrder.sumLessOne P depth
def sum := RelationalRealRuntime.sum P depth
def aliasLeft : Real P depth := .add (sum P depth) (sum P depth)
def shiftedRight : Real P depth := .add (one P depth) (sum P depth)
def oldLeft := executeReal (aliasLeft P depth) 0
def oldRight := executeReal (shiftedRight P depth) 0
def translated := translateRight (origin P depth) (sum P depth) (oldLeft P depth).next (oldRight P depth).next
def translatedOrder := (translated P depth).order

theorem currentOutputs : (translated P depth).attempt.pair.left = executeAt (aliasLeft P depth)
    (oldLeft P depth).next ((origin P depth).accuracy + 5) ∧
    (translated P depth).attempt.pair.right = executeAt (shiftedRight P depth)
      (oldRight P depth).next ((origin P depth).accuracy + 5) := ⟨rfl, rfl⟩

theorem ownsOrigin : (translated P depth).originOwned = origin P depth := (translated P depth).originExact
theorem aliasKeepsBothRoles : (translated P depth).attempt.pair.left.resource.action.action.operands =
    ((translated P depth).attempt.pair.left.resource.left, (translated P depth).attempt.pair.left.resource.right) := by
  rw [(translated P depth).attempt.pair.left.resource.action.action.operandsExact,
    (translated P depth).attempt.pair.left.resource.action.searchResult_is_receivedContextOutput,
    (translated P depth).attempt.pair.left.resource.action.receivedContext_is_produced]
  rfl
theorem translatedHistory : (translated P depth).attempt.pair.left.next.retained.length = 2 := rfl
theorem exactTranslatedTarget : (translated P depth).attempt.pair.left.code =
    (translated P depth).attempt.pair.left.resource.action.action.code :=
  (additionPacketSameTarget _).1

def positiveUnit := onePositive P depth
def positiveCancelled : Positive (RelationalRealInverse.cancelled P depth) :=
  (transportOrder (positiveUnit P depth) (Equivalent.refl _) (RelationalRealInverse.cancelledEquivalent P depth)
    (positiveUnit P depth).pair.left.next
    (environment (RelationalRealInverse.cancelled P depth)).initialArchive).order

def product := positiveProduct (positiveUnit P depth) (positiveCancelled P depth)
  (positiveCancelled P depth).pair.left.next
  (startProductAt (one P depth) (RelationalRealInverse.cancelled P depth)
    (positiveUnit P depth).pair.right.next (positiveCancelled P depth).pair.right.next)
def productPositive := (product P depth).positive
theorem productOwnsPositivity : (product P depth).leftOwned = positiveUnit P depth ∧
    (product P depth).rightOwned = positiveCancelled P depth := ⟨(product P depth).leftExact, (product P depth).rightExact⟩
theorem productBudget : positiveProductAccuracy (positiveUnit P depth) (positiveCancelled P depth) =
    ((positiveUnit P depth).accuracy + 2) + ((positiveCancelled P depth).accuracy + 2) + 1 := rfl
def productLeftCertificate := (product P depth).leftCertificate
def productRightCertificate := (product P depth).rightCertificate

def continuedProduct := positiveProduct (positiveUnit P depth) (positiveCancelled P depth)
  (product P depth).attempt.pair.left.next (product P depth).attempt.pair.right.next

theorem productContinuesCurrent : (continuedProduct P depth).attempt.pair.right =
    executeAt (.mul (one P depth) (RelationalRealInverse.cancelled P depth))
      (product P depth).attempt.pair.right.next
      (positiveProductAccuracy (positiveUnit P depth) (positiveCancelled P depth) + 3) := rfl

theorem productHistory : (continuedProduct P depth).attempt.pair.right.next.retained.length = 2 := rfl

def aliasedProduct := positiveProduct (positiveUnit P depth) (positiveUnit P depth)
  (positiveUnit P depth).pair.left.next
  (startProductAt (one P depth) (one P depth) (positiveUnit P depth).pair.right.next (positiveUnit P depth).pair.right.next)

theorem aliasedProductKeepsBothRoles : (aliasedProduct P depth).attempt.pair.right.resource.action.action.operands =
    ((aliasedProduct P depth).attempt.pair.right.resource.left,
      (aliasedProduct P depth).attempt.pair.right.resource.right) := by
  rw [(aliasedProduct P depth).attempt.pair.right.resource.action.action.operandsExact,
    (aliasedProduct P depth).attempt.pair.right.resource.action.searchResult_is_receivedContextOutput,
    (aliasedProduct P depth).attempt.pair.right.resource.action.receivedContext_is_produced]
  rfl

def multiplied := multiplyRight (origin P depth) (positiveUnit P depth)
  (startNegationAt (sum P depth) (origin P depth).pair.left.next) (positiveUnit P depth).pair.left.next
  (executeReal (.mul (sum P depth) (one P depth)) 0).next
def multipliedOrder := (multiplied P depth).order
theorem finalLeftConsumesExactSuccessor : (multiplied P depth).transported.target.left =
    executeAt (.mul (sum P depth) (one P depth))
      (multiplied P depth).translated.attempt.pair.left.resource.right.next
      (precisionPool (transportPrecisions (multiplied P depth).translated.order
        (zero_add (.mul (sum P depth) (one P depth))) (differenceProductCancellation _ _ _))) := rfl
theorem finalRightConsumesExactChildren :
    (multiplied P depth).transported.target.right.resource.leftProbe =
      executeAt (one P depth) (multiplied P depth).translated.attempt.pair.right.resource.left.resource.left.resource.left.next 0 ∧
    (multiplied P depth).transported.target.right.resource.rightProbe =
      executeAt (one P depth) (multiplied P depth).translated.attempt.pair.right.resource.left.resource.right.next 0 := ⟨rfl, rfl⟩

def rightMonotone := mulOrderRight (origin P depth) (positiveUnit P depth)
def leftMonotone := mulOrderLeft (origin P depth) (positiveUnit P depth)
def reflectedAddition := reflectAddRight (translatedOrder P depth)
def apartTranslated := apartAddRight (.backward (origin P depth)) (sum P depth)
def apartMultiplied := apartMulPositiveRight (.forward (origin P depth)) (positiveUnit P depth)
def laws := orderedFieldLaws P depth
def futureLaws := orderedFieldFutureLaws P depth
def futureTransport := (futureLaws P depth).transport (origin P depth)
  (RelationalRealAddition.neg_neg (sum P depth)).symm.toFutures (Equivalent.refl _).toFutures
  (executeReal (.neg (.neg (sum P depth))) 0).next (origin P depth).pair.right.next

end RelationalPerimeter.Tests.RelationalRealOrderedField

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.origin
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.sum
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.aliasLeft
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.shiftedRight
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.oldLeft
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.oldRight
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.translated
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.translatedOrder
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.currentOutputs
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.ownsOrigin
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.aliasKeepsBothRoles
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.translatedHistory
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.exactTranslatedTarget
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.positiveUnit
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.positiveCancelled
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.product
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productPositive
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productOwnsPositivity
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productBudget
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productLeftCertificate
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productRightCertificate
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.continuedProduct
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productContinuesCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.productHistory
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.aliasedProduct
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.aliasedProductKeepsBothRoles
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.multiplied
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.multipliedOrder
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.finalLeftConsumesExactSuccessor
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.finalRightConsumesExactChildren
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.rightMonotone
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.leftMonotone
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.reflectedAddition
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.apartTranslated
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.apartMultiplied
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.laws
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.futureLaws
#print axioms RelationalPerimeter.Tests.RelationalRealOrderedField.futureTransport
/- AXIOM_AUDIT_END -/
