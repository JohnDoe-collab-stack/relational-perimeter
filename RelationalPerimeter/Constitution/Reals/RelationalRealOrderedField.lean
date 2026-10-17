import RelationalPerimeter.Constitution.Reals.RelationalRealInverseLaws
import RelationalPerimeter.Constitution.Reals.DyadicOrderedField

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Constructive ordered-field compatibility. Native arithmetic runtimes are
unchanged. Finite packets own their received witnesses and actual arithmetic
Steps/actions; numerical equivalences only support directed fresh transports.
There is no global comparison decision or nonnegative complement relation. -/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField
open StrongPerimetralTurning HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder
open RelationalRealMultiplication DyadicReciprocal
variable {P : CircularPresentation} {baseDepth : Nat}

structure TranslatedOrder {a b : Real P baseDepth} (origin : StrictOrder a b) (shift : Real P baseDepth)
    (la : (environment (.add a shift)).Archive) (ra : (environment (.add b shift)).Archive) where
  private mk ::
  originOwned : StrictOrder a b
  originExact : originOwned = origin
  attempt : ComparisonAttempt (environment (.add a shift)) (environment (.add b shift)) la ra
    (origin.accuracy + 2) (origin.accuracy + 5)
  leftNear : Near (origin.accuracy + 2) origin.pair.left.code attempt.pair.left.resource.left.code
  rightNear : Near (origin.accuracy + 2) origin.pair.right.code attempt.pair.right.resource.left.code
  shiftCodesExact : attempt.pair.left.resource.right.code = attempt.pair.right.resource.right.code
  separation : StrictSeparation (origin.accuracy + 2) attempt.pair.left.code attempt.pair.right.code

def translateRight {a b : Real P baseDepth} (origin : StrictOrder a b) (shift : Real P baseDepth)
    (la : (environment (.add a shift)).Archive) (ra : (environment (.add b shift)).Archive) :
    TranslatedOrder origin shift la ra := by
  let attempt := produceComparison (environment (.add a shift)) (environment (.add b shift)) la ra
    (origin.accuracy + 2) (origin.accuracy + 5) (PrecisionExtension.refl _)
  dsimp only [environment, addEnvironment] at la ra attempt
  have old : PrecisionExtension (origin.accuracy + 2) origin.response :=
    (PrecisionExtension.next (origin.accuracy + 2)).trans origin.beyond
  have fine : PrecisionExtension (origin.accuracy + 2) (origin.accuracy + 5 + 1) := PrecisionExtension.first _ 4
  let leftNear := (coherent a).near _ _ _ origin.pair.left attempt.pair.left.resource.left old fine
  let rightNear := (coherent b).near _ _ _ origin.pair.right attempt.pair.right.resource.left old fine
  have sameShift : attempt.pair.left.resource.right.code = attempt.pair.right.resource.right.code :=
    (currentReadout shift _ _ attempt.pair.left.resource.right).trans
      (currentReadout shift _ _ attempt.pair.right.resource.right).symm
  have gap : StrictSeparation (origin.accuracy + 2) attempt.pair.left.code attempt.pair.right.code := by
    change StrictSeparation _ attempt.pair.left.resource.code attempt.pair.right.resource.code
    rw [AdditionProduction.readoutExact, AdditionProduction.readoutExact, ← sameShift]
    exact (strengthenSeparation origin.separation leftNear rightNear).addRight _
  exact ⟨origin, rfl, attempt, leftNear, rightNear, sameShift, gap⟩

def TranslatedOrder.order {a b shift : Real P baseDepth} {origin : StrictOrder a b}
    {la : (environment (.add a shift)).Archive} {ra : (environment (.add b shift)).Archive}
    (packet : TranslatedOrder origin shift la ra) : StrictOrder (.add a shift) (.add b shift) :=
  packet.attempt.forward packet.separation

def positiveProductAccuracy {a b : Real P baseDepth} (left : Positive a) (right : Positive b) : Nat :=
  (left.accuracy + 2) + (right.accuracy + 2) + 1

structure PositiveProduct {a b : Real P baseDepth} (left : Positive a) (right : Positive b)
    (za : (environment (zero P baseDepth)).Archive) (archive : (environment (.mul a b)).Archive) where
  private mk ::
  leftOwned : Positive a
  leftExact : leftOwned = left
  rightOwned : Positive b
  rightExact : rightOwned = right
  attempt : ComparisonAttempt (environment (zero P baseDepth)) (environment (.mul a b)) za archive
    (positiveProductAccuracy left right) (positiveProductAccuracy left right + 3)
  leftCertificate : NonzeroCode .positive (left.accuracy + 2) attempt.pair.right.resource.left.code
  rightCertificate : NonzeroCode .positive (right.accuracy + 2) attempt.pair.right.resource.right.code
  separation : StrictSeparation (positiveProductAccuracy left right) attempt.pair.left.code attempt.pair.right.code

def positiveProduct {a b : Real P baseDepth} (left : Positive a) (right : Positive b)
    (za : (environment (zero P baseDepth)).Archive) (archive : (environment (.mul a b)).Archive) :
    PositiveProduct left right za archive := by
  let p := positiveProductAccuracy left right
  let attempt := produceComparison (environment (zero P baseDepth)) (environment (.mul a b)) za archive
    p (p + 3) (PrecisionExtension.refl _)
  dsimp only [environment, mulEnvironment] at archive attempt
  have leftBeyond : PrecisionExtension (left.accuracy + 2) (p + 3) :=
    (PrecisionExtension.first (left.accuracy + 2) (right.accuracy + 2)).trans (PrecisionExtension.first _ 4)
  have rightBeyond : PrecisionExtension (right.accuracy + 2) (p + 3) :=
    (PrecisionExtension.second (left.accuracy + 2) (right.accuracy + 2)).trans (PrecisionExtension.first _ 4)
  let first := ReciprocalDomain.nonzero (.backward left) attempt.pair.right.resource.left
    (leftBeyond.trans (PrecisionExtension.refine (p + 3) _))
  let second := ReciprocalDomain.nonzero (.backward right) attempt.pair.right.resource.right
    (rightBeyond.trans (PrecisionExtension.refine (p + 3) _))
  have gap : StrictSeparation p attempt.pair.left.code attempt.pair.right.code := by
    change StrictSeparation p _ attempt.pair.right.resource.code
    rw [MultiplicationProduction.readoutExact]
    exact StrictSeparation.ofSameLeft (ReciprocalDomain.zeroStepSameValue attempt.pair.left)
      (first.mulPositive second)
  exact ⟨left, rfl, right, rfl, attempt, first, second, gap⟩

def PositiveProduct.positive {a b : Real P baseDepth} {left : Positive a} {right : Positive b}
    {za : (environment (zero P baseDepth)).Archive} {archive : (environment (.mul a b)).Archive}
    (packet : PositiveProduct left right za archive) : Positive (.mul a b) :=
  packet.attempt.forward packet.separation

def onePositive (P : CircularPresentation) (baseDepth : Nat) : Positive (one P baseDepth) := by
  let attempt := compareCurrent (zero P baseDepth) (one P baseDepth)
    (environment (zero P baseDepth)).initialArchive (environment (one P baseDepth)).initialArchive 1
  have margin : StrictSeparation 1 SignedDyadicCode.zero SignedDyadicCode.one :=
    ⟨⟨1, 1, 1, rfl, rfl⟩, 0, rfl, by decide⟩
  have unitSame : SameValue attempt.pair.right.code SignedDyadicCode.one := by
    rw [currentReadout (one P baseDepth) _ _ attempt.pair.right]
    exact constant_readout _ _
  exact attempt.forward ((margin.ofSameRight unitSame.symm).ofSameLeft
    (ReciprocalDomain.zeroStepSameValue attempt.pair.left))

/-- Fresh composite occurrence, anchored at received native archives. This
never resets an already existing composite archive or either child archive. -/
def startAdditionAt (a b : Real P baseDepth) (aa : (environment a).Archive) (ba : (environment b).Archive) :
    (environment (.add a b)).Archive :=
  RelationalRealAddition.seedAdditionArchive aa ba

def startProductAt (a b : Real P baseDepth) (aa : (environment a).Archive) (ba : (environment b).Archive) :
    (environment (.mul a b)).Archive :=
  RelationalRealMultiplication.seedMultiplicationArchive aa ba

def startNegationAt (a : Real P baseDepth) (aa : (environment a).Archive) :
    (environment (.neg a)).Archive :=
  RelationalRealNegation.seedNegationArchive aa

structure PositiveDifference {a b : Real P baseDepth} (origin : StrictOrder a b)
    (na : (environment (.neg a)).Archive) (za : (environment (zero P baseDepth)).Archive) where
  private mk ::
  translated : TranslatedOrder origin (.neg a)
    (startAdditionAt a (.neg a) origin.pair.left.next na)
    (startAdditionAt b (.neg a) origin.pair.right.next na)
  transported : OrderTransport translated.order (add_neg a) (Equivalent.refl (.add b (.neg a)))
    za translated.attempt.pair.right.next

def positiveDifference {a b : Real P baseDepth} (origin : StrictOrder a b)
    (na : (environment (.neg a)).Archive) (za : (environment (zero P baseDepth)).Archive) :
    PositiveDifference origin na za :=
  let translated := translateRight origin (.neg a)
    (startAdditionAt a (.neg a) origin.pair.left.next na)
    (startAdditionAt b (.neg a) origin.pair.right.next na)
  let transported := transportOrder translated.order (add_neg a) (Equivalent.refl _)
    za translated.attempt.pair.right.next
  ⟨translated, transported⟩

def PositiveDifference.positive {a b : Real P baseDepth} {origin : StrictOrder a b}
    {na : (environment (.neg a)).Archive} {za : (environment (zero P baseDepth)).Archive}
    (packet : PositiveDifference origin na za) : Positive (.add b (.neg a)) := packet.transported.order

/-- Algebraic cancellation at Equivalent, never equality of occurrences. -/
def differenceProductCancellation (a b c : Real P baseDepth) :
    Equivalent (.add (.mul (.add b (.neg a)) c) (.mul a c)) (.mul b c) :=
  (add_congr (add_mul b (.neg a) c) (Equivalent.refl _)).trans
    ((add_congr (add_congr (Equivalent.refl _) (neg_mul a c)) (Equivalent.refl _)).trans
      ((add_assoc (.mul b c) (.neg (.mul a c)) (.mul a c)).trans
        ((add_congr (Equivalent.refl _) (neg_add (.mul a c))).trans (add_zero _))))

structure MultipliedOrder {a b c : Real P baseDepth} (origin : StrictOrder a b) (factor : Positive c)
    (na : (environment (.neg a)).Archive) (za : (environment (zero P baseDepth)).Archive)
    (ac : (environment (.mul a c)).Archive) where
  private mk ::
  difference : PositiveDifference origin na za
  product : PositiveProduct difference.positive factor difference.positive.pair.left.next
    (startProductAt (.add b (.neg a)) c difference.positive.pair.right.next factor.pair.right.next)
  translated : TranslatedOrder product.positive (.mul a c)
    (startAdditionAt (zero P baseDepth) (.mul a c) product.attempt.pair.left.next ac)
    (startAdditionAt (.mul (.add b (.neg a)) c) (.mul a c) product.attempt.pair.right.next ac)
  transported : OrderTransport translated.order (zero_add (.mul a c)) (differenceProductCancellation a b c)
    translated.attempt.pair.left.resource.right.next
    (startProductAt b c translated.attempt.pair.right.resource.left.resource.left.resource.left.next
      translated.attempt.pair.right.resource.left.resource.right.next)

/-- Monotonicity for a received strictly positive factor only. Each operation
executes its native runtime; the last transport starts at exact owned child
successors. There is no nonnegative predicate or global sign decision. -/
def multiplyRight {a b c : Real P baseDepth} (origin : StrictOrder a b) (factor : Positive c)
    (na : (environment (.neg a)).Archive) (za : (environment (zero P baseDepth)).Archive)
    (ac : (environment (.mul a c)).Archive) : MultipliedOrder origin factor na za ac :=
  let difference := positiveDifference origin na za
  let product := positiveProduct difference.positive factor difference.positive.pair.left.next
    (startProductAt (.add b (.neg a)) c difference.positive.pair.right.next factor.pair.right.next)
  let translated := translateRight product.positive (.mul a c)
    (startAdditionAt (zero P baseDepth) (.mul a c) product.attempt.pair.left.next ac)
    (startAdditionAt (.mul (.add b (.neg a)) c) (.mul a c) product.attempt.pair.right.next ac)
  let transported := transportOrder translated.order (zero_add (.mul a c)) (differenceProductCancellation a b c)
    translated.attempt.pair.left.resource.right.next
    (startProductAt b c translated.attempt.pair.right.resource.left.resource.left.resource.left.next
      translated.attempt.pair.right.resource.left.resource.right.next)
  ⟨difference, product, translated, transported⟩

def MultipliedOrder.order {a b c : Real P baseDepth} {origin : StrictOrder a b} {factor : Positive c}
    {na : (environment (.neg a)).Archive} {za : (environment (zero P baseDepth)).Archive}
    {ac : (environment (.mul a c)).Archive} (packet : MultipliedOrder origin factor na za ac) :
    StrictOrder (.mul a c) (.mul b c) := packet.transported.order

def addOrderRight {a b : Real P baseDepth} (origin : StrictOrder a b) (shift : Real P baseDepth) :
    StrictOrder (.add a shift) (.add b shift) :=
  (translateRight origin shift
    (startAdditionAt a shift origin.pair.left.next (environment shift).initialArchive)
    (startAdditionAt b shift origin.pair.right.next (environment shift).initialArchive)).order

def addOrderLeft {a b : Real P baseDepth} (origin : StrictOrder a b) (shift : Real P baseDepth) :
    StrictOrder (.add shift a) (.add shift b) :=
  let right := addOrderRight origin shift
  (transportOrder right (add_comm a shift) (add_comm b shift)
    (startAdditionAt shift a right.pair.left.resource.right.next right.pair.left.resource.left.next)
    (startAdditionAt shift b right.pair.right.resource.right.next right.pair.right.resource.left.next)).order

def mulOrderRight {a b c : Real P baseDepth} (origin : StrictOrder a b) (factor : Positive c) :
    StrictOrder (.mul a c) (.mul b c) :=
  (multiplyRight origin factor (startNegationAt a origin.pair.left.next) factor.pair.left.next
    (startProductAt a c origin.pair.left.next factor.pair.right.next)).order

def mulOrderLeft {a b c : Real P baseDepth} (origin : StrictOrder a b) (factor : Positive c) :
    StrictOrder (.mul c a) (.mul c b) :=
  let right := mulOrderRight origin factor
  (transportOrder right (mul_comm a c) (mul_comm b c)
    (startProductAt c a right.pair.left.resource.right.next right.pair.left.resource.left.next)
    (startProductAt c b right.pair.right.resource.right.next right.pair.right.resource.left.next)).order

def addCancellation (a shift : Real P baseDepth) :
    Equivalent (.add (.add a shift) (.neg shift)) a :=
  (add_assoc _ _ _).trans ((add_congr (Equivalent.refl _) (add_neg shift)).trans (add_zero a))

def reflectAddRight {a b : Real P baseDepth} {shift : Real P baseDepth}
    (order : StrictOrder (.add a shift) (.add b shift)) : StrictOrder a b :=
  let translated := addOrderRight order (.neg shift)
  (transportOrder translated (addCancellation a shift) (addCancellation b shift)
    translated.pair.left.resource.left.resource.left.next
    translated.pair.right.resource.left.resource.left.next).order

def apartAddRight {a b : Real P baseDepth} (apart : Apartness a b) (shift : Real P baseDepth) :
    Apartness (.add a shift) (.add b shift) :=
  match apart with
  | .forward order => .forward (addOrderRight order shift)
  | .backward order => .backward (addOrderRight order shift)

def apartMulPositiveRight {a b c : Real P baseDepth} (apart : Apartness a b) (factor : Positive c) :
    Apartness (.mul a c) (.mul b c) :=
  match apart with
  | .forward order => .forward (mulOrderRight order factor)
  | .backward order => .backward (mulOrderRight order factor)

/-- Quotient-free constructive ordered-field laws at Equivalent. The inverse
domain is received Apartness to zero and multiplication monotonicity receives
Positive. This is not a total/extensive ordered-field instance. -/
structure ConstructiveOrderedFieldLaws (P : CircularPresentation) (baseDepth : Nat) where
  additive : AdditiveGroupLaws P baseDepth
  multiplicative : MultiplicativeLaws P baseDepth
  unitPositive : Positive (one P baseDepth)
  irreflexive : {a : Real P baseDepth} → StrictOrder a a → Empty
  asymmetric : {a b : Real P baseDepth} → StrictOrder a b → StrictOrder b a → Empty
  transitive : {a b c : Real P baseDepth} → StrictOrder a b → StrictOrder b c → StrictOrder a c
  cotransitive : {a b : Real P baseDepth} → (order : StrictOrder a b) → (middle : Real P baseDepth) →
    (ma : (environment middle).Archive) → StrictOrder a middle ⊕ StrictOrder middle b
  transport : {a b c d : Real P baseDepth} → StrictOrder a b → Equivalent a c → Equivalent b d →
    (environment c).Archive → (environment d).Archive → StrictOrder c d
  translateRight : {a b : Real P baseDepth} → StrictOrder a b → (shift : Real P baseDepth) →
    StrictOrder (.add a shift) (.add b shift)
  translateLeft : {a b : Real P baseDepth} → StrictOrder a b → (shift : Real P baseDepth) →
    StrictOrder (.add shift a) (.add shift b)
  reflectTranslation : {a b shift : Real P baseDepth} → StrictOrder (.add a shift) (.add b shift) → StrictOrder a b
  positiveProduct : {a b : Real P baseDepth} → Positive a → Positive b → Positive (.mul a b)
  multiplyPositiveRight : {a b c : Real P baseDepth} → StrictOrder a b → Positive c → StrictOrder (.mul a c) (.mul b c)
  multiplyPositiveLeft : {a b c : Real P baseDepth} → StrictOrder a b → Positive c → StrictOrder (.mul c a) (.mul c b)
  inverseUnitRight : (a : Real P baseDepth) → (witness : Apartness a (zero P baseDepth)) →
    Equivalent (.mul a (RelationalRealInverse.inverse a witness)) (one P baseDepth)
  inverseUnitLeft : (a : Real P baseDepth) → (witness : Apartness a (zero P baseDepth)) →
    Equivalent (.mul (RelationalRealInverse.inverse a witness) a) (one P baseDepth)
  inverseWitnessIndependent : (a : Real P baseDepth) → (first second : Apartness a (zero P baseDepth)) →
    Equivalent (RelationalRealInverse.inverse a first) (RelationalRealInverse.inverse a second)

def orderedFieldLaws (P : CircularPresentation) (baseDepth : Nat) : ConstructiveOrderedFieldLaws P baseDepth where
  additive := additiveGroupLaws P baseDepth
  multiplicative := multiplicativeLaws P baseDepth
  unitPositive := onePositive P baseDepth
  irreflexive := StrictOrder.irreflexive
  asymmetric := StrictOrder.asymmetric
  transitive := StrictOrder.transitive
  cotransitive order middle ma := (cotransition order middle order.pair.left.next ma order.pair.right.next).orders
  transport order left right ca da := (transportOrder order left right ca da).order
  translateRight := addOrderRight
  translateLeft := addOrderLeft
  reflectTranslation := reflectAddRight
  positiveProduct left right := (positiveProduct left right left.pair.left.next
    (startProductAt _ _ left.pair.right.next right.pair.right.next)).positive
  multiplyPositiveRight := mulOrderRight
  multiplyPositiveLeft := mulOrderLeft
  inverseUnitRight := RelationalRealInverse.mul_inverse
  inverseUnitLeft := RelationalRealInverse.inverse_mul
  inverseWitnessIndependent := RelationalRealInverse.witness_independent

/-- The same constructive order with numerical-future algebra and transport.
None of these fields compares rich or live events across environments. -/
structure ConstructiveOrderedFieldFutureLaws (P : CircularPresentation) (baseDepth : Nat) where
  ordered : ConstructiveOrderedFieldLaws P baseDepth
  additive : AdditiveGroupFutureLaws P baseDepth
  multiplicative : MultiplicativeFutureLaws P baseDepth
  transport : {a b c d : Real P baseDepth} → StrictOrder a b → NumericalFutureEquivalent a c →
    NumericalFutureEquivalent b d → (environment c).Archive → (environment d).Archive → StrictOrder c d
  inverseUnitRight : (a : Real P baseDepth) → (witness : Apartness a (zero P baseDepth)) →
    NumericalFutureEquivalent (.mul a (RelationalRealInverse.inverse a witness)) (one P baseDepth)
  inverseUnitLeft : (a : Real P baseDepth) → (witness : Apartness a (zero P baseDepth)) →
    NumericalFutureEquivalent (.mul (RelationalRealInverse.inverse a witness) a) (one P baseDepth)
  inverseWitnessIndependent : (a : Real P baseDepth) → (first second : Apartness a (zero P baseDepth)) →
    NumericalFutureEquivalent (RelationalRealInverse.inverse a first) (RelationalRealInverse.inverse a second)

def orderedFieldFutureLaws (P : CircularPresentation) (baseDepth : Nat) : ConstructiveOrderedFieldFutureLaws P baseDepth where
  ordered := orderedFieldLaws P baseDepth
  additive := additiveGroupFutureLaws P baseDepth
  multiplicative := multiplicativeFutureLaws P baseDepth
  transport order left right ca da := (transportOrderFutures order left right ca da).order
  inverseUnitRight := RelationalRealInverse.mul_inverse_futures
  inverseUnitLeft := RelationalRealInverse.inverse_mul_futures
  inverseWitnessIndependent := RelationalRealInverse.witness_independent_futures

end RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.TranslatedOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.translateRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.TranslatedOrder.order
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.positiveProductAccuracy
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.PositiveProduct
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.positiveProduct
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.PositiveProduct.positive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.onePositive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.startAdditionAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.startProductAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.startNegationAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.PositiveDifference
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.positiveDifference
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.PositiveDifference.positive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.differenceProductCancellation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.MultipliedOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.multiplyRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.MultipliedOrder.order
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.addOrderRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.addOrderLeft
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.mulOrderRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.mulOrderLeft
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.addCancellation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.reflectAddRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.apartAddRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.apartMulPositiveRight
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.ConstructiveOrderedFieldLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.orderedFieldLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.ConstructiveOrderedFieldFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField.orderedFieldFutureLaws
/- AXIOM_AUDIT_END -/
