import RelationalPerimeter.Constitution.Reals.RelationalRealMultiplicativeLaws
import RelationalPerimeter.Constitution.Reals.DyadicOrder

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Positive order from owned finite executions

A total finite attempt is not a decision of real order. Its inconclusive
branch only bounds the two answers of that attempt. A successful witness owns
both native Steps, their current archives, an oriented strict margin and the
three-bit response budget. No persistent classifier runtime or memory is
invented: subsequent executions use the existing native successor archives.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealOrder
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition
variable {P : CircularPresentation} {baseDepth : Nat}

structure ComparisonPair (left right : Service P baseDepth)
    (leftArchive : left.Archive) (rightArchive : right.Archive) (response : Nat) where
  private mk ::
  left : Step left leftArchive response
  right : Step right rightArchive response

def executePair (left right : Service P baseDepth) (la : left.Archive) (ra : right.Archive) (response : Nat) :
    ComparisonPair left right la ra response :=
  let first := perform left la response
  let second := perform right ra response
  ⟨first, second⟩

inductive FiniteDirection (p : Nat) (left right : SignedDyadicCode) where
  | forward : StrictSeparation p left right → FiniteDirection p left right
  | backward : StrictSeparation p right left → FiniteDirection p left right
  | inconclusive : DirectedUpper p right left → DirectedUpper p left right → FiniteDirection p left right

def classifyFinite (p : Nat) (left right : SignedDyadicCode) : FiniteDirection p left right :=
  match inspectGap p left right with
  | .inl gap => .forward gap
  | .inr upper => match inspectGap p right left with
    | .inl gap => .backward gap
    | .inr reverse => .inconclusive upper reverse

structure ComparisonAttempt (left right : Service P baseDepth)
    (la : left.Archive) (ra : right.Archive) (accuracy response : Nat) where
  private mk ::
  beyond : PrecisionExtension (accuracy + 3) response
  pair : ComparisonPair left right la ra response
  direction : FiniteDirection accuracy pair.left.code pair.right.code
  classified : direction = classifyFinite accuracy pair.left.code pair.right.code

def produceComparison (left right : Service P baseDepth) (la : left.Archive) (ra : right.Archive)
    (accuracy response : Nat) (beyond : PrecisionExtension (accuracy + 3) response) :
    ComparisonAttempt left right la ra accuracy response :=
  let pair := executePair left right la ra response
  let direction := classifyFinite accuracy pair.left.code pair.right.code
  ⟨beyond, pair, direction, rfl⟩

def compareCurrent (left right : Real P baseDepth) (la : (environment left).Archive)
    (ra : (environment right).Archive) (accuracy : Nat) :=
  produceComparison (environment left) (environment right) la ra accuracy (accuracy + 3) (PrecisionExtension.refl _)

def continueComparison {left right : Service P baseDepth} {la : left.Archive} {ra : right.Archive} {p r : Nat}
    (prior : ComparisonAttempt left right la ra p r) (accuracy : Nat) :
    ComparisonAttempt left right prior.pair.left.next prior.pair.right.next accuracy (accuracy + 3) :=
  produceComparison left right prior.pair.left.next prior.pair.right.next accuracy (accuracy + 3) (PrecisionExtension.refl _)

structure StrictOrder (left right : Real P baseDepth) where
  private mk ::
  leftArchive : (environment left).Archive
  rightArchive : (environment right).Archive
  accuracy : Nat
  response : Nat
  beyond : PrecisionExtension (accuracy + 3) response
  pair : ComparisonPair (environment left) (environment right) leftArchive rightArchive response
  separation : StrictSeparation accuracy pair.left.code pair.right.code

inductive Apartness (left right : Real P baseDepth) where
  | forward : StrictOrder left right → Apartness left right
  | backward : StrictOrder right left → Apartness left right

def ComparisonAttempt.apartness? {left right : Real P baseDepth}
    {la : (environment left).Archive} {ra : (environment right).Archive} {p r : Nat}
    (attempt : ComparisonAttempt (environment left) (environment right) la ra p r) : Option (Apartness left right) :=
  match attempt.direction with
  | .forward gap => some (.forward ⟨la, ra, p, r, attempt.beyond, attempt.pair, gap⟩)
  | .backward gap => some (.backward ⟨ra, la, p, r, attempt.beyond,
      ⟨attempt.pair.right, attempt.pair.left⟩, gap⟩)
  | .inconclusive _ _ => none

/-- Extract the certificate actually produced by the attempt. The received
margin only excludes its other finite branches; it cannot replace the Steps. -/
def ComparisonAttempt.forward {left right : Real P baseDepth}
    {la : (environment left).Archive} {ra : (environment right).Archive} {p r : Nat}
    (attempt : ComparisonAttempt (environment left) (environment right) la ra p r)
    (expected : StrictSeparation p attempt.pair.left.code attempt.pair.right.code) : StrictOrder left right :=
  match attempt.direction with
  | .forward received => ⟨la, ra, p, r, attempt.beyond, attempt.pair, received⟩
  | .backward reverse => (expected.refuteUpper (reverse.forwardUpper p)).elim
  | .inconclusive upper _ => (expected.refuteUpper upper).elim

def Apartness.symm {left right : Real P baseDepth} : Apartness left right → Apartness right left
  | .forward order => .backward order
  | .backward order => .forward order

def Positive (real : Real P baseDepth) : Type := StrictOrder (zero P baseDepth) real
def Negative (real : Real P baseDepth) : Type := StrictOrder real (zero P baseDepth)

/-- Empty is derived from the positive margin and coherence, not a decision
procedure for equality or apartness. -/
def StrictOrder.irreflexive {real : Real P baseDepth} (order : StrictOrder real real) : Empty :=
  order.separation.refuteUpper (DirectedUpper.ofNear
    ((coherent real).near order.accuracy order.response order.response order.pair.right order.pair.left
      ((PrecisionExtension.first order.accuracy 3).trans order.beyond)
      ((PrecisionExtension.first order.accuracy 3).trans order.beyond)))

def Apartness.irreflexive {real : Real P baseDepth} : Apartness real real → Empty
  | .forward order => order.irreflexive
  | .backward order => order.irreflexive

/-- The result retains the original witness and the exact newly produced pair. -/
structure HistoricalRefinement {left right : Real P baseDepth} (origin : StrictOrder left right)
    (response : Nat) where
  private mk ::
  originOwned : StrictOrder left right
  originExact : originOwned = origin
  pair : ComparisonPair (environment left) (environment right) origin.pair.left.next origin.pair.right.next response
  beyond : PrecisionExtension (origin.accuracy + 5) response
  leftNear : Near (origin.accuracy + 2) origin.pair.left.code pair.left.code
  rightNear : Near (origin.accuracy + 2) origin.pair.right.code pair.right.code
  separation : StrictSeparation (origin.accuracy + 2) pair.left.code pair.right.code

def refineHistorical {left right : Real P baseDepth} (origin : StrictOrder left right)
    (response : Nat) (beyond : PrecisionExtension (origin.accuracy + 5) response) : HistoricalRefinement origin response :=
  let pair := executePair (environment left) (environment right) origin.pair.left.next origin.pair.right.next response
  let budget : PrecisionExtension (origin.accuracy + 3) response :=
    (PrecisionExtension.first (origin.accuracy + 3) 2).trans beyond
  let first := (coherent left).near (origin.accuracy + 3) _ _ origin.pair.left pair.left origin.beyond budget
  let second := (coherent right).near (origin.accuracy + 3) _ _ origin.pair.right pair.right origin.beyond budget
  let leftNear := first.weaken (PrecisionExtension.next (origin.accuracy + 2))
  let rightNear := second.weaken (PrecisionExtension.next (origin.accuracy + 2))
  ⟨origin, rfl, pair, beyond, leftNear, rightNear, strengthenSeparation origin.separation leftNear rightNear⟩

def HistoricalRefinement.order {left right : Real P baseDepth} {origin : StrictOrder left right} {response : Nat}
    (refinement : HistoricalRefinement origin response) : StrictOrder left right :=
  ⟨origin.pair.left.next, origin.pair.right.next, origin.accuracy + 2, response,
    refinement.beyond, refinement.pair, refinement.separation⟩

/-- Transport thresholds are finite data selected from this received witness. -/
def transportPrecisions {a b c d : Real P baseDepth} (origin : StrictOrder a b)
    (left : Equivalent a c) (right : Equivalent b d) : List Nat :=
  [origin.accuracy + 5, left.threshold (origin.accuracy + 3), right.threshold (origin.accuracy + 3)]

structure OrderTransport {a b c d : Real P baseDepth} (origin : StrictOrder a b)
    (left : Equivalent a c) (right : Equivalent b d)
    (ca : (environment c).Archive) (da : (environment d).Archive) where
  private mk ::
  originOwned : StrictOrder a b
  originExact : originOwned = origin
  source : ComparisonPair (environment a) (environment b) origin.pair.left.next origin.pair.right.next
    (precisionPool (transportPrecisions origin left right))
  target : ComparisonPair (environment c) (environment d) ca da (precisionPool (transportPrecisions origin left right))
  sourceLeftNear : Near (origin.accuracy + 3) origin.pair.left.code source.left.code
  sourceRightNear : Near (origin.accuracy + 3) origin.pair.right.code source.right.code
  equivalentLeftNear : Near (origin.accuracy + 3) source.left.code target.left.code
  equivalentRightNear : Near (origin.accuracy + 3) source.right.code target.right.code
  separation : StrictSeparation (origin.accuracy + 2) target.left.code target.right.code

def transportOrder {a b c d : Real P baseDepth} (origin : StrictOrder a b)
    (left : Equivalent a c) (right : Equivalent b d)
    (ca : (environment c).Archive) (da : (environment d).Archive) : OrderTransport origin left right ca da := by
  let pool := transportPrecisions origin left right
  let response := precisionPool pool
  let source := executePair (environment a) (environment b) origin.pair.left.next origin.pair.right.next response
  let target := executePair (environment c) (environment d) ca da response
  have minimum : PrecisionMember (origin.accuracy + 5) pool := .here
  have leftMember : PrecisionMember (left.threshold (origin.accuracy + 3)) pool := .there .here
  have rightMember : PrecisionMember (right.threshold (origin.accuracy + 3)) pool := .there (.there .here)
  have beyond : PrecisionExtension (origin.accuracy + 3) response :=
    (PrecisionExtension.first (origin.accuracy + 3) 2).trans minimum.extension
  have first := (coherent a).near (origin.accuracy + 3) _ _ origin.pair.left source.left origin.beyond beyond
  have second := (coherent b).near (origin.accuracy + 3) _ _ origin.pair.right source.right origin.beyond beyond
  have leftNear : Near (origin.accuracy + 3) source.left.code target.left.code := by
    rw [currentReadout a _ _ source.left, currentReadout c _ _ target.left]
    exact left.near _ _ _ leftMember.extension leftMember.extension
  have rightNear : Near (origin.accuracy + 3) source.right.code target.right.code := by
    rw [currentReadout b _ _ source.right, currentReadout d _ _ target.right]
    exact right.near _ _ _ rightMember.extension rightMember.extension
  exact ⟨origin, rfl, source, target, first, second, leftNear, rightNear,
    strengthenSeparation origin.separation (Near.compose first leftNear) (Near.compose second rightNear)⟩

def OrderTransport.order {a b c d : Real P baseDepth} {origin : StrictOrder a b}
    {left : Equivalent a c} {right : Equivalent b d} {ca : (environment c).Archive} {da : (environment d).Archive}
    (transported : OrderTransport origin left right ca da) : StrictOrder c d :=
  ⟨ca, da, origin.accuracy + 2, _, (show PrecisionMember (origin.accuracy + 5)
    (transportPrecisions origin left right) from .here).extension, transported.target, transported.separation⟩

def transportOrderFutures {a b c d : Real P baseDepth} (origin : StrictOrder a b)
    (left : NumericalFutureEquivalent a c) (right : NumericalFutureEquivalent b d)
    (ca : (environment c).Archive) (da : (environment d).Archive) :=
  transportOrder origin left.toEquivalent right.toEquivalent ca da

def StrictOrder.asymmetric {a b : Real P baseDepth} (first : StrictOrder a b) (reverse : StrictOrder b a) : Empty := by
  let response := (reverse.accuracy + 5) + (first.accuracy + 3)
  let refined := refineHistorical reverse response (PrecisionExtension.first _ _)
  have fine : PrecisionExtension (first.accuracy + 2) response :=
    (PrecisionExtension.next (first.accuracy + 2)).trans (PrecisionExtension.second _ _)
  have old : PrecisionExtension (first.accuracy + 2) first.response :=
    (PrecisionExtension.next (first.accuracy + 2)).trans first.beyond
  have leftNear := (coherent a).near (first.accuracy + 2) _ _ first.pair.left refined.pair.right old fine
  have rightNear := (coherent b).near (first.accuracy + 2) _ _ first.pair.right refined.pair.left old fine
  exact first.separation.refuteUpper (DirectedUpper.compose
    (DirectedUpper.compose (DirectedUpper.ofNear rightNear) (refined.separation.forwardUpper (first.accuracy + 2)))
    ((DirectedUpper.ofNear leftNear.symm).weaken (PrecisionExtension.next (first.accuracy + 1))))

def signsExclusive {real : Real P baseDepth} (positive : Positive real) (negative : Negative real) : Empty :=
  positive.asymmetric negative

def StrictOrder.refutesEquivalent {a b : Real P baseDepth} (order : StrictOrder a b) (same : Equivalent a b) : Empty :=
  (transportOrder order (Equivalent.refl a) same.symm (environment a).initialArchive (environment a).initialArchive).order.irreflexive

structure ComparisonTriple (left middle right : Service P baseDepth)
    (la : left.Archive) (ma : middle.Archive) (ra : right.Archive) (response : Nat) where
  private mk ::
  leftMiddle : ComparisonPair left middle la ma response
  right : Step right ra response

def executeTriple (left middle right : Service P baseDepth)
    (la : left.Archive) (ma : middle.Archive) (ra : right.Archive) (response : Nat) :
    ComparisonTriple left middle right la ma ra response :=
  let first := executePair left middle la ma response
  let last := perform right ra response
  ⟨first, last⟩

structure Cotransition {a c : Real P baseDepth} (origin : StrictOrder a c) (middle : Real P baseDepth)
    (aa : (environment a).Archive) (ma : (environment middle).Archive) (ca : (environment c).Archive) where
  private mk ::
  originOwned : StrictOrder a c
  originExact : originOwned = origin
  triple : ComparisonTriple (environment a) (environment middle) (environment c) aa ma ca (origin.accuracy + 5)
  leftNear : Near (origin.accuracy + 2) origin.pair.left.code triple.leftMiddle.left.code
  rightNear : Near (origin.accuracy + 2) origin.pair.right.code triple.right.code
  choice : StrictSeparation (origin.accuracy + 2) triple.leftMiddle.left.code triple.leftMiddle.right.code ⊕
    StrictSeparation (origin.accuracy + 2) triple.leftMiddle.right.code triple.right.code

/-- Four p+2 bounds consume exactly two bits. The middle execution is shared
by both comparisons; neither a global trichotomy nor a real equality is used. -/
def cotransition {a c : Real P baseDepth} (origin : StrictOrder a c) (middle : Real P baseDepth)
    (aa : (environment a).Archive) (ma : (environment middle).Archive) (ca : (environment c).Archive) :
    Cotransition origin middle aa ma ca := by
  let triple := executeTriple (environment a) (environment middle) (environment c) aa ma ca (origin.accuracy + 5)
  have old : PrecisionExtension (origin.accuracy + 2) origin.response :=
    (PrecisionExtension.next (origin.accuracy + 2)).trans origin.beyond
  have fine : PrecisionExtension (origin.accuracy + 2) (origin.accuracy + 5) := PrecisionExtension.first _ 3
  let leftNear := (coherent a).near (origin.accuracy + 2) _ _ origin.pair.left triple.leftMiddle.left old fine
  let rightNear := (coherent c).near (origin.accuracy + 2) _ _ origin.pair.right triple.right old fine
  refine ⟨origin, rfl, triple, leftNear, rightNear, ?_⟩
  cases inspectGap (origin.accuracy + 2) triple.leftMiddle.left.code triple.leftMiddle.right.code with
  | inl gap => exact .inl gap
  | inr upper =>
      cases inspectGap (origin.accuracy + 2) triple.leftMiddle.right.code triple.right.code with
      | inl gap => exact .inr gap
      | inr second =>
          exact (origin.separation.refuteUpper (DirectedUpper.compose
            (DirectedUpper.compose (DirectedUpper.ofNear rightNear) second)
            (DirectedUpper.compose upper (DirectedUpper.ofNear leftNear.symm)))).elim

def Cotransition.orders {a c : Real P baseDepth} {origin : StrictOrder a c} {middle : Real P baseDepth}
    {aa : (environment a).Archive} {ma : (environment middle).Archive} {ca : (environment c).Archive}
    (transition : Cotransition origin middle aa ma ca) : StrictOrder a middle ⊕ StrictOrder middle c :=
  match transition.choice with
  | .inl gap => .inl ⟨aa, ma, origin.accuracy + 2, origin.accuracy + 5,
      PrecisionExtension.refl _, transition.triple.leftMiddle, gap⟩
  | .inr gap => .inr ⟨ma, ca, origin.accuracy + 2, origin.accuracy + 5,
      PrecisionExtension.refl _, ⟨transition.triple.leftMiddle.right, transition.triple.right⟩, gap⟩

def Apartness.cotransitive {a c : Real P baseDepth} (apart : Apartness a c) (middle : Real P baseDepth)
    (aa : (environment a).Archive) (ma : (environment middle).Archive) (ca : (environment c).Archive) :
    Apartness a middle ⊕ Apartness middle c :=
  match apart with
  | .forward origin => match (cotransition origin middle aa ma ca).orders with
    | .inl first => .inl (.forward first)
    | .inr second => .inr (.forward second)
  | .backward origin => match (cotransition origin middle ca ma aa).orders with
    | .inl first => .inr (.backward first)
    | .inr second => .inl (.backward second)

def transportApartness {a b c d : Real P baseDepth} (apart : Apartness a b)
    (left : Equivalent a c) (right : Equivalent b d)
    (ca : (environment c).Archive) (da : (environment d).Archive) : Apartness c d :=
  match apart with
  | .forward order => .forward (transportOrder order left right ca da).order
  | .backward order => .backward (transportOrder order right left da ca).order

def transportApartnessFutures {a b c d : Real P baseDepth} (apart : Apartness a b)
    (left : NumericalFutureEquivalent a c) (right : NumericalFutureEquivalent b d)
    (ca : (environment c).Archive) (da : (environment d).Archive) : Apartness c d :=
  transportApartness apart left.toEquivalent right.toEquivalent ca da

def StrictOrder.transitive {a b c : Real P baseDepth} (first : StrictOrder a b) (second : StrictOrder b c) :
    StrictOrder a c :=
  match (cotransition first c first.pair.left.next second.pair.right.next first.pair.right.next).orders with
  | .inl order => order
  | .inr reverse => (second.asymmetric reverse).elim

def Apartness.refutesEquivalent {a b : Real P baseDepth} (apart : Apartness a b) (same : Equivalent a b) : Empty :=
  match apart with
  | .forward order => order.refutesEquivalent same
  | .backward order => order.refutesEquivalent same.symm

/-- A received equivalence excludes successful finite branches. There is no
converse: an unsuccessful finite attempt does not decide the real relation. -/
theorem ComparisonAttempt.noneOfEquivalent {a b : Real P baseDepth}
    {aa : (environment a).Archive} {ba : (environment b).Archive} {p r : Nat}
    (attempt : ComparisonAttempt (environment a) (environment b) aa ba p r) (same : Equivalent a b) :
    attempt.apartness? = none := by
  cases result : attempt.apartness? with
  | none => rfl
  | some apart => exact (apart.refutesEquivalent same).elim

/-- Sign is the oriented comparison with an actually executed zero operand. -/
def signCurrent (real : Real P baseDepth) (zeroArchive : (environment (zero P baseDepth)).Archive)
    (archive : (environment real).Archive) (accuracy : Nat) :=
  compareCurrent (zero P baseDepth) real zeroArchive archive accuracy

def ComparisonAttempt.sign? {real : Real P baseDepth}
    {za : (environment (zero P baseDepth)).Archive} {ra : (environment real).Archive} {p r : Nat}
    (attempt : ComparisonAttempt (environment (zero P baseDepth)) (environment real) za ra p r) :
    Option (Positive real ⊕ Negative real) :=
  match attempt.apartness? with
  | some (.forward positive) => some (.inl positive)
  | some (.backward negative) => some (.inr negative)
  | none => none

structure NegatedOrder {a b : Real P baseDepth} (origin : StrictOrder a b)
    (ba : (environment (.neg b)).Archive) (aa : (environment (.neg a)).Archive) where
  private mk ::
  originOwned : StrictOrder a b
  originExact : originOwned = origin
  pair : ComparisonPair (environment (.neg b)) (environment (.neg a)) ba aa (origin.accuracy + 5)
  leftNear : Near (origin.accuracy + 2) origin.pair.right.code.neg pair.left.code
  rightNear : Near (origin.accuracy + 2) origin.pair.left.code.neg pair.right.code
  separation : StrictSeparation (origin.accuracy + 2) pair.left.code pair.right.code

def negateOrder {a b : Real P baseDepth} (origin : StrictOrder a b)
    (ba : (environment (.neg b)).Archive) (aa : (environment (.neg a)).Archive) : NegatedOrder origin ba aa := by
  let pair := executePair (environment (.neg b)) (environment (.neg a)) ba aa (origin.accuracy + 5)
  dsimp only [environment, RelationalRealNegation.negEnvironment] at ba aa pair
  have old : PrecisionExtension (origin.accuracy + 2) origin.response :=
    (PrecisionExtension.next (origin.accuracy + 2)).trans origin.beyond
  have fine : PrecisionExtension (origin.accuracy + 2) (origin.accuracy + 5) := PrecisionExtension.first _ 3
  have leftNear : Near (origin.accuracy + 2) origin.pair.right.code.neg pair.left.code := by
    change Near _ _ pair.left.resource.code
    rw [RelationalRealNegation.NegationProduction.readoutExact]
    exact ((coherent b).near _ _ _ origin.pair.right pair.left.resource.source old fine).neg
  have rightNear : Near (origin.accuracy + 2) origin.pair.left.code.neg pair.right.code := by
    change Near _ _ pair.right.resource.code
    rw [RelationalRealNegation.NegationProduction.readoutExact]
    exact ((coherent a).near _ _ _ origin.pair.left pair.right.resource.source old fine).neg
  exact ⟨origin, rfl, pair, leftNear, rightNear, strengthenSeparation origin.separation.negReverse leftNear rightNear⟩

def NegatedOrder.order {a b : Real P baseDepth} {origin : StrictOrder a b}
    {ba : (environment (.neg b)).Archive} {aa : (environment (.neg a)).Archive}
    (negated : NegatedOrder origin ba aa) : StrictOrder (.neg b) (.neg a) :=
  ⟨ba, aa, origin.accuracy + 2, origin.accuracy + 5, PrecisionExtension.refl _, negated.pair, negated.separation⟩

/-! ## Downstream numerical projections and fresh executable reflection -/

structure PresentationOrder (left right : EffectiveDyadicPresentation) where
  accuracy : Nat
  response : Nat
  beyond : PrecisionExtension (accuracy + 3) response
  separation : StrictSeparation accuracy (left.approximation response) (right.approximation response)

def PresentationApartness (left right : EffectiveDyadicPresentation) : Type :=
  PresentationOrder left right ⊕ PresentationOrder right left

def StrictOrder.toPresentation {a b : Real P baseDepth} (order : StrictOrder a b) :
    PresentationOrder (RelationalRealAddition.toPresentation a) (RelationalRealAddition.toPresentation b) := by
  have gap := order.separation
  rw [currentReadout a _ _ order.pair.left, currentReadout b _ _ order.pair.right] at gap
  exact ⟨order.accuracy, order.response, order.beyond, gap⟩

/-- This produces fresh native Steps at the received current archives. It
does not reconstruct the erased occurrences of the numerical projection. -/
def reflectPresentationOrder {a b : Real P baseDepth}
    (numeric : PresentationOrder (RelationalRealAddition.toPresentation a) (RelationalRealAddition.toPresentation b))
    (aa : (environment a).Archive) (ba : (environment b).Archive) : StrictOrder a b := by
  let attempt := produceComparison (environment a) (environment b) aa ba numeric.accuracy numeric.response numeric.beyond
  have gap : StrictSeparation numeric.accuracy attempt.pair.left.code attempt.pair.right.code := by
    rw [currentReadout a _ _ attempt.pair.left, currentReadout b _ _ attempt.pair.right]
    exact numeric.separation
  exact attempt.forward gap

def Apartness.toPresentation {a b : Real P baseDepth} (apart : Apartness a b) :
    PresentationApartness (RelationalRealAddition.toPresentation a) (RelationalRealAddition.toPresentation b) :=
  match apart with
  | .forward order => .inl order.toPresentation
  | .backward order => .inr order.toPresentation

def reflectPresentationApartness {a b : Real P baseDepth}
    (numeric : PresentationApartness (RelationalRealAddition.toPresentation a) (RelationalRealAddition.toPresentation b))
    (aa : (environment a).Archive) (ba : (environment b).Archive) : Apartness a b :=
  match numeric with
  | .inl order => .forward (reflectPresentationOrder order aa ba)
  | .inr order => .backward (reflectPresentationOrder order ba aa)

def realizePresentationOrder (left right : EffectiveDyadicPresentation) (numeric : PresentationOrder left right)
    (aa : (environment (ofPresentation P baseDepth left)).Archive)
    (ba : (environment (ofPresentation P baseDepth right)).Archive) :
    StrictOrder (ofPresentation P baseDepth left) (ofPresentation P baseDepth right) := by
  let attempt := produceComparison (environment (ofPresentation P baseDepth left)) (environment (ofPresentation P baseDepth right))
    aa ba numeric.accuracy numeric.response numeric.beyond
  have gap : StrictSeparation numeric.accuracy attempt.pair.left.code attempt.pair.right.code := by
    rw [currentReadout _ _ _ attempt.pair.left, currentReadout _ _ _ attempt.pair.right,
      ofPresentation_readout, ofPresentation_readout]
    exact numeric.separation
  exact attempt.forward gap

def CarrierOrder (left right : EffectiveCauchyReal.Carrier) : Type :=
  PresentationOrder (EffectiveCauchyReal.toPresentation left) (EffectiveCauchyReal.toPresentation right)

def CarrierApartness (left right : EffectiveCauchyReal.Carrier) : Type := CarrierOrder left right ⊕ CarrierOrder right left

def StrictOrder.toCarrier {a b : Real P baseDepth} (order : StrictOrder a b) : CarrierOrder (toCarrier a) (toCarrier b) :=
  ⟨order.accuracy, order.response, order.beyond, order.toPresentation.separation⟩

def reflectCarrierOrder {a b : Real P baseDepth} (numeric : CarrierOrder (toCarrier a) (toCarrier b))
    (aa : (environment a).Archive) (ba : (environment b).Archive) : StrictOrder a b :=
  reflectPresentationOrder ⟨numeric.accuracy, numeric.response, numeric.beyond, numeric.separation⟩ aa ba

def Apartness.toCarrier {a b : Real P baseDepth} (apart : Apartness a b) : CarrierApartness (toCarrier a) (toCarrier b) :=
  match apart with
  | .forward order => .inl order.toCarrier
  | .backward order => .inr order.toCarrier

def reflectCarrierApartness {a b : Real P baseDepth} (numeric : CarrierApartness (toCarrier a) (toCarrier b))
    (aa : (environment a).Archive) (ba : (environment b).Archive) : Apartness a b :=
  match numeric with
  | .inl order => .forward (reflectCarrierOrder order aa ba)
  | .inr order => .backward (reflectCarrierOrder order ba aa)

def realizeCarrierOrder (left right : EffectiveCauchyReal.Carrier) (numeric : CarrierOrder left right)
    (aa : (environment (ofCarrier P baseDepth left)).Archive) (ba : (environment (ofCarrier P baseDepth right)).Archive) :
    StrictOrder (ofCarrier P baseDepth left) (ofCarrier P baseDepth right) :=
  realizePresentationOrder _ _ numeric aa ba

end RelationalPerimeter.Constitution.Reals.RelationalRealOrder

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonPair
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.executePair
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.FiniteDirection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.classifyFinite
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonAttempt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.produceComparison
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.compareCurrent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.continueComparison
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonAttempt.apartness?
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonAttempt.forward
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness.symm
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Positive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Negative
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder.irreflexive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness.irreflexive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.HistoricalRefinement
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.refineHistorical
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.HistoricalRefinement.order
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.transportPrecisions
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.OrderTransport
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.transportOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.OrderTransport.order
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.transportOrderFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder.asymmetric
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.signsExclusive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder.refutesEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonTriple
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.executeTriple
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Cotransition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.cotransition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Cotransition.orders
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness.cotransitive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.transportApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.transportApartnessFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder.transitive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness.refutesEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonAttempt.noneOfEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.signCurrent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.ComparisonAttempt.sign?
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.NegatedOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.negateOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.NegatedOrder.order
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.PresentationOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.PresentationApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder.toPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.reflectPresentationOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness.toPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.reflectPresentationApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.realizePresentationOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.CarrierOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.CarrierApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.StrictOrder.toCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.reflectCarrierOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.Apartness.toCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.reflectCarrierApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealOrder.realizeCarrierOrder
/- AXIOM_AUDIT_END -/
