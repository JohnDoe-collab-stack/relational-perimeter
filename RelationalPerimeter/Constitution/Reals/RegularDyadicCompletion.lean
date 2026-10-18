import RelationalPerimeter.Constitution.Reals.RegularDyadicNameOrderedField
import RelationalPerimeter.Constitution.Reals.PresentedDyadicOrderedField

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion
open PresentedDyadicCompletion RegularDyadicName

/-- The received name itself is the computational carrier. -/
def regularPresentedCore : PresentedDyadicStructure where
  Carrier := RegularDyadicName
  approximation := RegularDyadicName.approximation
  modulus _ p := p
  modulusMonotone _ {_ _} extension := extension
  coherent := RegularDyadicName.coherent
  dyadic := constantName
  dyadicExact := constantNameSameValue
  Equivalent := NameEquivalent
  equivalentRefl := NameEquivalent.refl
  equivalentSymm := NameEquivalent.symm
  equivalentTrans := NameEquivalent.trans
  toApprox same := ⟨same.responseThreshold, same.responseThreshold, same.near⟩
  fromApprox same := {
    responseThreshold := fun p => max (same.firstThreshold p) (same.secondThreshold p)
    near := fun p r s hr hs => same.near p r s
      ((PrecisionExtension.ofLe (regularMaxLeft _ _)).trans hr)
      ((PrecisionExtension.ofLe (regularMaxRight _ _)).trans hs) }

/-- Structural adaptation; no term, modulus or Cauchy production is changed. -/
def regularFamily (family : PresentedFamily regularPresentedCore) : RegularPresentedFamily where
  name := family.terms
  modulus := family.modulus
  modulusMonotone := family.modulusMonotone
  cauchy p n m r s hn hm hr hs := family.cauchy p n m r s hn hm hr hs

def regularPresentedCompletion : PresentedDyadicCompletion regularPresentedCore where
  complete family :=
    let produced := regularLimitResult (regularFamily family)
    { value := produced.value
      convergence := ⟨produced.convergence.threshold, produced.convergence.near⟩
      unique := fun other convergence => produced.unique other ⟨convergence.threshold, convergence.near⟩ }

def conventionalCompletionObject : PresentedDyadicCompletionObject :=
  ⟨regularPresentedCore, regularPresentedCompletion⟩

theorem completionDiagonalExact (family : PresentedFamily regularPresentedCore) :
    (regularPresentedCompletion.complete family).value = diagonalName (regularFamily family) := rfl

def regularAdditiveConverges (a b : RegularDyadicName) :
    Converges regularPresentedCore (canonicalAdditiveFamily regularPresentedCore a b) (addName a b) where
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (constantNameSameValue _ _)
    ((addName a b).coherent p n s hn hs)

def regularNegativeConverges (a : RegularDyadicName) :
    Converges regularPresentedCore (canonicalNegativeFamily regularPresentedCore a) (negName a) where
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (constantNameSameValue _ _)
    ((negName a).coherent p n s hn hs)

def regularMultiplicativeConverges (a b : RegularDyadicName) :
    Converges regularPresentedCore (canonicalMultiplicativeFamily regularPresentedCore a b) (mulName a b) where
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (constantNameSameValue _ _)
    ((mulName a b).coherent p n s hn hs)

def regularAdditiveLaws : PresentedAdditiveGroupLaws regularPresentedCore zeroName addName negName :=
  ⟨addNameCongr, addNameComm, addNameAssoc, zeroNameLeft, zeroNameRight,
    negNameCongr, negNameInvolutive, addNameInverseLeft, addNameInverseRight, negNameSum⟩

def regularMultiplicativeLaws :
    PresentedMultiplicativeLaws regularPresentedCore zeroName oneName addName negName mulName :=
  ⟨mulNameCongr, mulNameComm, mulNameAssoc, mulNameOneLeft, mulNameOneRight,
    mulNameZeroLeft, mulNameZeroRight, mulNameDistributeLeft, mulNameDistributeRight,
    mulNameNegLeft, mulNameNegRight⟩

def regularOrderLaws : PresentedConstructiveOrderLaws regularPresentedCore zeroName oneName
    addName negName mulName NameOrder NameApartness inverseName where
  unitPositive := NameOrder.unitPositive
  irreflexive := NameOrder.irreflexive
  asymmetric := NameOrder.asymmetric
  transitive := NameOrder.transitive
  cotransitive := NameOrder.cotransitive
  transportOrder := transportNameOrder
  transportApartness := transportNameApartness
  translateRight := NameOrder.translateRight
  translateLeft := NameOrder.translateLeft
  reflectTranslationRight := NameOrder.reflectTranslationRight
  positiveProduct := NameOrder.positiveProduct
  multiplyPositiveRight := NameOrder.multiplyPositiveRight
  multiplyPositiveLeft := NameOrder.multiplyPositiveLeft
  inverseUnitRight := fun w => inverseNameUnitRight _ w
  inverseUnitLeft := fun w => inverseNameUnitLeft _ w
  inverseWitnessIndependent := fun first second => inverseNameWitnessIndependent _ first second
  inverseCongr := inverseNameCongr

def regularOrderedData : PresentedDyadicOrderedFieldData regularPresentedCore where
  zero := zeroName
  one := oneName
  zeroExact := NameEquivalent.refl _
  oneExact := NameEquivalent.refl _
  add := addName
  mul := mulName
  neg := negName
  Order := NameOrder
  Apartness := NameApartness
  inverse := inverseName
  additiveConverges := regularAdditiveConverges
  negativeConverges := regularNegativeConverges
  multiplicativeConverges := regularMultiplicativeConverges
  additiveLaws := regularAdditiveLaws
  multiplicativeLaws := regularMultiplicativeLaws
  orderedLaws := regularOrderLaws
  orderToSeparation order := ⟨order.accuracy, order.response, order.beyond, order.separation⟩
  separationToOrder order := ⟨order.accuracy, order.response, order.beyond, order.separation⟩
  apartnessToOrder apart := apart
  orderToApartness apart := apart
  density order :=
    let produced := nameDensity order
    ⟨produced.code, produced.left, produced.right⟩
  naturalBounds name :=
    let produced := nameNaturalBounds name
    ⟨produced.lower, produced.upper, produced.lowerOrder, produced.upperOrder⟩

def regularOrderedCompletion : PresentedDyadicOrderedFieldCompletion :=
  ⟨regularPresentedCore, regularPresentedCompletion, regularOrderedData⟩

end RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularPresentedCore
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularFamily
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularPresentedCompletion
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.conventionalCompletionObject
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.completionDiagonalExact
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularAdditiveConverges
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularNegativeConverges
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularMultiplicativeConverges
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularAdditiveLaws
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularMultiplicativeLaws
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularOrderLaws
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularOrderedData
#print axioms RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion.regularOrderedCompletion
/- AXIOM_AUDIT_END -/
