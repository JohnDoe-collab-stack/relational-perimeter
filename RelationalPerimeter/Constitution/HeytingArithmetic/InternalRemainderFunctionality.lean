import RelationalPerimeter.Constitution.HeytingArithmetic.InternalMultiplication
import RelationalPerimeter.Constitution.HeytingArithmetic.InternalOrder

/-!
# Internal functionality of remainder and Goedel beta

The semantic uniqueness theorem from `ArithmeticFormulaTools` is rebuilt here
inside HA.  It is this object proof, rather than semantic truth, that makes
negative numeralwise representability available to Rosser's argument.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def quotientBlockLessOrEqualAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right modulus : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (lessOrEqualFormula
        (ScopedTerm.add (ScopedTerm.mul left modulus) modulus)
        (ScopedTerm.mul right modulus)) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let quotientEquation : Derivation LogicMode.intuitionistic haTheory
      witnessContext witnessBody := Derivation.hypothesis ContextMember.here
  let gap := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let leftBlock := ScopedTerm.add
    (ScopedTerm.mul left.lift modulus.lift) modulus.lift
  let extra := ScopedTerm.mul gap modulus.lift
  let initialBound := (lessOrEqualAddRightProof leftBlock extra)
    |>.weakenClosedTo witnessContext
  let reassociate := (addAssociativeProof
    (ScopedTerm.mul left.lift modulus.lift) modulus.lift extra)
    |>.weakenClosedTo witnessContext
  let commuteTail := (addCommutativeProof modulus.lift extra)
    |>.weakenClosedTo witnessContext
  let commuteInside := addCongruenceRightAt
    (fixed := ScopedTerm.mul left.lift modulus.lift) commuteTail
  let successorProduct := (successorMultiplyProof gap modulus.lift)
    |>.weakenClosedTo witnessContext
  let replaceProduct := addCongruenceRightAt
    (fixed := ScopedTerm.mul left.lift modulus.lift)
    (Derivation.equalitySymmetry successorProduct)
  let distribute := (multiplyDistributesLeftProof left.lift gap.succ
    modulus.lift).weakenClosedTo witnessContext
  let replaceQuotient := multiplyCongruenceLeftAt
    (fixed := modulus.lift) quotientEquation
  let blockEquality := Derivation.equalityTransitivity reassociate
    (Derivation.equalityTransitivity commuteInside
      (Derivation.equalityTransitivity replaceProduct
        (Derivation.equalityTransitivity
          (Derivation.equalitySymmetry distribute) replaceQuotient)))
  let transported : Derivation LogicMode.intuitionistic haTheory witnessContext
      (lessOrEqualFormula leftBlock
        (ScopedTerm.mul right.lift modulus.lift)) := by
    let lessCase := scopedLessThanFormulaAt leftBlock
      (ScopedTerm.add leftBlock extra)
    let equalCase := ScopedFormula.equal leftBlock
      (ScopedTerm.add leftBlock extra)
    let lessContext := FormulaContext.cons lessCase witnessContext
    let lessHypothesis : Derivation LogicMode.intuitionistic haTheory lessContext
        lessCase := Derivation.hypothesis ContextMember.here
    let mappedLess := lessThanTransportRightAt leftBlock
      (ScopedTerm.add leftBlock extra)
      (ScopedTerm.mul right.lift modulus.lift)
      (Derivation.weaken lessCase blockEquality) lessHypothesis
    let lessBranch : Derivation LogicMode.intuitionistic haTheory lessContext
        (lessOrEqualFormula leftBlock
          (ScopedTerm.mul right.lift modulus.lift)) :=
      Derivation.disjunctionIntroductionLeft
        (right := ScopedFormula.equal leftBlock
          (ScopedTerm.mul right.lift modulus.lift)) mappedLess
    let equalContext := FormulaContext.cons equalCase witnessContext
    let equalHypothesis : Derivation LogicMode.intuitionistic haTheory equalContext
        equalCase := Derivation.hypothesis ContextMember.here
    let mappedEqual := Derivation.equalityTransitivity equalHypothesis
      (Derivation.weaken equalCase blockEquality)
    let equalBranch := Derivation.disjunctionIntroductionRight
      (left := scopedLessThanFormulaAt leftBlock
        (ScopedTerm.mul right.lift modulus.lift)) mappedEqual
    exact Derivation.disjunctionElimination initialBound lessBranch equalBranch
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  have branch : Derivation LogicMode.intuitionistic haTheory witnessContext
      (lessOrEqualFormula
        (ScopedTerm.add (ScopedTerm.mul left modulus) modulus)
        (ScopedTerm.mul right modulus)).lift := by
    apply Derivation.castConclusion
      (lessOrEqualFormula_lift
        (ScopedTerm.add (ScopedTerm.mul left modulus) modulus)
        (ScopedTerm.mul right modulus))
    simpa [leftBlock, ScopedTerm.lift, ScopedTerm.add,
      ScopedTerm.mul, RawTerm.rename] using transported
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := lessOrEqualFormula
      (ScopedTerm.add (ScopedTerm.mul left modulus) modulus)
      (ScopedTerm.mul right modulus))
    normalizedStrict branch

def boundedProductSumsStrictAt
    {bound : Nat}
    {context : FormulaContext bound}
    (leftQuotient rightQuotient modulus leftRemainder rightRemainder :
      ScopedTerm bound)
    (quotientStrict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt leftQuotient rightQuotient))
    (remainderBound : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt leftRemainder modulus)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt
        (ScopedTerm.add
          (ScopedTerm.mul leftQuotient modulus) leftRemainder)
        (ScopedTerm.add
          (ScopedTerm.mul rightQuotient modulus) rightRemainder)) := by
  let leftProduct := ScopedTerm.mul leftQuotient modulus
  let rightProduct := ScopedTerm.mul rightQuotient modulus
  let firstStrict := lessThanAddLeftAt leftProduct leftRemainder modulus
    remainderBound
  let blockBound := quotientBlockLessOrEqualAt leftQuotient rightQuotient
    modulus quotientStrict
  let toRightProduct := lessThanThenLessOrEqualAt
    (ScopedTerm.add leftProduct leftRemainder)
    (ScopedTerm.add leftProduct modulus) rightProduct firstStrict blockBound
  let finalBound := (lessOrEqualAddRightProof rightProduct rightRemainder)
    |>.weakenClosedTo context
  exact lessThanThenLessOrEqualAt
    (ScopedTerm.add leftProduct leftRemainder) rightProduct
    (ScopedTerm.add rightProduct rightRemainder) toRightProduct finalBound

def boundedProductSumsUnequalAt
    {bound : Nat}
    {context : FormulaContext bound}
    (leftQuotient rightQuotient modulus leftRemainder rightRemainder :
      ScopedTerm bound)
    (quotientStrict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt leftQuotient rightQuotient))
    (remainderBound : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt leftRemainder modulus))
    (sumEquality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal
        (ScopedTerm.add
          (ScopedTerm.mul leftQuotient modulus) leftRemainder)
        (ScopedTerm.add
          (ScopedTerm.mul rightQuotient modulus) rightRemainder))) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.falsum bound) :=
  lessThanAndEqualityContradiction _ _
    (boundedProductSumsStrictAt leftQuotient rightQuotient modulus
      leftRemainder rightRemainder quotientStrict remainderBound)
    sumEquality

def scopedRemainderFormulaAt
    {bound : Nat}
    (dividend modulus remainder : ScopedTerm bound) : ScopedFormula bound :=
  { raw := remainderFormula dividend.raw modulus.raw remainder.raw
    isScoped := remainderFormula_wellScoped dividend.raw modulus.raw
      remainder.raw dividend.isScoped modulus.isScoped remainder.isScoped }

def scopedBetaValueFormulaAt
    {bound : Nat}
    (dividend coefficient index value : ScopedTerm bound) :
    ScopedFormula bound :=
  { raw := betaValueFormula dividend.raw coefficient.raw index.raw value.raw
    isScoped := betaValueFormula_wellScoped _ _ _ _
      dividend.isScoped coefficient.isScoped index.isScoped value.isScoped }

def remainderFunctionalAt
    {bound : Nat}
    {context : FormulaContext bound}
    (dividend modulus leftRemainder rightRemainder : ScopedTerm bound)
    (leftProof : Derivation LogicMode.intuitionistic haTheory context
      (scopedRemainderFormulaAt dividend modulus leftRemainder))
    (rightProof : Derivation LogicMode.intuitionistic haTheory context
      (scopedRemainderFormulaAt dividend modulus rightRemainder)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal leftRemainder rightRemainder) := by
  let leftEquationBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal dividend.lift
      (ScopedTerm.add
        (ScopedTerm.mul
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)) modulus.lift)
        leftRemainder.lift)
  have leftExact : scopedRemainderFormulaAt dividend modulus leftRemainder =
      ScopedFormula.conj
        (scopedLessThanFormulaAt leftRemainder modulus)
        (ScopedFormula.ex leftEquationBody) := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedLeft := Derivation.castConclusion leftExact leftProof
  let leftBound := Derivation.conjunctionEliminationLeft normalizedLeft
  let leftExists := Derivation.conjunctionEliminationRight normalizedLeft
  let rightEquationBodyOne : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal dividend.lift
      (ScopedTerm.add
        (ScopedTerm.mul
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)) modulus.lift)
        rightRemainder.lift)
  have rightExact : scopedRemainderFormulaAt dividend modulus rightRemainder =
      ScopedFormula.conj
        (scopedLessThanFormulaAt rightRemainder modulus)
        (ScopedFormula.ex rightEquationBodyOne) := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedRight := Derivation.castConclusion rightExact rightProof
  let rightBound := Derivation.conjunctionEliminationLeft normalizedRight
  let rightExists := Derivation.conjunctionEliminationRight normalizedRight
  let leftContext := FormulaContext.cons leftEquationBody context.lift
  let leftEquation : Derivation LogicMode.intuitionistic haTheory leftContext
      leftEquationBody := Derivation.hypothesis ContextMember.here
  let liftedRightExists := Derivation.weaken leftEquationBody
    (Derivation.liftVariables rightExists)
  let rightEquationBody : ScopedFormula (Nat.succ (Nat.succ bound)) :=
    ScopedFormula.equal dividend.lift.lift
      (ScopedTerm.add
        (ScopedTerm.mul
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ (Nat.succ bound)))
          modulus.lift.lift)
        rightRemainder.lift.lift)
  let rightContext := FormulaContext.cons rightEquationBody leftContext.lift
  let rightEquation : Derivation LogicMode.intuitionistic haTheory rightContext
      rightEquationBody := Derivation.hypothesis ContextMember.here
  let liftedLeftEquation : Derivation LogicMode.intuitionistic haTheory
      rightContext leftEquationBody.lift :=
    Derivation.weaken rightEquationBody
      (Derivation.liftVariables leftEquation)
  let leftQuotient := ScopedTerm.bvar 1
    (Nat.succ_lt_succ (Nat.zero_lt_succ bound))
  let rightQuotient := ScopedTerm.bvar 0
    (Nat.zero_lt_succ (Nat.succ bound))
  let liftedModulus := modulus.lift.lift
  let liftedLeftRemainder := leftRemainder.lift.lift
  let liftedRightRemainder := rightRemainder.lift.lift
  let leftSum := ScopedTerm.add
    (ScopedTerm.mul leftQuotient liftedModulus) liftedLeftRemainder
  let rightSum := ScopedTerm.add
    (ScopedTerm.mul rightQuotient liftedModulus) liftedRightRemainder
  have explicitLeftEquation : Derivation LogicMode.intuitionistic haTheory
      rightContext
      (ScopedFormula.equal dividend.lift.lift leftSum) := by
    apply Derivation.castConclusion ?_ liftedLeftEquation
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let sumsEqual : Derivation LogicMode.intuitionistic haTheory rightContext
      (ScopedFormula.equal leftSum rightSum) :=
    Derivation.equalityTransitivity
      (Derivation.equalitySymmetry explicitLeftEquation) rightEquation
  let liftedLeftBound : Derivation LogicMode.intuitionistic haTheory rightContext
      (scopedLessThanFormulaAt liftedLeftRemainder liftedModulus) := by
    let twice := Derivation.liftVariables (Derivation.liftVariables leftBound)
    have normalizedTwice : Derivation LogicMode.intuitionistic haTheory
        context.lift.lift
        (scopedLessThanFormulaAt liftedLeftRemainder liftedModulus) := by
      apply Derivation.castConclusion
        ((scopedLessThanFormulaAt_lift leftRemainder.lift modulus.lift).trans
          (congrArg ScopedFormula.lift
            (scopedLessThanFormulaAt_lift leftRemainder modulus))).symm
      exact twice
    exact Derivation.weaken rightEquationBody
      (Derivation.weaken leftEquationBody.lift normalizedTwice)
  let liftedRightBound : Derivation LogicMode.intuitionistic haTheory rightContext
      (scopedLessThanFormulaAt liftedRightRemainder liftedModulus) := by
    let twice := Derivation.liftVariables (Derivation.liftVariables rightBound)
    have normalizedTwice : Derivation LogicMode.intuitionistic haTheory
        context.lift.lift
        (scopedLessThanFormulaAt liftedRightRemainder liftedModulus) := by
      apply Derivation.castConclusion
        ((scopedLessThanFormulaAt_lift rightRemainder.lift modulus.lift).trans
          (congrArg ScopedFormula.lift
            (scopedLessThanFormulaAt_lift rightRemainder modulus))).symm
      exact twice
    exact Derivation.weaken rightEquationBody
      (Derivation.weaken leftEquationBody.lift normalizedTwice)
  let trichotomy := (orderTrichotomyProof leftQuotient rightQuotient)
    |>.weakenClosedTo rightContext
  let leftStrictFormula := scopedLessThanFormulaAt leftQuotient rightQuotient
  let quotientEqualityFormula := ScopedFormula.equal leftQuotient rightQuotient
  let rightStrictFormula := scopedLessThanFormulaAt rightQuotient leftQuotient
  let leftStrictContext := FormulaContext.cons leftStrictFormula rightContext
  let leftStrictHypothesis : Derivation LogicMode.intuitionistic haTheory
      leftStrictContext leftStrictFormula := Derivation.hypothesis ContextMember.here
  let leftContradiction := boundedProductSumsUnequalAt leftQuotient
    rightQuotient liftedModulus liftedLeftRemainder liftedRightRemainder
    leftStrictHypothesis (Derivation.weaken leftStrictFormula liftedLeftBound)
    (Derivation.weaken leftStrictFormula sumsEqual)
  let leftBranch := Derivation.falsumElimination
    (conclusion := ScopedFormula.equal
      liftedLeftRemainder liftedRightRemainder) leftContradiction
  let middleFormula := ScopedFormula.disj quotientEqualityFormula
    rightStrictFormula
  let middleContext := FormulaContext.cons middleFormula rightContext
  let middleHypothesis : Derivation LogicMode.intuitionistic haTheory middleContext
      middleFormula := Derivation.hypothesis ContextMember.here
  let equalityContext := FormulaContext.cons quotientEqualityFormula
    middleContext
  let quotientEquality : Derivation LogicMode.intuitionistic haTheory
      equalityContext quotientEqualityFormula :=
    Derivation.hypothesis ContextMember.here
  let productEquality := multiplyCongruenceLeftAt
    (fixed := liftedModulus) quotientEquality
  let productWithLeftRemainder := addCongruenceLeftAt
    (fixed := liftedLeftRemainder) productEquality
  let commonPrefixEquality := Derivation.equalityTransitivity
    (Derivation.equalitySymmetry productWithLeftRemainder)
    (Derivation.weaken quotientEqualityFormula
      (Derivation.weaken middleFormula sumsEqual))
  let cancellation := (addLeftCancellationProof
    (ScopedTerm.mul rightQuotient liftedModulus)
    liftedLeftRemainder liftedRightRemainder)
    |>.weakenClosedTo equalityContext
  let equalityBranch := Derivation.implicationElimination cancellation
    commonPrefixEquality
  let rightStrictContext := FormulaContext.cons rightStrictFormula
    middleContext
  let rightStrictHypothesis : Derivation LogicMode.intuitionistic haTheory
      rightStrictContext rightStrictFormula :=
    Derivation.hypothesis ContextMember.here
  let rightContradiction := boundedProductSumsUnequalAt rightQuotient
    leftQuotient liftedModulus liftedRightRemainder liftedLeftRemainder
    rightStrictHypothesis
    (Derivation.weaken rightStrictFormula
      (Derivation.weaken middleFormula liftedRightBound))
    (Derivation.equalitySymmetry
      (Derivation.weaken rightStrictFormula
        (Derivation.weaken middleFormula sumsEqual)))
  let rightBranch := Derivation.falsumElimination
    (conclusion := ScopedFormula.equal
      liftedLeftRemainder liftedRightRemainder) rightContradiction
  let middleBranch := Derivation.disjunctionElimination middleHypothesis
    equalityBranch rightBranch
  let allCases := Derivation.disjunctionElimination trichotomy
    leftBranch middleBranch
  have normalizedRightExists : Derivation LogicMode.intuitionistic haTheory
      leftContext (ScopedFormula.ex rightEquationBody) := by
    apply Derivation.castConclusion ?_ liftedRightExists
    apply ScopedFormula.eq_of_raw_eq
    dsimp [rightEquationBodyOne, rightEquationBody,
      ScopedFormula.ex, ScopedFormula.equal, ScopedFormula.lift,
      ScopedTerm.lift, ScopedTerm.add, ScopedTerm.mul,
      ScopedTerm.bvar, RawFormula.rename, RawTerm.rename,
      liftRenaming]
    repeat' rw [RawTerm.renameSucc_renameLiftSucc]
  have rightBranchResult : Derivation LogicMode.intuitionistic haTheory
      rightContext
      (ScopedFormula.equal leftRemainder.lift rightRemainder.lift).lift := by
    apply Derivation.castConclusion ?_ allCases
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let eliminateRight := Derivation.existentialElimination
    (body := rightEquationBody)
    (conclusion := ScopedFormula.equal
      leftRemainder.lift rightRemainder.lift)
    normalizedRightExists rightBranchResult
  have leftBranchResult : Derivation LogicMode.intuitionistic haTheory
      leftContext
      (ScopedFormula.equal leftRemainder rightRemainder).lift := by
    apply Derivation.castConclusion ?_ eliminateRight
    apply ScopedFormula.eq_of_raw_eq
    rfl
  exact Derivation.existentialElimination
    (body := leftEquationBody)
    (conclusion := ScopedFormula.equal leftRemainder rightRemainder)
    leftExists leftBranchResult

def betaValueFunctionalAt
    {bound : Nat}
    {context : FormulaContext bound}
    (dividend coefficient index leftValue rightValue : ScopedTerm bound)
    (leftProof : Derivation LogicMode.intuitionistic haTheory context
      (scopedBetaValueFormulaAt dividend coefficient index leftValue))
    (rightProof : Derivation LogicMode.intuitionistic haTheory context
      (scopedBetaValueFormulaAt dividend coefficient index rightValue)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal leftValue rightValue) := by
  exact remainderFunctionalAt dividend
    (ScopedTerm.succ (ScopedTerm.mul index.succ coefficient))
    leftValue rightValue (by
      simpa [betaValueFormula, betaModulusTerm,
        scopedRemainderFormulaAt, scopedBetaValueFormulaAt,
        ScopedTerm.succ, ScopedTerm.mul] using leftProof)
    (by
      simpa [betaValueFormula, betaModulusTerm,
        scopedRemainderFormulaAt, scopedBetaValueFormulaAt,
        ScopedTerm.succ, ScopedTerm.mul] using rightProof)

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.quotientBlockLessOrEqualAt
#print axioms RelationalPerimeter.HeytingArithmetic.boundedProductSumsStrictAt
#print axioms RelationalPerimeter.HeytingArithmetic.boundedProductSumsUnequalAt
#print axioms RelationalPerimeter.HeytingArithmetic.remainderFunctionalAt
#print axioms RelationalPerimeter.HeytingArithmetic.scopedBetaValueFormulaAt
#print axioms RelationalPerimeter.HeytingArithmetic.betaValueFunctionalAt
/- AXIOM_AUDIT_END -/
