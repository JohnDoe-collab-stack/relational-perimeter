import RelationalPerimeter.Instances.HeytingArithmetic.InternalAddition

/-!
# Internally derived multiplication laws of HA
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def zeroMultiplyUniversal
    (bound : Nat) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal
          (ScopedTerm.mul (ScopedTerm.zero _) value)
          (ScopedTerm.zero _))) := by
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal (ScopedTerm.mul (ScopedTerm.zero _) value)
      (ScopedTerm.zero _)
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul (ScopedTerm.zero bound) (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero (ScopedTerm.zero bound))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let ih : Derivation LogicMode.intuitionistic haTheory stepContext body :=
      Derivation.hypothesis ContextMember.here
    let unfold : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul (ScopedTerm.zero _) value.succ)
          (ScopedTerm.add
            (ScopedTerm.mul (ScopedTerm.zero _) value)
            (ScopedTerm.zero _))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor
          (ScopedTerm.zero _) value)
    let congruence := addCongruenceLeftAt
      (fixed := ScopedTerm.zero _) ih
    let addZero : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add (ScopedTerm.zero _) (ScopedTerm.zero _))
          (ScopedTerm.zero _)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addZero (ScopedTerm.zero _))
    let result := Derivation.equalityTransitivity unfold
      (Derivation.equalityTransitivity congruence addZero)
    simpa [body, value, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.zero, ScopedTerm.succ,
      RawTerm.renameSucc_substituteKeepingScope] using result
  exact Derivation.byArithmeticInduction body (by
    simpa [body, value, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.mul, ScopedTerm.zero,
      RawTerm.renameSucc_substituteSingle] using base) step

def zeroMultiplyProof
    {bound : Nat}
    (value : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul (ScopedTerm.zero _) value)
        (ScopedTerm.zero _)) := by
  let instantiated := Derivation.universalElimination value
    (zeroMultiplyUniversal bound)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.mul, ScopedTerm.zero,
    RawTerm.renameSucc_substituteSingle] using instantiated

def successorMultiplyUniversal
    {bound : Nat}
    (left : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal
          (ScopedTerm.mul left.lift.succ right)
          (ScopedTerm.add (ScopedTerm.mul left.lift right) right))) := by
  let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.mul left.lift.succ right)
      (ScopedTerm.add (ScopedTerm.mul left.lift right) right)
  let leftZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul left.succ (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero left.succ)
  let rightZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul left (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero left)
  let addZeros : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add (ScopedTerm.zero bound) (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero (ScopedTerm.zero bound))
  let rightNormalized := Derivation.equalityTransitivity
    (addCongruenceLeftAt (fixed := ScopedTerm.zero bound) rightZero)
    addZeros
  let base := Derivation.equalityTransitivity leftZero
    (Derivation.equalitySymmetry rightNormalized)
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let ih : Derivation LogicMode.intuitionistic haTheory stepContext body :=
      Derivation.hypothesis ContextMember.here
    let unfoldLeft : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul left.lift.succ right.succ)
          (ScopedTerm.add (ScopedTerm.mul left.lift.succ right)
            left.lift.succ)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor left.lift.succ right)
    let replaceIH := addCongruenceLeftAt
      (fixed := left.lift.succ) ih
    let unfoldInner : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul left.lift right.succ)
          (ScopedTerm.add (ScopedTerm.mul left.lift right) left.lift)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor left.lift right)
    let innerCongruence := addCongruenceLeftAt
      (fixed := right.succ) unfoldInner
    let sourceReassociate := addAssociativeProof
      (ScopedTerm.mul left.lift right) right left.lift.succ
      |>.weakenClosedTo stepContext
    let rightSuccessor : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add right left.lift.succ)
          (ScopedTerm.succ (ScopedTerm.add right left.lift))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor right left.lift)
    let swapInner := addCommutativeProof right left.lift
      |>.weakenClosedTo stepContext
    let swapSuccessor := successorCongruenceAt swapInner
    let leftSuccessor : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add left.lift right.succ)
          (ScopedTerm.succ (ScopedTerm.add left.lift right))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor left.lift right)
    let swapTail := Derivation.equalityTransitivity rightSuccessor
      (Derivation.equalityTransitivity swapSuccessor
        (Derivation.equalitySymmetry leftSuccessor))
    let swapCongruence := addCongruenceRightAt
      (fixed := ScopedTerm.mul left.lift right) swapTail
    let targetReassociate := addAssociativeProof
      (ScopedTerm.mul left.lift right) left.lift right.succ
      |>.weakenClosedTo stepContext
    let result := Derivation.equalityTransitivity unfoldLeft
      (Derivation.equalityTransitivity replaceIH
        (Derivation.equalityTransitivity sourceReassociate
          (Derivation.equalityTransitivity swapCongruence
            (Derivation.equalityTransitivity
              (Derivation.equalitySymmetry targetReassociate)
              (Derivation.equalitySymmetry innerCongruence)))))
    simpa [body, right, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.succ, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using result
  exact Derivation.byArithmeticInduction body (by
    simpa [body, right, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.succ, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using base) step

def successorMultiplyProof
    {bound : Nat}
    (left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.mul left.succ right)
        (ScopedTerm.add (ScopedTerm.mul left right) right)) := by
  let instantiated := Derivation.universalElimination right
    (successorMultiplyUniversal left)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.mul, ScopedTerm.add,
    ScopedTerm.succ, ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using instantiated

def multiplyCommutativeUniversal
    {bound : Nat}
    (left : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal (ScopedTerm.mul left.lift right)
          (ScopedTerm.mul right left.lift))) := by
  let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal (ScopedTerm.mul left.lift right)
      (ScopedTerm.mul right left.lift)
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul left (ScopedTerm.zero bound))
        (ScopedTerm.mul (ScopedTerm.zero bound) left)) :=
    Derivation.equalityTransitivity
    (Derivation.theoryAxiom
      (StandardArithmeticAxiom.multiplyZero left))
    (Derivation.equalitySymmetry (zeroMultiplyProof left))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let ih : Derivation LogicMode.intuitionistic haTheory stepContext body :=
      Derivation.hypothesis ContextMember.here
    let unfoldLeft : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal (ScopedTerm.mul left.lift right.succ)
          (ScopedTerm.add (ScopedTerm.mul left.lift right) left.lift)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor left.lift right)
    let ihCongruence := addCongruenceLeftAt
      (fixed := left.lift) ih
    let unfoldRight := (successorMultiplyProof right left.lift).weakenClosedTo
      stepContext
    let result := Derivation.equalityTransitivity unfoldLeft
      (Derivation.equalityTransitivity ihCongruence
        (Derivation.equalitySymmetry unfoldRight))
    simpa [body, right, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.succ, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using result
  exact Derivation.byArithmeticInduction body (by
    simpa [body, right, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.mul,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using base) step

def multiplyCommutativeProof
    {bound : Nat}
    (left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.mul left right)
        (ScopedTerm.mul right left)) := by
  let instantiated := Derivation.universalElimination right
    (multiplyCommutativeUniversal left)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.mul,
    ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using instantiated

def multiplyDistributesRightUniversal
    {bound : Nat}
    (factor first : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let second := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal
          (ScopedTerm.mul factor.lift
            (ScopedTerm.add first.lift second))
          (ScopedTerm.add
            (ScopedTerm.mul factor.lift first.lift)
            (ScopedTerm.mul factor.lift second)))) := by
  let second := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.mul factor.lift (ScopedTerm.add first.lift second))
      (ScopedTerm.add (ScopedTerm.mul factor.lift first.lift)
        (ScopedTerm.mul factor.lift second))
  let firstZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add first (ScopedTerm.zero bound)) first) :=
    Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero first)
  let normalizeLeft := multiplyCongruenceRightAt
    (fixed := factor) firstZero
  let factorZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul factor (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero factor)
  let normalizeRightInner := addCongruenceRightAt
    (fixed := ScopedTerm.mul factor first) factorZero
  let normalizeRightOuter :
      Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
        (ScopedFormula.equal
          (ScopedTerm.add (ScopedTerm.mul factor first)
            (ScopedTerm.zero bound))
          (ScopedTerm.mul factor first)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero (ScopedTerm.mul factor first))
  let base := Derivation.equalityTransitivity normalizeLeft
    (Derivation.equalitySymmetry
      (Derivation.equalityTransitivity normalizeRightInner
        normalizeRightOuter))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let ih : Derivation LogicMode.intuitionistic haTheory stepContext body :=
      Derivation.hypothesis ContextMember.here
    let addStep : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add first.lift second.succ)
          (ScopedTerm.succ (ScopedTerm.add first.lift second))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor first.lift second)
    let multiplyAddStep := multiplyCongruenceRightAt
      (fixed := factor.lift) addStep
    let unfoldProduct : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul factor.lift
            (ScopedTerm.succ (ScopedTerm.add first.lift second)))
          (ScopedTerm.add
            (ScopedTerm.mul factor.lift
              (ScopedTerm.add first.lift second)) factor.lift)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor factor.lift
          (ScopedTerm.add first.lift second))
    let ihCongruence := addCongruenceLeftAt
      (fixed := factor.lift) ih
    let reassociate := addAssociativeProof
      (ScopedTerm.mul factor.lift first.lift)
      (ScopedTerm.mul factor.lift second) factor.lift
      |>.weakenClosedTo stepContext
    let unfoldSecond : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul factor.lift second.succ)
          (ScopedTerm.add (ScopedTerm.mul factor.lift second) factor.lift)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor factor.lift second)
    let outerCongruence := addCongruenceRightAt
      (fixed := ScopedTerm.mul factor.lift first.lift) unfoldSecond
    let result := Derivation.equalityTransitivity multiplyAddStep
      (Derivation.equalityTransitivity unfoldProduct
        (Derivation.equalityTransitivity ihCongruence
          (Derivation.equalityTransitivity reassociate
            (Derivation.equalitySymmetry outerCongruence))))
    simpa [body, second, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.succ, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using result
  exact Derivation.byArithmeticInduction body (by
    simpa [body, second, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using base) step

def multiplyDistributesRightProof
    {bound : Nat}
    (factor first second : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul factor (ScopedTerm.add first second))
        (ScopedTerm.add (ScopedTerm.mul factor first)
          (ScopedTerm.mul factor second))) := by
  let instantiated := Derivation.universalElimination second
    (multiplyDistributesRightUniversal factor first)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.mul, ScopedTerm.add,
    ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using instantiated

def multiplyDistributesLeftProof
    {bound : Nat}
    (first second factor : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul (ScopedTerm.add first second) factor)
        (ScopedTerm.add (ScopedTerm.mul first factor)
          (ScopedTerm.mul second factor))) := by
  let commuteOuter := multiplyCommutativeProof
    (ScopedTerm.add first second) factor
  let distribute := multiplyDistributesRightProof factor first second
  let commuteFirst := multiplyCommutativeProof factor first
  let commuteSecond := multiplyCommutativeProof factor second
  let replaceFirst := addCongruenceLeftAt
    (fixed := ScopedTerm.mul factor second) commuteFirst
  let replaceSecond := addCongruenceRightAt
    (fixed := ScopedTerm.mul first factor) commuteSecond
  exact Derivation.equalityTransitivity commuteOuter
    (Derivation.equalityTransitivity distribute
      (Derivation.equalityTransitivity replaceFirst replaceSecond))

def multiplyAssociativeUniversal
    {bound : Nat}
    (first second : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let third := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal
          (ScopedTerm.mul (ScopedTerm.mul first.lift second.lift) third)
          (ScopedTerm.mul first.lift
            (ScopedTerm.mul second.lift third)))) := by
  let third := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.mul (ScopedTerm.mul first.lift second.lift) third)
      (ScopedTerm.mul first.lift (ScopedTerm.mul second.lift third))
  let leftZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul (ScopedTerm.mul first second) (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero
      (ScopedTerm.mul first second))
  let secondZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul second (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero second)
  let firstZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul first (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.multiplyZero first)
  let rightCongruence := multiplyCongruenceRightAt
    (fixed := first) secondZero
  let base := Derivation.equalityTransitivity leftZero
    (Derivation.equalityTransitivity
      (Derivation.equalitySymmetry firstZero)
      (Derivation.equalitySymmetry rightCongruence))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let ih : Derivation LogicMode.intuitionistic haTheory stepContext body :=
      Derivation.hypothesis ContextMember.here
    let unfoldLeft : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul (ScopedTerm.mul first.lift second.lift) third.succ)
          (ScopedTerm.add
            (ScopedTerm.mul (ScopedTerm.mul first.lift second.lift) third)
            (ScopedTerm.mul first.lift second.lift))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor
          (ScopedTerm.mul first.lift second.lift) third)
    let replaceIH := addCongruenceLeftAt
      (fixed := ScopedTerm.mul first.lift second.lift) ih
    let unfoldInner : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.mul second.lift third.succ)
          (ScopedTerm.add (ScopedTerm.mul second.lift third) second.lift)) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplySuccessor second.lift third)
    let innerCongruence := multiplyCongruenceRightAt
      (fixed := first.lift) unfoldInner
    let distribute := multiplyDistributesRightProof first.lift
      (ScopedTerm.mul second.lift third) second.lift
      |>.weakenClosedTo stepContext
    let result := Derivation.equalityTransitivity unfoldLeft
      (Derivation.equalityTransitivity replaceIH
        (Derivation.equalityTransitivity
          (Derivation.equalitySymmetry distribute)
          (Derivation.equalitySymmetry innerCongruence)))
    simpa [body, third, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.mul, ScopedTerm.add,
      ScopedTerm.succ, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using result
  exact Derivation.byArithmeticInduction body (by
    simpa [body, third, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.mul,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using base) step

def multiplyAssociativeProof
    {bound : Nat}
    (first second third : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul (ScopedTerm.mul first second) third)
        (ScopedTerm.mul first (ScopedTerm.mul second third))) := by
  let instantiated := Derivation.universalElimination third
    (multiplyAssociativeUniversal first second)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.mul,
    ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using instantiated

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.zeroMultiplyProof
#print axioms RelationalPerimeter.HeytingArithmetic.successorMultiplyProof
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyCommutativeProof
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyDistributesRightProof
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyDistributesLeftProof
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyAssociativeProof
/- AXIOM_AUDIT_END -/
