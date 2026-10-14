import RelationalPerimeter.Constitution.HeytingArithmetic.InternalInduction

/-!
# Internally derived addition laws of HA
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

theorem RawTerm.renameSucc_substituteKeepingScope
    (term : RawTerm) :
    (term.rename Nat.succ).substitute
        ScopedFormula.replaceNewestKeepingScopeSubstitution =
      term.rename Nat.succ := by
  induction term with
  | bvar _index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

def successorAddUniversal
    {bound : Nat}
    (left : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal
          (ScopedTerm.add left.lift.succ right)
          (ScopedTerm.succ (ScopedTerm.add left.lift right)))) := by
  let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift.succ right)
      (ScopedTerm.succ (ScopedTerm.add left.lift right))
  let leftAddZero : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add left (ScopedTerm.zero bound))
        left) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero left)
  let successorLeftAddZero : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add left.succ (ScopedTerm.zero bound)) left.succ) :=
    Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero left.succ)
  let successorOfLeftAddZero := successorCongruenceAt leftAddZero
  let base := Derivation.equalityTransitivity successorLeftAddZero
    (Derivation.equalitySymmetry successorOfLeftAddZero)
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let inductionHypothesis : Derivation LogicMode.intuitionistic haTheory
        stepContext body := Derivation.hypothesis ContextMember.here
    let unfoldLeft : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add left.lift.succ right.succ)
          (ScopedTerm.succ (ScopedTerm.add left.lift.succ right))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor left.lift.succ right)
    let liftedInduction := successorCongruenceAt inductionHypothesis
    let unfoldRight : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add left.lift right.succ)
          (ScopedTerm.succ (ScopedTerm.add left.lift right))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor left.lift right)
    let liftUnfoldRight := successorCongruenceAt unfoldRight
    let combined := Derivation.equalityTransitivity unfoldLeft
      (Derivation.equalityTransitivity liftedInduction
        (Derivation.equalitySymmetry liftUnfoldRight))
    simpa [body, right, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using combined
  exact Derivation.byArithmeticInduction body (by
    simpa [body, right, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle,
      ScopedTerm.add, ScopedTerm.succ] using base) step

def successorAddProof
    {bound : Nat}
    (left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add left.succ right)
        (ScopedTerm.succ (ScopedTerm.add left right))) := by
  let universal := successorAddUniversal left
  let instantiated := Derivation.universalElimination right universal
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral, RawFormula.instantiateTerm,
    RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle,
    ScopedTerm.add, ScopedTerm.succ] using instantiated

def zeroAddUniversal
    (bound : Nat) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal (ScopedTerm.add (ScopedTerm.zero _) value)
          value)) := by
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal (ScopedTerm.add (ScopedTerm.zero _) value) value
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add (ScopedTerm.zero bound) (ScopedTerm.zero bound))
        (ScopedTerm.zero bound)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero (ScopedTerm.zero bound))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let inductionHypothesis : Derivation LogicMode.intuitionistic haTheory
        stepContext body := Derivation.hypothesis ContextMember.here
    let unfoldZero : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add (ScopedTerm.zero _) value.succ)
          (ScopedTerm.succ
            (ScopedTerm.add (ScopedTerm.zero _) value))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor (ScopedTerm.zero _) value)
    let successorIH := successorCongruenceAt inductionHypothesis
    let combined := Derivation.equalityTransitivity unfoldZero successorIH
    simpa [body, value, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.zero, RawTerm.renameSucc_substituteKeepingScope] using combined
  exact Derivation.byArithmeticInduction body (by
    simpa [body, value, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.add, ScopedTerm.zero,
      RawTerm.renameSucc_substituteSingle] using base) step

def zeroAddProof
    {bound : Nat}
    (value : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add (ScopedTerm.zero _) value) value) := by
  let instantiated := Derivation.universalElimination value
    (zeroAddUniversal bound)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral, RawFormula.instantiateTerm,
    RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.add, ScopedTerm.zero,
    RawTerm.renameSucc_substituteSingle] using instantiated

def addCommutativeUniversal
    {bound : Nat}
    (left : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal (ScopedTerm.add left.lift right)
          (ScopedTerm.add right left.lift))) := by
  let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal (ScopedTerm.add left.lift right)
      (ScopedTerm.add right left.lift)
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add left (ScopedTerm.zero bound))
        (ScopedTerm.add (ScopedTerm.zero bound) left)) :=
    Derivation.equalityTransitivity
    (Derivation.theoryAxiom
      (StandardArithmeticAxiom.addZero left))
    (Derivation.equalitySymmetry (zeroAddProof left))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let ih : Derivation LogicMode.intuitionistic haTheory stepContext body :=
      Derivation.hypothesis ContextMember.here
    let unfoldLeft : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal (ScopedTerm.add left.lift right.succ)
          (ScopedTerm.succ (ScopedTerm.add left.lift right))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor left.lift right)
    let successorIH := successorCongruenceAt ih
    let unfoldRight := (successorAddProof right left.lift).weakenClosedTo
      stepContext
    let combined := Derivation.equalityTransitivity unfoldLeft
      (Derivation.equalityTransitivity successorIH
        (Derivation.equalitySymmetry unfoldRight))
    simpa [body, right, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using combined
  exact Derivation.byArithmeticInduction body (by
    simpa [body, right, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle,
      ScopedTerm.add] using base) step

def addCommutativeProof
    {bound : Nat}
    (left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add left right)
        (ScopedTerm.add right left)) := by
  let instantiated := Derivation.universalElimination right
    (addCommutativeUniversal left)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral, RawFormula.instantiateTerm,
    RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle,
    ScopedTerm.add] using instantiated

def addAssociativeUniversal
    {bound : Nat}
    (first second : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let third := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.equal
          (ScopedTerm.add (ScopedTerm.add first.lift second.lift) third)
          (ScopedTerm.add first.lift
            (ScopedTerm.add second.lift third)))) := by
  let third := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add (ScopedTerm.add first.lift second.lift) third)
      (ScopedTerm.add first.lift (ScopedTerm.add second.lift third))
  let leftZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add (ScopedTerm.add first second) (ScopedTerm.zero bound))
        (ScopedTerm.add first second)) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero (ScopedTerm.add first second))
  let secondZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add second (ScopedTerm.zero bound))
        second) := Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero second)
  let firstCongruence := addCongruenceRightAt
    (fixed := first) secondZero
  let base := Derivation.equalityTransitivity leftZero
    (Derivation.equalitySymmetry firstCongruence)
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
          (ScopedTerm.add (ScopedTerm.add first.lift second.lift) third.succ)
          (ScopedTerm.succ
            (ScopedTerm.add (ScopedTerm.add first.lift second.lift) third))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor
          (ScopedTerm.add first.lift second.lift) third)
    let successorIH := successorCongruenceAt ih
    let unfoldSecond : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add second.lift third.succ)
          (ScopedTerm.succ (ScopedTerm.add second.lift third))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor second.lift third)
    let firstCongruence := addCongruenceRightAt
      (fixed := first.lift) unfoldSecond
    let unfoldFirst : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.equal
          (ScopedTerm.add first.lift
            (ScopedTerm.succ (ScopedTerm.add second.lift third)))
          (ScopedTerm.succ
            (ScopedTerm.add first.lift
              (ScopedTerm.add second.lift third)))) :=
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addSuccessor first.lift
          (ScopedTerm.add second.lift third))
    let combined := Derivation.equalityTransitivity unfoldLeft
      (Derivation.equalityTransitivity successorIH
        (Derivation.equalityTransitivity
          (Derivation.equalitySymmetry unfoldFirst)
          (Derivation.equalitySymmetry firstCongruence)))
    simpa [body, third, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using combined
  exact Derivation.byArithmeticInduction body (by
    simpa [body, third, ScopedFormula.instantiate, ScopedTerm.instantiate,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.numeral, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle,
      ScopedTerm.add] using base) step

def addAssociativeProof
    {bound : Nat}
    (first second third : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add (ScopedTerm.add first second) third)
        (ScopedTerm.add first (ScopedTerm.add second third))) := by
  let instantiated := Derivation.universalElimination third
    (addAssociativeUniversal first second)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral, RawFormula.instantiateTerm,
    RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle,
    ScopedTerm.add] using instantiated

def addRightCancellationUniversal
    {bound : Nat}
    (left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let added := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.impl
          (ScopedFormula.equal
            (ScopedTerm.add left.lift added)
            (ScopedTerm.add right.lift added))
          (ScopedFormula.equal left.lift right.lift))) := by
  let added := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let conclusion := ScopedFormula.equal left.lift right.lift
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.impl
      (ScopedFormula.equal
        (ScopedTerm.add left.lift added)
        (ScopedTerm.add right.lift added)) conclusion
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate (ScopedTerm.zero bound)) := by
    let equality := ScopedFormula.equal
      (ScopedTerm.add left (ScopedTerm.zero bound))
      (ScopedTerm.add right (ScopedTerm.zero bound))
    let context := FormulaContext.cons equality FormulaContext.nil
    have core : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
        (ScopedFormula.impl equality (ScopedFormula.equal left right)) := by
      apply Derivation.implicationIntroduction
      let assumed : Derivation LogicMode.intuitionistic haTheory context equality :=
        Derivation.hypothesis ContextMember.here
      let leftZero : Derivation LogicMode.intuitionistic haTheory context
          (ScopedFormula.equal
            (ScopedTerm.add left (ScopedTerm.zero bound)) left) :=
        (Derivation.theoryAxiom
          (context := FormulaContext.nil)
          (StandardArithmeticAxiom.addZero left)).weakenClosedTo context
      let rightZero : Derivation LogicMode.intuitionistic haTheory context
          (ScopedFormula.equal
            (ScopedTerm.add right (ScopedTerm.zero bound)) right) :=
        (Derivation.theoryAxiom
          (context := FormulaContext.nil)
          (StandardArithmeticAxiom.addZero right)).weakenClosedTo context
      exact Derivation.equalityTransitivity
        (Derivation.equalitySymmetry leftZero)
        (Derivation.equalityTransitivity assumed rightZero)
    simpa [body, conclusion, equality, added,
      ScopedFormula.instantiate,
      ScopedTerm.instantiate, ScopedFormula.equal, ScopedFormula.impl,
      ScopedTerm.bvar, ScopedTerm.numeral,
      RawFormula.instantiateTerm,
      RawTerm.instantiateTerm, RawFormula.substitute,
      RawTerm.substitute, singleTermSubstitution,
      ScopedTerm.lift, RawTerm.rename, ScopedTerm.add,
      RawTerm.renameSucc_substituteSingle] using core
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let currentEquality := ScopedFormula.equal
      (ScopedTerm.add left.lift added.succ)
      (ScopedTerm.add right.lift added.succ)
    let stepContext := FormulaContext.cons currentEquality
      (FormulaContext.cons body FormulaContext.nil)
    have core : Derivation LogicMode.intuitionistic haTheory
        (FormulaContext.cons body FormulaContext.nil)
        (ScopedFormula.impl currentEquality conclusion) := by
      apply Derivation.implicationIntroduction
      let current : Derivation LogicMode.intuitionistic haTheory stepContext
          currentEquality := Derivation.hypothesis ContextMember.here
      let unfoldLeft : Derivation LogicMode.intuitionistic haTheory stepContext
          (ScopedFormula.equal
            (ScopedTerm.add left.lift added.succ)
            (ScopedTerm.succ (ScopedTerm.add left.lift added))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addSuccessor left.lift added)
      let unfoldRight : Derivation LogicMode.intuitionistic haTheory stepContext
          (ScopedFormula.equal
            (ScopedTerm.add right.lift added.succ)
            (ScopedTerm.succ (ScopedTerm.add right.lift added))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addSuccessor right.lift added)
      let successorEquality := Derivation.equalityTransitivity
        (Derivation.equalitySymmetry unfoldLeft)
        (Derivation.equalityTransitivity current unfoldRight)
      let reduced := Derivation.implicationElimination
        (Derivation.theoryAxiom
          (StandardArithmeticAxiom.successorInjective
            (ScopedTerm.add left.lift added)
            (ScopedTerm.add right.lift added))) successorEquality
      let inductionImplication : Derivation LogicMode.intuitionistic haTheory
          stepContext body :=
        Derivation.hypothesis (ContextMember.there ContextMember.here)
      exact Derivation.implicationElimination inductionImplication reduced
    simpa [body, conclusion, currentEquality, added, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
      ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteKeepingScope] using core
  exact Derivation.byArithmeticInduction body base step

def addRightCancellationProof
    {bound : Nat}
    (left right added : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl
        (ScopedFormula.equal (ScopedTerm.add left added)
          (ScopedTerm.add right added))
        (ScopedFormula.equal left right)) := by
  let instantiated := Derivation.universalElimination added
    (addRightCancellationUniversal left right)
  simpa [ScopedFormula.instantiate, ScopedTerm.instantiate,
    ScopedFormula.equal, ScopedFormula.impl, ScopedTerm.bvar,
    ScopedTerm.numeral, RawFormula.instantiateTerm,
    RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedTerm.lift, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle,
    ScopedTerm.add] using instantiated

def addLeftCancellationProof
    {bound : Nat}
    (added left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl
        (ScopedFormula.equal (ScopedTerm.add added left)
          (ScopedTerm.add added right))
        (ScopedFormula.equal left right)) := by
  apply Derivation.implicationIntroduction
  let equality := ScopedFormula.equal (ScopedTerm.add added left)
    (ScopedTerm.add added right)
  let context := FormulaContext.cons equality FormulaContext.nil
  let assumed : Derivation LogicMode.intuitionistic haTheory context equality :=
    Derivation.hypothesis ContextMember.here
  let leftCommute := (addCommutativeProof added left).weakenClosedTo context
  let rightCommute := (addCommutativeProof added right).weakenClosedTo context
  let reordered := Derivation.equalityTransitivity
    (Derivation.equalitySymmetry leftCommute)
    (Derivation.equalityTransitivity assumed rightCommute)
  let cancellation := (addRightCancellationProof left right added).weakenClosedTo
    context
  exact Derivation.implicationElimination cancellation reordered

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.successorAddProof
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.renameSucc_substituteKeepingScope
#print axioms RelationalPerimeter.HeytingArithmetic.zeroAddProof
#print axioms RelationalPerimeter.HeytingArithmetic.addCommutativeProof
#print axioms RelationalPerimeter.HeytingArithmetic.addAssociativeProof
#print axioms RelationalPerimeter.HeytingArithmetic.addRightCancellationProof
#print axioms RelationalPerimeter.HeytingArithmetic.addLeftCancellationProof
/- AXIOM_AUDIT_END -/
