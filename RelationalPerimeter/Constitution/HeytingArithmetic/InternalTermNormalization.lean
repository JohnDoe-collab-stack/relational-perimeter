import RelationalPerimeter.Constitution.HeytingArithmetic.InternalNumeralProofs

/-!
# Object-level normalization of closed arithmetic terms

Every closed term is connected to its computed numeral by an explicit HA
derivation.  This is the arithmetic kernel used to certify concrete beta
witnesses and primitive-recursive traces.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem normalizationBinaryCongr
    {alpha beta gamma : Type}
    (operation : alpha -> beta -> gamma)
    {left₁ left₂ : alpha}
    {right₁ right₂ : beta}
    (leftEqual : left₁ = left₂)
    (rightEqual : right₁ = right₂) :
    operation left₁ right₁ = operation left₂ right₂ := by
  cases leftEqual
  cases rightEqual
  rfl

theorem RawTerm.renameSucc_substituteSingle
    (term replacement : RawTerm) :
    (term.rename Nat.succ).substitute
        (singleTermSubstitution replacement) = term := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact normalizationBinaryCongr RawTerm.add
        leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact normalizationBinaryCongr RawTerm.mul
        leftHypothesis rightHypothesis

def successorCongruence
    {left right : ScopedTerm 0}
    (equality : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left.succ right.succ) := by
  let body : ScopedFormula 1 :=
    ScopedFormula.equal left.lift.succ
      (ScopedTerm.succ (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left.succ left.succ) :=
    Derivation.equalityReflexivity left.succ
  have atLeft : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.succ,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
      RawTerm.raise, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.succ,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def addCongruenceLeft
    {left right fixed : ScopedTerm 0}
    (equality : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add left fixed)
        (ScopedTerm.add right fixed)) := by
  let body : ScopedFormula 1 :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift fixed.lift)
      (ScopedTerm.add (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)) fixed.lift)
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add left fixed)
        (ScopedTerm.add left fixed)) :=
    Derivation.equalityReflexivity (ScopedTerm.add left fixed)
  have atLeft : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.add,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
      RawTerm.raise, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.add,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def addCongruenceRight
    {fixed left right : ScopedTerm 0}
    (equality : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add fixed left)
        (ScopedTerm.add fixed right)) := by
  let body : ScopedFormula 1 :=
    ScopedFormula.equal
      (ScopedTerm.add fixed.lift left.lift)
      (ScopedTerm.add fixed.lift (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.add fixed left)
        (ScopedTerm.add fixed left)) :=
    Derivation.equalityReflexivity (ScopedTerm.add fixed left)
  have atLeft : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.add,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
      RawTerm.raise, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.add,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def multiplyCongruenceLeft
    {left right fixed : ScopedTerm 0}
    (equality : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.mul left fixed)
        (ScopedTerm.mul right fixed)) := by
  let body : ScopedFormula 1 :=
    ScopedFormula.equal
      (ScopedTerm.mul left.lift fixed.lift)
      (ScopedTerm.mul (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)) fixed.lift)
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.mul left fixed)
        (ScopedTerm.mul left fixed)) :=
    Derivation.equalityReflexivity (ScopedTerm.mul left fixed)
  have atLeft : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.mul,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
      RawTerm.raise, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.mul,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def multiplyCongruenceRight
    {fixed left right : ScopedTerm 0}
    (equality : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.mul fixed left)
        (ScopedTerm.mul fixed right)) := by
  let body : ScopedFormula 1 :=
    ScopedFormula.equal
      (ScopedTerm.mul fixed.lift left.lift)
      (ScopedTerm.mul fixed.lift (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.mul fixed left)
        (ScopedTerm.mul fixed left)) :=
    Derivation.equalityReflexivity (ScopedTerm.mul fixed left)
  have atLeft : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.mul,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
      RawTerm.raise, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.bvar, ScopedTerm.mul,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def addNumeralsProof : (left right : Nat) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add (ScopedTerm.numeral 0 left)
          (ScopedTerm.numeral 0 right))
        (ScopedTerm.numeral 0 (left + right)))
  | left, 0 =>
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.addZero (ScopedTerm.numeral 0 left))
  | left, Nat.succ right => by
      let unfolded : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
          (ScopedFormula.equal
            (ScopedTerm.add (ScopedTerm.numeral 0 left)
              (ScopedTerm.numeral 0 (Nat.succ right)))
            (ScopedTerm.succ
              (ScopedTerm.add (ScopedTerm.numeral 0 left)
                (ScopedTerm.numeral 0 right)))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.addSuccessor
            (ScopedTerm.numeral 0 left) (ScopedTerm.numeral 0 right))
      let recursive := successorCongruence (addNumeralsProof left right)
      exact Derivation.equalityTransitivity unfolded recursive

def multiplyNumeralsProof : (left right : Nat) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.mul (ScopedTerm.numeral 0 left)
          (ScopedTerm.numeral 0 right))
        (ScopedTerm.numeral 0 (left * right)))
  | left, 0 =>
      Derivation.theoryAxiom
        (StandardArithmeticAxiom.multiplyZero (ScopedTerm.numeral 0 left))
  | left, Nat.succ right => by
      let unfolded : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
          (ScopedFormula.equal
            (ScopedTerm.mul (ScopedTerm.numeral 0 left)
              (ScopedTerm.numeral 0 (Nat.succ right)))
            (ScopedTerm.add
              (ScopedTerm.mul (ScopedTerm.numeral 0 left)
                (ScopedTerm.numeral 0 right))
              (ScopedTerm.numeral 0 left))) :=
        Derivation.theoryAxiom
          (StandardArithmeticAxiom.multiplySuccessor
            (ScopedTerm.numeral 0 left) (ScopedTerm.numeral 0 right))
      let recursiveCongruence :=
        addCongruenceLeft (fixed := ScopedTerm.numeral 0 left)
          (multiplyNumeralsProof left right)
      let addition := addNumeralsProof (left * right) left
      exact Derivation.equalityTransitivity unfolded
        (Derivation.equalityTransitivity recursiveCongruence addition)

def normalizeRawClosedTerm :
    (term : RawTerm) ->
    (scopeEvidence : term.WellScoped 0) ->
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        ⟨term, scopeEvidence⟩
        (ScopedTerm.numeral 0 (term.evaluate emptyEnvironment)))
  | RawTerm.bvar index, scopeEvidence =>
      (Nat.not_lt_zero index scopeEvidence).elim
  | RawTerm.zero, _scopeEvidence =>
      Derivation.equalityReflexivity (ScopedTerm.zero 0)
  | RawTerm.succ body, scopeEvidence => by
      exact successorCongruence
        (normalizeRawClosedTerm body scopeEvidence)
  | RawTerm.add left right, scopeEvidence => by
      let leftTerm : ScopedTerm 0 := ⟨left, scopeEvidence.1⟩
      let rightTerm : ScopedTerm 0 := ⟨right, scopeEvidence.2⟩
      let normalizeLeft :=
        addCongruenceLeft (fixed := rightTerm)
          (normalizeRawClosedTerm left scopeEvidence.1)
      let normalizeRight :=
        addCongruenceRight
          (fixed := ScopedTerm.numeral 0 (left.evaluate emptyEnvironment))
          (normalizeRawClosedTerm right scopeEvidence.2)
      exact Derivation.equalityTransitivity normalizeLeft
        (Derivation.equalityTransitivity normalizeRight
          (addNumeralsProof (left.evaluate emptyEnvironment)
            (right.evaluate emptyEnvironment)))
  | RawTerm.mul left right, scopeEvidence => by
      let leftTerm : ScopedTerm 0 := ⟨left, scopeEvidence.1⟩
      let rightTerm : ScopedTerm 0 := ⟨right, scopeEvidence.2⟩
      let normalizeLeft :=
        multiplyCongruenceLeft (fixed := rightTerm)
          (normalizeRawClosedTerm left scopeEvidence.1)
      let normalizeRight :=
        multiplyCongruenceRight
          (fixed := ScopedTerm.numeral 0 (left.evaluate emptyEnvironment))
          (normalizeRawClosedTerm right scopeEvidence.2)
      exact Derivation.equalityTransitivity normalizeLeft
        (Derivation.equalityTransitivity normalizeRight
          (multiplyNumeralsProof (left.evaluate emptyEnvironment)
            (right.evaluate emptyEnvironment)))

def normalizeClosedTerm
    (term : ScopedTerm 0) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal term
        (ScopedTerm.numeral 0 (term.raw.evaluate emptyEnvironment))) :=
  normalizeRawClosedTerm term.raw term.isScoped

def closedTermEqualityProof
    (left right : ScopedTerm 0)
    (sameValue :
      left.raw.evaluate emptyEnvironment =
        right.raw.evaluate emptyEnvironment) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal left right) := by
  let leftNormalized := normalizeClosedTerm left
  let rightNormalized := normalizeClosedTerm right
  let valuesEqual := numeralEqualityProof 0
    (left.raw.evaluate emptyEnvironment)
    (right.raw.evaluate emptyEnvironment) sameValue
  exact Derivation.equalityTransitivity leftNormalized
    (Derivation.equalityTransitivity valuesEqual
      (Derivation.equalitySymmetry rightNormalized))

def closedTermInequalityProof
    (left right : ScopedTerm 0)
    (differentValue :
      left.raw.evaluate emptyEnvironment =
        right.raw.evaluate emptyEnvironment -> False) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.neg (ScopedFormula.equal left right)) := by
  let equality := ScopedFormula.equal left right
  let assumed : Derivation LogicMode.intuitionistic haTheory
      (FormulaContext.cons equality FormulaContext.nil) equality :=
    Derivation.hypothesis ContextMember.here
  let leftNormalized := Derivation.weaken equality (normalizeClosedTerm left)
  let rightNormalized := Derivation.weaken equality (normalizeClosedTerm right)
  let valueEquality : Derivation LogicMode.intuitionistic haTheory
      (FormulaContext.cons equality FormulaContext.nil)
      (numeralEqualityFormula 0
        (left.raw.evaluate emptyEnvironment)
        (right.raw.evaluate emptyEnvironment)) :=
    Derivation.equalityTransitivity
      (Derivation.equalitySymmetry leftNormalized)
      (Derivation.equalityTransitivity assumed rightNormalized)
  let valuesDiffer : Derivation LogicMode.intuitionistic haTheory
      (FormulaContext.cons equality FormulaContext.nil)
      (ScopedFormula.neg
        (numeralEqualityFormula 0
          (left.raw.evaluate emptyEnvironment)
          (right.raw.evaluate emptyEnvironment))) :=
    Derivation.weaken equality
      (numeralInequalityProof 0
        (left.raw.evaluate emptyEnvironment)
        (right.raw.evaluate emptyEnvironment) differentValue)
  exact Derivation.implicationIntroduction
    (Derivation.implicationElimination valuesDiffer valueEquality)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.addNumeralsProof
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyNumeralsProof
#print axioms RelationalPerimeter.HeytingArithmetic.normalizeClosedTerm
#print axioms RelationalPerimeter.HeytingArithmetic.closedTermEqualityProof
#print axioms RelationalPerimeter.HeytingArithmetic.closedTermInequalityProof
/- AXIOM_AUDIT_END -/
