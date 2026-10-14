import RelationalPerimeter.Constitution.HeytingArithmetic.InternalDerivationTools

/-!
# Reusable object-level induction builder
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def Derivation.byArithmeticInduction
    {bound : Nat}
    (body : ScopedFormula (Nat.succ bound))
    (base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate (ScopedTerm.zero bound)))
    (step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance))) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all body) :=
  Derivation.implicationElimination
    (Derivation.theoryAxiom (StandardArithmeticAxiom.induction body))
    (Derivation.conjunctionIntroduction base step)

def Derivation.byArithmeticInductionAt
    {bound : Nat}
    {context : FormulaContext bound}
    (body : ScopedFormula (Nat.succ bound))
    (base : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate (ScopedTerm.zero bound)))
    (step : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance))) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.all body) :=
  Derivation.implicationElimination
    (Derivation.theoryAxiom (StandardArithmeticAxiom.induction body))
    (Derivation.conjunctionIntroduction base step)

def addCongruenceLeftAt
    {bound : Nat}
    {context : FormulaContext bound}
    {left right fixed : ScopedTerm bound}
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.add left fixed)
        (ScopedTerm.add right fixed)) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift fixed.lift)
      (ScopedTerm.add
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)) fixed.lift)
  let reflexive : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.add left fixed)
        (ScopedTerm.add left fixed)) :=
    Derivation.equalityReflexivity (ScopedTerm.add left fixed)
  have atLeft : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.add,
      ScopedTerm.bvar, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm, RawFormula.substitute,
      RawTerm.substitute, singleTermSubstitution, RawTerm.raise,
      RawTerm.rename, RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.add,
    ScopedTerm.bvar,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def addCongruenceRightAt
    {bound : Nat}
    {context : FormulaContext bound}
    {fixed left right : ScopedTerm bound}
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.add fixed left)
        (ScopedTerm.add fixed right)) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add fixed.lift left.lift)
      (ScopedTerm.add fixed.lift
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.add fixed left)
        (ScopedTerm.add fixed left)) :=
    Derivation.equalityReflexivity (ScopedTerm.add fixed left)
  have atLeft : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.add,
      ScopedTerm.bvar, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm, RawFormula.substitute,
      RawTerm.substitute, singleTermSubstitution, RawTerm.raise,
      RawTerm.rename, RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.add,
    ScopedTerm.bvar,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def multiplyCongruenceLeftAt
    {bound : Nat}
    {context : FormulaContext bound}
    {left right fixed : ScopedTerm bound}
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.mul left fixed)
        (ScopedTerm.mul right fixed)) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.mul left.lift fixed.lift)
      (ScopedTerm.mul
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)) fixed.lift)
  let reflexive : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.mul left fixed)
        (ScopedTerm.mul left fixed)) :=
    Derivation.equalityReflexivity (ScopedTerm.mul left fixed)
  have atLeft : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.mul,
      ScopedTerm.bvar, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm, RawFormula.substitute,
      RawTerm.substitute, singleTermSubstitution, RawTerm.raise,
      RawTerm.rename, RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.mul,
    ScopedTerm.bvar,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def multiplyCongruenceRightAt
    {bound : Nat}
    {context : FormulaContext bound}
    {fixed left right : ScopedTerm bound}
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.mul fixed left)
        (ScopedTerm.mul fixed right)) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.mul fixed.lift left.lift)
      (ScopedTerm.mul fixed.lift
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.mul fixed left)
        (ScopedTerm.mul fixed left)) :=
    Derivation.equalityReflexivity (ScopedTerm.mul fixed left)
  have atLeft : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.mul,
      ScopedTerm.bvar, RawFormula.instantiateTerm,
      RawTerm.instantiateTerm, RawFormula.substitute,
      RawTerm.substitute, singleTermSubstitution, RawTerm.raise,
      RawTerm.rename, RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.mul,
    ScopedTerm.bvar,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.byArithmeticInduction
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.byArithmeticInductionAt
#print axioms RelationalPerimeter.HeytingArithmetic.addCongruenceLeftAt
#print axioms RelationalPerimeter.HeytingArithmetic.addCongruenceRightAt
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyCongruenceLeftAt
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyCongruenceRightAt
/- AXIOM_AUDIT_END -/
