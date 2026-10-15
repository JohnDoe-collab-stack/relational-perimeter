import RelationalPerimeter.Instances.HeytingArithmetic.InternalNaturalCases

/-!
# Structural tools for internally generated derivations
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def ScopedTerm.liftMany {bound : Nat} :
    (count : Nat) -> ScopedTerm bound -> ScopedTerm (count + bound)
  | 0, term =>
      Eq.mpr (congrArg ScopedTerm (Nat.zero_add bound)) term
  | Nat.succ count, term =>
      Eq.mpr (congrArg ScopedTerm (Nat.succ_add count bound))
        (term.liftMany count).lift

def ScopedFormula.liftMany {bound : Nat} :
    (count : Nat) -> ScopedFormula bound -> ScopedFormula (count + bound)
  | 0, formula =>
      Eq.mpr (congrArg ScopedFormula (Nat.zero_add bound)) formula
  | Nat.succ count, formula =>
      Eq.mpr (congrArg ScopedFormula (Nat.succ_add count bound))
        (formula.liftMany count).lift

def FormulaContext.liftMany {bound : Nat} :
    (count : Nat) -> FormulaContext bound -> FormulaContext (count + bound)
  | 0, context =>
      Eq.mpr (congrArg FormulaContext (Nat.zero_add bound)) context
  | Nat.succ count, context =>
      Eq.mpr (congrArg FormulaContext (Nat.succ_add count bound))
        (context.liftMany count).lift

theorem ScopedFormula.transport_raw
    {source target : Nat}
    (sameBound : source = target)
    (formula : ScopedFormula source) :
    (Eq.mp (congrArg ScopedFormula sameBound) formula).raw = formula.raw := by
  cases sameBound
  rfl

def Derivation.castConclusion
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {source target : ScopedFormula bound}
    (sameConclusion : source = target)
    (proof : Derivation mode theory context source) :
    Derivation mode theory context target := by
  cases sameConclusion
  exact proof

def Derivation.transportBound
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {source target : Nat}
    (sameBound : source = target)
    {context : FormulaContext source}
    {conclusion : ScopedFormula source}
    (proof : Derivation mode theory context conclusion) :
    Derivation mode theory
      (Eq.mp (congrArg FormulaContext sameBound) context)
      (Eq.mp (congrArg ScopedFormula sameBound) conclusion) := by
  cases sameBound
  exact proof

def Derivation.liftMany
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound} :
    (count : Nat) ->
    Derivation mode theory context conclusion ->
      Derivation mode theory (context.liftMany count)
        (conclusion.liftMany count)
  | 0, proof =>
      Derivation.transportBound (Nat.zero_add bound).symm proof
  | Nat.succ count, proof =>
      Derivation.transportBound (Nat.succ_add count bound).symm
        (Derivation.liftVariables (proof.liftMany count))

def Derivation.weakenClosedTo
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {conclusion : ScopedFormula bound} :
    (context : FormulaContext bound) ->
    Derivation mode theory FormulaContext.nil conclusion ->
      Derivation mode theory context conclusion
  | FormulaContext.nil, proof => proof
  | FormulaContext.cons head tail, proof =>
      Derivation.weaken head (proof.weakenClosedTo tail)

def successorCongruenceAt
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedTerm bound}
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left.succ right.succ) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal left.lift.succ
      (ScopedTerm.succ
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)))
  let reflexive : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left.succ left.succ) :=
    Derivation.equalityReflexivity left.succ
  have atLeft : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate left) := by
    simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
      ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.succ,
      ScopedTerm.bvar,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
      RawTerm.raise, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using reflexive
  have substituted := Derivation.equalitySubstitution body equality atLeft
  simpa [body, ScopedFormula.instantiate, ScopedFormula.equal,
    ScopedTerm.instantiate, ScopedTerm.lift, ScopedTerm.succ,
    ScopedTerm.bvar,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute, singleTermSubstitution,
    RawTerm.raise, RawTerm.rename,
    RawTerm.renameSucc_substituteSingle] using substituted

def transportFormulaAlongEquality
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedTerm bound}
    (body : ScopedFormula (Nat.succ bound))
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right))
    (atLeft : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate left)) :
    Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate right) :=
  Derivation.equalitySubstitution body equality atLeft

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.liftMany
#print axioms RelationalPerimeter.HeytingArithmetic.ScopedFormula.transport_raw
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.castConclusion
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.transportBound
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.weakenClosedTo
#print axioms RelationalPerimeter.HeytingArithmetic.successorCongruenceAt
#print axioms RelationalPerimeter.HeytingArithmetic.transportFormulaAlongEquality
/- AXIOM_AUDIT_END -/
