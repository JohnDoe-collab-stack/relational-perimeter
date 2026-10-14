import RelationalPerimeter.Constitution.HeytingArithmetic.GeneralInstantiation
import RelationalPerimeter.Constitution.HeytingArithmetic.Representability

/-!
# Constructive object proof calculus for PA and HA

Derivations are positive finite values in `Type`.  Every logical rule operates
only on raw first-order syntax with explicit De Bruijn scoping evidence.  PA
and HA share exactly the same arithmetic postulate schemes; their sole difference
is the availability of double-negation elimination in the classical mode.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Scoped syntax constructors -/

/-- A raw term paired with its ambient De Bruijn scope. -/
structure ScopedTerm (bound : Nat) where
  raw : RawTerm
  isScoped : raw.WellScoped bound

namespace ScopedTerm

def bvar {bound : Nat} (index : Nat) (bounded : index < bound) :
    ScopedTerm bound :=
  { raw := RawTerm.bvar index, isScoped := bounded }

def zero (bound : Nat) : ScopedTerm bound :=
  { raw := RawTerm.zero, isScoped := trivial }

def succ {bound : Nat} (term : ScopedTerm bound) : ScopedTerm bound :=
  { raw := RawTerm.succ term.raw, isScoped := term.isScoped }

def add {bound : Nat}
    (left right : ScopedTerm bound) : ScopedTerm bound :=
  { raw := RawTerm.add left.raw right.raw
    isScoped := And.intro left.isScoped right.isScoped }

def mul {bound : Nat}
    (left right : ScopedTerm bound) : ScopedTerm bound :=
  { raw := RawTerm.mul left.raw right.raw
    isScoped := And.intro left.isScoped right.isScoped }

def numeral (bound value : Nat) : ScopedTerm bound :=
  { raw := RawTerm.numeral value
    isScoped := RawTerm.numeral_wellScoped value bound }

def lift {bound : Nat} (term : ScopedTerm bound) :
    ScopedTerm (Nat.succ bound) :=
  { raw := term.raw.rename Nat.succ
    isScoped := term.raw.wellScoped_rename term.isScoped Nat.succ
      (fun _index bounded => Nat.succ_lt_succ bounded) }

def instantiate {bound : Nat}
    (body : ScopedTerm (Nat.succ bound))
    (replacement : ScopedTerm bound) : ScopedTerm bound :=
  { raw := body.raw.instantiateTerm replacement.raw
    isScoped := body.raw.instantiateTerm_wellScoped replacement.raw bound
      body.isScoped replacement.isScoped }

end ScopedTerm

namespace ScopedFormula

def falsum (bound : Nat) : ScopedFormula bound :=
  { raw := RawFormula.falsum, isScoped := trivial }

def equal {bound : Nat}
    (left right : ScopedTerm bound) : ScopedFormula bound :=
  { raw := RawFormula.equal left.raw right.raw
    isScoped := And.intro left.isScoped right.isScoped }

def conj {bound : Nat}
    (left right : ScopedFormula bound) : ScopedFormula bound :=
  { raw := RawFormula.conj left.raw right.raw
    isScoped := And.intro left.isScoped right.isScoped }

def disj {bound : Nat}
    (left right : ScopedFormula bound) : ScopedFormula bound :=
  { raw := RawFormula.disj left.raw right.raw
    isScoped := And.intro left.isScoped right.isScoped }

def impl {bound : Nat}
    (left right : ScopedFormula bound) : ScopedFormula bound :=
  { raw := RawFormula.impl left.raw right.raw
    isScoped := And.intro left.isScoped right.isScoped }

def neg {bound : Nat} (formula : ScopedFormula bound) :
    ScopedFormula bound :=
  impl formula (falsum bound)

def all {bound : Nat} (body : ScopedFormula (Nat.succ bound)) :
    ScopedFormula bound :=
  { raw := RawFormula.all body.raw, isScoped := body.isScoped }

def ex {bound : Nat} (body : ScopedFormula (Nat.succ bound)) :
    ScopedFormula bound :=
  { raw := RawFormula.ex body.raw, isScoped := body.isScoped }

def lift {bound : Nat} (formula : ScopedFormula bound) :
    ScopedFormula (Nat.succ bound) :=
  { raw := formula.raw.rename Nat.succ
    isScoped := formula.raw.wellScoped_rename formula.isScoped Nat.succ
      (fun _index bounded => Nat.succ_lt_succ bounded) }

def instantiate {bound : Nat}
    (body : ScopedFormula (Nat.succ bound))
    (replacement : ScopedTerm bound) : ScopedFormula bound :=
  { raw := body.raw.instantiateTerm replacement.raw
    isScoped := body.raw.instantiateTerm_wellScoped replacement.raw bound
      body.isScoped replacement.isScoped }

/-- Replace variable zero while retaining the same ambient scope. -/
def replaceNewestKeepingScopeSubstitution : Substitution
  | 0 => RawTerm.succ (RawTerm.bvar 0)
  | Nat.succ index => RawTerm.bvar (Nat.succ index)

theorem replaceNewestKeepingScopeSubstitution_wellScoped
    (bound index : Nat)
    (bounded : index < Nat.succ bound) :
    (replaceNewestKeepingScopeSubstitution index).WellScoped
      (Nat.succ bound) := by
  cases index with
  | zero => exact Nat.zero_lt_succ bound
  | succ index => exact bounded

/-- In an induction step, replace the induction variable by its successor. -/
def successorInstance {bound : Nat}
    (body : ScopedFormula (Nat.succ bound)) :
    ScopedFormula (Nat.succ bound) :=
  { raw := body.raw.substitute replaceNewestKeepingScopeSubstitution
    isScoped := body.raw.wellScoped_substitute body.isScoped
      replaceNewestKeepingScopeSubstitution
      (replaceNewestKeepingScopeSubstitution_wellScoped bound) }

/-- Full induction formula with every ambient parameter retained. -/
def induction {bound : Nat}
    (body : ScopedFormula (Nat.succ bound)) : ScopedFormula bound :=
  let base := instantiate body (ScopedTerm.zero bound)
  let stepBody := impl body (successorInstance body)
  impl (conj base (all stepBody)) (all body)

end ScopedFormula

/-! ## Positive local contexts -/

inductive FormulaContext (bound : Nat) : Type
  | nil : FormulaContext bound
  | cons : ScopedFormula bound -> FormulaContext bound -> FormulaContext bound

namespace FormulaContext

def lift {bound : Nat} : FormulaContext bound ->
    FormulaContext (Nat.succ bound)
  | FormulaContext.nil => FormulaContext.nil
  | FormulaContext.cons head tail =>
      FormulaContext.cons head.lift tail.lift

def instantiate {bound : Nat}
    (replacement : ScopedTerm bound) :
    FormulaContext (Nat.succ bound) -> FormulaContext bound
  | FormulaContext.nil => FormulaContext.nil
  | FormulaContext.cons head tail =>
      FormulaContext.cons (head.instantiate replacement)
        (tail.instantiate replacement)

end FormulaContext

/-- Positive occurrence of a formula in a local context. -/
inductive ContextMember {bound : Nat} :
    ScopedFormula bound -> FormulaContext bound -> Type
  | here {formula context} :
      ContextMember formula (FormulaContext.cons formula context)
  | there {formula head context} :
      ContextMember formula context ->
      ContextMember formula (FormulaContext.cons head context)

/-! ## Arithmetic theory and exact postulate schemes -/

/-- A theory is only a positive family of syntactic postulate witnesses. -/
structure ArithmeticTheory where
  Axiom : (bound : Nat) -> ScopedFormula bound -> Type

/-- The six defining equations and full parameterized induction. -/
inductive StandardArithmeticAxiom :
    {bound : Nat} -> ScopedFormula bound -> Type
  | successorNotZero {bound : Nat} (term : ScopedTerm bound) :
      StandardArithmeticAxiom
        (ScopedFormula.neg
          (ScopedFormula.equal term.succ (ScopedTerm.zero bound)))
  | successorInjective {bound : Nat}
      (left right : ScopedTerm bound) :
      StandardArithmeticAxiom
        (ScopedFormula.impl
          (ScopedFormula.equal left.succ right.succ)
          (ScopedFormula.equal left right))
  | addZero {bound : Nat} (term : ScopedTerm bound) :
      StandardArithmeticAxiom
        (ScopedFormula.equal
          (ScopedTerm.add term (ScopedTerm.zero bound)) term)
  | addSuccessor {bound : Nat}
      (left right : ScopedTerm bound) :
      StandardArithmeticAxiom
        (ScopedFormula.equal
          (ScopedTerm.add left right.succ)
          (ScopedTerm.succ (ScopedTerm.add left right)))
  | multiplyZero {bound : Nat} (term : ScopedTerm bound) :
      StandardArithmeticAxiom
        (ScopedFormula.equal
          (ScopedTerm.mul term (ScopedTerm.zero bound))
          (ScopedTerm.zero bound))
  | multiplySuccessor {bound : Nat}
      (left right : ScopedTerm bound) :
      StandardArithmeticAxiom
        (ScopedFormula.equal
          (ScopedTerm.mul left right.succ)
          (ScopedTerm.add (ScopedTerm.mul left right) left))
  | induction {bound : Nat}
      (body : ScopedFormula (Nat.succ bound)) :
      StandardArithmeticAxiom (ScopedFormula.induction body)

/-- PA and HA use this same positive arithmetic postulate family. -/
def standardArithmeticTheory : ArithmeticTheory :=
  { Axiom := fun _bound formula => StandardArithmeticAxiom formula }

def paTheory : ArithmeticTheory := standardArithmeticTheory
def haTheory : ArithmeticTheory := standardArithmeticTheory

/-! ## Logical modes -/

inductive LogicMode where
  | intuitionistic
  | classical
deriving DecidableEq

/-- Positive permission for the unique classical rule. -/
inductive ClassicalPermission : LogicMode -> Type
  | available : ClassicalPermission LogicMode.classical

/-! ## Natural deduction as positive data -/

inductive Derivation
    (mode : LogicMode)
    (theory : ArithmeticTheory) :
    {bound : Nat} ->
    FormulaContext bound -> ScopedFormula bound -> Type
  | theoryAxiom {bound : Nat}
      {context : FormulaContext bound}
      {conclusion : ScopedFormula bound}
      (witness : theory.Axiom bound conclusion) :
      Derivation mode theory context conclusion
  | hypothesis {bound : Nat}
      {context : FormulaContext bound}
      {conclusion : ScopedFormula bound}
      (member : ContextMember conclusion context) :
      Derivation mode theory context conclusion
  | weaken {bound : Nat}
      {context : FormulaContext bound}
      {conclusion : ScopedFormula bound}
      (extra : ScopedFormula bound) :
      Derivation mode theory context conclusion ->
      Derivation mode theory (FormulaContext.cons extra context) conclusion
  | implicationIntroduction {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory (FormulaContext.cons left context) right ->
      Derivation mode theory context (ScopedFormula.impl left right)
  | implicationElimination {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory context (ScopedFormula.impl left right) ->
      Derivation mode theory context left ->
      Derivation mode theory context right
  | conjunctionIntroduction {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory context left ->
      Derivation mode theory context right ->
      Derivation mode theory context (ScopedFormula.conj left right)
  | conjunctionEliminationLeft {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory context (ScopedFormula.conj left right) ->
      Derivation mode theory context left
  | conjunctionEliminationRight {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory context (ScopedFormula.conj left right) ->
      Derivation mode theory context right
  | disjunctionIntroductionLeft {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory context left ->
      Derivation mode theory context (ScopedFormula.disj left right)
  | disjunctionIntroductionRight {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedFormula bound} :
      Derivation mode theory context right ->
      Derivation mode theory context (ScopedFormula.disj left right)
  | disjunctionElimination {bound : Nat}
      {context : FormulaContext bound}
      {left right conclusion : ScopedFormula bound} :
      Derivation mode theory context (ScopedFormula.disj left right) ->
      Derivation mode theory (FormulaContext.cons left context) conclusion ->
      Derivation mode theory (FormulaContext.cons right context) conclusion ->
      Derivation mode theory context conclusion
  | falsumElimination {bound : Nat}
      {context : FormulaContext bound}
      {conclusion : ScopedFormula bound} :
      Derivation mode theory context (ScopedFormula.falsum bound) ->
      Derivation mode theory context conclusion
  | universalIntroduction {bound : Nat}
      {context : FormulaContext bound}
      {body : ScopedFormula (Nat.succ bound)} :
      Derivation mode theory context.lift body ->
      Derivation mode theory context (ScopedFormula.all body)
  | universalElimination {bound : Nat}
      {context : FormulaContext bound}
      {body : ScopedFormula (Nat.succ bound)}
      (term : ScopedTerm bound) :
      Derivation mode theory context (ScopedFormula.all body) ->
      Derivation mode theory context (body.instantiate term)
  | existentialIntroduction {bound : Nat}
      {context : FormulaContext bound}
      {body : ScopedFormula (Nat.succ bound)}
      (term : ScopedTerm bound) :
      Derivation mode theory context (body.instantiate term) ->
      Derivation mode theory context (ScopedFormula.ex body)
  | existentialElimination {bound : Nat}
      {context : FormulaContext bound}
      {body : ScopedFormula (Nat.succ bound)}
      {conclusion : ScopedFormula bound} :
      Derivation mode theory context (ScopedFormula.ex body) ->
      Derivation mode theory
        (FormulaContext.cons body context.lift) conclusion.lift ->
      Derivation mode theory context conclusion
  | equalityReflexivity {bound : Nat}
      {context : FormulaContext bound}
      (term : ScopedTerm bound) :
      Derivation mode theory context (ScopedFormula.equal term term)
  | equalitySymmetry {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedTerm bound} :
      Derivation mode theory context (ScopedFormula.equal left right) ->
      Derivation mode theory context (ScopedFormula.equal right left)
  | equalityTransitivity {bound : Nat}
      {context : FormulaContext bound}
      {left middle right : ScopedTerm bound} :
      Derivation mode theory context (ScopedFormula.equal left middle) ->
      Derivation mode theory context (ScopedFormula.equal middle right) ->
      Derivation mode theory context (ScopedFormula.equal left right)
  | equalitySubstitution {bound : Nat}
      {context : FormulaContext bound}
      {left right : ScopedTerm bound}
      (body : ScopedFormula (Nat.succ bound)) :
      Derivation mode theory context (ScopedFormula.equal left right) ->
      Derivation mode theory context (body.instantiate left) ->
      Derivation mode theory context (body.instantiate right)
  | liftVariables {bound : Nat}
      {context : FormulaContext bound}
      {conclusion : ScopedFormula bound} :
      Derivation mode theory context conclusion ->
      Derivation mode theory context.lift conclusion.lift
  | freeInstantiation {bound : Nat}
      {context : FormulaContext (Nat.succ bound)}
      {conclusion : ScopedFormula (Nat.succ bound)}
      (replacement : ScopedTerm bound) :
      Derivation mode theory context conclusion ->
      Derivation mode theory
        (context.instantiate replacement)
        (conclusion.instantiate replacement)
  | doubleNegationElimination {bound : Nat}
      {context : FormulaContext bound}
      {conclusion : ScopedFormula bound}
      (permission : ClassicalPermission mode) :
      Derivation mode theory context
        (ScopedFormula.neg (ScopedFormula.neg conclusion)) ->
      Derivation mode theory context conclusion

namespace Derivation

def weakening
    {mode theory bound context conclusion}
    (extra : ScopedFormula bound)
    (proof : Derivation mode theory context conclusion) :
    Derivation mode theory (FormulaContext.cons extra context) conclusion :=
  Derivation.weaken extra proof

def substitute
    {mode theory bound context conclusion}
    (replacement : ScopedTerm bound)
    (proof : Derivation mode theory context conclusion) :
    Derivation mode theory
      (context.instantiate replacement)
      (conclusion.instantiate replacement) :=
  Derivation.freeInstantiation replacement proof

def modusPonens
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {left right : ScopedFormula bound}
    (implication :
      Derivation mode theory context (ScopedFormula.impl left right))
    (argument : Derivation mode theory context left) :
    Derivation mode theory context right :=
  Derivation.implicationElimination implication argument

end Derivation

/-! ## Closed PA and HA provability -/

def Sentence.scopedFormula (sentence : Sentence) : ScopedFormula 0 :=
  { raw := sentence.raw, isScoped := sentence.isScoped }

def TheoryProvable
    (mode : LogicMode)
    (theory : ArithmeticTheory)
    (sentence : Sentence) : Prop :=
  Nonempty
    (Derivation mode theory FormulaContext.nil sentence.scopedFormula)

def PAProvable (sentence : Sentence) : Prop :=
  TheoryProvable LogicMode.classical paTheory sentence

def HAProvable (sentence : Sentence) : Prop :=
  TheoryProvable LogicMode.intuitionistic haTheory sentence

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.StandardArithmeticAxiom
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.substitute
#print axioms RelationalPerimeter.HeytingArithmetic.PAProvable
#print axioms RelationalPerimeter.HeytingArithmetic.HAProvable
/- AXIOM_AUDIT_END -/
