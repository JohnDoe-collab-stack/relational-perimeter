import RelationalPerimeter.Constitution.HeytingArithmetic.Syntax

/-!
# Intrinsic scoping for bare arithmetic

Closed sentences and unary predicates are raw formulas paired with positive
De Bruijn scoping evidence.  Closure is therefore a property, never a semantic
instruction in the grammar.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Every variable of a term is strictly below the available binder count. -/
def RawTerm.WellScoped : Nat -> RawTerm -> Prop
  | bound, RawTerm.bvar index => index < bound
  | _bound, RawTerm.zero => True
  | bound, RawTerm.succ term => term.WellScoped bound
  | bound, RawTerm.add left right =>
      left.WellScoped bound ∧ right.WellScoped bound
  | bound, RawTerm.mul left right =>
      left.WellScoped bound ∧ right.WellScoped bound

/-- Every free De Bruijn variable of a formula is below `bound`. -/
def RawFormula.WellScoped : Nat -> RawFormula -> Prop
  | _bound, RawFormula.falsum => True
  | bound, RawFormula.equal left right =>
      left.WellScoped bound ∧ right.WellScoped bound
  | bound, RawFormula.conj left right =>
      left.WellScoped bound ∧ right.WellScoped bound
  | bound, RawFormula.disj left right =>
      left.WellScoped bound ∧ right.WellScoped bound
  | bound, RawFormula.impl left right =>
      left.WellScoped bound ∧ right.WellScoped bound
  | bound, RawFormula.all body => body.WellScoped (Nat.succ bound)
  | bound, RawFormula.ex body => body.WellScoped (Nat.succ bound)

/-- Increasing the available context preserves term scoping. -/
theorem RawTerm.wellScoped_mono
    {smaller larger : Nat}
    (bounded : smaller <= larger) :
    (term : RawTerm) -> term.WellScoped smaller -> term.WellScoped larger
  | RawTerm.bvar _index, evidence => Nat.lt_of_lt_of_le evidence bounded
  | RawTerm.zero, _evidence => trivial
  | RawTerm.succ term, evidence => term.wellScoped_mono bounded evidence
  | RawTerm.add left right, evidence =>
      And.intro
        (left.wellScoped_mono bounded evidence.1)
        (right.wellScoped_mono bounded evidence.2)
  | RawTerm.mul left right, evidence =>
      And.intro
        (left.wellScoped_mono bounded evidence.1)
        (right.wellScoped_mono bounded evidence.2)

/-- Increasing the available context preserves formula scoping. -/
theorem RawFormula.wellScoped_mono
    {smaller larger : Nat}
    (bounded : smaller <= larger) :
    (formula : RawFormula) ->
      formula.WellScoped smaller -> formula.WellScoped larger
  | RawFormula.falsum, _evidence => trivial
  | RawFormula.equal left right, evidence =>
      And.intro
        (left.wellScoped_mono bounded evidence.1)
        (right.wellScoped_mono bounded evidence.2)
  | RawFormula.conj left right, evidence =>
      And.intro
        (left.wellScoped_mono bounded evidence.1)
        (right.wellScoped_mono bounded evidence.2)
  | RawFormula.disj left right, evidence =>
      And.intro
        (left.wellScoped_mono bounded evidence.1)
        (right.wellScoped_mono bounded evidence.2)
  | RawFormula.impl left right, evidence =>
      And.intro
        (left.wellScoped_mono bounded evidence.1)
        (right.wellScoped_mono bounded evidence.2)
  | RawFormula.all body, evidence =>
      body.wellScoped_mono (Nat.succ_le_succ bounded) evidence
  | RawFormula.ex body, evidence =>
      body.wellScoped_mono (Nat.succ_le_succ bounded) evidence

/-- Numerals are scoped in every context. -/
theorem RawTerm.numeral_wellScoped (value bound : Nat) :
    (RawTerm.numeral value).WellScoped bound := by
  induction value with
  | zero => exact trivial
  | succ value inductionHypothesis => exact inductionHypothesis

/-- A closed formula, with closure carried positively as syntax evidence. -/
structure Sentence where
  raw : RawFormula
  isScoped : raw.WellScoped 0

/-- A formula with at most one free De Bruijn variable. -/
structure Predicate where
  raw : RawFormula
  isScoped : raw.WellScoped 1

/-- A closed sentence remains scoped when embedded below one free variable. -/
theorem Sentence.scopedOne (sentence : Sentence) :
  sentence.raw.WellScoped 1 :=
  sentence.raw.wellScoped_mono (Nat.zero_le 1) sentence.isScoped

/-- Equality of raw sentence syntax determines equality of sentences. -/
theorem Sentence.eq_of_raw_eq
    {left right : Sentence}
    (sameRaw : left.raw = right.raw) :
    left = right := by
  cases left with
  | mk leftRaw leftScoped =>
      cases right with
      | mk rightRaw rightScoped =>
          cases sameRaw
          rfl

/-- Equality of raw predicate syntax determines equality of predicates. -/
theorem Predicate.eq_of_raw_eq
    {left right : Predicate}
    (sameRaw : left.raw = right.raw) :
    left = right := by
  cases left with
  | mk leftRaw leftScoped =>
      cases right with
      | mk rightRaw rightScoped =>
          cases sameRaw
          rfl

/-- The closed false sentence. -/
def falseSentence : Sentence where
  raw := RawFormula.falsum
  isScoped := trivial

/-- The unary predicate which is false at every input. -/
def falsePredicate : Predicate where
  raw := RawFormula.falsum
  isScoped := trivial

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.WellScoped
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.WellScoped
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence
#print axioms RelationalPerimeter.HeytingArithmetic.Predicate
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence.scopedOne
/- AXIOM_AUDIT_END -/
