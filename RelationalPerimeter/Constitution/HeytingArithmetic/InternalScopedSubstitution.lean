import RelationalPerimeter.Constitution.HeytingArithmetic.InternalDerivationTools

/-!
# Constructive extensionality for scoped substitutions

These lemmas isolate the exact finite information used by a scoped term or
formula.  They avoid function extensionality: agreement is required only at
indices certified to lie inside the scope.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

theorem RawTerm.substitute_eq_of_scoped_agreement
    {bound : Nat}
    (term : RawTerm)
    (scope : term.WellScoped bound)
    (first second : Substitution)
    (agreement : (index : Nat) -> index < bound ->
      first index = second index) :
    term.substitute first = term.substitute second := by
  induction term generalizing bound first second with
  | bvar index => exact agreement index scope
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ
        (inductionHypothesis scope first second agreement)
  | add left right leftInduction rightInduction =>
      exact congrArgTwo RawTerm.add
        (leftInduction scope.1 first second agreement)
        (rightInduction scope.2 first second agreement)
  | mul left right leftInduction rightInduction =>
      exact congrArgTwo RawTerm.mul
        (leftInduction scope.1 first second agreement)
        (rightInduction scope.2 first second agreement)

theorem RawFormula.substitute_eq_of_scoped_agreement
    {bound : Nat}
    (formula : RawFormula)
    (scope : formula.WellScoped bound)
    (first second : Substitution)
    (agreement : (index : Nat) -> index < bound ->
      first index = second index) :
    formula.substitute first = formula.substitute second := by
  induction formula generalizing bound first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.substitute_eq_of_scoped_agreement scope.1
          first second agreement)
        (right.substitute_eq_of_scoped_agreement scope.2
          first second agreement)
  | conj left right leftInduction rightInduction =>
      exact congrArgTwo RawFormula.conj
        (leftInduction scope.1 first second agreement)
        (rightInduction scope.2 first second agreement)
  | disj left right leftInduction rightInduction =>
      exact congrArgTwo RawFormula.disj
        (leftInduction scope.1 first second agreement)
        (rightInduction scope.2 first second agreement)
  | impl left right leftInduction rightInduction =>
      exact congrArgTwo RawFormula.impl
        (leftInduction scope.1 first second agreement)
        (rightInduction scope.2 first second agreement)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis scope (liftSubstitution first)
        (liftSubstitution second)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (agreement index (Nat.lt_of_succ_lt_succ bounded))
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis scope (liftSubstitution first)
        (liftSubstitution second)
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (agreement index (Nat.lt_of_succ_lt_succ bounded))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.substitute_eq_of_scoped_agreement
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitute_eq_of_scoped_agreement
/- AXIOM_AUDIT_END -/
