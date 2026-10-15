import RelationalPerimeter.Instances.HeytingArithmetic.ProofTheoryTransport

/-!
# Constructive standard-model soundness of HA

The interpretation is direct in `Nat`; no classical meta-principle is used.
The impossible classical-rule branch is eliminated from the positive
`ClassicalPermission intuitionistic` witness.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def FormulaContext.StandardHolds
    {bound : Nat} : FormulaContext bound -> Environment -> Prop
  | FormulaContext.nil, _environment => True
  | FormulaContext.cons head tail, environment =>
      head.raw.Holds environment ∧ tail.StandardHolds environment

theorem ContextMember.standardHolds
    {bound : Nat}
    {formula : ScopedFormula bound}
    {context : FormulaContext bound}
    (member : ContextMember formula context)
    (environment : Environment)
    (contextHolds : context.StandardHolds environment) :
    formula.raw.Holds environment := by
  induction member with
  | here => exact contextHolds.1
  | there earlier inductionHypothesis =>
      exact inductionHypothesis contextHolds.2

theorem FormulaContext.standardHolds_congr
    {bound : Nat}
    (context : FormulaContext bound)
    (left right : Environment)
    (agree : (index : Nat) -> index < bound ->
      left index = right index) :
    context.StandardHolds left ↔ context.StandardHolds right := by
  induction context with
  | nil => exact Iff.rfl
  | cons head tail inductionHypothesis =>
      exact and_congr
        (head.raw.holds_iff_of_scoped_agreement
          head.isScoped left right agree)
        inductionHypothesis

theorem ScopedFormula.holds_lift
    {bound : Nat}
    (formula : ScopedFormula bound)
    (environment : Environment)
    (value : Nat) :
    formula.lift.raw.Holds (pushEnvironment environment value) ↔
      formula.raw.Holds environment := by
  unfold ScopedFormula.lift
  apply Iff.trans
    (RawFormula.holds_rename formula.raw Nat.succ
      (pushEnvironment environment value))
  exact formula.raw.holds_congr
    (fun index => pushEnvironment environment value (Nat.succ index))
    environment (fun _index => rfl)

theorem FormulaContext.standardHolds_lift
    {bound : Nat}
    (context : FormulaContext bound)
    (environment : Environment)
    (value : Nat)
    (contextHolds : context.StandardHolds environment) :
    context.lift.StandardHolds (pushEnvironment environment value) := by
  induction context with
  | nil => exact trivial
  | cons head tail inductionHypothesis =>
      exact And.intro
        ((head.holds_lift environment value).mpr contextHolds.1)
        (inductionHypothesis contextHolds.2)

theorem FormulaContext.standardHolds_lift_iff
    {bound : Nat}
    (context : FormulaContext bound)
    (environment : Environment)
    (value : Nat) :
    context.lift.StandardHolds (pushEnvironment environment value) ↔
      context.StandardHolds environment := by
  induction context with
  | nil => exact Iff.rfl
  | cons head tail inductionHypothesis =>
      exact and_congr (head.holds_lift environment value)
        inductionHypothesis

theorem ScopedFormula.holds_instantiate
    {bound : Nat}
    (formula : ScopedFormula (Nat.succ bound))
    (term : ScopedTerm bound)
    (environment : Environment) :
    (formula.instantiate term).raw.Holds environment ↔
      formula.raw.Holds
        (pushEnvironment environment (term.raw.evaluate environment)) :=
  RawFormula.holds_instantiateTerm formula.raw term.raw environment

theorem FormulaContext.standardHolds_instantiate
    {bound : Nat}
    (context : FormulaContext (Nat.succ bound))
    (term : ScopedTerm bound)
    (environment : Environment) :
    (context.instantiate term).StandardHolds environment ↔
      context.StandardHolds
        (pushEnvironment environment (term.raw.evaluate environment)) := by
  induction context with
  | nil => exact Iff.rfl
  | cons head tail inductionHypothesis =>
      exact and_congr (head.holds_instantiate term environment)
        inductionHypothesis

theorem ScopedFormula.holds_successorInstance
    {bound : Nat}
    (formula : ScopedFormula (Nat.succ bound))
    (environment : Environment)
    (value : Nat) :
    formula.successorInstance.raw.Holds
        (pushEnvironment environment value) ↔
      formula.raw.Holds
        (pushEnvironment environment (Nat.succ value)) := by
  unfold ScopedFormula.successorInstance
  apply Iff.trans
    (formula.raw.holds_substitute
      ScopedFormula.replaceNewestKeepingScopeSubstitution
      (pushEnvironment environment value))
  apply formula.raw.holds_congr
  intro index
  cases index <;> rfl

theorem standardArithmeticAxiom_sound
    {bound : Nat}
    {formula : ScopedFormula bound}
    (axiomWitness : StandardArithmeticAxiom formula)
    (environment : Environment) :
    formula.raw.Holds environment := by
  cases axiomWitness with
  | successorNotZero term =>
      intro impossible
      exact Nat.noConfusion impossible
  | successorInjective left right =>
      exact fun equality => Nat.succ.inj equality
  | addZero term => exact Nat.add_zero _
  | addSuccessor left right => exact Nat.add_succ _ _
  | multiplyZero term => exact Nat.mul_zero _
  | multiplySuccessor left right => exact Nat.mul_succ _ _
  | induction body =>
      intro premises value
      have base : body.raw.Holds (pushEnvironment environment 0) :=
        (body.holds_instantiate (ScopedTerm.zero bound) environment).mp
          premises.1
      have step : (index : Nat) ->
          body.raw.Holds (pushEnvironment environment index) ->
          body.raw.Holds
            (pushEnvironment environment (Nat.succ index)) := by
        intro index atIndex
        exact (body.holds_successorInstance environment index).mp
          (premises.2 index atIndex)
      exact Nat.rec base (fun index earlier => step index earlier) value

theorem haDerivation_sound
    {bound : Nat}
    {sourceContext : FormulaContext bound}
    {sourceConclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic haTheory
      sourceContext sourceConclusion)
    (environment : Environment)
    (contextHolds : sourceContext.StandardHolds environment) :
    sourceConclusion.raw.Holds environment := by
  induction proof generalizing environment with
  | theoryAxiom witness =>
      exact standardArithmeticAxiom_sound witness environment
  | hypothesis member =>
      exact member.standardHolds environment contextHolds
  | weaken extra premise inductionHypothesis =>
      exact inductionHypothesis environment contextHolds.2
  | implicationIntroduction premise inductionHypothesis =>
      exact fun leftHolds =>
        inductionHypothesis environment (And.intro leftHolds contextHolds)
  | implicationElimination implication argument
      implicationHypothesis argumentHypothesis =>
      exact (implicationHypothesis environment contextHolds)
        (argumentHypothesis environment contextHolds)
  | conjunctionIntroduction left right leftHypothesis rightHypothesis =>
      exact And.intro (leftHypothesis environment contextHolds)
        (rightHypothesis environment contextHolds)
  | conjunctionEliminationLeft premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).1
  | conjunctionEliminationRight premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).2
  | disjunctionIntroductionLeft premise inductionHypothesis =>
      exact Or.inl (inductionHypothesis environment contextHolds)
  | disjunctionIntroductionRight premise inductionHypothesis =>
      exact Or.inr (inductionHypothesis environment contextHolds)
  | disjunctionElimination disjunction leftBranch rightBranch
      disjunctionHypothesis leftHypothesis rightHypothesis =>
      rename_i context leftFormula rightFormula conclusion
      cases disjunctionHypothesis environment contextHolds with
      | inl leftHolds =>
          exact leftHypothesis environment (And.intro leftHolds contextHolds)
      | inr rightHolds =>
          exact rightHypothesis environment (And.intro rightHolds contextHolds)
  | falsumElimination premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).elim
  | universalIntroduction premise inductionHypothesis =>
      rename_i context body
      intro value
      exact inductionHypothesis (pushEnvironment environment value)
        (context.standardHolds_lift environment value contextHolds)
  | universalElimination term premise inductionHypothesis =>
      rename_i context body
      exact (body.holds_instantiate term environment).mpr
        (inductionHypothesis environment contextHolds
          (term.raw.evaluate environment))
  | existentialIntroduction term premise inductionHypothesis =>
      rename_i context body
      exact Exists.intro (term.raw.evaluate environment)
        ((body.holds_instantiate term environment).mp
          (inductionHypothesis environment contextHolds))
  | existentialElimination existential branch
      existentialHypothesis branchHypothesis =>
      rename_i context body conclusion
      cases existentialHypothesis environment contextHolds with
      | intro value bodyHolds =>
          have branchConclusion := branchHypothesis
            (pushEnvironment environment value)
            (And.intro bodyHolds
              (context.standardHolds_lift environment value contextHolds))
          exact (conclusion.holds_lift environment value).mp branchConclusion
  | equalityReflexivity term => rfl
  | equalitySymmetry premise inductionHypothesis =>
      exact (inductionHypothesis environment contextHolds).symm
  | equalityTransitivity first second firstHypothesis secondHypothesis =>
      exact (firstHypothesis environment contextHolds).trans
        (secondHypothesis environment contextHolds)
  | equalitySubstitution body equality premise
      equalityHypothesis premiseHypothesis =>
      rename_i context left right
      have termEquality := equalityHypothesis environment contextHolds
      have atLeft := (body.holds_instantiate left environment).mp
        (premiseHypothesis environment contextHolds)
      have atRight : body.raw.Holds
          (pushEnvironment environment (right.raw.evaluate environment)) := by
        rw [← termEquality]
        exact atLeft
      exact (body.holds_instantiate right environment).mpr atRight
  | liftVariables premise inductionHypothesis =>
      rename_i context conclusion
      let tailEnvironment : Environment := fun index =>
        environment (Nat.succ index)
      have rebuilt : (index : Nat) ->
          pushEnvironment tailEnvironment (environment 0) index =
            environment index := by
        intro index
        cases index <;> rfl
      have canonicalLiftedContext : context.lift.StandardHolds
          (pushEnvironment tailEnvironment (environment 0)) :=
        (context.lift.standardHolds_congr environment
          (pushEnvironment tailEnvironment (environment 0))
          (fun index _bounded => (rebuilt index).symm)).mp contextHolds
      have earlierContext : context.StandardHolds tailEnvironment :=
        (context.standardHolds_lift_iff tailEnvironment
          (environment 0)).mp canonicalLiftedContext
      have earlierConclusion := inductionHypothesis tailEnvironment earlierContext
      exact conclusion.lift.raw.holds_congr
        (pushEnvironment tailEnvironment (environment 0)) environment rebuilt
        |>.mp ((conclusion.holds_lift tailEnvironment (environment 0)).mpr
          earlierConclusion)
  | freeInstantiation replacement premise inductionHypothesis =>
      rename_i context conclusion
      have earlierContext : context.StandardHolds
          (pushEnvironment environment
            (replacement.raw.evaluate environment)) :=
        (context.standardHolds_instantiate replacement environment).mp
          contextHolds
      exact (conclusion.holds_instantiate replacement environment).mpr
        (inductionHypothesis
          (pushEnvironment environment (replacement.raw.evaluate environment))
          earlierContext)
  | doubleNegationElimination permission premise inductionHypothesis =>
      cases permission

theorem ha_not_provable_false
    (provable : HAProvable falseSentence) : False :=
  Nonempty.elim provable (fun proof =>
    haDerivation_sound proof emptyEnvironment trivial)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.standardArithmeticAxiom_sound
#print axioms RelationalPerimeter.HeytingArithmetic.haDerivation_sound
#print axioms RelationalPerimeter.HeytingArithmetic.ha_not_provable_false
/- AXIOM_AUDIT_END -/
