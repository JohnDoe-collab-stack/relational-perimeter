import RelationalPerimeter.Instances.HeytingArithmetic.HASoundness
import RelationalPerimeter.Instances.HeytingArithmetic.TheoryHistoryCoding

/-!
# Positive soundness certificates for finite theory histories

An extension is sound only when it carries the standard-truth witness of the
exact sentence stored by that extension.  Soundness of a historical derivation
is then reconstructed from the indexed history, its positive certificate, and
the derivation itself.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Positive standard-model soundness of an intrinsically indexed finite
    theory history. -/
inductive SoundTheoryHistory : (history : TheoryHistory) → Type
  | root : SoundTheoryHistory .root
  | extend {history : TheoryHistory} {sentence : Sentence} :
      SoundTheoryHistory history →
      PLift sentence.models →
      SoundTheoryHistory (.extend history sentence)

namespace SoundTheoryHistory

/-- Recover the truth witness attached to the exact historical occurrence. -/
def containsTruth
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {sentence : Sentence}
    (contains : history.Contains sentence) :
    PLift sentence.models :=
  match sound with
  | .root => nomatch contains
  | .extend previous newestTruth =>
      match contains with
      | .newest => newestTruth
      | .earlier earlier => previous.containsTruth earlier

end SoundTheoryHistory

/-- A closed sentence lifted into an ambient scope keeps its standard truth. -/
theorem Sentence.atBound_holds_iff_models
    (sentence : Sentence)
    (bound : Nat)
    (environment : Environment) :
    (sentence.atBound bound).raw.Holds environment ↔ sentence.models := by
  induction bound generalizing environment with
  | zero =>
      change sentence.raw.Holds environment ↔
        sentence.raw.Holds emptyEnvironment
      exact sentence.holds_environment_independent environment emptyEnvironment
  | succ bound inductionHypothesis =>
      let tailEnvironment : Environment := fun index =>
        environment (Nat.succ index)
      have rebuilt : (index : Nat) →
          pushEnvironment tailEnvironment (environment 0) index =
            environment index := by
        intro index
        cases index <;> rfl
      have sameEnvironment :
          (sentence.atBound bound).lift.raw.Holds environment ↔
            (sentence.atBound bound).lift.raw.Holds
              (pushEnvironment tailEnvironment (environment 0)) :=
        (sentence.atBound bound).lift.raw.holds_congr
          environment
          (pushEnvironment tailEnvironment (environment 0))
          (fun index => (rebuilt index).symm)
      exact sameEnvironment.trans
        (((sentence.atBound bound).holds_lift tailEnvironment
          (environment 0)).trans
        (inductionHypothesis tailEnvironment))

/-- Every theory-assumption occurrence in a sound history is true in every
    environment. -/
theorem SoundTheoryHistory.axiomSound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {bound : Nat}
    {formula : ScopedFormula bound}
    (witness : HistoryAxiom history formula)
    (environment : Environment) :
    formula.raw.Holds environment := by
  cases witness with
  | arithmetic arithmeticWitness =>
      exact standardArithmeticAxiom_sound arithmeticWitness environment
  | @added sentence contains =>
      exact (sentence.atBound_holds_iff_models bound environment).mpr
        (sound.containsTruth contains).down

/-- Constructive standard-model soundness for derivations over a positively
    certified finite theory history. -/
theorem historyDerivation_sound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {bound : Nat}
    {sourceContext : FormulaContext bound}
    {sourceConclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic history.theory
      sourceContext sourceConclusion)
    (environment : Environment)
    (contextHolds : sourceContext.StandardHolds environment) :
    sourceConclusion.raw.Holds environment := by
  induction proof generalizing environment with
  | theoryAxiom witness =>
      exact sound.axiomSound witness environment
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
      have rebuilt : (index : Nat) →
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

/-- Closed derivability in a sound history entails standard truth. -/
theorem historyProvable_sound
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history)
    {sentence : Sentence}
    (provable : HistoryProvable history sentence) :
    sentence.models :=
  Nonempty.elim provable (fun proof =>
    historyDerivation_sound sound proof emptyEnvironment trivial)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory.root
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory.extend
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory.containsTruth
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence.atBound_holds_iff_models
#print axioms RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory.axiomSound
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivation_sound
#print axioms RelationalPerimeter.HeytingArithmetic.historyProvable_sound
/- AXIOM_AUDIT_END -/
