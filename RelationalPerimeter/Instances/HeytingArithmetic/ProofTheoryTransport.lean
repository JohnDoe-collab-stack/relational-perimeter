import RelationalPerimeter.Instances.HeytingArithmetic.TheoryHistoryCoding

/-!
# Constructive transport of derivations between arithmetic theories

Every logical constructor is preserved verbatim.  Only positive theory-postulate
witnesses are translated; no semantic soundness principle is involved.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def Derivation.mapAxioms
    {mode : LogicMode}
    {source target : ArithmeticTheory}
    (translate : forall {bound : Nat} {formula : ScopedFormula bound},
      source.Axiom bound formula -> target.Axiom bound formula) :
    {bound : Nat} ->
    {context : FormulaContext bound} ->
    {conclusion : ScopedFormula bound} ->
    Derivation mode source context conclusion ->
      Derivation mode target context conclusion
  | _, _, _, Derivation.theoryAxiom witness =>
      Derivation.theoryAxiom (translate witness)
  | _, _, _, Derivation.hypothesis member =>
      Derivation.hypothesis member
  | _, _, _, Derivation.weaken extra proof =>
      Derivation.weaken extra (proof.mapAxioms translate)
  | _, _, _, Derivation.implicationIntroduction proof =>
      Derivation.implicationIntroduction (proof.mapAxioms translate)
  | _, _, _, Derivation.implicationElimination implication argument =>
      Derivation.implicationElimination
        (implication.mapAxioms translate) (argument.mapAxioms translate)
  | _, _, _, Derivation.conjunctionIntroduction left right =>
      Derivation.conjunctionIntroduction
        (left.mapAxioms translate) (right.mapAxioms translate)
  | _, _, _, Derivation.conjunctionEliminationLeft proof =>
      Derivation.conjunctionEliminationLeft (proof.mapAxioms translate)
  | _, _, _, Derivation.conjunctionEliminationRight proof =>
      Derivation.conjunctionEliminationRight (proof.mapAxioms translate)
  | _, _, _, Derivation.disjunctionIntroductionLeft proof =>
      Derivation.disjunctionIntroductionLeft (proof.mapAxioms translate)
  | _, _, _, Derivation.disjunctionIntroductionRight proof =>
      Derivation.disjunctionIntroductionRight (proof.mapAxioms translate)
  | _, _, _, Derivation.disjunctionElimination disjunction left right =>
      Derivation.disjunctionElimination
        (disjunction.mapAxioms translate)
        (left.mapAxioms translate)
        (right.mapAxioms translate)
  | _, _, _, Derivation.falsumElimination proof =>
      Derivation.falsumElimination (proof.mapAxioms translate)
  | _, _, _, Derivation.universalIntroduction proof =>
      Derivation.universalIntroduction (proof.mapAxioms translate)
  | _, _, _, Derivation.universalElimination term proof =>
      Derivation.universalElimination term (proof.mapAxioms translate)
  | _, _, _, Derivation.existentialIntroduction term proof =>
      Derivation.existentialIntroduction term (proof.mapAxioms translate)
  | _, _, _, Derivation.existentialElimination existential branch =>
      Derivation.existentialElimination
        (existential.mapAxioms translate) (branch.mapAxioms translate)
  | _, _, _, Derivation.equalityReflexivity term =>
      Derivation.equalityReflexivity term
  | _, _, _, Derivation.equalitySymmetry proof =>
      Derivation.equalitySymmetry (proof.mapAxioms translate)
  | _, _, _, Derivation.equalityTransitivity first second =>
      Derivation.equalityTransitivity
        (first.mapAxioms translate) (second.mapAxioms translate)
  | _, _, _, Derivation.equalitySubstitution body equality premise =>
      Derivation.equalitySubstitution body
        (equality.mapAxioms translate) (premise.mapAxioms translate)
  | _, _, _, Derivation.liftVariables proof =>
      Derivation.liftVariables (proof.mapAxioms translate)
  | _, _, _, Derivation.freeInstantiation replacement proof =>
      Derivation.freeInstantiation replacement (proof.mapAxioms translate)
  | _, _, _, Derivation.doubleNegationElimination permission proof =>
      Derivation.doubleNegationElimination permission
        (proof.mapAxioms translate)

def rootDerivationToHA
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic TheoryHistory.root.theory
      context conclusion) :
    Derivation LogicMode.intuitionistic haTheory context conclusion :=
  proof.mapAxioms rootAxiomToStandard

def haDerivationToRoot
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic haTheory context conclusion) :
    Derivation LogicMode.intuitionistic TheoryHistory.root.theory
      context conclusion :=
  proof.mapAxioms standardAxiomToRoot

def haDerivationToHistory
    (history : TheoryHistory)
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic haTheory context conclusion) :
    Derivation LogicMode.intuitionistic history.theory context conclusion :=
  proof.mapAxioms (fun witness => HistoryAxiom.arithmetic witness)

theorem rootHistoryProvable_iff_haProvable
    (sentence : Sentence) :
    HistoryProvable TheoryHistory.root sentence ↔ HAProvable sentence := by
  constructor
  · intro rootProof
    exact Nonempty.elim rootProof
      (fun proof => Nonempty.intro (rootDerivationToHA proof))
  · intro haProof
    exact Nonempty.elim haProof
      (fun proof => Nonempty.intro (haDerivationToRoot proof))

def historyDerivationPreserve
    {history : TheoryHistory}
    {newest : Sentence}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic history.theory
      context conclusion) :
    Derivation LogicMode.intuitionistic
      (TheoryHistory.extend history newest).theory context conclusion :=
  proof.mapAxioms HistoryAxiom.preserve

theorem historyProvable_preserved
    {history : TheoryHistory}
    {newest sentence : Sentence}
    (provable : HistoryProvable history sentence) :
    HistoryProvable (TheoryHistory.extend history newest) sentence :=
  Nonempty.elim provable
    (fun proof => Nonempty.intro (historyDerivationPreserve proof))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.Derivation.mapAxioms
#print axioms RelationalPerimeter.HeytingArithmetic.rootHistoryProvable_iff_haProvable
#print axioms RelationalPerimeter.HeytingArithmetic.haDerivationToHistory
#print axioms RelationalPerimeter.HeytingArithmetic.historyProvable_preserved
/- AXIOM_AUDIT_END -/
