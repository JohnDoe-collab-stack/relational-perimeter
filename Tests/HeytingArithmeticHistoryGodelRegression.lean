import RelationalPerimeter.Instances.HeytingArithmetic.HistoryGodel

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace HeytingArithmeticHistoryGodelRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic

abbrev TestHistoryProof
    (history : TheoryHistory)
    (sentence : Sentence) : Type :=
  CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence

abbrev TestHistoryExecution
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history) :=
  ExecutedGodelProduction
    (soundHistoryEffectiveGodelSystem sound).toGodelSyntax
    (soundHistoryEffectiveGodelSystem sound).unprovabilityFormula
    (soundHistoryEffectiveGodelSystem sound).toGodelInterpretation

def rootSound : SoundTheoryHistory .root :=
  rootSoundTheoryHistory

def rootSystem : EffectivelyPresentedSoundGodelSystem :=
  soundHistoryEffectiveGodelSystem rootSound

def rootExecution : TestHistoryExecution rootSound :=
  soundHistoryGodelExecution rootSound

theorem root_checker_reuses_HA_checker
    (proofCode sentenceCode : Nat) :
    rootSystem.proofCheck proofCode sentenceCode =
      haProofCheck proofCode sentenceCode :=
  rfl

theorem root_equivalence_checker_reuses_HA_checker
    (certificateCode leftCode rightCode : Nat) :
    rootSystem.equivalenceCheck certificateCode leftCode rightCode =
      haEquivalenceCheck certificateCode leftCode rightCode :=
  rfl

theorem root_truth_reuses_HA_truth (sentence : Sentence) :
    rootSystem.Truth sentence = haTruth sentence :=
  rfl

theorem root_unprovability_formula_reuses_HA_formula :
    rootSystem.unprovabilityFormula = haUnprovabilityPredicate :=
  rfl

theorem root_diagonal_expression_reuses_HA_godel_sentence :
    (haDiagonalize (historyUnprovabilityPredicate .root)).applyNumeral
        (haDiagonalize (historyUnprovabilityPredicate .root)).raw.code =
      (haDiagonalize haUnprovabilityPredicate).applyNumeral
        (haDiagonalize haUnprovabilityPredicate).raw.code :=
  rootHistoryGodelRawSentence_eq_haGodelRawSentence

def oneStepSound :
    SoundTheoryHistory
      (.extend .root rootExecution.witness.production.sentence) :=
  .extend rootSound rootExecution.witness.trueWitness

def oneStepExecution : TestHistoryExecution oneStepSound :=
  soundHistoryGodelExecution oneStepSound

def old_sentence_has_checked_proof_in_extension :
    TestHistoryProof (.extend .root rootExecution.witness.production.sentence)
      rootExecution.witness.production.sentence :=
  newestHistoryCheckedProof .root rootExecution.witness.production.sentence

def old_checked_proofs_are_preserved
    {sentence : Sentence}
    (proof : TestHistoryProof .root sentence) :
    TestHistoryProof
      (.extend .root rootExecution.witness.production.sentence) sentence :=
  historyCheckedProofPreserved proof

end HeytingArithmeticHistoryGodelRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms HeytingArithmeticHistoryGodelRegression.rootSound
#print axioms HeytingArithmeticHistoryGodelRegression.rootSystem
#print axioms HeytingArithmeticHistoryGodelRegression.rootExecution
#print axioms HeytingArithmeticHistoryGodelRegression.root_checker_reuses_HA_checker
#print axioms HeytingArithmeticHistoryGodelRegression.root_equivalence_checker_reuses_HA_checker
#print axioms HeytingArithmeticHistoryGodelRegression.root_truth_reuses_HA_truth
#print axioms HeytingArithmeticHistoryGodelRegression.root_unprovability_formula_reuses_HA_formula
#print axioms HeytingArithmeticHistoryGodelRegression.root_diagonal_expression_reuses_HA_godel_sentence
#print axioms HeytingArithmeticHistoryGodelRegression.oneStepSound
#print axioms HeytingArithmeticHistoryGodelRegression.oneStepExecution
#print axioms HeytingArithmeticHistoryGodelRegression.old_sentence_has_checked_proof_in_extension
#print axioms HeytingArithmeticHistoryGodelRegression.old_checked_proofs_are_preserved
/- AXIOM_AUDIT_END -/
