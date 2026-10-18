import StrongPerimetralTurning

/-! Executed syntactic production of a diagonal sentence.  This module has no
truth family and no semantic fixed-point law. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.checkUnivs false
namespace StrongPerimetralTurning

universe uC uB uS uK uX

structure TarskiDiagonalSyntax where
  Candidate : Type uC
  Sentence : Type uS
  Code : Type uK
  quote : Sentence → Code
  applyCandidate : Candidate → Code → Sentence
  diagonalize : Candidate → Sentence

structure TarskiExecutionRefinement
    (coding : TarskiDiagonalSyntax.{uC,uS,uK}) where
  Body : Type uB
  buildBody : coding.Candidate → Body
  substituteAtOwnCode : Body → coding.Sentence
  SubstitutionExecution : Body → coding.Code → Type uX
  runSubstitution : Body → coding.Code
  executeSubstitution :
    (body : Body) → SubstitutionExecution body (runSubstitution body)
  substitutionExact :
    (body : Body) → runSubstitution body = coding.quote (substituteAtOwnCode body)
  diagonalExact :
    (candidate : coding.Candidate) →
      coding.diagonalize candidate = substituteAtOwnCode (buildBody candidate)

structure ExecutedTarskiBody
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    (refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding)
    (candidate : coding.Candidate) where
  body : refinement.Body
  builtExact : body = refinement.buildBody candidate

def executeTarskiBody
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    (refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding)
    (candidate : coding.Candidate) : ExecutedTarskiBody refinement candidate :=
  ⟨refinement.buildBody candidate, rfl⟩

structure ExecutedTarskiSubstitution
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    (built : ExecutedTarskiBody refinement candidate) where
  computedOutput : coding.Code
  execution : refinement.SubstitutionExecution built.body computedOutput
  runExact : computedOutput = refinement.runSubstitution built.body

def executeTarskiSubstitution
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    (built : ExecutedTarskiBody refinement candidate) :
    ExecutedTarskiSubstitution built :=
  ⟨refinement.runSubstitution built.body, refinement.executeSubstitution built.body, rfl⟩

structure ExecutedTarskiSentence
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {built : ExecutedTarskiBody refinement candidate}
    (substitution : ExecutedTarskiSubstitution built) where
  sentence : coding.Sentence
  sentenceExact : sentence = refinement.substituteAtOwnCode built.body
  outputExact : substitution.computedOutput = coding.quote sentence

def executeTarskiSentence
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {built : ExecutedTarskiBody refinement candidate}
    (substitution : ExecutedTarskiSubstitution built) :
    ExecutedTarskiSentence substitution where
  sentence := refinement.substituteAtOwnCode built.body
  sentenceExact := rfl
  outputExact := substitution.runExact.trans (refinement.substitutionExact built.body)

structure ExecutedTarskiSyntaxProduction
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    (refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding)
    (candidate : coding.Candidate) where
  built : ExecutedTarskiBody refinement candidate
  substitution : ExecutedTarskiSubstitution built
  produced : ExecutedTarskiSentence substitution
  diagonalExact : produced.sentence = coding.diagonalize candidate

namespace ExecutedTarskiSyntaxProduction
variable {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
  {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
  {candidate : coding.Candidate}

def body (production : ExecutedTarskiSyntaxProduction refinement candidate) : refinement.Body :=
  production.built.body

def computedOutput (production : ExecutedTarskiSyntaxProduction refinement candidate) : coding.Code :=
  production.substitution.computedOutput

def sentence (production : ExecutedTarskiSyntaxProduction refinement candidate) : coding.Sentence :=
  production.produced.sentence

def execution (production : ExecutedTarskiSyntaxProduction refinement candidate) :
    refinement.SubstitutionExecution production.body production.computedOutput :=
  production.substitution.execution

theorem body_is_built (production : ExecutedTarskiSyntaxProduction refinement candidate) :
    production.body = refinement.buildBody candidate := production.built.builtExact

theorem output_is_sentence_quote
    (production : ExecutedTarskiSyntaxProduction refinement candidate) :
    production.computedOutput = coding.quote production.sentence := production.produced.outputExact

theorem sentence_is_diagonal
    (production : ExecutedTarskiSyntaxProduction refinement candidate) :
    production.sentence = coding.diagonalize candidate := production.diagonalExact

end ExecutedTarskiSyntaxProduction

def completeTarskiSyntaxProduction
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    (candidate : coding.Candidate)
    (built : ExecutedTarskiBody refinement candidate)
    (substitution : ExecutedTarskiSubstitution built)
    (produced : ExecutedTarskiSentence substitution) :
    ExecutedTarskiSyntaxProduction refinement candidate where
  built := built
  substitution := substitution
  produced := produced
  diagonalExact := by
    rw [produced.sentenceExact, built.builtExact]
    exact (refinement.diagonalExact candidate).symm

inductive ExecutedTarskiProductionState
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    (refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding)
    (candidate : coding.Candidate) where
  | candidateReceived
  | bodyBuilt (built : ExecutedTarskiBody refinement candidate)
  | substitutionExecuted {built : ExecutedTarskiBody refinement candidate}
      (substitution : ExecutedTarskiSubstitution built)
  | sentenceProduced {built : ExecutedTarskiBody refinement candidate}
      {substitution : ExecutedTarskiSubstitution built}
      (produced : ExecutedTarskiSentence substitution)
  | productionCompleted (production : ExecutedTarskiSyntaxProduction refinement candidate)

inductive ExecutedTarskiProductionStep
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate} :
    ExecutedTarskiProductionState refinement candidate →
      ExecutedTarskiProductionState refinement candidate → Type _ where
  | build : ExecutedTarskiProductionStep .candidateReceived
      (.bodyBuilt (executeTarskiBody refinement candidate))
  | substitute (built : ExecutedTarskiBody refinement candidate) :
      ExecutedTarskiProductionStep (.bodyBuilt built)
        (.substitutionExecuted (executeTarskiSubstitution built))
  | formSentence (built : ExecutedTarskiBody refinement candidate)
      (substitution : ExecutedTarskiSubstitution built) :
      ExecutedTarskiProductionStep (.substitutionExecuted substitution)
        (.sentenceProduced (executeTarskiSentence substitution))
  | complete (built : ExecutedTarskiBody refinement candidate)
      (substitution : ExecutedTarskiSubstitution built)
      (produced : ExecutedTarskiSentence substitution) :
      ExecutedTarskiProductionStep (.sentenceProduced produced)
        (.productionCompleted
          (completeTarskiSyntaxProduction candidate built substitution produced))

structure ExecutedTarskiProduction
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    (refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding)
    (candidate : coding.Candidate) where
  production : ExecutedTarskiSyntaxProduction refinement candidate
  history : History (@ExecutedTarskiProductionStep coding refinement candidate)
    .candidateReceived (.productionCompleted production)

def executeTarskiProduction
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    (refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding)
    (candidate : coding.Candidate) : ExecutedTarskiProduction refinement candidate := by
  let built := executeTarskiBody refinement candidate
  let substitution := executeTarskiSubstitution built
  let produced := executeTarskiSentence substitution
  let production := completeTarskiSyntaxProduction candidate built substitution produced
  exact
    { production := production
      history := .extend (.extend (.extend (.extend .root .build)
        (.substitute built)) (.formSentence built substitution))
        (.complete built substitution produced) }

structure ExecutedTarskiProductionOccurrences
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    (execution : ExecutedTarskiProduction refinement candidate) where
  buildOccurrence : History.Occurrence execution.history
  substitutionOccurrence : History.Occurrence execution.history
  sentenceOccurrence : History.Occurrence execution.history
  completionOccurrence : History.Occurrence execution.history
  buildNextSubstitution :
    History.OccurrenceNext buildOccurrence substitutionOccurrence
  substitutionNextSentence :
    History.OccurrenceNext substitutionOccurrence sentenceOccurrence
  sentenceNextCompletion :
    History.OccurrenceNext sentenceOccurrence completionOccurrence

def ExecutedTarskiProduction.occurrences
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    (execution : ExecutedTarskiProduction refinement candidate) :
    ExecutedTarskiProductionOccurrences execution := by
  cases execution with
  | mk production history =>
      cases history with
      | extend beforeComplete completeStep =>
          cases completeStep with
          | complete built substitution produced =>
              cases beforeComplete with
              | extend beforeSentence sentenceStep =>
                  cases sentenceStep with
                  | formSentence _ _ =>
                      cases beforeSentence with
                      | extend beforeSubstitution substitutionStep =>
                          cases substitutionStep with
                          | substitute _ =>
                              cases beforeSubstitution with
                              | extend beforeBuild buildStep =>
                                  cases buildStep with
                                  | build =>
                                      cases beforeBuild with
                                      | root =>
                                          exact
                                            { buildOccurrence := .earlier (.earlier (.earlier .last))
                                              substitutionOccurrence := .earlier (.earlier .last)
                                              sentenceOccurrence := .earlier .last
                                              completionOccurrence := .last
                                              buildNextSubstitution := .earlier_earlier
                                                (.earlier_earlier .previous_last)
                                              substitutionNextSentence := .earlier_earlier .previous_last
                                              sentenceNextCompletion := .previous_last }
                                      | extend _ impossible => cases impossible

end StrongPerimetralTurning
/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.TarskiDiagonalSyntax
#print axioms StrongPerimetralTurning.TarskiExecutionRefinement
#print axioms StrongPerimetralTurning.ExecutedTarskiBody
#print axioms StrongPerimetralTurning.executeTarskiBody
#print axioms StrongPerimetralTurning.ExecutedTarskiSubstitution
#print axioms StrongPerimetralTurning.executeTarskiSubstitution
#print axioms StrongPerimetralTurning.ExecutedTarskiSentence
#print axioms StrongPerimetralTurning.executeTarskiSentence
#print axioms StrongPerimetralTurning.ExecutedTarskiSyntaxProduction
#print axioms StrongPerimetralTurning.ExecutedTarskiSyntaxProduction.execution
#print axioms StrongPerimetralTurning.ExecutedTarskiSyntaxProduction.body_is_built
#print axioms StrongPerimetralTurning.ExecutedTarskiSyntaxProduction.output_is_sentence_quote
#print axioms StrongPerimetralTurning.ExecutedTarskiSyntaxProduction.sentence_is_diagonal
#print axioms StrongPerimetralTurning.completeTarskiSyntaxProduction
#print axioms StrongPerimetralTurning.ExecutedTarskiProductionState
#print axioms StrongPerimetralTurning.ExecutedTarskiProductionStep
#print axioms StrongPerimetralTurning.ExecutedTarskiProduction
#print axioms StrongPerimetralTurning.executeTarskiProduction
#print axioms StrongPerimetralTurning.ExecutedTarskiProductionOccurrences
#print axioms StrongPerimetralTurning.ExecutedTarskiProduction.occurrences
/- AXIOM_AUDIT_END -/
