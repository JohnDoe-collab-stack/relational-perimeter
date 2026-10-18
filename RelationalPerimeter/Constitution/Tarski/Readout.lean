import RelationalPerimeter.Constitution.Tarski.SyntaxExecution

/-! Readout families are attached only after the executed syntactic production
has been constructed. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.checkUnivs false
namespace StrongPerimetralTurning

universe uC uB uS uK uX uT

structure TarskiReadout (coding : TarskiDiagonalSyntax.{uC,uS,uK}) where
  Truth : coding.Sentence → Type uT

structure TarskiLocalAdequacy
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) where
  valueToCandidate :
    readout.Truth execution.production.sentence →
      readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput)
  candidateToValue :
    readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) →
      readout.Truth execution.production.sentence

end StrongPerimetralTurning
/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.TarskiReadout
#print axioms StrongPerimetralTurning.TarskiLocalAdequacy
/- AXIOM_AUDIT_END -/
