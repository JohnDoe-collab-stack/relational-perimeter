import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace GodelPerimetralCorrespondenceRegression

open StrongPerimetralTurning

universe uA uB uC uP uV

theorem produced_sentence_is_the_executed_diagonal
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    execution.witness.production.sentence =
      godelSentence coding unprovabilityFormula :=
  execution.witness.production.sentence_is_godelSentence

def exact_executed_occurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ExecutedGodelPerimetralOccurrenceCorrespondence execution :=
  executedGodelPerimetralOccurrenceCorrespondence execution

theorem produced_and_certified_occurrences_are_distinct
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    (godelAffirmativeConstitution execution).productionOccurrence ≠
      (godelAffirmativeConstitution execution).certificationOccurrence :=
  (godelAffirmativeConstitution execution).productionCertificationDistinct

theorem continued_source_is_the_certified_witness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    implicitRead
        (perimeterEndpoint (godelPerimetralPresentation execution)) =
      ReturnedImplicit.source
        (ExecutedGodelPerimeterResource.continued execution.witness) :=
  godelContinuation_sourceResource_is_continued execution

theorem free_action_and_closing_junction_remain_separate
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    HEq (godelContinuationGeneratedStep execution).compatibility
        (ReturnedCompatible.leaveBoundary
          (godelPerimetralPresentation execution).perimeter.finalNode) ∧
      HEq (godelPerimetralPresentation execution).finalJunction
        (ExecutedGodelPerimeterCompatible.continuationToProduction
          (witness := execution.witness)) :=
  ⟨godelContinuation_compatibility_is_leaveBoundary execution,
    godelFinalJunction_is_continuationToProduction execution⟩

def affirmative_whole_exists_before_admission
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelAffirmativeConstitution execution :=
  godelAffirmativeConstitution execution

def admission_keeps_refinement_and_positive_witness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    Sigma fun refinement :
        CircularRefinement (godelPerimetralPresentation execution)
          (godelPerimetralContinuation execution) =>
      PositiveContinuation refinement.extension :=
  admission

def final_attempt_is_indexed_by_the_same_admission
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    BilateralClosureAttemptAt (godelFinalInterpretationOf admission) :=
  godelBilateralClosureAttemptOf admission

def both_positive_kernels_are_extracted
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    ExplicitContractionKernel (godelPerimetralPresentation execution) ×
      ImplicitContractionKernel (godelPerimetralPresentation execution) :=
  ⟨godelExplicitKernelOf admission, godelImplicitKernelOf admission⟩

def explicit_admission_produces_truth_to_proof
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    interpretation.Truth execution.witness.production.sentence ->
      coding.Proof execution.witness.production.sentence :=
  godelExplicitAdmissionToProducedCompleteness admission

def explicit_admission_reaches_empty_before_false
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : Empty :=
  rejectGodelExplicitAdmissionToEmpty admission

theorem explicit_admission_then_reaches_false
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : False :=
  rejectGodelExplicitSameRegimeAdmission admission

def kernel_identification_has_the_concrete_loop_meaning
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (kernel : ExplicitContractionKernel (godelCircularPresentation witness)) :
    (godelCircularPresentation witness).TotalLoop :=
  godelExplicitKernelToTotalLoop kernel

def generic_result_keeps_positive_and_negative_outputs
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ExecutedGodelPerimetralCorrespondence execution :=
  executedGodelPerimetralCorrespondence execution

end GodelPerimetralCorrespondenceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms GodelPerimetralCorrespondenceRegression.produced_sentence_is_the_executed_diagonal
#print axioms GodelPerimetralCorrespondenceRegression.exact_executed_occurrences
#print axioms GodelPerimetralCorrespondenceRegression.produced_and_certified_occurrences_are_distinct
#print axioms GodelPerimetralCorrespondenceRegression.continued_source_is_the_certified_witness
#print axioms GodelPerimetralCorrespondenceRegression.free_action_and_closing_junction_remain_separate
#print axioms GodelPerimetralCorrespondenceRegression.affirmative_whole_exists_before_admission
#print axioms GodelPerimetralCorrespondenceRegression.admission_keeps_refinement_and_positive_witness
#print axioms GodelPerimetralCorrespondenceRegression.final_attempt_is_indexed_by_the_same_admission
#print axioms GodelPerimetralCorrespondenceRegression.both_positive_kernels_are_extracted
#print axioms GodelPerimetralCorrespondenceRegression.explicit_admission_produces_truth_to_proof
#print axioms GodelPerimetralCorrespondenceRegression.explicit_admission_reaches_empty_before_false
#print axioms GodelPerimetralCorrespondenceRegression.explicit_admission_then_reaches_false
#print axioms GodelPerimetralCorrespondenceRegression.kernel_identification_has_the_concrete_loop_meaning
#print axioms GodelPerimetralCorrespondenceRegression.generic_result_keeps_positive_and_negative_outputs
/- AXIOM_AUDIT_END -/
