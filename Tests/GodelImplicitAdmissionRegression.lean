import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace GodelImplicitAdmissionRegression

open StrongPerimetralTurning

universe uA uB uC uP uV

def implicit_admission_produces_truth_to_proof
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) :
    interpretation.Truth execution.witness.production.sentence ->
      coding.Proof execution.witness.production.sentence :=
  godelImplicitAdmissionToProducedCompleteness admission

def implicit_admission_reaches_empty_before_false
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : Empty :=
  rejectGodelImplicitAdmissionToEmpty admission

theorem implicit_admission_then_reaches_false
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (admission : GodelPositiveSameRegimeAdmission execution) : False :=
  rejectGodelImplicitSameRegimeAdmission admission

end GodelImplicitAdmissionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms GodelImplicitAdmissionRegression.implicit_admission_produces_truth_to_proof
#print axioms GodelImplicitAdmissionRegression.implicit_admission_reaches_empty_before_false
#print axioms GodelImplicitAdmissionRegression.implicit_admission_then_reaches_false
/- AXIOM_AUDIT_END -/
