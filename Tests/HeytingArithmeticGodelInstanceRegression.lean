import RelationalPerimeter.Instances.HeytingArithmetic.Godel

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace HeytingArithmeticGodelInstanceRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic

def named_ha_system_is_effective :
    EffectivelyPresentedSoundGodelSystem :=
  heytingArithmeticEffectiveGodelSystem

theorem ha_checker_is_the_real_checker
    (proofCode sentenceCode : Nat) :
    heytingArithmeticEffectiveGodelSystem.proofCheck proofCode sentenceCode =
      haProofCheck proofCode sentenceCode :=
  rfl

theorem ha_produced_sentence_is_its_executed_diagonal :
    heytingArithmeticGodelExecution.witness.production.sentence =
      godelSentence
        heytingArithmeticEffectiveGodelSystem.toGodelSyntax
        heytingArithmeticEffectiveGodelSystem.unprovabilityFormula :=
  heytingArithmeticGodelExecution.witness.production.sentence_is_godelSentence

def ha_executed_correspondence :
    ExecutedGodelPerimetralCorrespondence
      heytingArithmeticGodelExecution :=
  heytingArithmeticGodelPerimetralCorrespondence

def ha_affirmative_whole :
    GodelAffirmativeConstitution heytingArithmeticGodelExecution :=
  heytingArithmeticAffirmativeConstitution

def ha_strict_continuation :
    StrictConstitutivePrefix
      (perimeterDeployment
        (godelPerimetralPresentation heytingArithmeticGodelExecution))
      (godelPerimetralContinuation heytingArithmeticGodelExecution) :=
  heytingArithmeticStrictContinuation

def ha_same_regime_admission_reaches_empty
    (admission :
      GodelPositiveSameRegimeAdmission heytingArithmeticGodelExecution) : Empty :=
  heytingArithmeticSameRegimeAdmissionToEmpty admission

theorem ha_same_regime_admission_is_rejected
    (admission :
      GodelPositiveSameRegimeAdmission heytingArithmeticGodelExecution) : False :=
  heytingArithmeticSameRegimeAdmissionRejected admission

end HeytingArithmeticGodelInstanceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms HeytingArithmeticGodelInstanceRegression.named_ha_system_is_effective
#print axioms HeytingArithmeticGodelInstanceRegression.ha_checker_is_the_real_checker
#print axioms HeytingArithmeticGodelInstanceRegression.ha_produced_sentence_is_its_executed_diagonal
#print axioms HeytingArithmeticGodelInstanceRegression.ha_executed_correspondence
#print axioms HeytingArithmeticGodelInstanceRegression.ha_affirmative_whole
#print axioms HeytingArithmeticGodelInstanceRegression.ha_strict_continuation
#print axioms HeytingArithmeticGodelInstanceRegression.ha_same_regime_admission_reaches_empty
#print axioms HeytingArithmeticGodelInstanceRegression.ha_same_regime_admission_is_rejected
/- AXIOM_AUDIT_END -/
