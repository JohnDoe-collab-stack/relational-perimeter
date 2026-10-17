import RelationalPerimeter.Constitution.Godel.RelationalCompleteness
import RelationalPerimeter.Instances.HeytingArithmetic.Godel

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Tests.GodelGroupingTowerRegression

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower
open StrongPerimetralTurning.GodelRelationalCompleteness
open ConstitutiveSearch.OccurrencePersistence
open RelationalPerimeter.HeytingArithmetic

/-- Six later phases give a concrete positive extension from Gödel depth one. -/
def oneToSeven : DepthExtension 1 7 :=
  extendDepthBy 1 6

def persistedTriple :
    PersistedGodelOccurrences heytingArithmeticGodelExecution 7 :=
  persistGodelOccurrences heytingArithmeticGodelExecution oneToSeven

theorem productionAndCertificationRemainDistinct :
    persistedTriple.production ≠ persistedTriple.certification :=
  persistedTriple.productionCertificationDistinct

theorem productionAndContinuationRemainDistinct :
    persistedTriple.production ≠ persistedTriple.continuation :=
  persistedTriple.productionContinuationDistinct

theorem certificationAndContinuationRemainDistinct :
    persistedTriple.certification ≠ persistedTriple.continuation :=
  persistedTriple.certificationContinuationDistinct

/-- Restriction, rather than a stored first-prefix field, yields the admission. -/
def firstPrefixOfGlobalClosure
    (closure : GlobalSameRegimeClosure heytingArithmeticGodelExecution) :
    GodelPositiveSameRegimeAdmission heytingArithmeticGodelExecution :=
  closure.restrictToGodelPrefix

/-- The global closure reaches the same Gödel contradiction by restriction. -/
def globalClosureRejected
    (closure : GlobalSameRegimeClosure heytingArithmeticGodelExecution) :
    Empty :=
  globalSameRegimeClosureToEmpty closure

end RelationalPerimeter.Tests.GodelGroupingTowerRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.oneToSeven
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.persistedTriple
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.productionAndCertificationRemainDistinct
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.productionAndContinuationRemainDistinct
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.certificationAndContinuationRemainDistinct
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.firstPrefixOfGlobalClosure
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.globalClosureRejected
/- AXIOM_AUDIT_END -/
