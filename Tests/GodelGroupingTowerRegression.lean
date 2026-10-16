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

def initialJournal : OperationJournal Nat :=
  .root

def precisionRequest : Nat :=
  4

/-- The public request is really executed as the six fine operations. -/
def requestExecution :
    ExecutedSchedule
      (godelPerimetralPresentation heytingArithmeticGodelExecution)
      initialJournal
      (schedule precisionRequest) :=
  executeRequest
    (godelPerimetralPresentation heytingArithmeticGodelExecution)
    initialJournal
    precisionRequest

theorem requestAddsSixOperations :
    (OperationJournal.appendOperations initialJournal
      (schedule precisionRequest)).depth = 6 :=
  OperationJournal.appendSchedule_depth initialJournal precisionRequest

def requestDepthWitness :
    DepthExtension initialJournal.depth
      (OperationJournal.appendOperations initialJournal
        (schedule precisionRequest)).depth :=
  OperationJournal.requestDepthExtension initialJournal precisionRequest

/-- A depth-one journal shares the already established Gödel continuation. -/
def depthOneJournal : OperationJournal Nat :=
  .snoc .root (fineOperation 0 .effectiveContinuation)

/-- The original production occurrence is transported through the actual request. -/
def productionOccurrenceThroughRequest :
    History.Occurrence
      (OperationJournal.history
        (godelPerimetralPresentation heytingArithmeticGodelExecution)
        (OperationJournal.appendOperations depthOneJournal
          (schedule precisionRequest))).history :=
  extendOccurrenceThroughRequest
    (godelPerimetralPresentation heytingArithmeticGodelExecution)
    depthOneJournal precisionRequest
    (godelAffirmativeConstitution
      heytingArithmeticGodelExecution).productionOccurrence

/-- Six later operations give a concrete extension from Gödel depth one. -/
def oneToSeven : DepthExtension 1 7 :=
  .step (.step (.step (.step (.step (.step (.refl 1))))))

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

theorem requestHistoryRetainsInitialObstruction :
    (OperationJournal.history
      (godelPerimetralPresentation heytingArithmeticGodelExecution)
      (OperationJournal.appendOperations initialJournal
        (schedule precisionRequest))).terminalClosureObstruction =
      (godelPerimetralPresentation
        heytingArithmeticGodelExecution).positiveClosureObstruction :=
  journal_terminalClosureObstruction_is_initial _ _

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
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.initialJournal
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.precisionRequest
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.requestExecution
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.requestAddsSixOperations
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.requestDepthWitness
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.depthOneJournal
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.productionOccurrenceThroughRequest
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.oneToSeven
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.persistedTriple
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.productionAndCertificationRemainDistinct
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.productionAndContinuationRemainDistinct
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.certificationAndContinuationRemainDistinct
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.requestHistoryRetainsInitialObstruction
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.firstPrefixOfGlobalClosure
#print axioms RelationalPerimeter.Tests.GodelGroupingTowerRegression.globalClosureRejected
/- AXIOM_AUDIT_END -/
