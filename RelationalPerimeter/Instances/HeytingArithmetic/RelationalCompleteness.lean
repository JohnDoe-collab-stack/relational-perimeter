import RelationalPerimeter.Constitution.Godel.RelationalCompleteness
import RelationalPerimeter.Instances.HeytingArithmetic.Godel

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Heyting-arithmetic instance of the Gödel/real raccord

The generic raccord is instantiated with the concrete effective Gödel
execution for Heyting arithmetic already proved in this repository.  For every
executed Cauchy family on that exact presentation it constructs a relational
real limit and executed convergence, while the HA diagonal witness rejects the
total-loop branch and any global same-regime closure by restriction to the
first prefix.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelRelationalCompleteness
open RelationalPerimeter.Constitution.Reals

abbrev heytingArithmeticGodelPresentation : CircularPresentation :=
  godelPerimetralPresentation heytingArithmeticGodelExecution

/-- Effective sequential completeness on the concrete HA Gödel perimeter. -/
def heytingArithmeticSequentialCompleteness
    (family : ExecutedCauchyFamily heytingArithmeticGodelPresentation) :
    SequentialCompletenessResult family :=
  effectiveSequentialCompleteness family

/--
The HA specialization retains the canonical typed master: source requests own
their executions and every limit request owns the complete executable
source–grouping–limit producer, not only the logical limit.
-/
def heytingArithmeticFullyExecutedSequentialCompleteness
    (family : ExecutedCauchyFamily heytingArithmeticGodelPresentation) :
    FullyExecutedSequentialCompleteness family :=
  fullyExecutedSequentialCompleteness family

/-- The complete two-branch raccord for the concrete HA execution. -/
def heytingArithmeticGodelRelationalRaccord
    (family : ExecutedCauchyFamily heytingArithmeticGodelPresentation) :
    Result heytingArithmeticGodelExecution family :=
  raccord heytingArithmeticGodelExecution family

/-- The HA-produced total loop is rejected by its own diagonal witness. -/
def heytingArithmeticTotalLoopToEmpty
    (loop : ExecutedGodelTotalLoop
      heytingArithmeticGodelExecution.witness) : Empty :=
  totalLoopToEmpty loop

/-- Same-regime closure at the HA first prefix remains impossible. -/
def heytingArithmeticFirstPrefixClosureToEmpty
    (admission :
      GodelPositiveSameRegimeAdmission heytingArithmeticGodelExecution) :
    Empty :=
  heytingArithmeticGodelPerimetralCorrespondence.explicitAdmissionToEmpty
    admission

/-- A global HA closure is rejected only after deriving its first restriction. -/
def heytingArithmeticGlobalClosureToEmpty
    (closure :
      GlobalSameRegimeClosure heytingArithmeticGodelExecution) : Empty :=
  globalSameRegimeClosureToEmpty closure

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelPresentation
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSequentialCompleteness
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticFullyExecutedSequentialCompleteness
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelRelationalRaccord
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTotalLoopToEmpty
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticFirstPrefixClosureToEmpty
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticGlobalClosureToEmpty
/- AXIOM_AUDIT_END -/
