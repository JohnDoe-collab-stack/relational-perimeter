import RelationalPerimeter.Instances.HeytingArithmetic.Godel
import RelationalPerimeter.Constitution.Godel.OperationalClosure

/-! Specializations reuse the one arithmetic production and add no arithmetic
hypothesis. The realization remains universally quantified. -/
set_option genInjectivity false
namespace RelationalPerimeter.HeytingArithmetic
open StrongPerimetralTurning ConstitutiveSearch.ContinuationSignatures

abbrev heytingArithmeticClosureContract := godelClosureContract heytingArithmeticGodelExecution
def heytingArithmeticOpenRuntime (pole : ClosurePole) := godelOpenRuntime heytingArithmeticGodelExecution pole
def heytingArithmeticIdentityRuntime := godelIdentityRealization heytingArithmeticGodelExecution
def heytingArithmeticClosureContext := godelReceivedClosureContext heytingArithmeticGodelExecution

theorem heytingArithmeticExactRuntimeSeparates {Memory : Type}
    (realization : ExactRealization heytingArithmeticClosureContract Memory) :
    ConstitutiveSearch.Grouping.Continuation.run realization.reduced.next
        (realization.project (semanticSource heytingArithmeticGodelExecution))
        [godelCloseRequest heytingArithmeticGodelExecution] ≠
      ConstitutiveSearch.Grouping.Continuation.run realization.reduced.next
        (realization.project (syntacticSource heytingArithmeticGodelExecution))
        [godelCloseRequest heytingArithmeticGodelExecution] :=
  godelExactRuntimeRejectsCommonTerminalMemory heytingArithmeticGodelExecution realization

def heytingArithmeticOperationalClosureToEmpty {Memory : Type}
    {realization : ExactRealization heytingArithmeticClosureContract Memory}
    (closure : OperationalSameRegimeClosureAt heytingArithmeticGodelExecution realization) : Empty :=
  rejectGodelOperationalClosureToEmpty closure

theorem heytingArithmeticOperationalClosureRejected {Memory : Type}
    {realization : ExactRealization heytingArithmeticClosureContract Memory}
    (closure : OperationalSameRegimeClosureAt heytingArithmeticGodelExecution realization) : False :=
  rejectGodelOperationalClosure closure

end RelationalPerimeter.HeytingArithmetic
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContract
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOpenRuntime
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticIdentityRuntime
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContext
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticExactRuntimeSeparates
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureToEmpty
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureRejected
/- AXIOM_AUDIT_END -/
