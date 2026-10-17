import RelationalPerimeter.Instances.HeytingArithmetic.OperationalClosure

set_option genInjectivity false
namespace HeytingArithmeticOperationalClosureRegression
open StrongPerimetralTurning RelationalPerimeter.HeytingArithmetic
open ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures

theorem ha_reuses_the_master_execution :
    heytingArithmeticClosureContract = godelClosureContract heytingArithmeticGodelExecution := rfl

theorem ha_open_runtime_continues :
    (heytingArithmeticOpenRuntime .left).terminal.depth = 2 := rfl

theorem ha_open_runtime_keeps_the_role :
    (heytingArithmeticOpenRuntime .left).terminal.pole = .left ∧
      (heytingArithmeticOpenRuntime .right).terminal.pole = .right := ⟨rfl, rfl⟩

theorem ha_every_exact_realization_separates {Memory : Type}
    (realization : ExactRealization heytingArithmeticClosureContract Memory) :
    Grouping.Continuation.run realization.reduced.next
        (realization.project (semanticSource heytingArithmeticGodelExecution))
        [godelCloseRequest heytingArithmeticGodelExecution] ≠
      Grouping.Continuation.run realization.reduced.next
        (realization.project (syntacticSource heytingArithmeticGodelExecution))
        [godelCloseRequest heytingArithmeticGodelExecution] :=
  heytingArithmeticExactRuntimeSeparates realization

theorem ha_operational_closure_rejected {Memory : Type}
    {realization : ExactRealization heytingArithmeticClosureContract Memory}
    (closure : OperationalSameRegimeClosureAt heytingArithmeticGodelExecution realization) : False :=
  heytingArithmeticOperationalClosureRejected closure

end HeytingArithmeticOperationalClosureRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms HeytingArithmeticOperationalClosureRegression.ha_reuses_the_master_execution
#print axioms HeytingArithmeticOperationalClosureRegression.ha_open_runtime_continues
#print axioms HeytingArithmeticOperationalClosureRegression.ha_open_runtime_keeps_the_role
#print axioms HeytingArithmeticOperationalClosureRegression.ha_every_exact_realization_separates
#print axioms HeytingArithmeticOperationalClosureRegression.ha_operational_closure_rejected
/- AXIOM_AUDIT_END -/
