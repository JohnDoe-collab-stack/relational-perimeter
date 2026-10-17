import Tests.GodelOperationalClosureDependencies

set_option genInjectivity false
namespace GodelOperationalClosureRegression
open StrongPerimetralTurning ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures

/-- A nonempty executed collision exists when the fixed contract permits it. -/
def trivialContract : FutureContract ClosurePole Unit Unit Unit where
  next := fun source _ => source
  event := fun _ _ => ()
  read := fun _ => ()
  Allow := fun _ _ => Unit
  decision := fun _ _ => .inl ()

def trivialReduced : FutureContract Unit Unit Unit Unit where
  next := fun _ _ => ()
  event := fun _ _ => ()
  read := fun _ => ()
  Allow := fun _ _ => Unit
  decision := fun _ _ => .inl ()

def trivialRealization : ExactRealization trivialContract Unit where
  reduced := trivialReduced
  project := fun _ => ()
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := fun _ _ _ => rfl
  forward_backward := fun _ _ _ => rfl
  next_exact := fun _ _ => rfl
  event_exact := fun _ _ => rfl
  read_exact := fun _ => rfl

def trivialExecutedGrouping :
    ExecutedCommonMemoryGrouping trivialRealization .left .right where
  requests := [()]
  nonempty := by intro impossible; cases impossible
  leftTerminal := .left
  leftEvents := [()]
  leftRun := .cons (perform trivialContract .left () ()) (.nil ClosurePole.left)
  rightTerminal := .right
  rightEvents := [()]
  rightRun := .cons (perform trivialContract .right () ()) (.nil ClosurePole.right)
  terminalCollision := rfl

theorem trivial_grouping_read_exact :
    trivialContract.read trivialExecutedGrouping.leftTerminal =
      trivialContract.read trivialExecutedGrouping.rightTerminal :=
  trivialExecutedGrouping.terminalReadEqual

variable {coding : GodelDiagonalSyntax} {formula : coding.UnaryFormula}
  {interpretation : GodelProvabilityInterpretation coding formula}
  (execution : ExecutedGodelProduction coding formula interpretation)

def history_exists_independently := godelAffirmativeConstitution execution

theorem sources_keep_the_same_H1 :
    (semanticSource execution).history = godelPerimetralContinuation execution ∧
      (syntacticSource execution).history = godelPerimetralContinuation execution :=
  ⟨initialize_history execution .left, initialize_history execution .right⟩

theorem continue_constructs_the_next_history :
    (godelOpenRuntime execution .left).terminal.history =
      appendGenerated (semanticSource execution).history
        (generate (semanticSource execution).history.endpoint) :=
  (semanticSource execution).history_continue

theorem identity_preserves_roles :
    ((godelIdentityRealization execution).project (semanticSource execution)).pole = .left ∧
      ((godelIdentityRealization execution).project (syntacticSource execution)).pole = .right := ⟨rfl, rfl⟩

/-- Each layer consumes the prior value. Both runs are constructed from the
two separately authorized steps and remain open in the identity realization. -/
def positiveExecution :=
  let context := godelReceivedClosureContext execution
  let action := godelSearchCloseAction context
  let authorization := godelAuthorizeCloseAction action
  let decomposition := godelDecomposeCloseAction authorization
  (GodelExecutedCloseAction.execute : GodelExecutedCloseAction decomposition)

theorem positive_execution_uses_singleton :
    (positiveExecution execution).leftRun.toAdmitted =
      Grouping.Continuation.Admitted.cons
        (godelAuthorizeCloseAction (godelSearchCloseAction (godelReceivedClosureContext execution))).left
        (.nil _) := rfl

theorem exact_identity_outputs_stay_distinct :
    godelRuntimeRun execution (semanticSource execution) [godelCloseRequest execution] ≠
      godelRuntimeRun execution (syntacticSource execution) [godelCloseRequest execution] :=
  godelIdentity_close_outputs_distinct execution

variable {execution} {Memory : Type}
  {realization : ExactRealization (godelClosureContract execution) Memory}

theorem kernel_direct_read_client
    (grouping : ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution)) :
    interpretation.Truth execution.witness.production.sentence = coding.Proof execution.witness.production.sentence := by
  have projections := grouping.projectedTerminalsEqual
  have terminalReads := (realization.read_exact grouping.leftTerminal).trans
    ((congrArg realization.reduced.read projections).trans (realization.read_exact grouping.rightTerminal).symm)
  have leftStable := (congrArg (godelClosureContract execution).read grouping.leftRun.terminal_eq_run).trans
    (read_run execution _ grouping.requests)
  have rightStable := (congrArg (godelClosureContract execution).read grouping.rightRun.terminal_eq_run).trans
    (read_run execution _ grouping.requests)
  exact leftStable.symm.trans (terminalReads.trans rightStable)

theorem all_futures_is_a_parallel_consequence
    (grouping : ExecutedCommonMemoryGrouping realization (semanticSource execution) (syntacticSource execution)) :
    FutureEquivalent (godelClosureContract execution) grouping.leftTerminal grouping.rightTerminal :=
  grouping.terminalFutureEquivalent

theorem historical_wrapper_keeps_singleton (closure : OperationalSameRegimeClosureAt execution realization) :
    closure.executedGrouping.requests = [godelCloseRequest execution] := closure.requests_exact

end GodelOperationalClosureRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms GodelOperationalClosureRegression.trivialContract
#print axioms GodelOperationalClosureRegression.trivialReduced
#print axioms GodelOperationalClosureRegression.trivialRealization
#print axioms GodelOperationalClosureRegression.trivialExecutedGrouping
#print axioms GodelOperationalClosureRegression.trivial_grouping_read_exact
#print axioms GodelOperationalClosureRegression.history_exists_independently
#print axioms GodelOperationalClosureRegression.sources_keep_the_same_H1
#print axioms GodelOperationalClosureRegression.continue_constructs_the_next_history
#print axioms GodelOperationalClosureRegression.identity_preserves_roles
#print axioms GodelOperationalClosureRegression.positiveExecution
#print axioms GodelOperationalClosureRegression.positive_execution_uses_singleton
#print axioms GodelOperationalClosureRegression.exact_identity_outputs_stay_distinct
#print axioms GodelOperationalClosureRegression.kernel_direct_read_client
#print axioms GodelOperationalClosureRegression.all_futures_is_a_parallel_consequence
#print axioms GodelOperationalClosureRegression.historical_wrapper_keeps_singleton
/- AXIOM_AUDIT_END -/
