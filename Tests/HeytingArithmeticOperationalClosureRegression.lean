import RelationalPerimeter.Instances.HeytingArithmetic.OperationalClosure
import Tests.GodelOperationalClosureRegression

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

def ha_positive_H1 :=
  GodelOperationalClosureRegression.history_exists_independently heytingArithmeticGodelExecution

theorem ha_production_origin_is_executed :
    ha_positive_H1.occurrenceOrigin ha_positive_H1.productionOccurrence =
      .executed (godelPositiveExecutionCore heytingArithmeticGodelExecution).occurrences.selfApplyOccurrence :=
  GodelOperationalClosureRegression.production_origin_is_executed heytingArithmeticGodelExecution

theorem ha_certification_origin_is_executed :
    ha_positive_H1.occurrenceOrigin ha_positive_H1.certificationOccurrence =
      .executed (godelPositiveExecutionCore heytingArithmeticGodelExecution).occurrences.certifyOccurrence :=
  GodelOperationalClosureRegression.certification_origin_is_executed heytingArithmeticGodelExecution

theorem ha_continuation_origin_is_generated :
    ha_positive_H1.occurrenceOrigin ha_positive_H1.continuationOccurrence = .generatedContinuation :=
  GodelOperationalClosureRegression.continuation_origin_is_generated heytingArithmeticGodelExecution

theorem ha_H1_occurrences_are_distinct :
    ha_positive_H1.productionOccurrence ≠ ha_positive_H1.certificationOccurrence ∧
      ha_positive_H1.certificationOccurrence ≠ ha_positive_H1.continuationOccurrence ∧
      ha_positive_H1.productionOccurrence ≠ ha_positive_H1.continuationOccurrence :=
  GodelOperationalClosureRegression.H1_occurrences_remain_distinct heytingArithmeticGodelExecution

theorem ha_sources_share_H1 :
    (semanticSource heytingArithmeticGodelExecution).h1 = ha_positive_H1 ∧
      (syntacticSource heytingArithmeticGodelExecution).h1 = ha_positive_H1 :=
  GodelOperationalClosureRegression.sources_keep_the_same_H1 heytingArithmeticGodelExecution

theorem ha_active_operational_memories_are_distinct :
    (godelOperationalRealizationWithoutRead heytingArithmeticGodelExecution).project
        (semanticSource heytingArithmeticGodelExecution) ≠
      (godelOperationalRealizationWithoutRead heytingArithmeticGodelExecution).project
        (syntacticSource heytingArithmeticGodelExecution) :=
  GodelOperationalClosureRegression.operational_initial_memories_are_distinct heytingArithmeticGodelExecution

theorem ha_close_changes_the_phase :
    (semanticSource heytingArithmeticGodelExecution).phase = .active ∧
      (godelRuntimeNext heytingArithmeticGodelExecution
        (semanticSource heytingArithmeticGodelExecution) .close).phase = .terminal :=
  GodelOperationalClosureRegression.close_changes_the_phase heytingArithmeticGodelExecution

theorem ha_rich_terminal_sources_remain_distinct :
    heytingArithmeticOperationalGroupingWithoutRead.leftTerminal ≠
      heytingArithmeticOperationalGroupingWithoutRead.rightTerminal :=
  GodelOperationalClosureRegression.rich_terminal_sources_remain_distinct heytingArithmeticGodelExecution

theorem ha_identity_terminals_remain_distinct :
    godelRuntimeRun heytingArithmeticGodelExecution
        (semanticSource heytingArithmeticGodelExecution) [godelCloseRequest heytingArithmeticGodelExecution] ≠
      godelRuntimeRun heytingArithmeticGodelExecution
        (syntacticSource heytingArithmeticGodelExecution) [godelCloseRequest heytingArithmeticGodelExecution] :=
  GodelOperationalClosureRegression.exact_identity_outputs_stay_distinct heytingArithmeticGodelExecution

theorem ha_operational_layer_allows_common_terminal_memory :
    Grouping.Continuation.run
        (godelOperationalRealizationWithoutRead heytingArithmeticGodelExecution).reduced.next
        ((godelOperationalRealizationWithoutRead heytingArithmeticGodelExecution).project
          (semanticSource heytingArithmeticGodelExecution))
        [godelCloseRequest heytingArithmeticGodelExecution] =
      Grouping.Continuation.run
        (godelOperationalRealizationWithoutRead heytingArithmeticGodelExecution).reduced.next
        ((godelOperationalRealizationWithoutRead heytingArithmeticGodelExecution).project
          (syntacticSource heytingArithmeticGodelExecution))
        [godelCloseRequest heytingArithmeticGodelExecution] :=
  heytingArithmeticOperationalGroupingWithoutRead.terminalCollision

theorem ha_operational_events_do_not_separate_the_poles :
    (heytingArithmeticOperationalGroupingWithoutRead).leftEvents =
      (heytingArithmeticOperationalGroupingWithoutRead).rightEvents :=
  godelOperationalGroupingWithoutRead_events_equal heytingArithmeticGodelExecution

def ha_adding_terminal_read_exact_is_rejected
    (reducedRead : GodelOperationalMemory heytingArithmeticGodelExecution → Type)
    (readExact : ∀ source,
      heytingArithmeticClosureContract.read source =
        reducedRead (godelOperationalProject heytingArithmeticGodelExecution source)) : Empty :=
  heytingArithmeticTerminalReadExactToEmpty reducedRead readExact

def ha_positive_execution :=
  GodelOperationalClosureRegression.positiveExecution heytingArithmeticGodelExecution

def ha_historical_bridge :=
  GodelOperationalClosureRegression.historical_bridge_consumes_the_same_core heytingArithmeticGodelExecution

theorem ha_bridge_is_exhaustive
    (occurrence : History.Occurrence ha_positive_H1.history) :
    ha_historical_bridge.transport.backward (ha_historical_bridge.transport.forward occurrence) = occurrence :=
  ha_historical_bridge.transport.forwardBackward occurrence

theorem ha_bridge_preserves_both_orders :
    History.OccurrenceNext (ha_historical_bridge.transport.forward ha_positive_H1.productionOccurrence)
        (ha_historical_bridge.transport.forward ha_positive_H1.certificationOccurrence) ∧
      History.OccurrenceNext (ha_historical_bridge.transport.forward ha_positive_H1.certificationOccurrence)
        (ha_historical_bridge.transport.forward ha_positive_H1.continuationOccurrence) :=
  GodelOperationalClosureRegression.bridge_preserves_both_immediate_orders heytingArithmeticGodelExecution

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

def ha_conversion_precedes_rejection {Memory : Type}
    {realization : ExactRealization heytingArithmeticClosureContract Memory}
    (closure : OperationalSameRegimeClosureAt heytingArithmeticGodelExecution realization) :
    ExecutedGodelProducedCompleteness heytingArithmeticGodelExecution.witness :=
  godelOperationalClosureToProducedCompleteness closure


-- Complete compatibility inventory against the base public declarations.
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContract
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticOpenRuntime
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticIdentityRuntime
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContext
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalGroupingWithoutRead
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticExactRuntimeSeparates
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureToEmpty
#check RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureRejected

end HeytingArithmeticOperationalClosureRegression

set_option maxHeartbeats 0
open Lean
run_cmd do
  let env ← getEnv
  let used := fun (roots : List Expr) => Id.run do
    let mut pending := roots
    let mut visited : ExprSet := {}
    let mut names : NameSet := {}
    while !pending.isEmpty do
      let expression := pending.head!
      pending := pending.tail!
      if visited.contains expression then continue
      visited := visited.insert expression
      match expression with
      | .const name _ => names := names.insert name
      | .app function argument => pending := function :: argument :: pending
      | .lam _ domain body _ | .forallE _ domain body _ => pending := domain :: body :: pending
      | .letE _ type value body _ => pending := type :: value :: body :: pending
      | .mdata _ body => pending := body :: pending
      | .proj recordName index body =>
          names := names.insert recordName
          if let some projection := (getStructureInfo? env recordName).bind (fun info => info.getProjFn? index) then
            names := names.insert projection
          pending := body :: pending
      | _ => pure ()
    return names
  let dependencyCache ← IO.mkRef ({} : NameMap NameSet)
  let dependencies : Name → Elab.Command.CommandElabM NameSet := fun name => do
    if let some cached := (← dependencyCache.get).find? name then
      return cached
    let some info := env.find? name | throwError "Missing HA dependency {name}"
    let mut names := used (info.type :: (info.value? (allowOpaque := true)).toList)
    let metadata := match info with
      | .inductInfo value => value.ctors
      | .recInfo value => value.all
      | _ => []
    for dependency in metadata do
      names := names.insert dependency
    dependencyCache.modify fun cache => cache.insert name names
    return names
  let closure := fun roots => do
    let mut pending : List Name := roots
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if visited.contains name then continue
      visited := visited.insert name
      pending := (← dependencies name).toList ++ pending
    pure visited
  let inherited ← closure [
    `StrongPerimetralTurning.ExecutedGodelProduction,
    `RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelExecution]
  logInfo m!"HA_RUNTIME_RECEIVED_PRODUCTION constants={inherited.size}; concrete arithmetic production types and opaque values"
  for name in inherited.toList do
    let direct ← dependencies name
    for elimination in [`Empty.elim, `False.elim] do
      if direct.contains elimination then
        logInfo m!"HA_RUNTIME_INHERITED_ELIMINATION {name} -> {elimination}"
  let forbidden := [
    `StrongPerimetralTurning.godelCircularPresentation,
    `StrongPerimetralTurning.godelPerimetralPresentation,
    `StrongPerimetralTurning.godelPerimetralContinuation,
    `StrongPerimetralTurning.ExecutedGodelTotalLoop,
    `StrongPerimetralTurning.ExplicitTotalization,
    `StrongPerimetralTurning.ImplicitTotalization,
    `StrongPerimetralTurning.ExplicitContractionKernel,
    `StrongPerimetralTurning.ImplicitContractionKernel,
    `StrongPerimetralTurning.CircularPresentation.rejectInitialContraction,
    `StrongPerimetralTurning.PositiveClosureObstruction.rejectsContraction,
    `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
    `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
    `StrongPerimetralTurning.ExecutedGodelWitness.rejectProducedCompleteness,
    `ConstitutiveSearch.ContinuationSignatures.FutureEquivalent,
    `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.event_exact,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.events_exact]
  for root in [
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContext,
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalGroupingWithoutRead,
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticOpenRuntime,
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticIdentityRuntime,
      `HeytingArithmeticOperationalClosureRegression.ha_conversion_precedes_rejection] do
    let visited ← closure [root]
    for name in visited.toList do
      if forbidden.any (fun bad => bad.isPrefixOf name) then
        throwError "Positive HA runtime {root} reaches forbidden {name} through types or values"
      if !inherited.contains name then
        let direct ← dependencies name
        for elimination in [`Empty.elim, `False.elim] do
          if direct.contains elimination then
            throwError "Positive HA runtime {root} introduces {elimination} in {name}"
    let inheritedCount := visited.toList.filter inherited.contains |>.length
    logInfo m!"HA_RUNTIME_DEPENDENCIES_OK {root} constants={visited.size} inheritedProduction={inheritedCount}"
  for root in [
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticTerminalReadExactToEmpty,
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticExactRuntimeSeparates,
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureToEmpty] do
    let visited ← closure [root]
    for required in [
        `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
        `StrongPerimetralTurning.ExecutedGodelWitness.unprovable] do
      unless visited.contains required do
        throwError "HA rejection {root} no longer consumes {required}"
    for bad in [
        `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.event_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.events_exact] do
      if visited.contains bad then
        throwError "HA rejection {root} reaches event separation {bad}"
    logInfo m!"HA_RUNTIME_REJECTION_DEPENDENCIES_OK {root} constants={visited.size}"

/- AXIOM_AUDIT_BEGIN -/
#print axioms HeytingArithmeticOperationalClosureRegression.ha_reuses_the_master_execution
#print axioms HeytingArithmeticOperationalClosureRegression.ha_open_runtime_continues
#print axioms HeytingArithmeticOperationalClosureRegression.ha_open_runtime_keeps_the_role
#print axioms HeytingArithmeticOperationalClosureRegression.ha_positive_H1
#print axioms HeytingArithmeticOperationalClosureRegression.ha_production_origin_is_executed
#print axioms HeytingArithmeticOperationalClosureRegression.ha_certification_origin_is_executed
#print axioms HeytingArithmeticOperationalClosureRegression.ha_continuation_origin_is_generated
#print axioms HeytingArithmeticOperationalClosureRegression.ha_H1_occurrences_are_distinct
#print axioms HeytingArithmeticOperationalClosureRegression.ha_sources_share_H1
#print axioms HeytingArithmeticOperationalClosureRegression.ha_active_operational_memories_are_distinct
#print axioms HeytingArithmeticOperationalClosureRegression.ha_close_changes_the_phase
#print axioms HeytingArithmeticOperationalClosureRegression.ha_rich_terminal_sources_remain_distinct
#print axioms HeytingArithmeticOperationalClosureRegression.ha_identity_terminals_remain_distinct
#print axioms HeytingArithmeticOperationalClosureRegression.ha_operational_layer_allows_common_terminal_memory
#print axioms HeytingArithmeticOperationalClosureRegression.ha_operational_events_do_not_separate_the_poles
#print axioms HeytingArithmeticOperationalClosureRegression.ha_adding_terminal_read_exact_is_rejected
#print axioms HeytingArithmeticOperationalClosureRegression.ha_positive_execution
#print axioms HeytingArithmeticOperationalClosureRegression.ha_historical_bridge
#print axioms HeytingArithmeticOperationalClosureRegression.ha_bridge_is_exhaustive
#print axioms HeytingArithmeticOperationalClosureRegression.ha_bridge_preserves_both_orders
#print axioms HeytingArithmeticOperationalClosureRegression.ha_every_exact_realization_separates
#print axioms HeytingArithmeticOperationalClosureRegression.ha_operational_closure_rejected
#print axioms HeytingArithmeticOperationalClosureRegression.ha_conversion_precedes_rejection
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContract
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOpenRuntime
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticIdentityRuntime
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticClosureContext
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalGroupingWithoutRead
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticExactRuntimeSeparates
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureToEmpty
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureRejected
/- AXIOM_AUDIT_END -/
