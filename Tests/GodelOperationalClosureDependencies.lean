import RelationalPerimeter.Constitution.Godel.OperationalClosure
import Lean

/-! Build-time inspection of actual kernel terms, including their transitive
types and values. The positive path must remain independent of the historical
presentation and of the separate all-futures consequence. -/
set_option maxHeartbeats 0
open Lean
run_cmd do
  let env ← getEnv
  let forbidden := [
    `StrongPerimetralTurning.godelCircularPresentation,
    `StrongPerimetralTurning.godelPerimetralPresentation,
    `StrongPerimetralTurning.ExecutedGodelTotalLoop,
    `StrongPerimetralTurning.ExplicitTotalization,
    `StrongPerimetralTurning.ImplicitTotalization,
    `StrongPerimetralTurning.ExplicitContractionKernel,
    `StrongPerimetralTurning.ImplicitContractionKernel,
    `StrongPerimetralTurning.ContractedClosureDifference,
    `StrongPerimetralTurning.CircularPresentation.TotalLoop,
    `StrongPerimetralTurning.CircularPresentation.rejectInitialContraction,
    `StrongPerimetralTurning.PositiveClosureObstruction.rejectsContraction,
    `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
    `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
    `StrongPerimetralTurning.ExecutedGodelWitness.rejectProducedCompleteness,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.equal_memory_same_futures,
    `ConstitutiveSearch.ContinuationSignatures.FutureEquivalent.read,
    `Empty.elim, `False.elim]
  for root in [
      `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.terminalReadEqual,
      `StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality] do
    let mut pending := [root]
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if visited.contains name then continue
      if forbidden.any (fun bad => bad.isPrefixOf name) then
        throwError "Runtime kernel {root} depends transitively on forbidden {name}"
      visited := visited.insert name
      let some info := env.find? name | throwError "Missing dependency {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
    for required in [
        `ConstitutiveSearch.ContinuationSignatures.ExecutedRun.terminal_eq_run,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.continuationBridge,
        `ConstitutiveSearch.Grouping.Continuation.Exact.run_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.terminalCollision,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact] do
      unless visited.contains required do
        throwError "Runtime kernel {root} no longer consumes required {required}"
    if root == `StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality then
      for required in [`StrongPerimetralTurning.pole_run, `StrongPerimetralTurning.read_run] do
        unless visited.contains required do
          throwError "Godel kernel no longer consumes role/read stability {required}"
    logInfo m!"GODEL_RUNTIME_DEPENDENCIES_OK {root} constants={visited.size}"
  let wrapper := `StrongPerimetralTurning.godelOperationalClosureToEndpointEquality
  let some wrapperInfo := env.find? wrapper | throwError "Missing historical wrapper"
  let some wrapperValue := wrapperInfo.value? | throwError "Missing wrapper body"
  let mut body := wrapperValue
  while let .lam _ _ rest _ := body do body := rest
  unless body.getAppFn.constName? == some `StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality do
    throwError "Historical wrapper no longer directly calls the positive kernel"
  unless body.getAppArgs.back!.getAppFn.constName? ==
      some `StrongPerimetralTurning.OperationalSameRegimeClosureAt.executedGrouping do
    throwError "Historical wrapper no longer projects the same executed grouping"
  for name in body.getUsedConstants do
    unless [
        `StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality,
        `StrongPerimetralTurning.OperationalSameRegimeClosureAt.executedGrouping].contains name do
      throwError "Unexpected historical wrapper body dependency {name}"
  let some sourceInfo := getStructureInfo? env `StrongPerimetralTurning.GodelClosureSource
    | throwError "Missing runtime source schema"
  unless sourceInfo.fieldNames.toList.map Name.getString! == ["pole", "depth"] do
    throwError "Runtime source must store exactly pole and depth"
  logInfo "GODEL_RUNTIME_HISTORY_WRAPPER_OK: direct kernel application; source stores pole and depth"

/- AXIOM_AUDIT_BEGIN -/
#print axioms Nat
/- AXIOM_AUDIT_END -/
