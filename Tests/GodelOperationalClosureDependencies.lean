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
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
    `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.terminalReadEqual,
    `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.projectedTerminalsEqual,
    `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.leftTerminalExact,
    `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.rightTerminalExact,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.equal_memory_same_futures,
    `ConstitutiveSearch.ContinuationSignatures.FutureEquivalent.read,
    `Empty.elim, `False.elim]
  for root in [`StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality] do
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
        `StrongPerimetralTurning.godelExactRunExact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.next_exact,
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
  let some eventInfo := getStructureInfo? env `StrongPerimetralTurning.GodelRuntimeEvent
    | throwError "Missing runtime event schema"
  unless eventInfo.fieldNames.toList.map Name.getString! ==
      ["beforeDepth", "request", "afterDepth"] do
    throwError "Runtime event must be role-blind and store only depths plus the request"
  let operational := `StrongPerimetralTurning.godelOperationalGroupingWithoutRead
  let mut operationalPending := [operational]
  let mut operationalVisited : NameSet := {}
  while !operationalPending.isEmpty do
    let name := operationalPending.head!
    operationalPending := operationalPending.tail!
    if operationalVisited.contains name then continue
    if [
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact,
        `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
        `StrongPerimetralTurning.ExecutedGodelWitness.unprovable].any
        (fun bad => bad.isPrefixOf name) then
      throwError "Positive operational collision depends transitively on forbidden {name}"
    operationalVisited := operationalVisited.insert name
    let some info := env.find? name | throwError "Missing operational dependency {name}"
    operationalPending := info.getUsedConstantsAsSet.toList ++ operationalPending
  for required in [
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead,
      `StrongPerimetralTurning.godelOperationalRealizationWithoutRead,
      `StrongPerimetralTurning.godelOpenCloseRun] do
    unless operationalVisited.contains required do
      throwError "Positive operational collision no longer contains required {required}"
  let readBarrier := `StrongPerimetralTurning.godelRoleBlindReadExactToEndpointEquality
  let mut readPending := [readBarrier]
  let mut readVisited : NameSet := {}
  while !readPending.isEmpty do
    let name := readPending.head!
    readPending := readPending.tail!
    if readVisited.contains name then continue
    if [
        `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
        `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
        `Empty.elim, `False.elim].any (fun bad => bad.isPrefixOf name) then
      throwError "Read barrier already consumes negative Godel fact {name}"
    readVisited := readVisited.insert name
    let some info := env.find? name | throwError "Missing read dependency {name}"
    readPending := info.getUsedConstantsAsSet.toList ++ readPending
  let rejection := `StrongPerimetralTurning.godelExactRuntimeRejectsCommonTerminalMemory
  let mut rejectionPending := [rejection]
  let mut rejectionVisited : NameSet := {}
  while !rejectionPending.isEmpty do
    let name := rejectionPending.head!
    rejectionPending := rejectionPending.tail!
    if rejectionVisited.contains name then continue
    if [
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.events_exact].any
        (fun bad => bad.isPrefixOf name) then
      throwError "Final Godel rejection still depends on event separation {name}"
    rejectionVisited := rejectionVisited.insert name
    let some info := env.find? name | throwError "Missing rejection dependency {name}"
    rejectionPending := info.getUsedConstantsAsSet.toList ++ rejectionPending
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact,
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable] do
    unless rejectionVisited.contains required do
      throwError "Final Godel rejection no longer consumes required {required}"
  logInfo m!"GODEL_RUNTIME_OPERATIONAL_COLLISION_OK constants={operationalVisited.size}; event is role-blind"
  logInfo m!"GODEL_RUNTIME_READ_BARRIER_OK equalityConstants={readVisited.size} rejectionConstants={rejectionVisited.size}"
  logInfo "GODEL_RUNTIME_HISTORY_WRAPPER_OK: direct kernel application; source stores pole and depth"

/- AXIOM_AUDIT_BEGIN -/
#print axioms Nat
/- AXIOM_AUDIT_END -/
