import RelationalPerimeter.Constitution.Godel.OperationalClosure
import Lean

/-! Inspect every transitive constant type and value. Dependencies already
present in the received ExecutedGodelProduction interface are reported apart
from the positive runtime. Negative witness projections are never exempted. -/
set_option maxHeartbeats 0
open Lean
run_cmd do
  let env ← getEnv
  let rec used (expression : Expr) : List Name :=
    match expression with
    | .const name _ => [name]
    | .app function argument => used function ++ used argument
    | .lam _ domain body _ | .forallE _ domain body _ => used domain ++ used body
    | .letE _ type value body _ => used type ++ used value ++ used body
    | .mdata _ body => used body
    | .proj recordName index body =>
        recordName :: ((getStructureInfo? env recordName).bind (fun info => info.getProjFn? index)).toList ++ used body
    | _ => []
  let dependencies := fun (info : ConstantInfo) =>
    used info.type ++ (info.value? (allowOpaque := true) |>.map used |>.getD []) ++
      (match info with
      | .inductInfo value => value.ctors
      | .recInfo value => value.all
      | _ => [])
  let closure := fun roots => do
    let mut pending : List Name := roots
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if visited.contains name then continue
      visited := visited.insert name
      let some info := env.find? name | throwError "Missing dependency {name}"
      pending := dependencies info ++ pending
    pure visited
  let interface ← closure [
    `StrongPerimetralTurning.ExecutedGodelProduction,
    `StrongPerimetralTurning.ExecutedGodelProduction.mk,
    `StrongPerimetralTurning.ExecutedGodelProduction.witness,
    `StrongPerimetralTurning.ExecutedGodelProduction.history]
  let inherent := interface
  logInfo m!"GODEL_RUNTIME_INHERENT_INTERFACE constants={interface.size}; received ExecutedGodelProduction constructor and projections"
  let forbidden := [
    `StrongPerimetralTurning.godelCircularPresentation,
    `StrongPerimetralTurning.godelPerimetralPresentation,
    `StrongPerimetralTurning.godelPerimetralContinuation,
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
    `ConstitutiveSearch.ContinuationSignatures.FutureEquivalent,
    `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.event_exact,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.events_exact,
    `ConstitutiveSearch.ContinuationSignatures.ExactRealization.equal_memory_same_futures]
  let roots := [
    `StrongPerimetralTurning.GodelPositiveExecutionCore,
    `StrongPerimetralTurning.godelPositiveExecutionCore,
    `StrongPerimetralTurning.GodelOperationalH1,
    `StrongPerimetralTurning.godelOperationalH1,
    `StrongPerimetralTurning.GodelOperationalH1.occurrenceOrigin,
    `StrongPerimetralTurning.GodelOperationalH1.productionOrigin,
    `StrongPerimetralTurning.GodelOperationalH1.certificationOrigin,
    `StrongPerimetralTurning.GodelOperationalH1.continuationOrigin,
    `StrongPerimetralTurning.GodelOperationalH1.executedOriginOrder,
    `StrongPerimetralTurning.GodelOperationalHistory.extendOccurrenceTransport,
    `StrongPerimetralTurning.GodelInitializedAt,
    `StrongPerimetralTurning.GodelClosureContextAt,
    `StrongPerimetralTurning.godelReceivedClosureContext,
    `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead,
    `StrongPerimetralTurning.godelOperationalRealizationWithoutRead,
    `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead,
    `StrongPerimetralTurning.godelOperationalGroupingWithoutRead,
    `StrongPerimetralTurning.OperationalSameRegimeClosureAt,
    `StrongPerimetralTurning.godelOperationalClosureOfTerminalCollision,
    `StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality,
    `StrongPerimetralTurning.godelExecutedOperationalGroupingToProducedCompleteness,
    `StrongPerimetralTurning.godelExecutedGroupingProjectedTerminalsEqual,
    `StrongPerimetralTurning.godelOperationalRunExact,
    `StrongPerimetralTurning.godelOperationalClosureToEndpointEquality,
    `StrongPerimetralTurning.godelOperationalClosureToProducedCompleteness,
    `StrongPerimetralTurning.godelTerminalReadExactToEndpointEquality]
  for root in roots do
    let visited ← closure [root]
    let mut accepted := true
    for name in visited.toList do
      if forbidden.any (fun bad => bad.isPrefixOf name) then
        accepted := false
        logError m!"Positive runtime {root} depends through type or value on forbidden {name}"
      let some info := env.find? name | throwError "Missing inspected constant {name}"
      if !inherent.contains name then
        let direct := dependencies info
        for elimination in [`Empty.elim, `False.elim] do
          if direct.contains elimination then
            accepted := false
            logError m!"Positive runtime {root} introduces {elimination} in {name}"
    let inheritedCount := visited.toList.filter inherent.contains |>.length
    if accepted then
      logInfo m!"GODEL_RUNTIME_DEPENDENCIES_OK {root} constants={visited.size} inherent={inheritedCount}"
  for root in [
      `StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality,
      `StrongPerimetralTurning.godelOperationalClosureToEndpointEquality,
      `StrongPerimetralTurning.godelOperationalClosureToProducedCompleteness] do
    let visited ← closure [root]
    for required in [
        `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.leftRun,
        `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.rightRun,
        `ConstitutiveSearch.ContinuationSignatures.ExecutedRun.terminal_eq_run,
        `StrongPerimetralTurning.godelExactRunExact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.next_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.terminalCollision,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact,
        `StrongPerimetralTurning.pole_run,
        `StrongPerimetralTurning.read_run] do
      unless visited.contains required do
        throwError "Readout bridge {root} no longer consumes {required}"
  let directedBridge ← closure
    [`StrongPerimetralTurning.godelExecutedOperationalGroupingToProducedCompleteness]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.leftRun,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rightRun,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedRun.terminal_eq_run,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.projectedTerminalsEqual,
      `ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.transport,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout,
      `StrongPerimetralTurning.pole_run,
      `StrongPerimetralTurning.read_run] do
    unless directedBridge.contains required do
      throwError "Directed Gödel readout bridge no longer consumes {required}"
  for forbidden in [
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact,
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
      `StrongPerimetralTurning.TarskiDiagonalCertification] do
    if directedBridge.contains forbidden then
      throwError "Directed Gödel readout bridge depends on forbidden {forbidden}"
  let operational ← closure [`StrongPerimetralTurning.godelOperationalGroupingWithoutRead]
  for required in [
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead,
      `StrongPerimetralTurning.godelOperationalRealizationWithoutRead,
      `StrongPerimetralTurning.godelReceivedClosureContext,
      `StrongPerimetralTurning.godelSearchCloseAction,
      `StrongPerimetralTurning.godelAuthorizeCloseAction,
      `StrongPerimetralTurning.godelDecomposeCloseAction,
      `StrongPerimetralTurning.GodelExecutedCloseAction.leftRun,
      `StrongPerimetralTurning.GodelExecutedCloseAction.rightRun] do
    unless operational.contains required do
      throwError "Positive operational grouping no longer consumes {required}"
  if operational.contains `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact then
    throwError "Positive operational grouping already requires readout exactness"
  let terminalSeparator ← closure [`StrongPerimetralTurning.godelTerminalSeparator]
  for required in [
      `StrongPerimetralTurning.godelOperationalGroupingWithoutRead,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.leftRun,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.rightRun,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedRun.terminal_eq_run,
      `StrongPerimetralTurning.read_run,
      `StrongPerimetralTurning.godelWitnessReadouts_ne,
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
      `ConstitutiveSearch.ContinuationSignatures.FutureContract.outcome,
      `ConstitutiveSearch.ContinuationSignatures.Outcome.read] do
    unless terminalSeparator.contains required do
      throwError "Terminal Gödel separator no longer consumes {required}"
  for forbiddenSeparator in [
      `StrongPerimetralTurning.godelExactRuntimeRejectsCommonTerminalMemory,
      `StrongPerimetralTurning.rejectGodelOperationalClosureToEmpty,
      `StrongPerimetralTurning.godelTerminalReadExactToEndpointEquality,
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.read_exact,
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact] do
    if terminalSeparator.contains forbiddenSeparator then
      throwError "Terminal Gödel separator depends on forbidden {forbiddenSeparator}"
  let universalTerminalSeparation ← closure [
    `StrongPerimetralTurning.godelEveryExactRealizationSeparatesTerminals]
  for required in [
      `StrongPerimetralTurning.godelTerminalSeparator,
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.distinct_memory_of_separator,
      `ConstitutiveSearch.ContinuationSignatures.ExactRealization.equal_memory_same_futures,
      `ConstitutiveSearch.ContinuationSignatures.FutureSeparator.not_equivalent] do
    unless universalTerminalSeparation.contains required do
      throwError "Universal Gödel terminal separation no longer consumes {required}"
  for forbiddenSeparation in [
      `StrongPerimetralTurning.godelExactRuntimeRejectsCommonTerminalMemory,
      `StrongPerimetralTurning.rejectGodelOperationalClosureToEmpty] do
    if universalTerminalSeparation.contains forbiddenSeparation then
      throwError "Universal Gödel terminal separation depends on forbidden {forbiddenSeparation}"
  logInfo m!"GODEL_TERMINAL_SEPARATOR_DEPENDENCIES_OK separator={terminalSeparator.size} universal={universalTerminalSeparation.size}"
  let terminalBridge ← closure [`StrongPerimetralTurning.godelTerminalReadExactToEndpointEquality]
  for required in [
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.leftRun,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.rightRun,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.terminalCollision,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedRun.terminal_eq_run,
      `StrongPerimetralTurning.godelOperationalRunExact,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.next_exact,
      `StrongPerimetralTurning.pole_run,
      `StrongPerimetralTurning.read_run] do
    unless terminalBridge.contains required do
      throwError "Terminal readout bridge no longer consumes {required}"
  for root in [
      `StrongPerimetralTurning.rejectGodelExecutedOperationalGroupingToEmpty,
      `StrongPerimetralTurning.rejectGodelOperationalClosureToEmpty,
      `StrongPerimetralTurning.rejectGodelTerminalReadExactToEmpty,
      `StrongPerimetralTurning.godelExactRuntimeRejectsCommonTerminalMemory] do
    let visited ← closure [root]
    for required in [
        `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
        `StrongPerimetralTurning.ExecutedGodelWitness.unprovable] do
      unless visited.contains required do
        throwError "Terminal rejection {root} no longer consumes {required}"
    for bad in [
        `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.event_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.event_exact,
        `ConstitutiveSearch.ContinuationSignatures.ExactRealization.events_exact] do
      if visited.contains bad then
        throwError "Terminal rejection {root} depends on event separation {bad}"
    logInfo m!"GODEL_RUNTIME_REJECTION_DEPENDENCIES_OK {root} constants={visited.size}"
  let some sourceInfo := getStructureInfo? env `StrongPerimetralTurning.GodelClosureSource
    | throwError "Missing rich runtime source schema"
  unless sourceInfo.fieldNames.toList.map Name.getString! ==
      ["core", "h1", "pole", "operationalHistory", "phase"] do
    throwError "Runtime source must store the shared positive core, H1, pole, operational history and phase"
  let some eventInfo := getStructureInfo? env `StrongPerimetralTurning.GodelRuntimeEvent
    | throwError "Missing runtime event schema"
  unless eventInfo.fieldNames.toList.map Name.getString! ==
      ["beforePhase", "beforeDepth", "request", "afterPhase", "afterDepth"] do
    throwError "Runtime event must expose phases and depths without a pole"
  let some groupingInfo := getStructureInfo? env
      `ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping
    | throwError "Missing generic grouping schema"
  unless groupingInfo.fieldNames.toList.map Name.getString! |>.contains "trace" do
    throwError "Executed grouping must store a positive nonempty request trace"
  if groupingInfo.fieldNames.toList.map Name.getString! |>.contains "nonempty" then
    throwError "Executed grouping still stores a negative nonemptiness field"
  for removed in [
      `StrongPerimetralTurning.godelRoleBlindReadExactToEndpointEquality,
      `StrongPerimetralTurning.rejectGodelRoleBlindReadExactToEmpty] do
    if env.contains removed then
      throwError "Obsolete static readout shortcut remains public: {removed}"
  logInfo "GODEL_RUNTIME_SCHEMAS_OK: positive H1 stored; dynamic phase; events omit pole; nonempty trace constructed"

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.godelOperationalGroupingWithoutRead
/- AXIOM_AUDIT_END -/
