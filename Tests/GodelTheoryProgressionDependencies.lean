import RelationalPerimeter.Instances.HeytingArithmetic.GodelTheoryProgression
import Lean

/-!
Audit the types and bodies of the theory-progression layer. Each selected
root is traversed transitively through every reached declaration introduced by
the three new production modules. Pre-existing declarations are recorded as
explicit audited boundaries instead of recursively reopening the whole
arithmetic library. The complete history-indexed Gödel-system value is also a
closed received interface when it occurs as an index of an execution type; its
own fields are audited separately in `HistoryGodel.lean`.

Positive constructors, proof transport, diagonal rejections, and
representation-level wrappers are checked separately. This prevents a
negative certificate from silently replacing a required positive construction
while retaining the already audited generic Gödel runtime as a named boundary.
-/

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
      | .lam _ domain body _ | .forallE _ domain body _ =>
          pending := domain :: body :: pending
      | .letE _ type value body _ =>
          pending := type :: value :: body :: pending
      | .mdata _ body => pending := body :: pending
      | .proj recordName index body =>
          names := names.insert recordName
          if let some projection :=
              (getStructureInfo? env recordName).bind
                (fun info => info.getProjFn? index) then
            names := names.insert projection
          pending := body :: pending
      | _ => pure ()
    return names

  let dependencyCache ← IO.mkRef ({} : NameMap NameSet)
  let dependencies : Name → Elab.Command.CommandElabM NameSet := fun name => do
    if let some cached := (← dependencyCache.get).find? name then
      return cached
    let some info := env.find? name
      | throwError "Missing inspected constant {name}"
    let mut names := used (info.type :: (info.value? (allowOpaque := true)).toList)
    let metadata := match info with
      | .inductInfo value => value.ctors
      | .recInfo value => value.all
      | _ => []
    for dependency in metadata do names := names.insert dependency
    dependencyCache.modify fun cache => cache.insert name names
    return names

  let directBody := fun name => do
    let some info := env.find? name
      | throwError "Missing inspected body {name}"
    pure (used (info.value? (allowOpaque := true)).toList)
  let auditedModules := ({} : NameSet)
    |>.insert `RelationalPerimeter.Instances.HeytingArithmetic.TheoryHistorySoundness
    |>.insert `RelationalPerimeter.Instances.HeytingArithmetic.HistoryGodel
    |>.insert `RelationalPerimeter.Instances.HeytingArithmetic.GodelTheoryProgression
  let closedInterfaces := ({} : NameSet)
    |>.insert `RelationalPerimeter.HeytingArithmetic.soundHistoryEffectiveGodelSystem
  let moduleOf? := fun name =>
    (env.getModuleIdxFor? name).map fun index =>
      env.header.moduleNames[index.toNat]!
  let closureThroughNewModules := fun roots => do
    let mut pending : List Name := roots
    let mut visited : NameSet := {}
    let mut boundaries : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if visited.contains name then continue
      visited := visited.insert name
      if closedInterfaces.contains name then
        boundaries := boundaries.insert name
      else
        match moduleOf? name with
        | some moduleName =>
            if auditedModules.contains moduleName then
              pending := (← dependencies name).toList ++ pending
            else
              boundaries := boundaries.insert name
        | none => boundaries := boundaries.insert name
    pure (visited, boundaries)

  let bodyClosureThroughNewModules := fun roots => do
    let mut pending : List Name := roots
    let mut visited : NameSet := {}
    let mut boundaries : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if visited.contains name then continue
      visited := visited.insert name
      if closedInterfaces.contains name then
        boundaries := boundaries.insert name
      else
        match moduleOf? name with
        | some moduleName =>
            if auditedModules.contains moduleName then
              pending := (← directBody name).toList ++ pending
            else
              boundaries := boundaries.insert name
        | none => boundaries := boundaries.insert name
    pure (visited, boundaries)

  let successorDirect ← directBody
    `RelationalPerimeter.HeytingArithmetic.soundGodelSuccessor
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundTheoryHistory.extend,
      `StrongPerimetralTurning.ExecutedGodelProduction.witness,
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness] do
    unless successorDirect.contains required do
      throwError "Successor soundness does not directly consume {required}"
  if successorDirect.contains
      `RelationalPerimeter.HeytingArithmetic.soundHistoryGodelExecution then
    throwError "Successor soundness reconstructs the source execution"

  let newestProof ← directBody
    `RelationalPerimeter.HeytingArithmetic.historyGodelSentenceProofAtSuccessor
  for required in [
      `RelationalPerimeter.HeytingArithmetic.newestHistoryCheckedProof,
      `StrongPerimetralTurning.ExecutedGodelProduction.witness,
      `StrongPerimetralTurning.ExecutedGodelWitness.production,
      `StrongPerimetralTurning.ExecutedGodelSentenceProduction.sentence] do
    unless newestProof.contains required do
      throwError "Successor sentence proof does not directly consume {required}"
  if newestProof.contains
      `RelationalPerimeter.HeytingArithmetic.soundHistoryGodelExecution then
    throwError "Successor sentence proof reconstructs the source execution"
  let newestImplementation ← directBody
    `RelationalPerimeter.HeytingArithmetic.newestHistoryCheckedProof
  for required in [
      `RelationalPerimeter.HeytingArithmetic.historyCheckedProofOfDerivation,
      `RelationalPerimeter.HeytingArithmetic.HistoryAxiom.added,
      `RelationalPerimeter.HeytingArithmetic.TheoryHistory.Contains.newest] do
    unless newestImplementation.contains required do
      throwError "Newest checked proof does not directly consume {required}"

  let positiveRoots := [
    `RelationalPerimeter.HeytingArithmetic.soundGodelSuccessor,
    `RelationalPerimeter.HeytingArithmetic.historyGodelSentenceProofAtSuccessor,
    `RelationalPerimeter.HeytingArithmetic.historyCheckedProofPreserved,
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.preserveOldProof,
    `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace.preserveProof,
    `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.preserveProof]
  let forbiddenPositive := [
    `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
    `StrongPerimetralTurning.ExecutedGodelWitness.rejectProducedCompleteness,
    `RelationalPerimeter.HeytingArithmetic.historyRepresentsUnprovabilityForward,
    `RelationalPerimeter.HeytingArithmetic.historyRepresentsUnprovabilityBackward,
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceUnprovable,
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetUnprovable,
    `Empty.elim,
    `False.elim]
  for root in positiveRoots do
    let rootBody ← directBody root
    let (visited, boundaries) ← closureThroughNewModules [root]
    let (bodyVisited, bodyBoundaries) ← bodyClosureThroughNewModules [root]
    for forbidden in forbiddenPositive do
      if rootBody.contains forbidden then
        throwError "Positive producer {root} directly consumes {forbidden}"
      if bodyVisited.contains forbidden then
        throwError "Positive producer body {root} transitively depends on {forbidden}"
      if visited.contains forbidden then
        throwError "Positive producer type or body {root} depends on {forbidden}"
    logInfo m!"GODEL_THEORY_PROGRESSION_POSITIVE_CLOSURE_OK {root} typeAndBody={visited.size} body={bodyVisited.size} boundaries={boundaries.size + bodyBoundaries.size}"

  let some progressionInfo := getStructureInfo? env
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression
    | throwError "Missing executed progression schema"
  unless progressionInfo.fieldNames.toList.map Name.getString! == [
      "sourceExecution", "sourceExecutionExact", "targetSound",
      "targetSoundExact", "oldSentenceProofAtTarget",
      "oldSentenceProofAtTargetExact", "targetExecution",
      "targetExecutionExact"] do
    throwError "Executed progression no longer stores the exact provenance fields"

  let executedStepFrom ← directBody
    `RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgressionFrom
  for required in [
      `RelationalPerimeter.HeytingArithmetic.soundGodelSuccessor,
      `RelationalPerimeter.HeytingArithmetic.historyGodelSentenceProofAtSuccessor,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.mk] do
    unless executedStepFrom.contains required do
      throwError "Retained-execution progression does not directly consume {required}"

  let executedStep ← directBody
    `RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgression
  for required in [
      `RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgressionFrom,
      `RelationalPerimeter.HeytingArithmetic.soundHistoryGodelExecution] do
    unless executedStep.contains required do
      throwError "Canonical first progression does not directly consume {required}"

  let some stageInfo := getStructureInfo? env
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage
    | throwError "Missing sound Godel stage schema"
  unless stageInfo.fieldNames.toList.map Name.getString! == [
      "history", "sound", "execution", "executionExact"] do
    throwError "Sound Godel stage no longer retains its master execution"

  let stageProgression ← directBody
    `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.progression
  for required in [
      `RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgressionFrom,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.execution,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executionExact] do
    unless stageProgression.contains required do
      throwError "Stage progression does not directly consume retained field {required}"
  if stageProgression.contains
      `RelationalPerimeter.HeytingArithmetic.soundHistoryGodelExecution then
    throwError "Stage progression reconstructs its retained source execution"

  let targetStage ← directBody
    `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.progressionTarget
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.mk,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetSound,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetExecution] do
    unless targetStage.contains required do
      throwError "Target stage does not directly retain {required}"

  let proofPreservation ← directBody
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.preserveOldProof
  unless proofPreservation.contains
      `RelationalPerimeter.HeytingArithmetic.historyCheckedProofPreserved do
    throwError "Forward proof preservation does not call historyCheckedProofPreserved"
  let preservationClosure ← closureThroughNewModules
    [`RelationalPerimeter.HeytingArithmetic.historyCheckedProofPreserved]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.historyDerivationOfCheckedProof,
      `RelationalPerimeter.HeytingArithmetic.historyDerivationPreserve,
      `RelationalPerimeter.HeytingArithmetic.historyCheckedProofOfDerivation] do
    unless preservationClosure.1.contains required do
      throwError "Checked proof preservation does not transitively consume {required}"

  let truthToTarget ← directBody
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldTruthToTargetProof
  unless truthToTarget.contains
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldSentenceProofAtTarget do
    throwError "Positive old-truth conversion does not reuse the produced target proof"
  for forbidden in [
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceUnprovable,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetUnprovable] do
    if truthToTarget.contains forbidden then
      throwError "Positive old-truth conversion depends on {forbidden}"

  let sentenceDifference ← directBody
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.successiveGodelSentences_ne
  for required in [
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldSentenceProofAtTarget,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetUnprovable,
      `Eq.mp,
      `congrArg] do
    unless sentenceDifference.contains required do
      throwError "Successive-sentence distinction does not directly consume {required}"
  if sentenceDifference.contains
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceUnprovable then
    throwError "Successive-sentence distinction consumes source nonprovability"

  let reverseRejection ← directBody
    `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.rejectUniformReverseProofTransport
  for required in [
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceUnprovable,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldSentenceProofAtTarget] do
    unless reverseRejection.contains required do
      throwError "Reverse-proof rejection does not directly consume {required}"
  if reverseRejection.contains
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetUnprovable then
    throwError "Reverse-proof rejection consumes target nonprovability"

  for ⟨label, root, executionProjection, genericRoot⟩ in [
      ("Source positive bridge",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceComputedGroupingToProducedCompleteness,
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceExecution,
        `StrongPerimetralTurning.godelComputedGroupingToProducedCompleteness),
      ("Target positive bridge",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetComputedGroupingToProducedCompleteness,
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetExecution,
        `StrongPerimetralTurning.godelComputedGroupingToProducedCompleteness),
      ("Source rejection",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.rejectSourceComputedGrouping,
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceExecution,
        `StrongPerimetralTurning.rejectGodelComputedGroupingToEmpty),
      ("Target rejection",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.rejectTargetComputedGrouping,
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetExecution,
        `StrongPerimetralTurning.rejectGodelComputedGroupingToEmpty)] do
    let inspected ← directBody root
    for required in [executionProjection, genericRoot] do
      unless inspected.contains required do
        throwError "{label} does not directly consume {required}"

  for ⟨label, root, required⟩ in [
      ("Source grouping",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceOperationalGroupingWithoutRead,
        `StrongPerimetralTurning.godelOperationalGroupingWithoutRead),
      ("Source separator",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceTerminalSeparator,
        `StrongPerimetralTurning.godelTerminalSeparator),
      ("Source universal separation",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceExactRealizationSeparatesTerminals,
        `StrongPerimetralTurning.godelEveryExactRealizationSeparatesTerminals),
      ("Target grouping",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetOperationalGroupingWithoutRead,
        `StrongPerimetralTurning.godelOperationalGroupingWithoutRead),
      ("Target separator",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetTerminalSeparator,
        `StrongPerimetralTurning.godelTerminalSeparator),
      ("Target universal separation",
        `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetExactRealizationSeparatesTerminals,
        `StrongPerimetralTurning.godelEveryExactRealizationSeparatesTerminals)] do
    let runtimeDirect ← directBody root
    unless runtimeDirect.contains required do
      throwError "{label} does not directly reuse {required}"

  let traceProofTransport ← bodyClosureThroughNewModules
    [`RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace.preserveProof]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace.rec,
      `RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.preserveOldProof,
      `RelationalPerimeter.HeytingArithmetic.historyCheckedProofPreserved] do
    unless traceProofTransport.1.contains required do
      throwError "Trace proof transport does not transitively consume {required}"
  if traceProofTransport.1.contains
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.advance then
    throwError "Trace proof transport reconstructs its endpoint through advance"

  let finiteTransport ← directBody
    `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.preserveProof
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace.preserveProof,
      `Eq.mp] do
    unless finiteTransport.contains required do
      throwError "Finite proof transport does not directly consume {required}"
  if finiteTransport.contains
      `RelationalPerimeter.HeytingArithmetic.historyCheckedProofPreserved then
    throwError "Finite proof transport bypasses the retained trace"
  let finiteTransportClosure ← bodyClosureThroughNewModules
    [`RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.preserveProof]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace_target_eq_advance,
      `congrArg] do
    unless finiteTransportClosure.1.contains required do
      throwError "Finite proof transport does not transitively consume {required}"

  let traceClosure ← bodyClosureThroughNewModules
    [`RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace.succ,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.progression,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.progressionTarget,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.execution,
      `Sigma.fst,
      `Sigma.snd] do
    unless traceClosure.1.contains required do
      throwError "Finite executed trace does not transitively consume {required}"
  if traceClosure.1.contains
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.advance then
    throwError "Finite executed trace reconstructs its source through advance"

  let traceEndpointExact ← bodyClosureThroughNewModules
    [`RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace_target_eq_advance]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace,
      `RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.advance] do
    unless traceEndpointExact.1.contains required do
      throwError "Trace endpoint comparison does not consume {required}"

  logInfo m!"GODEL_THEORY_PROGRESSION_DEPENDENCIES_OK stepFromDirect={executedStepFrom.size} firstStepDirect={executedStep.size} stageStepDirect={stageProgression.size} preservationClosure={preservationClosure.1.size} distinctionDirect={sentenceDifference.size} reverseDirect={reverseRejection.size} traceClosure={traceClosure.1.size} traceProofClosure={traceProofTransport.1.size} finiteTransportDirect={finiteTransport.size} finiteTransportClosure={finiteTransportClosure.1.size}"

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.preserveProof
/- AXIOM_AUDIT_END -/
