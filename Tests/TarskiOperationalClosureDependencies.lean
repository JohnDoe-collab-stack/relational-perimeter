import RelationalPerimeter.Constitution.Tarski.OperationalClosure
import RelationalPerimeter.Instances.HeytingArithmetic.Tarski
import Lean

/-! Transitive inspection of types and values.  Operational production and
grouping must remain independent of the diagonal rejection and of Gödel. -/
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
        recordName :: ((getStructureInfo? env recordName).bind
          (fun info => info.getProjFn? index)).toList ++ used body
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

  -- Deciding the empty terminal authorization branch is intrinsic to the
  -- operational interface.  Its generated matcher eliminates an impossible
  -- authorization witness; it is not a diagonal or semantic contradiction.
  let inherentPositiveElimination ← closure [
    `StrongPerimetralTurning.TarskiOperationalAllow,
    `StrongPerimetralTurning.tarskiOperationalDecision,
    `StrongPerimetralTurning.ExecutedTarskiProduction.occurrences]

  let positiveRoots := [
    `StrongPerimetralTurning.executeTarskiProduction,
    `StrongPerimetralTurning.tarskiOperationalProject,
    `StrongPerimetralTurning.tarskiOperationalNext,
    `StrongPerimetralTurning.tarskiOperationalEvent,
    `StrongPerimetralTurning.tarskiOperationalRealization,
    `StrongPerimetralTurning.tarskiExecutedOperationalGrouping]
  let forbiddenPositive := [
    `StrongPerimetralTurning.TarskiDiagonalCertification,
    `StrongPerimetralTurning.TarskiDiagonalCertification.diagonalForward,
    `StrongPerimetralTurning.TarskiDiagonalCertification.diagonalBackward,
    `StrongPerimetralTurning.rejectTarskiLocalAdequacy,
    `StrongPerimetralTurning.tarskiExactClosureRejected,
    `StrongPerimetralTurning.TarskiLocalAdequacy,
    `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
    `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
    `StrongPerimetralTurning.ExecutedGodelTotalLoop]
  for root in positiveRoots do
    let visited ← closure [root]
    for forbidden in forbiddenPositive do
      if visited.contains forbidden then
        throwError "Positive Tarski layer {root} depends on forbidden {forbidden}"
    for name in visited.toList do
      let some info := env.find? name | throwError "Missing inspected constant {name}"
      unless inherentPositiveElimination.contains name do
        let direct := dependencies info
        for elimination in [`Empty.elim, `False.elim] do
          if direct.contains elimination then
            throwError "Positive Tarski layer {root} introduces {elimination} in {name}"
    logInfo m!"TARSKI_POSITIVE_DEPENDENCIES_OK {root} constants={visited.size}"

  let affirmative ← closure [`StrongPerimetralTurning.tarskiExecutedGroupingToLocalAdequacy]
  for forbidden in [
      `StrongPerimetralTurning.TarskiDiagonalCertification,
      `StrongPerimetralTurning.rejectTarskiLocalAdequacy,
      `StrongPerimetralTurning.tarskiExactClosureRejected,
      `RelationalPerimeter.HeytingArithmetic.diagonal_spec,
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable] do
    if affirmative.contains forbidden then
      throwError "Affirmative readout bridge depends on forbidden {forbidden}"
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.leftRun,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rightRun,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.terminalCollision,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.projectedTerminalsEqual,
      `ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.transport,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.reverseDirectedReadout,
      `ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence.leftToRightPreservation,
      `ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence.rightToLeftPreservation,
      `StrongPerimetralTurning.tarskiExecutedGroupingValueToCandidate,
      `StrongPerimetralTurning.tarskiExecutedGroupingCandidateToValue,
      `StrongPerimetralTurning.tarskiTerminalRead_value,
      `StrongPerimetralTurning.tarskiTerminalRead_candidate] do
    unless affirmative.contains required do
      throwError "Affirmative readout bridge no longer consumes {required}"

  for partialCheck in [
      (`StrongPerimetralTurning.tarskiValueToCandidateClosureConsequences,
        `StrongPerimetralTurning.tarskiExecutedGroupingValueToCandidate,
        `StrongPerimetralTurning.tarskiExecutedGroupingCandidateToValue),
      (`StrongPerimetralTurning.tarskiCandidateToValueClosureConsequences,
        `StrongPerimetralTurning.tarskiExecutedGroupingCandidateToValue,
        `StrongPerimetralTurning.tarskiExecutedGroupingValueToCandidate)] do
    let visited ← closure [partialCheck.1]
    for required in [
        partialCheck.2.1,
        `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.projectedTerminalsEqual,
        `ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.transport,
        `StrongPerimetralTurning.TarskiDiagonalCertification.diagonalForward,
        `StrongPerimetralTurning.TarskiDiagonalCertification.diagonalBackward] do
      unless visited.contains required do
        throwError "Partial Tarski closure {partialCheck.1} no longer consumes {required}"
    unless visited.contains
        (if partialCheck.1 == `StrongPerimetralTurning.tarskiValueToCandidateClosureConsequences then
          `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout
        else
          `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.reverseDirectedReadout) do
      throwError "Partial Tarski closure {partialCheck.1} no longer consumes its directed grouping bridge"
    for forbidden in [
        partialCheck.2.2,
        `StrongPerimetralTurning.tarskiExecutedGroupingToLocalAdequacy,
        `StrongPerimetralTurning.rejectTarskiLocalAdequacy,
        `StrongPerimetralTurning.tarskiExactClosureRejected] do
      if visited.contains forbidden then
        throwError "Partial Tarski closure {partialCheck.1} depends on reverse/full bridge {forbidden}"

  let rejection ← closure [`StrongPerimetralTurning.tarskiExactClosureRejected]
  for required in [
      `StrongPerimetralTurning.tarskiExecutedGroupingToLocalAdequacy,
      `StrongPerimetralTurning.rejectTarskiLocalAdequacy,
      `StrongPerimetralTurning.TarskiDiagonalCertification.diagonalForward,
      `StrongPerimetralTurning.TarskiDiagonalCertification.diagonalBackward] do
    unless rejection.contains required do
      throwError "Final Tarski rejection no longer consumes {required}"

  let ha ← closure
    [`RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiExactClosureRejected]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.PRFunction.runCore,
      `RelationalPerimeter.HeytingArithmetic.PRFunction.captureAvoidingDiagonalSubstitution,
      `RelationalPerimeter.HeytingArithmetic.diagonal_spec,
      `RelationalPerimeter.HeytingArithmetic.certifyHATarskiDiagonal] do
    unless ha.contains required do
      throwError "Concrete HA Tarski result no longer consumes {required}"
  for forbidden in [
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
      `StrongPerimetralTurning.ExecutedGodelWitness.rejectProducedCompleteness] do
    if ha.contains forbidden then
      throwError "Concrete HA Tarski result depends on Gödel witness {forbidden}"

  let semantic ← closure
    [`RelationalPerimeter.HeytingArithmetic.heytingArithmeticRejectsSemanticTruthCandidate]
  for required in [
      `RelationalPerimeter.HeytingArithmetic.heytingArithmeticRejectsTotalTruthCandidate,
      `RelationalPerimeter.HeytingArithmetic.diagonal_spec] do
    unless semantic.contains required do
      throwError "Direct semantic Tarski theorem no longer consumes {required}"
  for forbidden in [
      `StrongPerimetralTurning.tarskiOperationalRealization,
      `StrongPerimetralTurning.tarskiExecutedOperationalGrouping,
      `StrongPerimetralTurning.tarskiExactClosureRejected,
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable] do
    if semantic.contains forbidden then
      throwError "Direct semantic Tarski theorem depends on forbidden runtime/Gödel result {forbidden}"

  let some eventInfo := getStructureInfo? env `StrongPerimetralTurning.TarskiRuntimeEvent
    | throwError "Missing Tarski runtime event schema"
  if eventInfo.fieldNames.toList.map Name.getString! |>.contains "pole" then
    throwError "Tarski runtime event exposes the source pole"
  let some operationalInfo := getStructureInfo? env
      `ConstitutiveSearch.ContinuationSignatures.OperationalContract
    | throwError "Missing readout-free operational contract"
  if operationalInfo.fieldNames.toList.map Name.getString! |>.contains "read" then
    throwError "Operational contract contains a readout field"
  let some groupingInfo := getStructureInfo? env
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping
    | throwError "Missing executed operational grouping"
  for hiddenTerminal in ["leftTerminal", "rightTerminal"] do
    if groupingInfo.fieldNames.toList.map Name.getString! |>.contains hiddenTerminal then
      throwError "Operational grouping hides indexed terminal {hiddenTerminal} as a field"
  logInfo "TARSKI_RUNTIME_SCHEMAS_OK: readout-free memory; pole-free event; indexed terminals"

/- AXIOM_AUDIT_BEGIN -/
#print axioms Nat
/- AXIOM_AUDIT_END -/
