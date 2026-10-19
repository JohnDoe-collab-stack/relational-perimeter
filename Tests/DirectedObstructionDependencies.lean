import RelationalPerimeter.Constitution.Continuation.DirectedObstruction
import RelationalPerimeter.Constitution.Godel.OperationalClosure
import RelationalPerimeter.Constitution.Tarski.ClosureObstruction
import RelationalPerimeter.Instances.HeytingArithmetic.OperationalClosure
import Lean

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
      | .letE _ type value body _ => pending := type :: value :: body :: pending
      | .mdata _ body => pending := body :: pending
      | .proj recordName index body =>
          names := names.insert recordName
          if let some projection :=
              (getStructureInfo? env recordName).bind (fun info => info.getProjFn? index) then
            names := names.insert projection
          pending := body :: pending
      | _ => pure ()
    return names
  let dependencyCache ← IO.mkRef ({} : NameMap NameSet)
  let dependencies : Name → Elab.Command.CommandElabM NameSet := fun name => do
    if let some cached := (← dependencyCache.get).find? name then
      return cached
    let some info := env.find? name | throwError "Missing dependency {name}"
    let mut names := used (info.type :: (info.value? (allowOpaque := true)).toList)
    let metadata := match info with
      | .inductInfo value => value.ctors
      | .recInfo value => value.all
      | _ => []
    for dependency in metadata do names := names.insert dependency
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

  let directed ← closure
    [`ConstitutiveSearch.ContinuationSignatures.rejectDirectedTransport]
  for forbiddenPrefix in [
      `ConstitutiveSearch.ContinuationSignatures.BilateralNegationCertificate,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping,
      `StrongPerimetralTurning,
      `RelationalPerimeter.HeytingArithmetic] do
    for name in directed.toList do
      if forbiddenPrefix.isPrefixOf name then
        throwError "Pure directed incompatibility depends on {name}"

  let bilateral ← closure
    [`ConstitutiveSearch.ContinuationSignatures.rejectBilateralTransport]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.BilateralNegationCertificate.forward,
      `ConstitutiveSearch.ContinuationSignatures.BilateralNegationCertificate.backward] do
    unless bilateral.contains required do
      throwError "Bilateral incompatibility no longer consumes {required}"
  for forbiddenPrefix in [
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping,
      `StrongPerimetralTurning,
      `RelationalPerimeter.HeytingArithmetic] do
    for name in bilateral.toList do
      if forbiddenPrefix.isPrefixOf name then
        throwError "Pure bilateral incompatibility depends on {name}"

  let executedDirected ← closure
    [`ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rejectDirectedEndpointIncompatibility]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout,
      `ConstitutiveSearch.ContinuationSignatures.rejectDirectedTransport] do
    unless executedDirected.contains required do
      throwError "Executed directed obstruction no longer consumes {required}"
  for forbiddenPrefix in [`StrongPerimetralTurning, `RelationalPerimeter.HeytingArithmetic] do
    for name in executedDirected.toList do
      if forbiddenPrefix.isPrefixOf name then
        throwError "Generic executed obstruction depends on specialization {name}"

  let executedBilateral ← closure
    [`ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rejectBilateralEndpointIncompatibility]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.reverseDirectedReadout,
      `ConstitutiveSearch.ContinuationSignatures.rejectBilateralTransport] do
    unless executedBilateral.contains required do
      throwError "Executed bilateral obstruction no longer consumes {required}"
  for forbiddenPrefix in [`StrongPerimetralTurning, `RelationalPerimeter.HeytingArithmetic] do
    for name in executedBilateral.toList do
      if forbiddenPrefix.isPrefixOf name then
        throwError "Generic bilateral obstruction depends on specialization {name}"

  let computedBridge ← closure
    [`StrongPerimetralTurning.godelComputedGroupingToProducedCompleteness]

  let godelAdapter ← closure [`StrongPerimetralTurning.godelOperationalRealization]
  for required in [
      `StrongPerimetralTurning.godelOperationalRealizationWithoutRead,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.toOperational,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.project,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.forward,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.backward,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.next_exact,
      `StrongPerimetralTurning.GodelOperationalRealizationWithoutRead.event_exact] do
    unless godelAdapter.contains required do
      throwError "Gödel operational adapter no longer consumes {required}"

  for required in [
      `StrongPerimetralTurning.godelOperationalGroupingWithoutRead,
      `StrongPerimetralTurning.GodelOperationalGroupingWithoutRead.toExecutedOperationalGrouping,
      `StrongPerimetralTurning.godelExecutedOperationalGroupingToProducedCompleteness,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout] do
    unless computedBridge.contains required do
      throwError "Computed Gödel bridge no longer consumes {required}"
  for forbidden in [
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
      `ConstitutiveSearch.ContinuationSignatures.rejectDirectedTransport] do
    if computedBridge.contains forbidden then
      throwError "Computed positive Gödel bridge depends on rejection data {forbidden}"

  let computedRejection ← closure
    [`StrongPerimetralTurning.rejectGodelComputedGroupingToEmpty]
  for required in [
      `StrongPerimetralTurning.godelComputedGroupingToProducedCompleteness,
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable,
      `ConstitutiveSearch.ContinuationSignatures.rejectDirectedTransport] do
    unless computedRejection.contains required do
      throwError "Computed Gödel rejection no longer consumes {required}"

  let tarskiRejection ← closure [`StrongPerimetralTurning.tarskiExactClosureRejected]
  for required in [
      `StrongPerimetralTurning.tarskiExecutedGroupingToLocalAdequacy,
      `StrongPerimetralTurning.TarskiDiagonalCertification.toBilateralNegationCertificate,
      `ConstitutiveSearch.ContinuationSignatures.rejectBilateralTransport] do
    unless tarskiRejection.contains required do
      throwError "Tarski bilateral rejection no longer consumes {required}"
  if tarskiRejection.contains `StrongPerimetralTurning.rejectTarskiLocalAdequacy then
    throwError "Tarski rejection bypasses the generic bilateral incompatibility API"

  let haBridge ← closure
    [`RelationalPerimeter.HeytingArithmetic.heytingArithmeticComputedGroupingToProducedCompleteness]
  unless haBridge.contains `StrongPerimetralTurning.godelComputedGroupingToProducedCompleteness do
    throwError "HA positive bridge no longer specializes the computed Gödel bridge"
  for forbidden in [
      `StrongPerimetralTurning.ExecutedGodelWitness.trueWitness,
      `StrongPerimetralTurning.ExecutedGodelWitness.unprovable] do
    if haBridge.contains forbidden then
      throwError "HA positive bridge consumes rejection witness {forbidden}"

  logInfo "DIRECTED_OBSTRUCTION_DEPENDENCIES_OK"

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rejectDirectedEndpointIncompatibility
/- AXIOM_AUDIT_END -/
