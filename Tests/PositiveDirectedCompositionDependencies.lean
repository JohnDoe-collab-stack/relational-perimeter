import RelationalPerimeter.Agents.ContinuationSignatures.PositiveDirectedComposition
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
    let some info := env.find? name | throwError "Missing positive dependency {name}"
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

  let producedEquality ← closure
    [`ConstitutiveSearch.ContinuationSignatures.positiveDirectedProducedBitsEqual]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.same_sources_other_resource_agree,
      `ConstitutiveSearch.ContinuationSignatures.produceRoleSignature_exact,
      `ConstitutiveSearch.ContinuationSignatures.FutureEquivalent.read] do
    unless producedEquality.contains required do
      throwError "Positive produced equality no longer consumes {required}"

  let grouping ← closure
    [`ConstitutiveSearch.ContinuationSignatures.positiveDirectedGrouping]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.positiveDirectedSourceRun,
      `ConstitutiveSearch.ContinuationSignatures.positiveDirectedTargetRun,
      `ConstitutiveSearch.ContinuationSignatures.positiveDirectedProducedBitsEqual,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.mk] do
    unless grouping.contains required do
      throwError "Positive grouping no longer consumes {required}"

  let transport ← closure
    [`ConstitutiveSearch.ContinuationSignatures.positiveDirectedTerminalTransport]
  for required in [
      `ConstitutiveSearch.ContinuationSignatures.positiveDirectedGrouping,
      `ConstitutiveSearch.ContinuationSignatures.positiveDirectedReadoutPreservation,
      `ConstitutiveSearch.ContinuationSignatures.encodePositiveDirectedBit,
      `ConstitutiveSearch.ContinuationSignatures.decodePositiveDirectedBit,
      `ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.sourceForward,
      `ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.targetBackward,
      `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout,
      `ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.transport] do
    unless transport.contains required do
      throwError "Positive directed transport no longer consumes {required}"

  let positiveRoots ← closure [
    `ConstitutiveSearch.ContinuationSignatures.positiveDirectedProducedBitsEqual,
    `ConstitutiveSearch.ContinuationSignatures.positiveDirectedGrouping,
    `ConstitutiveSearch.ContinuationSignatures.positiveDirectedTerminalTransport]
  for name in positiveRoots.toList do
    for forbiddenPrefix in [
        `ConstitutiveSearch.ContinuationSignatures.rejectDirectedTransport,
        `ConstitutiveSearch.ContinuationSignatures.rejectBilateralTransport,
        `ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rejectDirectedEndpointIncompatibility,
        `StrongPerimetralTurning.ExecutedGodelWitness,
        `StrongPerimetralTurning.TarskiDiagonalCertification,
        `RelationalPerimeter.HeytingArithmetic] do
      if forbiddenPrefix.isPrefixOf name then
        throwError "Positive non-diagonal construction depends on obstruction {name}"

  logInfo "POSITIVE_DIRECTED_COMPOSITION_DEPENDENCIES_OK"

/- AXIOM_AUDIT_BEGIN -/
#print axioms Nat
/- AXIOM_AUDIT_END -/
