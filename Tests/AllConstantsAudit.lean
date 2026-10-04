import Lean
import Tests.AristotleCorrectionRegression
import Tests.ComputationalPhenomenonRegression
import Tests.ConstitutiveComplexityHierarchyRegression
import Tests.ConstitutiveContinuityRegression
import Tests.ConstitutiveExecutionRegression
import Tests.ConstitutiveNormalizerSuccinctnessRegression
import Tests.ConstitutiveObjectiveRegression
import Tests.DeepPreservationRegression
import Tests.EndogenousOperationalStabilityRegression
import Tests.EndogenousWidthBridgeRegression
import Tests.ProducedContinuation
import Tests.ProductionTimelineRegression
import Tests.PublicRootImport
import Tests.RealizedConstitutionRegression
import Tests.RelationalExtensiveIffRegression
import Tests.SemanticImageRegression
import Tests.UnifiedConstitution
import Tests.UnifiedMasterInstance

/-! Build-time tooling, not a mathematical hypothesis or a new production
dependency. Scan every constant in every imported repository module, including
private declarations. Classify compiler exceptions using source locations and
the constructor/definition metadata; an unclassified exception fails closed.
The selected declarations printed in each module remain independently audited. -/
set_option maxHeartbeats 0
open Lean
run_cmd do
  let env ← Lean.getEnv
  let mut checked := 0
  let mut generated := 0
  let mut modules : Lean.NameSet := {}
  let mut sources : Lean.NameMap String := {}
  for moduleName in env.header.moduleNames do
    let moduleText := moduleName.toString
    if moduleText.startsWith "RelationalPerimeter" || moduleText.startsWith "Tests." ||
        ["SegmentedResidualRole", "AbstractSegmentedTurning", "ExactTypeTransport",
          "StrongPerimetralTurning"].contains moduleText then
      modules := modules.insert moduleName
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index.toNat]!
    let moduleText := moduleName.toString
    unless moduleText.startsWith "RelationalPerimeter" || moduleText.startsWith "Tests." ||
        ["SegmentedResidualRole", "AbstractSegmentedTurning", "ExactTypeTransport",
          "StrongPerimetralTurning"].contains moduleText do continue
    checked := checked + 1
    modules := modules.insert moduleName
    let dependencies ← Lean.collectAxioms name
    if dependencies.isEmpty then continue
    let source ← match sources.find? moduleName with
      | some source => pure source
      | none =>
          let source ← IO.FS.readFile (moduleText.replace "." "/" ++ ".lean")
          sources := sources.insert moduleName source
          pure source
    let mut selected := ""
    if let some location ← Lean.findDeclarationRangesCore? name then
      let range := location.selectionRange
      if range.pos.line == range.endPos.line then
        let line := (source.splitOn "\n")[range.pos.line - 1]!
        selected := String.ofList ((line.toList.drop range.pos.column).take
          (range.endPos.column - range.pos.column))
    let userName := (Lean.privateToUserName name).toString
    let authored := !selected.isEmpty &&
      (userName == selected || userName.endsWith ("." ++ selected))
    let leaf := name.getString!
    let parent := name.getPrefix
    let category := if !authored && leaf == "injEq" && env.isConstructor parent then
        "compiler-constructor-equation"
      else if !authored && leaf == "eq_def" && (env.find? parent).any (fun value =>
          match value with | .defnInfo _ => true | _ => false) then
        "compiler-unfold-equation"
      else if !authored && leaf == "congr_simp" && (env.find? parent).isSome then
        "compiler-congruence"
      else if !authored && userName.contains "instRepr" && source.contains "deriving" &&
          (match info with | .defnInfo _ => true | _ => false) then
        "compiler-derived-representation"
      else "REJECTED"
    if category == "REJECTED" then
      throwError "All-constant audit rejected {name}; source identifier '{selected}'; dependencies {dependencies}"
    generated := generated + 1
    logInfo m!"ALL_CONSTANTS_EXCEPTION\t{moduleName}\t{name}\t{category}\t{dependencies}"
  logInfo m!"ALL_CONSTANTS_OK constants={checked} modules={modules.size} generatedExceptions={generated} writtenExceptions=0"

/- AXIOM_AUDIT_BEGIN -/
#print axioms Nat
/- AXIOM_AUDIT_END -/
