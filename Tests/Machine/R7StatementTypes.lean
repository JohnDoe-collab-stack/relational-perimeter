import RelationalPerimeter.Computation.Machine.ConstitutiveLiveExecution
import Lean

/-! Frozen explicit types for the fifteen R7 production interfaces. This tool
is never imported by the runtime. No expected type is read from its producer. -/
set_option autoImplicit false
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R7StatementTypes
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures
open StrongPerimetralTurning
open Lean Elab Command Term

run_cmd liftTermElabM do
  let rec binders : Expr → List BinderInfo
    | .forallE _ _ body mode => mode :: binders body
    | _ => []
  let expectations : Array (Name × Syntax) := #[
    (`ConstitutiveDiscovery.receivedDecoys_exact, ← `(∀ {P : CircularPresentation}
      {source : PositiveConstitution P} (target : PositiveConstitution P)
      (step : GeneratedStep source target),
      ConstitutiveDiscovery.receivedDecoys target step =
        ConstitutiveDiscovery.foldFormations target.2.1.2)),
    (`ConstitutiveDiscovery.measuredFormula_exact, ← `(∀ {depth : Nat}
      (generation : Generation depth) (seed : Nat)
      (seedExact : seed = generatedSearchSeed generation.full),
      ConstitutiveDiscovery.measuredFormula generation seed seedExact = constructMeasuredFormula seed)),
    (`ConstitutiveDiscovery.extraction_exact, ← `(∀ (front : Frontier),
      ConstitutiveDiscovery.extraction front =
        measuredGeneratedExtractionFromSeed front.generation.full front.searchSeed front.seedExact)),
    (`ConstitutiveDiscovery.discovery_exact, ← `(∀ (front : Frontier),
      ConstitutiveDiscovery.discover front = LiveReduction.discover front)),
    (`ConstitutiveExecution.buildAction_exact, ← `(∀ (front : Frontier),
      ConstitutiveExecution.buildAction front = LiveReduction.buildAction front)),
    (`ConstitutiveExecution.produce_exact, ← `(∀ {scope : ConnectedFabric.Scope} (live : Live scope),
      ConstitutiveExecution.produce live = produceReduced live)),
    (`ConstitutiveExecution.perform_exact, ← `(∀ {scope : ConnectedFabric.Scope}
      (memory : Runtime scope) (request : Request),
      ConstitutiveExecution.perform memory request = performReduced memory request)),
    (`ConstitutiveExecution.realization, ← `(∀ (scope : ConnectedFabric.Scope),
      ExactRealization (runtimeContract scope) (Runtime scope))),
    (`ConstitutiveExecution.run_exact, ← `(∀ {scope : ConnectedFabric.Scope}
      (memory : Runtime scope) (requests : List (ULift.{3} Request)),
      ConstitutiveExecution.run memory requests = runReduced memory requests)),
    (`ConstitutiveExecution.run_contract_exact, ← `(∀ {scope : ConnectedFabric.Scope}
      (memory : Runtime scope) (requests : List (ULift.{3} Request)),
      ConstitutiveExecution.run memory requests =
        (ConstitutiveExecution.contract scope).outcome memory requests)),
    (`ConstitutiveExecution.all_sources_exact, ← `(∀ (scope : ConnectedFabric.Scope)
      (memory : Memory) (requests : List (ULift.{3} Request)),
      (runtimeContract scope).outcome memory requests =
        ConstitutiveExecution.run (projectMemory scope memory) requests)),
    (`ConstitutiveExecution.rich_sources_exact, ← `(∀ (scope : ConnectedFabric.Scope)
      (frame : Frame) (requests : List (ULift.{3} Request)),
      (sourceContract scope).outcome frame requests =
        ConstitutiveExecution.run (projectMemory scope (project scope frame)) requests)),
    (`ConstitutiveExecution.minimality, ← `(∀ (scope : ConnectedFabric.Scope) {one two : Memory}
      (first : Coherent scope one) (second : Coherent scope two),
      projectMemory scope one = projectMemory scope two ↔
        ∀ requests, ConstitutiveExecution.run (projectMemory scope one) requests =
          ConstitutiveExecution.run (projectMemory scope two) requests)),
    (`ConstitutiveExecution.any_realization, ← `(∀ {scope : ConnectedFabric.Scope} {Other : Type 3}
      (other : ExactRealization (runtimeContract scope) Other) {one two : Memory}
      (first : Coherent scope one) (second : Coherent scope two)
      (same : other.project one = other.project two),
      projectMemory scope one = projectMemory scope two)),
    (`ConstitutiveExecution.refusal_continues, ← `(∀ {scope : ConnectedFabric.Scope}
      (memory : Runtime scope) (left right : Signals)
      (wrong : pulseFits scope left right = false) (rest : List (ULift.{3} Request)),
      ConstitutiveExecution.run memory (⟨.pulse left right⟩ :: rest) =
        Outcome.step (readRuntime memory) false Event.refused (ConstitutiveExecution.run memory rest)))]
  for (shortName, expectedSyntax) in expectations do
    let name := `ConstitutiveSearch.ReconfigurableMachine.LiveReduction ++ shortName
    let actual ← getConstInfo name
    match actual with
    | .defnInfo _ =>
        if shortName != `ConstitutiveExecution.realization then
          throwError "R7_EXPECTED_THEOREM {name}"
    | .thmInfo _ =>
        if shortName == `ConstitutiveExecution.realization then
          throwError "R7_EXPECTED_DATA_DEFINITION {name}"
    | _ => throwError "R7_UNEXPECTED_DECLARATION_KIND {name}"
    -- Generalize expectation universes independently, before comparing to the
    -- producer. The fixed list cannot be inferred from the controlled type.
    let expectedLevels : List Name := if shortName == `ConstitutiveDiscovery.receivedDecoys_exact
      then [`u_1, `u_2, `u_3, `u_4, `u_5, `u_6, `u_7] else []
    let (expected, levels) ← withLevelNames [] do
      let elaborated ← elabType expectedSyntax
      synthesizeSyntheticMVarsNoPostponing
      let instantiated ← instantiateMVars elaborated
      if instantiated.hasExprMVar then
        throwError "R7_OPEN_EXPECTATION {name}"
      let closed ← levelMVarToParam instantiated
      pure (closed, (← getLevelNames).reverse)
    if levels != expectedLevels || actual.levelParams != expectedLevels then
      throwError "R7_UNIVERSE_MISMATCH {name}"
    if expected.hasMVar || expected.hasLevelMVar then
      throwError "R7_OPEN_EXPECTATION {name}"
    if !(← Meta.isDefEq actual.type expected) then
      throwError "R7_TYPE_MISMATCH {name}\nActual: {actual.type}\nExpected: {expected}"
    let closed ← instantiateMVars expected
    if closed.hasMVar || closed.hasLevelMVar then
      throwError "R7_OPEN_EXPECTATION {name}"
    if binders actual.type != binders closed then
      throwError "R7_BINDER_MODE_MISMATCH {name}"
    logInfo m!"R7_TYPE_VERIFIED {name}"
    logInfo m!"R7_UNIVERSES_VERIFIED {name}"
  let badAll ← elabType (← `(∀ (scope : ConnectedFabric.Scope) (memory : Memory)
    (coherent : Coherent scope memory) (requests : List (ULift.{3} Request)),
    (runtimeContract scope).outcome memory requests =
      ConstitutiveExecution.run (projectMemory scope memory) requests))
  let badMinimal ← elabType (← `(∀ (scope : ConnectedFabric.Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) (sameLive : one.live = two.live),
    projectMemory scope one = projectMemory scope two ↔
      ∀ requests, ConstitutiveExecution.run (projectMemory scope one) requests =
        ConstitutiveExecution.run (projectMemory scope two) requests))
  for (name, bad) in #[
      (`ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.all_sources_exact, badAll),
      (`ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.minimality, badMinimal)] do
    let actual ← getConstInfo name
    if ← Meta.isDefEq actual.type bad then
      throwError "R7_NARROWING_ACCEPTED {name}"
    logInfo m!"R7_NARROWING_REJECTED {name}"

theorem gate_domain (scope : ConnectedFabric.Scope) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests =
      ConstitutiveExecution.run (projectMemory scope memory) requests :=
  ConstitutiveExecution.all_sources_exact scope memory requests

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R7StatementTypes
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R7StatementTypes.gate_domain
/- AXIOM_AUDIT_END -/
