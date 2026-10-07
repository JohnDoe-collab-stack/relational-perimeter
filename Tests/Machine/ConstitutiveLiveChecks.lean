import RelationalPerimeter.Computation.Machine.ConstitutiveLiveExecution
import Tests.Machine.R4ContractChecks
import Tests.Machine.ReducedLiveChecks
/-! R5 client checks, on the unchanged domains. Runtime calls use the new
constitutive path; the former path is only the proved correspondence reference. -/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures
open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open ConstitutiveDiscovery

theorem clause_from_received (front : Frontier) :
    (measuredClause front.generation front.searchSeed front.seedExact).value =
      (receivedDecoys front.generation.target front.generation.generated).clause := rfl

theorem current_formation_consumed {P : CircularPresentation} {source : PositiveConstitution P}
    (target : PositiveConstitution P) (step : GeneratedStep source target) :
    receivedDecoys target step = emitFormation step.integratesCurrentDifference.layer.formationTerm
      (previousFormations target) := rfl

theorem formed_clause {P : CircularPresentation} {cursor : PerimeterCursor P}
    (witness : CompatibleExplicitation P cursor) (previous : Decoys) :
    (emitFormation (.admissible witness) previous).clause =
      Literal.positive (previous.last + 2) :: Literal.positive (previous.last + 1) :: previous.clause := rfl

theorem candidate_root_agreement (front : Frontier) :
    (extraction front).operationalRoot =
      (measuredGeneratedExtractionFromSeed front.generation.full front.searchSeed front.seedExact).operationalRoot :=
  congrArg GeneratedExtractionBundle.operationalRoot (extraction_exact front)

theorem actual_kernel (front : Frontier) :
    (ConstitutiveDiscovery.discover front).candidates =
      (filterCandidatesByProvenance front.provenance (extraction front).extraction.candidates).retained := rfl

theorem request_pair {scope : Scope} (memory : Runtime scope) (request : ULift.{3} Request)
    (rest : List (ULift.{3} Request)) :
    (ConstitutiveExecution.run memory (request :: rest)).tail =
      ConstitutiveExecution.run (ConstitutiveExecution.perform memory request.down).1 rest := rfl

theorem unchanged_source_domain (scope : Scope) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests =
      ConstitutiveExecution.run (projectMemory scope memory) requests :=
  ConstitutiveExecution.all_sources_exact scope memory requests

theorem unchanged_rich_domain (scope : Scope) (frame : Frame)
    (requests : List (ULift.{3} Request)) :
    (sourceContract scope).outcome frame requests =
      ConstitutiveExecution.run (projectMemory scope (project scope frame)) requests :=
  ConstitutiveExecution.rich_sources_exact scope frame requests

theorem no_equal_live_premise (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) :
    projectMemory scope one = projectMemory scope two ↔
      ∀ requests, ConstitutiveExecution.run (projectMemory scope one) requests =
        ConstitutiveExecution.run (projectMemory scope two) requests :=
  ConstitutiveExecution.minimality scope first second

theorem arbitrary_realization_type3 {scope : Scope} {Other : Type 3}
    (other : ExactRealization (runtimeContract scope) Other) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : other.project one = other.project two) :
    projectMemory scope one = projectMemory scope two :=
  ConstitutiveExecution.any_realization other first second same

theorem refusal_keeps_tail {scope : Scope} (memory : Runtime scope) (left right : Signals)
    (wrong : pulseFits scope left right = false) (rest : List (ULift.{3} Request)) :
    ConstitutiveExecution.run memory (⟨.pulse left right⟩ :: rest) =
      .step (readRuntime memory) false .refused (ConstitutiveExecution.run memory rest) :=
  ConstitutiveExecution.refusal_continues memory left right wrong rest

theorem forward_return (scope : Scope) (memory : Memory) (request : ULift.{3} Request)
    (witness : (runtimeContract scope).Allow memory request) :
    (ConstitutiveExecution.realization scope).backward memory request
      ((ConstitutiveExecution.realization scope).forward memory request witness) = witness := rfl

theorem backward_return (scope : Scope) (memory : Memory) (request : ULift.{3} Request)
    (witness : (ConstitutiveExecution.contract scope).Allow (projectMemory scope memory) request) :
    (ConstitutiveExecution.realization scope).forward memory request
      ((ConstitutiveExecution.realization scope).backward memory request witness) = witness := rfl

theorem validation_is_received {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    (ValidatedScheduleExecution.executeValidation validation).search = validation.search :=
  ValidatedScheduleExecution.executeValidation_search validation

def closedLive : LiveContinuation.Memory :=
  LiveContinuation.project (UnifiedMaster.publicInstance 0).cursor

def incoherentMemory : Memory := ⟨closedLive, [⟨false⟩], .shared []⟩

theorem genuinely_incoherent : ¬ Coherent [] incoherentMemory := by
  intro coherent
  exact Nat.noConfusion coherent.1

theorem incoherent_sources_exact (requests : List (ULift.{3} Request)) :
    (runtimeContract []).outcome incoherentMemory requests =
      ConstitutiveExecution.run (projectMemory [] incoherentMemory) requests :=
  ConstitutiveExecution.all_sources_exact [] incoherentMemory requests

def coherentMemory : Memory := ⟨closedLive, [], .shared []⟩
def differentLiveMemory : Memory :=
  { coherentMemory with live := additionalDiagnostic coherentMemory.live }

theorem closed_coherent_pair : Coherent [] coherentMemory ∧ Coherent [] differentLiveMemory :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem genuinely_different_live : differentLiveMemory.live ≠ coherentMemory.live :=
  diagnostics_are_distinct closedLive

theorem different_live_minimality :
    projectMemory [] coherentMemory = projectMemory [] differentLiveMemory ↔
      ∀ requests, ConstitutiveExecution.run (projectMemory [] coherentMemory) requests =
        ConstitutiveExecution.run (projectMemory [] differentLiveMemory) requests :=
  ConstitutiveExecution.minimality [] closed_coherent_pair.1 closed_coherent_pair.2

theorem closed_empty_scope (requests : List (ULift.{3} Request)) :
    (runtimeContract []).outcome coherentMemory requests =
      ConstitutiveExecution.run (projectMemory [] coherentMemory) requests :=
  ConstitutiveExecution.all_sources_exact [] coherentMemory requests

theorem closed_repeated_scope (requests : List (ULift.{3} Request)) :
    (runtimeContract [Channel.singleton 0, Channel.singleton 0]).outcome coherentMemory requests =
      ConstitutiveExecution.run
        (projectMemory [Channel.singleton 0, Channel.singleton 0] coherentMemory) requests :=
  ConstitutiveExecution.all_sources_exact _ coherentMemory requests

theorem closed_finder_failure :
    (searchMeasuredRelation 0 (GeneratedStructuralBranchContext.root [[Literal.positive 0]])
      (GeneratedStructuralBranchContext.root [[Literal.positive 0]])).result = none := rfl

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.clause_from_received
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.current_formation_consumed
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.formed_clause
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.candidate_root_agreement
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.actual_kernel
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.request_pair
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.unchanged_source_domain
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.unchanged_rich_domain
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.no_equal_live_premise
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.arbitrary_realization_type3
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.refusal_keeps_tail
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.forward_return
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.backward_return
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.validation_is_received
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.closedLive
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.incoherentMemory
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.genuinely_incoherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.incoherent_sources_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.coherentMemory
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.differentLiveMemory
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.closed_coherent_pair
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.genuinely_different_live
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.different_live_minimality
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.closed_empty_scope
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.closed_repeated_scope
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.R5Checks.closed_finder_failure
/- AXIOM_AUDIT_END -/
