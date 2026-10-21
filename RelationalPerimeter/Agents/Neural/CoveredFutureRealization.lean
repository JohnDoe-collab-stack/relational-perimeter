import RelationalPerimeter.Agents.Neural.FiniteCausalBasis

/-!
# Exact realization of every covered finite future

This module only packages the local simulation laws required by the existing
`ExactRealization` interface.  It introduces no second future semantics.  The
generic all-futures theorem is obtained from `ExactRealization.outcome_exact`,
whose induction is already over the complete finite request list.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures

universe u v

/-- The seven local laws from which an exact realization is assembled. -/
structure FutureContractSimulationData
    {Source Reduced Input : Type u}
    {Event Observation : Type v}
    (sourceContract : FutureContract Source Input Event Observation)
    (reducedContract : FutureContract Reduced Input Event Observation)
    (project : Source -> Reduced) where
  forward : forall source input,
    sourceContract.Allow source input ->
      reducedContract.Allow (project source) input
  backward : forall source input,
    reducedContract.Allow (project source) input ->
      sourceContract.Allow source input
  backwardForward : forall source input witness,
    backward source input (forward source input witness) = witness
  forwardBackward : forall source input witness,
    forward source input (backward source input witness) = witness
  nextExact : forall source input,
    project (sourceContract.next source input) =
      reducedContract.next (project source) input
  eventExact : forall source input,
    sourceContract.event source input =
      reducedContract.event (project source) input
  readExact : forall source,
    sourceContract.read source = reducedContract.read (project source)

def FutureContractSimulationData.toExactRealization
    {Source Reduced Input : Type u}
    {Event Observation : Type v}
    {sourceContract : FutureContract Source Input Event Observation}
    {reducedContract : FutureContract Reduced Input Event Observation}
    {project : Source -> Reduced}
    (simulation : FutureContractSimulationData
      sourceContract reducedContract project) :
    ExactRealization sourceContract Reduced where
  reduced := reducedContract
  project := project
  forward := simulation.forward
  backward := simulation.backward
  backward_forward := simulation.backwardForward
  forward_backward := simulation.forwardBackward
  next_exact := simulation.nextExact
  event_exact := simulation.eventExact
  read_exact := simulation.readExact

/-- Existing exact realizations can be exposed as their local simulation laws
without changing either contract or reconstructing their runtime. -/
def FutureContractSimulationData.ofExactRealization
    {Source Reduced Input : Type u}
    {Event Observation : Type v}
    {sourceContract : FutureContract Source Input Event Observation}
    (realization : ExactRealization sourceContract Reduced) :
    FutureContractSimulationData sourceContract realization.reduced
      realization.project where
  forward := realization.forward
  backward := realization.backward
  backwardForward := realization.backward_forward
  forwardBackward := realization.forward_backward
  nextExact := realization.next_exact
  eventExact := realization.event_exact
  readExact := realization.read_exact

/-- The local laws preserve the outcome of every finite request list. -/
theorem simulation_preserves_every_finite_future
    {Source Reduced Input : Type u}
    {Event Observation : Type v}
    {sourceContract : FutureContract Source Input Event Observation}
    {reducedContract : FutureContract Reduced Input Event Observation}
    {project : Source -> Reduced}
    (simulation : FutureContractSimulationData
      sourceContract reducedContract project)
    (source : Source)
    (requests : List Input) :
    sourceContract.outcome source requests =
      reducedContract.outcome (project source) requests :=
  simulation.toExactRealization.outcome_exact source requests

/-- A contract-indexed future realization keeps the exact contract carried by
the operational contract and records only its reduced carrier and local laws. -/
structure CoveredFutureRealization (contract : ConstitutiveContract) : Type 4 where
  ReducedMemory : Type 3
  reducedContract : FutureContract ReducedMemory contract.FutureInput
    contract.FutureEvent contract.FutureObservation
  project : contract.FutureSource -> ReducedMemory
  simulation : FutureContractSimulationData contract.futureContract
    reducedContract project

def CoveredFutureRealization.exact
    {contract : ConstitutiveContract}
    (realization : CoveredFutureRealization contract) :
    ExactRealization contract.futureContract realization.ReducedMemory :=
  realization.simulation.toExactRealization

theorem CoveredFutureRealization.everyFiniteFuture
    {contract : ConstitutiveContract}
    (realization : CoveredFutureRealization contract)
    (source : contract.FutureSource)
    (requests : List contract.FutureInput) :
    contract.futureContract.outcome source requests =
      realization.reducedContract.outcome (realization.project source)
        requests :=
  simulation_preserves_every_finite_future realization.simulation source
    requests

/-! ## Closed public realization -/

def publicOperationalFutureSimulationData : FutureContractSimulationData
    PublicReconfiguredOperationalContract.futureContract
    reconfiguredOperationalMemoryFutureContract
    ReconfiguredExecutionState.memory :=
  FutureContractSimulationData.ofExactRealization
    publicReconfiguredOperationalMemoryRealization

def publicCoveredFutureRealization :
    CoveredFutureRealization PublicReconfiguredOperationalContract where
  ReducedMemory := Agent.Memory
  reducedContract := reconfiguredOperationalMemoryFutureContract
  project := ReconfiguredExecutionState.memory
  simulation := publicOperationalFutureSimulationData

/-- Every finite future covered by the reconfigured operational contract is
preserved exactly by the already established operational-memory projection. -/
theorem publicOperationalContract_preserves_every_finite_future
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (requests : List (ULift.{3} Agent.Request)) :
    PublicReconfiguredOperationalContract.futureContract.outcome source
        requests =
      reconfiguredOperationalMemoryFutureContract.outcome source.memory
        requests :=
  publicCoveredFutureRealization.everyFiniteFuture source requests

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.FutureContractSimulationData
#print axioms ConstitutiveSearch.NeuralAgent.FutureContractSimulationData.toExactRealization
#print axioms ConstitutiveSearch.NeuralAgent.FutureContractSimulationData.ofExactRealization
#print axioms ConstitutiveSearch.NeuralAgent.simulation_preserves_every_finite_future
#print axioms ConstitutiveSearch.NeuralAgent.CoveredFutureRealization
#print axioms ConstitutiveSearch.NeuralAgent.CoveredFutureRealization.exact
#print axioms ConstitutiveSearch.NeuralAgent.CoveredFutureRealization.everyFiniteFuture
#print axioms ConstitutiveSearch.NeuralAgent.publicOperationalFutureSimulationData
#print axioms ConstitutiveSearch.NeuralAgent.publicCoveredFutureRealization
#print axioms ConstitutiveSearch.NeuralAgent.publicOperationalContract_preserves_every_finite_future
/- AXIOM_AUDIT_END -/
