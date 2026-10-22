import RelationalPerimeter.Agents.Neural.CheckedState

/-!
# Common production kernel for operational-contract transitions

The complete and incremental checkers must agree on what one admitted
transition executes, without sharing either a verdict or a target
certificate.  This module isolates that common semantic production.

A fixed kernel receives the exact checked source, the exact admitted
meta-contract transition, and transition material.  Its `produce` function
first constructs an execution object.  `targetOf` reads the successor from
that object, and the execution witness is indexed by that exact readout, so
callers cannot provide a target independently and attach an execution proof
afterwards.

The material is an associated family owned by the fixed kernel.  Received
proof-free updates will be decoded into this family by later checker layers;
the generic kernel itself is an honest conditional interface and contains no
decoder, acceptance verdict, state certificate, or checked update.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- Fixed semantic producer shared by every checker for one meta-contract.
`Material` names only the data required to execute a transition. `Production`
is the constitutive execution object, `produce` is the producer owned by this
boundary, `targetOf` reads its successor, and `execution` certifies that exact
readout from the exact checked source. -/
structure TransitionProductionKernel
    (constitution : ConstitutiveMetaContract) : Type 6 where
  Material : constitution.Contract -> constitution.Contract -> Type 3
  Production :
    {currentContract nextContract : constitution.Contract} ->
      (current : CheckedAgent constitution currentContract) ->
      (transition : OperationalContractTransition constitution
        currentContract nextContract) ->
      Material currentContract nextContract ->
      Type 3
  produce :
    {currentContract nextContract : constitution.Contract} ->
      (current : CheckedAgent constitution currentContract) ->
      (transition : OperationalContractTransition constitution
        currentContract nextContract) ->
      (material : Material currentContract nextContract) ->
      Production current transition material
  targetOf :
    {currentContract nextContract : constitution.Contract} ->
      (current : CheckedAgent constitution currentContract) ->
      (transition : OperationalContractTransition constitution
        currentContract nextContract) ->
      (material : Material currentContract nextContract) ->
      Production current transition material ->
      ReconfiguredExecutionState
        (constitution.operational nextContract).family
  execution :
    {currentContract nextContract : constitution.Contract} ->
      (current : CheckedAgent constitution currentContract) ->
      (transition : OperationalContractTransition constitution
        currentContract nextContract) ->
      (material : Material currentContract nextContract) ->
      (production : Production current transition material) ->
      constitution.ExecutedStateTransition transition.permission
        current.state (targetOf current transition material production)

/-- One execution produced by the fixed kernel.  All material dependencies
are indices.  The private constructor prevents a client from replacing the
kernel's execution witness with an independently assembled one. -/
structure ExecutedTransitionProduction
    {constitution : ConstitutiveMetaContract}
    (kernel : TransitionProductionKernel constitution)
    {currentContract nextContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    (transition : OperationalContractTransition constitution
      currentContract nextContract)
    (material : kernel.Material currentContract nextContract) : Type 5 where
  private mk ::
  production : kernel.Production current transition material
  execution : constitution.ExecutedStateTransition transition.permission
    current.state
      (kernel.targetOf current transition material production)

/-- Execute the unique target-producing function installed in the kernel.
Neither a successor nor a certificate is accepted as an argument. -/
def produceTransition
    {constitution : ConstitutiveMetaContract}
    (kernel : TransitionProductionKernel constitution)
    {currentContract nextContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    (transition : OperationalContractTransition constitution
      currentContract nextContract)
    (material : kernel.Material currentContract nextContract) :
    ExecutedTransitionProduction kernel current transition material :=
  let production := kernel.produce current transition material
  .mk production
    (kernel.execution current transition material production)

/-- The successor exposed by a production is definitionally the value
computed by the fixed kernel. -/
def ExecutedTransitionProduction.targetState
    {constitution : ConstitutiveMetaContract}
    {kernel : TransitionProductionKernel constitution}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    {transition : OperationalContractTransition constitution
      currentContract nextContract}
    {material : kernel.Material currentContract nextContract}
    (_production : ExecutedTransitionProduction kernel current transition
      material) :
    ReconfiguredExecutionState
      (constitution.operational nextContract).family :=
  kernel.targetOf current transition material _production.production

theorem ExecutedTransitionProduction.target_exact
    {constitution : ConstitutiveMetaContract}
    {kernel : TransitionProductionKernel constitution}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    {transition : OperationalContractTransition constitution
      currentContract nextContract}
    {material : kernel.Material currentContract nextContract}
    (production : ExecutedTransitionProduction kernel current transition
      material) :
    production.targetState =
      kernel.targetOf current transition material production.production := by
  rfl

/-! ## Closed public realization -/

/-- Proof-free material consumed by the public transition producer.  Its only
constructor exists at the admitted endpoint pair and carries the next received
requirement that drives the native reconfiguration. -/
inductive PublicTransitionMaterial :
    PublicOperationalContract -> PublicOperationalContract -> Type 3 where
  | reconfigure (nextInput : PublicRequirementInput) :
      PublicTransitionMaterial .initial .reconfigured

def publicTransitionProductionData
    {currentContract nextContract : PublicOperationalContract}
    (current : CheckedAgent publicConstitutiveMetaContract currentContract)
    (_transition : OperationalContractTransition publicConstitutiveMetaContract
      currentContract nextContract) :
    PublicTransitionMaterial currentContract nextContract ->
      Type 3
  | .reconfigure nextInput =>
      ReconfiguredCausalStage publicReconfigurationBuilder
        publicAgentActionChannel publicReconfigurationCertificateForState
        current.state nextInput

def publicProduceTransitionData
    {currentContract nextContract : PublicOperationalContract}
    (current : CheckedAgent publicConstitutiveMetaContract currentContract)
    (transition : OperationalContractTransition publicConstitutiveMetaContract
      currentContract nextContract) :
    (material : PublicTransitionMaterial currentContract nextContract) ->
      publicTransitionProductionData current transition material := by
  intro material
  cases material with
  | reconfigure nextInput =>
      exact executeReconfiguredCausalStage publicReconfigurationBuilder
        publicAgentActionChannel publicReconfigurationCertificateForState
        current.state nextInput

def publicProducedTransitionTarget
    {currentContract nextContract : PublicOperationalContract}
    (current : CheckedAgent publicConstitutiveMetaContract currentContract)
    (transition : OperationalContractTransition publicConstitutiveMetaContract
      currentContract nextContract)
    (material : PublicTransitionMaterial currentContract nextContract)
    (production : publicTransitionProductionData current transition material) :
    ReconfiguredExecutionState
      (publicOperationalContract nextContract).family := by
  cases material with
  | reconfigure nextInput =>
      exact production.action.targetState

def publicProducedTransitionExecution
    {currentContract nextContract : PublicOperationalContract}
    (current : CheckedAgent publicConstitutiveMetaContract currentContract)
    (transition : OperationalContractTransition publicConstitutiveMetaContract
      currentContract nextContract)
    (material : PublicTransitionMaterial currentContract nextContract)
    (production : publicTransitionProductionData current transition material) :
    PublicExecutedContractStateTransition transition.permission current.state
      (publicProducedTransitionTarget current transition material
        production) := by
  cases material with
  | reconfigure nextInput =>
      cases transition.permission
      change PublicExecutedContractStateTransition
        PublicContractTransitionPermission.executeReconfiguration
        current.state production.action.targetState
      rw [production.actionExact]
      exact .execute current.state nextInput

/-- The public semantic kernel closes the generic interface with the actual
reconfigured action.  The target is computed from the checked source and the
received next requirement; it is not read from the target artifact. -/
def publicTransitionProductionKernel :
    TransitionProductionKernel publicConstitutiveMetaContract where
  Material := PublicTransitionMaterial
  Production := publicTransitionProductionData
  produce := publicProduceTransitionData
  targetOf := publicProducedTransitionTarget
  execution := publicProducedTransitionExecution

def publicReferenceTransitionMaterial :
    publicTransitionProductionKernel.Material .initial .reconfigured :=
  .reconfigure publicSubstantiveNext

/-- Common execution consumed by both complete and incremental public update
paths. -/
def publicReferenceTransitionProduction :
    ExecutedTransitionProduction publicTransitionProductionKernel
      publicInitialCheckedAgent publicOperationalTransition
      publicReferenceTransitionMaterial :=
  produceTransition publicTransitionProductionKernel publicInitialCheckedAgent
    publicOperationalTransition publicReferenceTransitionMaterial

theorem publicReferenceTransitionProduction_target_exact :
    publicReferenceTransitionProduction.targetState =
      publicReferenceUpdatedState := by
  change publicReferenceTransitionProduction.production.action.targetState =
    publicReferenceUpdateExecution.targetState
  rw [publicReferenceTransitionProduction.production.actionExact]
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.TransitionProductionKernel
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.produceTransition
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedTransitionProduction.targetState
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedTransitionProduction.target_exact
#print axioms ConstitutiveSearch.NeuralAgent.PublicTransitionMaterial
#print axioms ConstitutiveSearch.NeuralAgent.publicTransitionProductionData
#print axioms ConstitutiveSearch.NeuralAgent.publicProduceTransitionData
#print axioms ConstitutiveSearch.NeuralAgent.publicProducedTransitionTarget
#print axioms ConstitutiveSearch.NeuralAgent.publicProducedTransitionExecution
#print axioms ConstitutiveSearch.NeuralAgent.publicTransitionProductionKernel
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceTransitionProduction_target_exact
/- AXIOM_AUDIT_END -/
