import RelationalPerimeter.Agents.Neural.ExecutableMetaContract

/-!
# Checked neural states and checked updates

`CheckedAgent` exposes only states carrying the exact constitutive certificate
for their fixed meta-contract member.  `CheckedUpdate` then links such a state
to the next checked state through both the admitted contract transition and
the executed state transition owned by the same meta-contract.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- An executable state that has already been certified under one named member
of the fixed meta-contract. -/
structure CheckedAgent
    (constitution : ConstitutiveMetaContract)
    (contractName : constitution.Contract) : Type 4 where
  private mk ::
  contractAdmitted : constitution.Admits contractName
  artifact : DecodedNeuralArtifact (constitution.operational contractName)
  state : ReconfiguredExecutionState
    (constitution.operational contractName).family
  certificate : StateConstitutiveCertificate
    (constitution.operational contractName) artifact state

/-- The public constructor consumes the exact certificate indexed by the
artifact and state returned in the resulting checked agent. -/
def certifyCheckedAgent
    {constitution : ConstitutiveMetaContract}
    {contractName : constitution.Contract}
    (contractAdmitted : constitution.Admits contractName)
    (artifact : DecodedNeuralArtifact (constitution.operational contractName))
    (state : ReconfiguredExecutionState
      (constitution.operational contractName).family)
    (certificate : StateConstitutiveCertificate
      (constitution.operational contractName) artifact state) :
    CheckedAgent constitution contractName :=
  .mk contractAdmitted artifact state certificate

/-- A checked update cannot choose its own successor.  Its successor is
already a checked agent, while `execution` is indexed by the exact source and
target states and by the exact transition permission stored in `transition`.
-/
structure CheckedUpdate
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    (nextContract : constitution.Contract) : Type 4 where
  private mk ::
  next : CheckedAgent constitution nextContract
  transition : OperationalContractTransition constitution
    currentContract nextContract
  execution : constitution.ExecutedStateTransition transition.permission
    current.state next.state

/-- The only public constructor for a checked update requires the exact
meta-contract transition and its exact executed state transition. -/
def certifyCheckedUpdate
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (next : CheckedAgent constitution nextContract)
    (transition : OperationalContractTransition constitution
      currentContract nextContract)
    (execution : constitution.ExecutedStateTransition transition.permission
      current.state next.state) :
    CheckedUpdate current nextContract :=
  .mk next transition execution

/-- The successor certificate is definitionally the certificate carried by
the exact successor of the update. -/
def CheckedUpdate.nextCertificate
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (update : CheckedUpdate current nextContract) :
    StateConstitutiveCertificate (constitution.operational nextContract)
      update.next.artifact update.next.state :=
  update.next.certificate

/-- Every finite future of the exact successor remains available through the
successor's constitutive certificate. -/
theorem CheckedUpdate.nextPreservesEveryFiniteFuture
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (update : CheckedUpdate current nextContract)
    (requests : List (constitution.operational nextContract).FutureInput) :
    (constitution.operational nextContract).futureContract.outcome
        ((constitution.operational nextContract).futureSourceOfState
          update.next.state)
        requests =
      update.next.certificate.futureRealization.reducedContract.outcome
        (update.next.certificate.futureRealization.project
          ((constitution.operational nextContract).futureSourceOfState
            update.next.state)) requests :=
  update.next.certificate.everyFiniteFuture requests

/-! ## Closed public checked initial state -/

def publicInitialCheckedAgent :
    CheckedAgent publicConstitutiveMetaContract
      PublicOperationalContract.initial :=
  certifyCheckedAgent PublicContractAdmission.initial
    publicDecodedRequirementArtifact publicInitialCertifiedState
    publicInitialStateConstitutiveCertificate

theorem publicInitialCheckedAgent_system_exact :
    publicInitialCheckedAgent.state.system =
      publicInitialCheckedAgent.artifact.system :=
  publicInitialCheckedAgent.certificate.systemExact

theorem publicInitialCheckedAgent_input_decided :
    Nonempty (Listed publicInitialCheckedAgent.state.input
      publicInitialCheckedAgent.certificate.basis.currentInputs) :=
  ⟨publicInitialCheckedAgent.certificate.inputInBasis⟩

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.certifyCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.CheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.certifyCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.CheckedUpdate.nextCertificate
#print axioms ConstitutiveSearch.NeuralAgent.CheckedUpdate.nextPreservesEveryFiniteFuture
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckedAgent_system_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckedAgent_input_decided
/- AXIOM_AUDIT_END -/
