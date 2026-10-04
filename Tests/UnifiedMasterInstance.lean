import RelationalPerimeter

/-! Public clients of the single resource execution. The code transport is a
readout of constituted roles, not a replacement for them. Scientific archives
and historical extensions do not belong to the restart memory. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace UnifiedMasterTests
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Grouping
open ConstitutiveSearch.Extensive ConstitutiveSearch.RelationalExtensive

theorem certificate_is_closed (input : Nat) :
    UnifiedMaster.Facts (UnifiedMaster.certificate input).master :=
  (UnifiedMaster.certificate input).facts

theorem certificate_uses_public_producer (input : Nat) :
    (UnifiedMaster.certificate input).master = UnifiedMaster.publicInstance input := rfl

theorem same_audited_execution (input : Nat) :
    (UnifiedMaster.publicInstance input).execution = publicCausalOperationalExecution input :=
  UnifiedMaster.public_execution_exact input

theorem same_class_carrier (input : Nat) :
    UnifiedMaster.binaryFamily.sourceCarrier (index := input) () =
      (UnifiedMaster.publicInstance input).carrier := rfl

theorem class_iff_direct (input : Nat) :
    (UnifiedMaster.publicInstance input).regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective (UnifiedMaster.publicInstance input).regime.carry :=
  BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
    UnifiedMaster.binaryFamily (index := input) () (UnifiedMaster.publicInstance input).regime

theorem code_return {input : Nat} (master : UnifiedMaster.Instance input)
    (p : RoleOccurrenceProfile master.roles) :
    master.code.backward (master.code.forward p) = p := master.code.forwardBackward p

theorem code_target_return {input : Nat} (master : UnifiedMaster.Instance input)
    (p : Binary.Profile (CertifiedRoleGrouping.roleShape master.roles)) :
    master.code.forward (master.code.backward p) = p := master.code.backwardForward p

theorem image_return {input : Nat} (master : UnifiedMaster.Instance input)
    (p : RolewiseObligation master.statuses.policy) :
    master.imageTransport.backward (master.imageTransport.forward p) = p :=
  master.imageTransport.forwardBackward p

theorem target_return {input : Nat} (master : UnifiedMaster.Instance input)
    (p : FiniteImage.Target master.groupingRules) :
    master.imageTransport.forward (master.imageTransport.backward p) = p :=
  master.imageTransport.backwardForward p

theorem produced_image_return {input : Nat} (master : UnifiedMaster.Instance input)
    (p : FiniteImage.Target master.groupingRules) :
    master.producedImageTransport.backward (master.producedImageTransport.forward p) = p :=
  master.producedImageTransport.forwardBackward p

theorem produced_value_return {input : Nat} (master : UnifiedMaster.Instance input)
    (p : master.regime.Obligation) :
    master.producedImageTransport.forward (master.producedImageTransport.backward p) = p :=
  master.producedImageTransport.backwardForward p

theorem image_carry_commutes {input : Nat} (master : UnifiedMaster.Instance input)
    (p : RoleOccurrenceProfile master.roles) :
    master.producedImageTransport.forward (FiniteImage.carry master.groupingRules p) =
      master.regime.carry p := master.producedImageTransport_carry p

theorem regime_does_not_identify_sources {input : Nat} (master : UnifiedMaster.Instance input) :
    master.distinctPair.left ≠ master.distinctPair.right ∧
    master.regime.carry master.distinctPair.left = master.regime.carry master.distinctPair.right :=
  ⟨master.distinctPair.distinct, master.distinctPair.carriedTogether⟩

theorem source_width {input : Nat} (master : UnifiedMaster.Instance input) :
    master.carrier.frontier.length = 2 ^ (input + 1) := master.source_width

theorem executed_width {input : Nat} (master : UnifiedMaster.Instance input) :
    master.regime.frontier.length = 1 := master.executed_width

theorem partial_width {input : Nat} (master : UnifiedMaster.Instance input)
    (history : RoleStatus.History master.roles) :
    (CertifiedRoleGrouping.composed history).frontier.length = 2 ^ history.pendingCount :=
  master.partial_width history

theorem head_objects_exact {input : Nat} (master : UnifiedMaster.Instance input) :
    master.execution.allHeadsExact master.origin.freshness := master.all_heads_exact

theorem same_restart (input : Nat) :
    (UnifiedMaster.publicInstance input).checkpoint
      (UnifiedMaster.publicInstance input).roles.headTransformedProfile =
        ProducedContinuation.publicStart input := UnifiedMaster.checkpoint_is_existing_restart input

theorem history_growth_preserves_sources (input extra : Nat)
    (p q : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles)
    (same : (UnifiedMaster.publicGrowth input extra).embedding p =
      (UnifiedMaster.publicGrowth input extra).embedding q) : p = q :=
  UnifiedMaster.public_growth_injective input extra p q same

theorem actual_growth_composes (input first second : Nat)
    (p : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles) :
    (UnifiedMaster.publicGrowthTwice input first second).embedding p =
      ((UnifiedMaster.publicContinuation input first).resume second).grown.historical.embedding
          ((UnifiedMaster.publicGrowth input first).embedding p) :=
  UnifiedMaster.public_growth_composes input first second p

theorem actual_growth_count {input extra : Nat} (master : UnifiedMaster.Instance input)
    (growth : UnifiedMaster.Growth master.execution master.cursor master.endpoint_exact extra) :
    growth.grown.count = resolutionLength input + extra := growth.count_exact

theorem actual_resource_reads {input extra : Nat} (master : UnifiedMaster.Instance input)
    (growth : UnifiedMaster.Growth master.execution master.cursor master.endpoint_exact extra)
    {kind : MasterResources.Kind} (ref : Resources.Ref master.origin.kinds kind) :
    growth.suffix.finish.support.read ((master.referencesThrough growth).references ref) =
      master.origin.support.read ref := master.referencesThrough_read growth ref

theorem actual_resource_distinction {input extra : Nat} (master : UnifiedMaster.Instance input)
    (growth : UnifiedMaster.Growth master.execution master.cursor master.endpoint_exact extra)
    {kind : MasterResources.Kind} (first second : Resources.Ref master.origin.kinds kind)
    (same : (master.referencesThrough growth).references first =
      (master.referencesThrough growth).references second) : first = second :=
  (master.referencesThrough growth).injective first second same

theorem actual_resource_composition {depth count extra more : Nat}
    {assignment : SequentialAssignment depth} {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {old : CausalOperationalExecutionHistory (_count := count) state context}
    {cursor : MasterResources.Cursor} {boundary : cursor.boundary = MasterResources.endpoint old}
    (one : UnifiedMaster.Growth old cursor boundary extra)
    (two : UnifiedMaster.Growth one.grown.history one.suffix.finish one.endpoint_exact more)
    {kind : MasterResources.Kind} (ref : Resources.Ref cursor.kinds kind) :
    (one.referencesThrough two).references ref =
      two.suffix.references.references (one.suffix.references.references ref) := rfl

def admission_preserved {input : Nat} (master : UnifiedMaster.Instance input)
    (p : RoleOccurrenceProfile master.roles) {requests : List (ProducedContinuation.Input master.normalization)}
    (admitted : Continuation.Admitted ProducedContinuation.sourceNext
      (fun source input => ProducedContinuation.allow (ProducedContinuation.project source) input)
      (master.source p) requests) :
    Continuation.Admitted ProducedContinuation.next ProducedContinuation.allow (master.checkpoint p) requests :=
  ProducedContinuation.all_requests_admitted (master.source p) admitted

def admission_reflected {input : Nat} (master : UnifiedMaster.Instance input)
    (p : RoleOccurrenceProfile master.roles) {requests : List (ProducedContinuation.Input master.normalization)}
    (admitted : Continuation.Admitted ProducedContinuation.next ProducedContinuation.allow
      (master.checkpoint p) requests) :
    Continuation.Admitted ProducedContinuation.sourceNext
      (fun source input => ProducedContinuation.allow (ProducedContinuation.project source) input)
      (master.source p) requests :=
  ProducedContinuation.all_requests_reflected (master.source p) admitted

theorem irreversible_profile_loss {input : Nat} (master : UnifiedMaster.Instance input) :
    ¬ (∃ recover : ProducedContinuation.Memory master.normalization → RoleOccurrenceProfile master.roles,
      ∀ p, recover (master.checkpoint p) = p) := master.profile_irrecoverable

def actual_checkpoint :=
  let master := UnifiedMaster.publicInstance 0
  master.checkpoint master.roles.headTransformedProfile

def actual_resume := ProducedContinuation.executeRequests actual_checkpoint
  [.advance 1, .inspect ProducedContinuation.publicFirstQuery]

def actual_growth :=
  let master := UnifiedMaster.publicInstance 0
  master.grow 1

def actual_growth_twice := actual_growth.resume 1

theorem resource_producer_pinned {input : Nat} (master : UnifiedMaster.Instance input) :
    HEq master.references
      (MasterResources.executeWithReferences (resolutionLength input) master.origin).references :=
  master.referencesExact

theorem runtime_events_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (p : RoleOccurrenceProfile master.roles) (requests : List (ProducedContinuation.Input master.normalization)) :
    (ProducedContinuation.executeRequests (master.checkpoint p) requests).2 =
      Continuation.events ProducedContinuation.sourceNext ProducedContinuation.sourceEvent (master.source p) requests :=
  (ProducedContinuation.executeRequests_events _ requests).trans (master.future_events_exact p requests).symm

#guard actual_checkpoint.live.depth == 1
#guard actual_checkpoint.readers.length == 1
#guard (ProducedContinuation.readTarget ProducedContinuation.publicFirstQuery actual_checkpoint.readers).isSome
#guard actual_resume.1.live.depth == 2
#guard actual_resume.2.length == 2
#guard actual_growth.grown.count == 2
#guard actual_growth.suffix.finish.depth == 2
#guard actual_growth_twice.grown.count == 3
#guard actual_growth_twice.suffix.finish.depth == 3

end UnifiedMasterTests
/- AXIOM_AUDIT_BEGIN -/
#print axioms UnifiedMasterTests.certificate_is_closed
#print axioms UnifiedMasterTests.certificate_uses_public_producer
#print axioms UnifiedMasterTests.same_audited_execution
#print axioms UnifiedMasterTests.same_class_carrier
#print axioms UnifiedMasterTests.class_iff_direct
#print axioms UnifiedMasterTests.code_return
#print axioms UnifiedMasterTests.code_target_return
#print axioms UnifiedMasterTests.image_return
#print axioms UnifiedMasterTests.target_return
#print axioms UnifiedMasterTests.produced_image_return
#print axioms UnifiedMasterTests.produced_value_return
#print axioms UnifiedMasterTests.image_carry_commutes
#print axioms UnifiedMasterTests.regime_does_not_identify_sources
#print axioms UnifiedMasterTests.source_width
#print axioms UnifiedMasterTests.executed_width
#print axioms UnifiedMasterTests.partial_width
#print axioms UnifiedMasterTests.head_objects_exact
#print axioms UnifiedMasterTests.same_restart
#print axioms UnifiedMasterTests.history_growth_preserves_sources
#print axioms UnifiedMasterTests.actual_growth_composes
#print axioms UnifiedMasterTests.actual_growth_count
#print axioms UnifiedMasterTests.actual_resource_reads
#print axioms UnifiedMasterTests.actual_resource_distinction
#print axioms UnifiedMasterTests.actual_resource_composition
#print axioms UnifiedMasterTests.admission_preserved
#print axioms UnifiedMasterTests.admission_reflected
#print axioms UnifiedMasterTests.irreversible_profile_loss
#print axioms UnifiedMasterTests.actual_checkpoint
#print axioms UnifiedMasterTests.actual_resume
#print axioms UnifiedMasterTests.actual_growth
#print axioms UnifiedMasterTests.actual_growth_twice
#print axioms UnifiedMasterTests.resource_producer_pinned
#print axioms UnifiedMasterTests.runtime_events_exact
/- AXIOM_AUDIT_END -/
