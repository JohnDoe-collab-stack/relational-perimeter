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
    (growth : UnifiedMaster.Growth master.origin master.execution master.cursor master.endpoint_exact extra) :
    growth.grown.count = resolutionLength input + extra := growth.count_exact

theorem actual_resource_reads {input extra : Nat} (master : UnifiedMaster.Instance input)
    (growth : UnifiedMaster.Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    {kind : MasterResources.Kind} (ref : Resources.Ref master.origin.kinds kind) :
    growth.suffix.finish.support.read ((master.referencesThrough growth).references ref) =
      master.origin.support.read ref := master.referencesThrough_read growth ref

theorem actual_resource_distinction {input extra : Nat} (master : UnifiedMaster.Instance input)
    (growth : UnifiedMaster.Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    {kind : MasterResources.Kind} (first second : Resources.Ref master.origin.kinds kind)
    (same : (master.referencesThrough growth).references first =
      (master.referencesThrough growth).references second) : first = second :=
  (master.referencesThrough growth).injective first second same

theorem actual_resource_composition {depth count extra more : Nat}
    {assignment : SequentialAssignment depth} {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {old : CausalOperationalExecutionHistory (_count := count) state context}
    {origin : MasterResources.Cursor}
    {cursor : MasterResources.Cursor} {boundary : cursor.boundary = MasterResources.endpoint old}
    (one : UnifiedMaster.Growth origin old cursor boundary extra)
    (two : UnifiedMaster.Growth origin one.grown.history one.suffix.finish one.endpoint_exact more)
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

/-- These guarantees are consumed through the closed certificate itself. -/
theorem certified_regime {input : Nat} (certificate : UnifiedMaster.Certificate input) :
    certificate.master.regime = certificate.master.normalization.operationalRegime :=
  certificate.facts.regimeExact

theorem certified_restart {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) :
    (certificate.master.checkpoint p).live = LiveContinuation.project certificate.master.cursor :=
  certificate.facts.restartCursorExact p

theorem certified_inspection {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) (query : ProducedContinuation.Query) :
    (ProducedContinuation.executeInput (certificate.master.checkpoint p) (.inspect query)).2 =
      .observed query (ProducedContinuation.readTarget query
        (ProducedContinuation.targetReaders certificate.master.reduction
          (certificate.master.normalization.target p))) :=
  certificate.facts.runtimeInspectEvent p query

theorem certified_rejection {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) (query : ProducedContinuation.Query)
    (outside : resolutionLength input ≤ query.slot) :
    ¬ Nonempty (ProducedContinuation.allow (certificate.master.checkpoint p) (.inspect query)) :=
  fun admitted => Nat.not_lt_of_ge outside
    ((certificate.facts.inspectAdmission (certificate.master.checkpoint p) query).mp admitted)

theorem certified_growth {input : Nat} (certificate : UnifiedMaster.Certificate input) (extra : Nat) :
    HEq (certificate.master.grow extra).grown.history
      (MasterResources.executeWithReferences (extra + resolutionLength input) certificate.master.origin).history :=
  certificate.facts.growthOneRun extra

theorem certified_advance {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) (steps : Nat) :
    Nonempty (ProducedContinuation.allow (certificate.master.checkpoint p) (.advance steps)) :=
  certificate.facts.advanceAdmission p steps

theorem certified_source_advance {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) (steps : Nat) :
    Nonempty (ProducedContinuation.allow
      (ProducedContinuation.project (certificate.master.source p)) (.advance steps)) :=
  certificate.facts.sourceAdvanceAdmission p steps

theorem certified_request_admission {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles)
    (requests : List (ProducedContinuation.Input certificate.master.normalization)) :
    Nonempty (Continuation.Admitted ProducedContinuation.sourceNext
      (fun source input => ProducedContinuation.allow (ProducedContinuation.project source) input)
      (certificate.master.source p) requests) ↔
    Nonempty (Continuation.Admitted ProducedContinuation.next ProducedContinuation.allow
      (certificate.master.checkpoint p) requests) := certificate.facts.requestAdmission p requests

theorem certified_source_admission_return {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) {requests}
    (witness : Continuation.Admitted ProducedContinuation.sourceNext
      (fun source input => ProducedContinuation.allow (ProducedContinuation.project source) input)
      (certificate.master.source p) requests) :
    ProducedContinuation.all_requests_reflected (certificate.master.source p)
      (ProducedContinuation.all_requests_admitted (certificate.master.source p) witness) = witness :=
  certificate.facts.sourceAdmissionReturn p witness

theorem certified_memory_admission_return {input : Nat} (certificate : UnifiedMaster.Certificate input)
    (p : RoleOccurrenceProfile certificate.master.roles) {requests}
    (witness : Continuation.Admitted ProducedContinuation.next ProducedContinuation.allow
      (certificate.master.checkpoint p) requests) :
    ProducedContinuation.all_requests_admitted (certificate.master.source p)
      (ProducedContinuation.all_requests_reflected (certificate.master.source p) witness) = witness :=
  certificate.facts.memoryAdmissionReturn p witness

theorem certified_references_injective {input : Nat} (certificate : UnifiedMaster.Certificate input)
    {kind : MasterResources.Kind} (first second : Resources.Ref certificate.master.origin.kinds kind)
    (same : certificate.master.references.references first = certificate.master.references.references second) :
    first = second := certificate.facts.referencesInjective first second same

theorem certified_growth_injective {input extra : Nat} (certificate : UnifiedMaster.Certificate input)
    (one : UnifiedMaster.Growth certificate.master.origin certificate.master.execution
      certificate.master.cursor certificate.master.endpoint_exact extra)
    {kind : MasterResources.Kind} (first second : Resources.Ref certificate.master.origin.kinds kind)
    (same : (certificate.master.referencesThrough one).references first =
      (certificate.master.referencesThrough one).references second) : first = second :=
  certificate.facts.growthReferencesInjective one first second same

theorem certified_composition {input extra more : Nat} (certificate : UnifiedMaster.Certificate input)
    (one : UnifiedMaster.Growth certificate.master.origin certificate.master.execution
      certificate.master.cursor certificate.master.endpoint_exact extra)
    (two : UnifiedMaster.Growth certificate.master.origin one.grown.history
      one.suffix.finish one.endpoint_exact more)
    {kind : MasterResources.Kind} (ref : Resources.Ref certificate.master.origin.kinds kind)
    (profile : RoleOccurrenceProfile certificate.master.roles)
    (obligation : Extension.Obligation (CertifiedRoleGrouping.rules certificate.master.statuses)) :
    (certificate.master.references.compose (one.referencesThrough two)).references ref =
      two.suffix.references.references ((certificate.master.referencesThrough one).references ref) ∧
    two.suffix.finish.support.read
      ((certificate.master.references.compose (one.referencesThrough two)).references ref) =
      certificate.master.origin.support.read ref ∧
    (one.grown.historical.compose two.grown.historical).embedding profile =
      two.grown.historical.embedding (one.grown.historical.embedding profile) ∧
    (one.grown.historical.compose two.grown.historical).extension.obligation obligation =
      two.grown.historical.extension.obligation (one.grown.historical.extension.obligation obligation) :=
  ⟨certificate.facts.growthReferencesCompose one two ref,
    certificate.facts.growthComposedReads one two ref,
    certificate.facts.growthProfilesCompose one two profile,
    certificate.facts.growthObligationsCompose one two obligation⟩

/-- A different resource origin is legitimate only under its own index. -/
def produced_prefix (count : Nat) (origin : MasterResources.Cursor) :
    MasterResources.ProducedPrefix origin
      (MasterResources.executeWithReferences count origin).history
      (MasterResources.executeWithReferences count origin).finish := ⟨rfl, HEq.rfl, rfl⟩

def preloaded_origin (origin : MasterResources.Cursor) : MasterResources.Cursor :=
  let support := origin.support.extend (MasterResources.discover origin.source)
  ⟨origin.depth, origin.assignment, _, support, .prior origin.source,
    .prior origin.past, .prior origin.fresh⟩

theorem preloaded_boundary (origin : MasterResources.Cursor) :
    (preloaded_origin origin).boundary = origin.boundary := rfl

theorem preloaded_origin_distinct (origin : MasterResources.Cursor) :
    preloaded_origin origin ≠ origin := by
  intro same
  have lengths := congrArg (fun cursor : MasterResources.Cursor => cursor.kinds.length) same
  exact Nat.ne_of_gt (Nat.lt_succ_self origin.kinds.length) lengths

theorem foreign_zero_prefix_rejected (origin : MasterResources.Cursor) :
    ¬ Nonempty (MasterResources.ProducedPrefix origin
      (MasterResources.executeWithReferences 0 origin).history (preloaded_origin origin)) := by
  intro witness
  cases witness with
  | intro produced => exact preloaded_origin_distinct origin produced.cursorExact

private theorem cancel_resource_suffix : (suffix first second : Nat) →
    first + suffix = second + suffix → first = second
  | 0, _, _, same => same
  | suffix + 1, first, second, same =>
      cancel_resource_suffix suffix first second (congrArg Nat.pred same)

theorem foreign_prefix_rejected (origin : MasterResources.Cursor) (count : Nat) :
    ¬ Nonempty (MasterResources.ProducedPrefix origin
      (MasterResources.executeWithReferences count origin).history
      (MasterResources.executeWithReferences count (preloaded_origin origin)).finish) := by
  intro witness
  cases witness with
  | intro produced =>
    have lengths := congrArg (fun cursor : MasterResources.Cursor => cursor.kinds.length) produced.cursorExact
    rw [MasterResources.execute_finish_resource_length,
      MasterResources.execute_finish_resource_length] at lengths
    change origin.kinds.length + 1 + 7 * count = origin.kinds.length + 7 * count at lengths
    exact Nat.ne_of_gt (Nat.lt_succ_self origin.kinds.length)
      (cancel_resource_suffix (7 * count) _ _ lengths)

def preloaded_growth (origin : MasterResources.Cursor) (count extra : Nat) :=
  let start := preloaded_origin origin
  let execution := MasterResources.executeWithReferences count start
  UnifiedMaster.resource_history_extension start execution.history execution.finish
    (MasterResources.executeWithReferences_endpoint count start).symm extra (produced_prefix count start)

theorem growth_keeps_produced_cursor {input : Nat} (master : UnifiedMaster.Instance input) (extra : Nat) :
    (master.grow extra).suffix.finish =
      (MasterResources.executeWithReferences (master.grow extra).grown.count
        (master.grow extra).producedPrefix.origin).finish :=
  (master.grow extra).producedPrefix.cursorExact

#guard actual_checkpoint.live.depth == 1
#guard actual_checkpoint.readers.length == 1
#guard (ProducedContinuation.readTarget ProducedContinuation.publicFirstQuery actual_checkpoint.readers).isSome
#guard actual_resume.1.live.depth == 2
#guard actual_resume.2.length == 2
#guard actual_growth.grown.count == 2
#guard actual_growth.suffix.finish.depth == 2
#guard actual_growth_twice.grown.count == 3
#guard actual_growth_twice.suffix.finish.depth == 3
#guard (preloaded_growth (ProducedContinuation.publicOrigin 0) 0 0).grown.count == 0
#guard (preloaded_growth (ProducedContinuation.publicOrigin 0) 0 1).grown.count == 1

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
#print axioms UnifiedMasterTests.certified_regime
#print axioms UnifiedMasterTests.certified_restart
#print axioms UnifiedMasterTests.certified_inspection
#print axioms UnifiedMasterTests.certified_rejection
#print axioms UnifiedMasterTests.certified_growth
#print axioms UnifiedMasterTests.certified_advance
#print axioms UnifiedMasterTests.certified_source_advance
#print axioms UnifiedMasterTests.certified_request_admission
#print axioms UnifiedMasterTests.certified_source_admission_return
#print axioms UnifiedMasterTests.certified_memory_admission_return
#print axioms UnifiedMasterTests.certified_references_injective
#print axioms UnifiedMasterTests.certified_growth_injective
#print axioms UnifiedMasterTests.certified_composition
#print axioms UnifiedMasterTests.produced_prefix
#print axioms UnifiedMasterTests.preloaded_origin
#print axioms UnifiedMasterTests.preloaded_boundary
#print axioms UnifiedMasterTests.preloaded_origin_distinct
#print axioms UnifiedMasterTests.foreign_zero_prefix_rejected
#print axioms UnifiedMasterTests.foreign_prefix_rejected
#print axioms UnifiedMasterTests.preloaded_growth
#print axioms UnifiedMasterTests.growth_keeps_produced_cursor
/- AXIOM_AUDIT_END -/
