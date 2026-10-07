import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ProducedProfileContinuation
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleGroupingSemantics
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.HistoricalRoleGrouping

/-!
# One master execution and its scientific consumers

The resource executor produces one result. Roles, normalization, grouping,
operational obligations and restart memory are derived from that result.
The historical audited API remains a specification connected by erasure;
it is not a second executor called by this entry.

The binary family below reads these same roles. Its class theorem applies
directly to the executed regime, without a carrier adapter. Forgetting concerns
the consumed normalization profile under the explicit future contract, not
all chronological provenance. Scientific evidence is not restart memory.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster
open SAT Extensive RelationalExtensive ConstitutiveSearch.Grouping

/-- Positive resource execution; the equations pin its actual producer. -/
structure Instance (input : Nat) : Type 3 where
  origin : MasterResources.Cursor
  originExact : origin = ProducedContinuation.publicOrigin input
  executed : CausalOperationalExecutionHistory (_count := resolutionLength input)
    origin.state origin.context × MasterResources.Cursor
  executedExact : executed = MasterResources.execute (resolutionLength input) origin
  references : Resources.Support.Extension origin.support executed.2.support
  referencesExact : HEq references
    (MasterResources.executeWithReferences (resolutionLength input) origin).references

def publicInstance (input : Nat) : Instance input :=
  let origin := ProducedContinuation.publicOrigin input
  let resources := MasterResources.executeWithReferences (resolutionLength input) origin
  ⟨origin, rfl, (resources.history, resources.finish), rfl, resources.references, HEq.rfl⟩

namespace Instance
variable {input : Nat}

def execution (master : Instance input) := master.executed.1
def cursor (master : Instance input) := master.executed.2
def stagewise (master : Instance input) := master.execution.stagewiseDecomposition
def roles (master : Instance input) := master.stagewise.roles
def program (master : Instance input) := compileRoleHistory master.roles
def reduction (master : Instance input) := master.stagewise.reduction
def carrier (master : Instance input) := roleProfileFiniteCarrier master.roles
def normalization (master : Instance input) := executedCausalNormalization master.reduction
def regime (master : Instance input) := master.normalization.operationalRegime
def statuses (master : Instance input) := RoleStatus.ofStagewise master.stagewise
def groupingRules (master : Instance input) := CertifiedRoleGrouping.rules master.statuses
def groupingAction (master : Instance input) := CertifiedRoleGrouping.acceptanceAction master.statuses
def code (master : Instance input) := CertifiedRoleGrouping.code master.roles

def source (master : Instance input) (profile : RoleOccurrenceProfile master.roles) :=
  ProducedContinuation.produce (state := causalStateOfThreadedState master.origin.state)
    master.normalization master.cursor profile

def checkpoint (master : Instance input) (profile : RoleOccurrenceProfile master.roles) :=
  ProducedContinuation.project (master.source profile)

def continuation (master : Instance input) := ProducedContinuation.contract master.normalization

def imageTransport (master : Instance input) := CertifiedRoleGrouping.targetTransport master.statuses

/-- The normal-position image and the actual produced-value image are connected
only after the executed reduction has supplied its convergence. This inverse
returns a normal position; it does not reconstruct an original source profile
or invert a map on arbitrary continuations. -/
def producedImageTransport (master : Instance input) :
    ExactTypeTransport (FiniteImage.Target master.groupingRules) master.regime.Obligation where
  forward := fun target => master.regime.carry target.1
  backward := fun _ => FiniteImage.carry master.groupingRules (retainedRoleProfile master.reduction)
  forwardBackward := fun target => by
    apply Subtype.ext
    exact (CertifiedRoleGrouping.stagewise_normal master.stagewise _).trans
      ((CertifiedRoleGrouping.stagewise_normal master.stagewise target.1).symm.trans target.2)
  backwardForward := fun obligation =>
    AuthorizedProducedTargetObligation.all_eq master.normalization _ obligation

theorem producedImageTransport_carry (master : Instance input) (p : RoleOccurrenceProfile master.roles) :
    master.producedImageTransport.forward (FiniteImage.carry master.groupingRules p) =
      master.regime.carry p :=
  (master.normalization.carry_eq_iff_target_eq _ p).mpr (master.normalization.targets_converge _ p)

theorem returned_action_exact (master : Instance input) (p : RoleOccurrenceProfile master.roles)
    (data : RoleProfilePayload p) :
    RoleStatus.executedPayloadOutput master.reduction p
        ((RoleStatus.executed master.reduction).transform p data) =
      RoleSemantics.actProfile master.reduction p data :=
  RoleStatus.executed_action_exact master.reduction p data

theorem execution_erases (master : Instance input) :
    master.execution = executeCausalOperationalExecutionHistory (resolutionLength input)
      master.origin.state master.origin.context master.origin.freshness := by
  unfold execution
  rw [master.executedExact]
  exact MasterResources.execute_erases _ _

theorem audited_execution_exact (master : Instance input) :
    HEq master.execution (publicCausalOperationalExecution input) :=
  (heq_of_eq master.execution_erases).trans (by rw [master.originExact]; rfl)

theorem all_heads_exact (master : Instance input) :
    master.execution.allHeadsExact master.origin.freshness := by
  rw [master.execution_erases]
  exact executeCausalOperationalExecutionHistory_allHeadsExact _ _ _ _

theorem source_width (master : Instance input) :
    master.carrier.frontier.length = 2 ^ (input + 1) :=
  roleProfileFiniteCarrier_width master.roles

theorem executed_width (master : Instance input) : master.regime.frontier.length = 1 :=
  master.normalization.width_exact

theorem partial_width (master : Instance input) (history : RoleStatus.History master.roles) :
    (CertifiedRoleGrouping.composed history).frontier.length = 2 ^ history.pendingCount :=
  CertifiedRoleGrouping.composed_width history

theorem carry_fibres (master : Instance input) (p q : RoleOccurrenceProfile master.roles) :
    master.regime.carry p = master.regime.carry q ↔
      master.normalization.target p = master.normalization.target q :=
  master.normalization.carry_eq_iff_target_eq p q

theorem coDetermination_fibres (master : Instance input) (p q : RoleOccurrenceProfile master.roles) :
    master.regime.carry p = master.regime.carry q ↔
      Nonempty (OperationallyCoDetermined master.normalization p q) :=
  master.normalization.carry_eq_iff_coDetermined p q

theorem grouping_fibres (master : Instance input) (p q : RoleOccurrenceProfile master.roles) :
    rolewiseCarry master.statuses.policy p = rolewiseCarry master.statuses.policy q ↔
      Nonempty (Chain master.groupingRules.Step p q) :=
  CertifiedRoleGrouping.carry_fibres master.statuses p q

theorem arbitrary_trace_preserves (master : Instance input)
    {p q : RoleOccurrenceProfile master.roles}
    (trace : Trace master.groupingRules.Step p q) (data : RoleProfilePayload p)
    (accepted : RoleSemantics.ProfileAccept p data) :
    RoleSemantics.ProfileAccept q (master.groupingAction.transport trace data) :=
  CertifiedRoleGrouping.all_trace_acceptance master.statuses trace data accepted

theorem normalizing_trace_coherent (master : Instance input) (p : RoleOccurrenceProfile master.roles)
    (first second : Trace master.groupingRules.Step p (master.statuses.selected p))
    (data : RoleProfilePayload p) :
    master.groupingAction.transport first data = master.groupingAction.transport second data :=
  CertifiedRoleGrouping.normalization_coherent master.statuses p first second data

theorem checkpoint_output_exact (master : Instance input) (profile : RoleOccurrenceProfile master.roles) :
    (master.checkpoint profile).output = master.normalization.target profile :=
  ProducedContinuation.output_is_executed (master.source profile)

theorem checkpoint_output_accepted (master : Instance input) (profile : RoleOccurrenceProfile master.roles) :
    RoleSemantics.TargetAccept master.reduction (master.checkpoint profile).output :=
  ProducedContinuation.output_accepted (master.source profile)

theorem future_events_exact (master : Instance input) (profile : RoleOccurrenceProfile master.roles)
    (requests : List (ProducedContinuation.Input master.normalization)) :
    Continuation.events ProducedContinuation.sourceNext ProducedContinuation.sourceEvent
        (master.source profile) requests =
      Continuation.events ProducedContinuation.next ProducedContinuation.event
        (master.checkpoint profile) requests :=
  ProducedContinuation.all_future_events _ _ _

theorem future_reads_exact (master : Instance input) (profile : RoleOccurrenceProfile master.roles)
    (requests : List (ProducedContinuation.Input master.normalization)) :
    Continuation.observations ProducedContinuation.sourceNext
        (fun source => ProducedContinuation.read (ProducedContinuation.project source)) (master.source profile) requests =
      Continuation.observations ProducedContinuation.next ProducedContinuation.read
        (master.checkpoint profile) requests :=
  ProducedContinuation.all_future_reads _ _ _

def distinctPair (master : Instance input) : ExecutedGroupedDistinctProfiles master.normalization :=
  let left := master.roles.headTransformedProfile
  let right := master.roles.headRetainedProfile
  let same := master.normalization.targets_converge left right
  { left := left
    right := right
    distinct := master.roles.headProfilesDistinct (Nat.zero_lt_succ input)
    coDetermined := master.normalization.coDeterminationOfTargetEq left right same
    carriedTogether := (master.normalization.carry_eq_iff_target_eq left right).mpr same }

theorem profile_irrecoverable (master : Instance input) :
    ¬ (∃ recover : ProducedContinuation.Memory master.normalization → RoleOccurrenceProfile master.roles,
      ∀ profile, recover (master.checkpoint profile) = profile) :=
  ProducedContinuation.profile_not_recoverable _ _ _ _ master.distinctPair.distinct

end Instance

set_option genSizeOf false in
/-- A stored old history is prolonged only from its reached resource cursor.
The suffix is executed once; its producer, reference transport and attachment
are pinned. Old heads are read, not executed again. -/
structure Growth {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (origin : MasterResources.Cursor)
    (old : CausalOperationalExecutionHistory (_count := count) state context)
    (cursor : MasterResources.Cursor) (boundary : cursor.boundary = MasterResources.endpoint old)
    (extra : Nat) : Type 3 where
  provenance : MasterResources.ProducedPrefix (depth := depth) (count := count)
    (assignment := assignment) (state := state) (context := context) origin old cursor
  suffix : MasterResources.Result extra cursor
  suffixExact : suffix = MasterResources.executeWithReferences extra cursor
  grown : CertifiedRoleGrouping.StoredGrowth old
  grownExact : grown = CertifiedRoleGrouping.growStored old
    (MasterResources.transportHistory boundary suffix.history)

def resource_history_extension {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (origin : MasterResources.Cursor)
    (old : CausalOperationalExecutionHistory (_count := count) state context)
    (cursor : MasterResources.Cursor) (boundary : cursor.boundary = MasterResources.endpoint old)
    (extra : Nat) (provenance : MasterResources.ProducedPrefix (depth := depth) (count := count)
      (assignment := assignment) (state := state) (context := context) origin old cursor) :
      Growth origin old cursor boundary extra :=
  let suffix := MasterResources.executeWithReferences extra cursor
  let grown := CertifiedRoleGrouping.growStored old
    (MasterResources.transportHistory boundary suffix.history)
  ⟨provenance, suffix, rfl, grown, rfl⟩

private theorem step_heq {depth firstCount secondCount : Nat}
    {assignment : SequentialAssignment depth} {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (stage : SequentialStageRun depth assignment) (run : ThreadedConstitutiveStageRun state stage)
    (production : ExecutedStageOperationalProduction context (causalStageOfThreadedStage run))
    (first : CausalOperationalExecutionHistory (depth := depth + 1) (_count := firstCount)
      (assignment := stage.next) run.nextRun.next production.nextContext)
    (second : CausalOperationalExecutionHistory (depth := depth + 1) (_count := secondCount)
      (assignment := stage.next) run.nextRun.next production.nextContext)
    (counts : firstCount = secondCount) (tails : HEq first second) :
    HEq (CausalOperationalExecutionHistory.step (depth := depth) (count := firstCount)
      (assignment := assignment) (state := state) (context := context) stage run production first)
      (CausalOperationalExecutionHistory.step (depth := depth) (count := secondCount)
        (assignment := assignment) (state := state) (context := context) stage run production second) := by
  cases counts
  exact heq_of_eq (congrArg
    (fun tail => CausalOperationalExecutionHistory.step (depth := depth) (count := firstCount)
      (assignment := assignment) (state := state) (context := context) stage run production tail)
    (eq_of_heq tails))

private theorem executed_history_count_heq (first second : Nat) (same : first = second)
    (origin : MasterResources.Cursor) :
    HEq (MasterResources.executeWithReferences first origin).history
      (MasterResources.executeWithReferences second origin).history := by
  cases same
  rfl

set_option maxHeartbeats 0 in
/-- Stored attachment agrees with one uninterrupted resource execution.
The right side is a specification in Prop, never a second runtime call. -/
theorem stored_growth_is_one_run (extra : Nat) : ∀ (count : Nat) (cursor : MasterResources.Cursor)
    (boundary : (MasterResources.execute count cursor).2.boundary =
      MasterResources.endpoint (MasterResources.execute count cursor).1),
    HEq (CertifiedRoleGrouping.growStored (MasterResources.execute count cursor).1
      (MasterResources.transportHistory boundary
        (MasterResources.execute extra (MasterResources.execute count cursor).2).1)).history
      (MasterResources.execute (extra + count) cursor).1
  | 0, _, boundary => by cases boundary; rfl
  | count + 1, cursor, boundary => by
      simp only [Nat.add_succ, MasterResources.execute_succ] at boundary ⊢
      dsimp only [MasterResources.endpoint] at boundary
      let resources := cursor.headResources
      let produced := (resources.1.read .here).down
      let next := (MasterResources.continueWithReferences resources.1 .here
        (.prior (.prior (.prior (.prior cursor.fresh))))).1
      let suffix := MasterResources.transportHistory
        (MasterResources.execute_endpoint count next).symm
        (MasterResources.execute extra (MasterResources.execute count next).2).1
      have rest := stored_growth_is_one_run extra count next
        (MasterResources.execute_endpoint count next).symm
      exact step_heq (depth := cursor.depth) (assignment := cursor.assignment)
        (state := cursor.state) (context := cursor.context)
        (firstCount := (CertifiedRoleGrouping.growStored (MasterResources.execute count next).1 suffix).count)
        (secondCount := extra + count) produced.stage produced.run produced.production
        (CertifiedRoleGrouping.growStored (MasterResources.execute count next).1 suffix).history
        (MasterResources.execute (extra + count) next).1
        ((CertifiedRoleGrouping.growStored_count (MasterResources.execute count next).1 suffix).trans
          (Nat.add_comm count extra)) rest

namespace Growth
variable {depth count extra : Nat} {assignment : SequentialAssignment depth}
  {state : ThreadedConstitutiveState depth assignment}
  {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
  {old : CausalOperationalExecutionHistory (_count := count) state context}
  {origin : MasterResources.Cursor}
  {cursor : MasterResources.Cursor} {boundary : cursor.boundary = MasterResources.endpoint old}

theorem count_exact (growth : Growth origin old cursor boundary extra) : growth.grown.count = count + extra := by
  rw [growth.grownExact]
  exact CertifiedRoleGrouping.growStored_count _ _

theorem endpoint_exact (growth : Growth origin old cursor boundary extra) :
    growth.suffix.finish.boundary = MasterResources.endpoint growth.grown.history := by
  rw [growth.grownExact]
  have agreement : MasterResources.endpoint
      (MasterResources.transportHistory boundary growth.suffix.history) =
        MasterResources.endpoint growth.suffix.history :=
    MasterResources.transportHistory_endpoint boundary growth.suffix.history
  have executedEnd : growth.suffix.finish.boundary = MasterResources.endpoint growth.suffix.history := by
    rw [growth.suffixExact]
    exact (MasterResources.executeWithReferences_endpoint _ _).symm
  exact executedEnd.trans
    (agreement.symm.trans (CertifiedRoleGrouping.growStored_endpoint _ _).symm)

theorem history_is_one_run (growth : Growth origin old cursor boundary extra) :
    HEq growth.grown.history
      (MasterResources.executeWithReferences (extra + count) growth.provenance.origin).history := by
  cases growth.provenance with
  | mk startExact historyExact cursorExact =>
    cases startExact
    have oldExact := eq_of_heq historyExact
    subst old
    subst cursor
    rw [growth.grownExact, growth.suffixExact]
    exact stored_growth_is_one_run extra count origin _

def producedPrefix (growth : Growth origin old cursor boundary extra) :
    MasterResources.ProducedPrefix (depth := depth) (count := growth.grown.count)
      (assignment := assignment) (state := state) (context := context)
      origin growth.grown.history growth.suffix.finish := by
  refine ⟨growth.provenance.originBoundary, ?_, ?_⟩
  · exact growth.history_is_one_run.trans
      (executed_history_count_heq _ _ (growth.count_exact.trans (Nat.add_comm count extra)).symm
        growth.provenance.origin)
  · have length := growth.count_exact.trans (Nat.add_comm count extra)
    exact (congrArg MasterResources.Result.finish growth.suffixExact).trans
      ((congrArg (fun next => (MasterResources.executeWithReferences extra next).finish)
        growth.provenance.cursorExact).trans
        ((MasterResources.execute_finish_append extra count growth.provenance.origin).trans
          (congrArg (fun n => (MasterResources.executeWithReferences n growth.provenance.origin).finish)
            length.symm)))

def resume (growth : Growth origin old cursor boundary extra) (more : Nat) :=
  resource_history_extension origin growth.grown.history growth.suffix.finish growth.endpoint_exact more
    growth.producedPrefix
end Growth

theorem Instance.endpoint_exact {input : Nat} (master : Instance input) :
    master.cursor.boundary = MasterResources.endpoint master.execution := by
  change master.executed.2.boundary = MasterResources.endpoint master.executed.1
  rw [master.executedExact]
  exact (MasterResources.execute_endpoint _ _).symm

def Instance.producedPrefix {input : Nat} (master : Instance input) :
    MasterResources.ProducedPrefix (depth := master.origin.depth) (count := resolutionLength input)
      (assignment := master.origin.assignment) (state := master.origin.state) (context := master.origin.context)
      master.origin master.execution master.cursor where
  originBoundary := rfl
  historyExact := by
    unfold Instance.execution
    rw [master.executedExact]
    rfl
  cursorExact := by
    unfold Instance.cursor
    rw [master.executedExact]
    rfl

def Instance.grow {input : Nat} (master : Instance input) (extra : Nat) :=
  resource_history_extension master.origin master.execution master.cursor master.endpoint_exact extra master.producedPrefix

/-- Transport from the original support through an already produced extension.
The extension is an argument, not a second call of its executor. -/
def Instance.referencesThrough {input extra : Nat} (master : Instance input)
    (growth : Growth master.origin master.execution master.cursor master.endpoint_exact extra) :=
  master.references.compose growth.suffix.references

theorem Instance.referencesThrough_read {input extra : Nat} (master : Instance input)
    (growth : Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    {kind : MasterResources.Kind} (ref : Resources.Ref master.origin.kinds kind) :
    growth.suffix.finish.support.read ((master.referencesThrough growth).references ref) =
      master.origin.support.read ref :=
  (master.referencesThrough growth).reads ref

def Growth.referencesThrough {depth count extra more : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {old : CausalOperationalExecutionHistory (_count := count) state context}
    {origin : MasterResources.Cursor}
    {cursor : MasterResources.Cursor} {boundary : cursor.boundary = MasterResources.endpoint old}
    (one : Growth origin old cursor boundary extra)
    (two : Growth origin one.grown.history one.suffix.finish one.endpoint_exact more) :=
  one.suffix.references.compose two.suffix.references

def publicContinuation (input extra : Nat) :=
  let master := publicInstance input
  master.grow extra

def publicGrowth (input extra : Nat) := (publicContinuation input extra).grown.historical

/-- The second extension consumes the first result and its final cursor. -/
def publicGrowthTwice (input first second : Nat) :=
  let master := publicInstance input
  let grown := master.grow first
  let next := grown.resume second
  grown.grown.historical.compose next.grown.historical

theorem public_growth_composes (input first second : Nat)
    (p : RoleOccurrenceProfile (publicInstance input).roles) :
    (publicGrowthTwice input first second).embedding p =
      ((publicContinuation input first).resume second).grown.historical.embedding
        ((publicGrowth input first).embedding p) := rfl

theorem public_obligations_compose (input first second : Nat)
    (p : Extension.Obligation (CertifiedRoleGrouping.rules (publicInstance input).statuses)) :
    ((publicContinuation input first).resume second).grown.historical.extension.obligation
      ((publicGrowth input first).extension.obligation p) =
        (publicGrowthTwice input first second).extension.obligation p :=
  CertifiedRoleGrouping.Historical.obligation_composes _ _ p

theorem public_growth_injective (input extra : Nat)
    (p q : RoleOccurrenceProfile (publicInstance input).roles)
    (same : (publicGrowth input extra).embedding p = (publicGrowth input extra).embedding q) : p = q :=
  (publicGrowth input extra).embedding_injective p q same

theorem public_growth_renormalizes (input extra : Nat)
    (p : RoleOccurrenceProfile (publicInstance input).roles) :
    (RoleStatus.ofStagewise (publicContinuation input extra).grown.history.stagewiseDecomposition).selected
        ((publicGrowth input extra).embedding ((publicInstance input).statuses.selected p)) =
      (RoleStatus.ofStagewise (publicContinuation input extra).grown.history.stagewiseDecomposition).selected
          ((publicGrowth input extra).embedding p) :=
  (publicGrowth input extra).renormalized p

/-- The family reads the one master result, not a separate Boolean-product carrier. -/
def family : RelationalRoleExtensiveFamily where
  State := CausalConstitutiveState
  Problem := fun _ => Unit
  initialState := fun {index} _ => causalStateOfThreadedState (publicInstance index).origin.state
  stageCount := fun {index} _ => resolutionLength index
  producedHistory := fun {index} _ => generalHistoryOfRoleHistory (publicInstance index).roles
  nontrivialOpenings := fun {index} _ => generalHistory_is_atLeastBinary (publicInstance index).roles
  unboundedIndex := id
  unboundedProblem := fun _ => ()
  unboundedStages := fun bound => Nat.le_succ bound

def binaryFamily : BinaryRelationalRoleExtensiveFamily where
  toRelationalRoleExtensiveFamily := family
  binaryOpenings := fun {index} _ => generalRoleHistory_uniformBinary (publicInstance index).roles

theorem class_carrier_exact (input : Nat) :
    binaryFamily.sourceCarrier (index := input) () = (publicInstance input).carrier := rfl

theorem class_iff_on_master_carrier (input : Nat)
    (regime : ObligationRegime (publicInstance input).carrier) :
    regime.frontier.length = 2 ^ (input + 1) ↔ Function.Injective regime.carry :=
  BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
    binaryFamily (index := input) () regime

theorem class_iff_on_executed_regime (input : Nat) :
    (publicInstance input).regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective (publicInstance input).regime.carry :=
  class_iff_on_master_carrier input (publicInstance input).regime

theorem checkpoint_is_existing_restart (input : Nat) :
    (publicInstance input).checkpoint (publicInstance input).roles.headTransformedProfile =
      ProducedContinuation.publicStart input := rfl

theorem public_execution_exact (input : Nat) :
    (publicInstance input).execution = publicCausalOperationalExecution input :=
  ProducedContinuation.public_execution_exact input

/-- All fields concern projections of this master. They are not independent runs. -/
structure Facts {input : Nat} (master : Instance input) : Prop where
  executionExact : HEq master.execution (publicCausalOperationalExecution input)
  headsExact : master.execution.allHeadsExact master.origin.freshness
  horizonIndependent : ∀ first second,
    (MasterResources.executeWithReferences (first + 1) master.origin).history.head? =
      (MasterResources.executeWithReferences (second + 1) master.origin).history.head?
  regimeExact : master.regime = master.normalization.operationalRegime
  imageCommutes : ∀ p, master.producedImageTransport.forward (FiniteImage.carry master.groupingRules p) =
    master.regime.carry p
  rolesConstituted : RelationalRoleHistoryConstitutionExact master.roles
  sourceWidth : master.carrier.frontier.length = 2 ^ (input + 1)
  executedWidth : master.regime.frontier.length = 1
  partialWidth : ∀ history : RoleStatus.History master.roles,
    (CertifiedRoleGrouping.composed history).frontier.length = 2 ^ history.pendingCount
  targetFibres : ∀ p q, master.regime.carry p = master.regime.carry q ↔
    master.normalization.target p = master.normalization.target q
  chainFibres : ∀ p q, rolewiseCarry master.statuses.policy p = rolewiseCarry master.statuses.policy q ↔
    Nonempty (Chain master.groupingRules.Step p q)
  sourceDistinct : master.distinctPair.left ≠ master.distinctPair.right
  grouped : master.regime.carry master.distinctPair.left = master.regime.carry master.distinctPair.right
  outputAccepted : ∀ p, RoleSemantics.TargetAccept master.reduction (master.checkpoint p).output
  outputExact : ∀ p, (master.checkpoint p).output = master.normalization.target p
  restartCursorExact : ∀ p, (master.checkpoint p).live = LiveContinuation.project master.cursor
  readersExact : ∀ p, (master.checkpoint p).readers =
    ProducedContinuation.targetReaders master.reduction (master.normalization.target p)
  advanceAdmission : ∀ p steps,
    Nonempty (ProducedContinuation.allow (master.checkpoint p) (.advance steps))
  sourceAdvanceAdmission : ∀ p steps,
    Nonempty (ProducedContinuation.allow (ProducedContinuation.project (master.source p)) (.advance steps))
  requestAdmission : ∀ p requests,
    Nonempty (Continuation.Admitted ProducedContinuation.sourceNext
      (fun source input => ProducedContinuation.allow (ProducedContinuation.project source) input)
      (master.source p) requests) ↔
      Nonempty (Continuation.Admitted ProducedContinuation.next ProducedContinuation.allow
        (master.checkpoint p) requests)
  sourceAdmissionReturn : ∀ p {requests} (witness : Continuation.Admitted ProducedContinuation.sourceNext
      (fun source input => ProducedContinuation.allow (ProducedContinuation.project source) input)
      (master.source p) requests),
    ProducedContinuation.all_requests_reflected (master.source p)
      (ProducedContinuation.all_requests_admitted (master.source p) witness) = witness
  memoryAdmissionReturn : ∀ p {requests} (witness : Continuation.Admitted ProducedContinuation.next
      ProducedContinuation.allow (master.checkpoint p) requests),
    ProducedContinuation.all_requests_admitted (master.source p)
      (ProducedContinuation.all_requests_reflected (master.source p) witness) = witness
  inspectAdmission : ∀ (memory : ProducedContinuation.Memory master.normalization) query,
    Nonempty (ProducedContinuation.allow memory (.inspect query)) ↔ query.slot < resolutionLength input
  inspectEvent : ∀ p query, ProducedContinuation.event (master.checkpoint p) (.inspect query) =
    .observed query (ProducedContinuation.readTarget query
      (ProducedContinuation.targetReaders master.reduction (master.normalization.target p)))
  sourceInspectEvent : ∀ p query, ProducedContinuation.sourceEvent (master.source p) (.inspect query) =
    .observed query (ProducedContinuation.readTarget query
      (ProducedContinuation.targetReaders master.reduction (master.normalization.target p)))
  runtimeInspectEvent : ∀ p query,
    (ProducedContinuation.executeInput (master.checkpoint p) (.inspect query)).2 =
      .observed query (ProducedContinuation.readTarget query
        (ProducedContinuation.targetReaders master.reduction (master.normalization.target p)))
  growthCount : ∀ extra, (master.grow extra).grown.count = resolutionLength input + extra
  growthEndpoint : ∀ extra, (master.grow extra).suffix.finish.boundary =
    MasterResources.endpoint (master.grow extra).grown.history
  growthOneRun : ∀ extra, HEq (master.grow extra).grown.history
    (MasterResources.executeWithReferences (extra + resolutionLength input) master.origin).history
  growthReferences : ∀ extra {kind : MasterResources.Kind} (ref : Resources.Ref master.origin.kinds kind),
    (master.grow extra).suffix.finish.support.read
      ((master.referencesThrough (master.grow extra)).references ref) = master.origin.support.read ref
  referencesInjective : ∀ {kind : MasterResources.Kind} (first second : Resources.Ref master.origin.kinds kind),
    master.references.references first = master.references.references second → first = second
  growthReferencesInjective : ∀ {extra}
    (growth : Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    {kind : MasterResources.Kind} (first second : Resources.Ref master.origin.kinds kind),
    (master.referencesThrough growth).references first =
      (master.referencesThrough growth).references second → first = second
  growthReferencesCompose : ∀ {extra more}
    (one : Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    (two : Growth master.origin one.grown.history one.suffix.finish one.endpoint_exact more)
    {kind : MasterResources.Kind} (ref : Resources.Ref master.origin.kinds kind),
    (master.references.compose (one.referencesThrough two)).references ref =
      two.suffix.references.references ((master.referencesThrough one).references ref)
  growthComposedReads : ∀ {extra more}
    (one : Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    (two : Growth master.origin one.grown.history one.suffix.finish one.endpoint_exact more)
    {kind : MasterResources.Kind} (ref : Resources.Ref master.origin.kinds kind),
    two.suffix.finish.support.read
      ((master.references.compose (one.referencesThrough two)).references ref) =
        master.origin.support.read ref
  growthProfilesCompose : ∀ {extra more}
    (one : Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    (two : Growth master.origin one.grown.history one.suffix.finish one.endpoint_exact more)
    (p : RoleOccurrenceProfile master.roles),
    (one.grown.historical.compose two.grown.historical).embedding p =
      two.grown.historical.embedding (one.grown.historical.embedding p)
  growthObligationsCompose : ∀ {extra more}
    (one : Growth master.origin master.execution master.cursor master.endpoint_exact extra)
    (two : Growth master.origin one.grown.history one.suffix.finish one.endpoint_exact more)
    (p : Extension.Obligation (CertifiedRoleGrouping.rules master.statuses)),
    (one.grown.historical.compose two.grown.historical).extension.obligation p =
      two.grown.historical.extension.obligation (one.grown.historical.extension.obligation p)
  arbitraryTracePreserves : ∀ {p q} (trace : Trace master.groupingRules.Step p q) (data : RoleProfilePayload p),
    RoleSemantics.ProfileAccept p data →
      RoleSemantics.ProfileAccept q (master.groupingAction.transport trace data)
  coherentTraces : ∀ p (first second : Trace master.groupingRules.Step p (master.statuses.selected p))
    (data : RoleProfilePayload p), master.groupingAction.transport first data = master.groupingAction.transport second data
  profileNotRecoverable : ¬ (∃ recover : ProducedContinuation.Memory master.normalization → RoleOccurrenceProfile master.roles,
    ∀ p, recover (master.checkpoint p) = p)
  exactFuture : ∀ p requests,
    Continuation.events ProducedContinuation.sourceNext ProducedContinuation.sourceEvent (master.source p) requests =
      Continuation.events ProducedContinuation.next ProducedContinuation.event (master.checkpoint p) requests
  exactReads : ∀ p requests,
    Continuation.observations ProducedContinuation.sourceNext
      (fun source => ProducedContinuation.read (ProducedContinuation.project source)) (master.source p) requests =
      Continuation.observations ProducedContinuation.next ProducedContinuation.read (master.checkpoint p) requests

theorem facts {input : Nat} (master : Instance input) : Facts master where
  executionExact := master.audited_execution_exact
  headsExact := master.all_heads_exact
  horizonIndependent := fun first second =>
    (congrArg CausalOperationalExecutionHistory.head? (MasterResources.execute_erases (first + 1) master.origin)).trans
      ((executeCausalOperationalExecutionHistory_head_independent first second
        master.origin.state master.origin.context master.origin.freshness).trans
        (congrArg CausalOperationalExecutionHistory.head?
          (MasterResources.execute_erases (second + 1) master.origin)).symm)
  regimeExact := rfl
  imageCommutes := master.producedImageTransport_carry
  rolesConstituted := master.stagewise.rolesConstitutionExact
  sourceWidth := master.source_width
  executedWidth := master.executed_width
  partialWidth := master.partial_width
  targetFibres := master.carry_fibres
  chainFibres := master.grouping_fibres
  sourceDistinct := master.distinctPair.distinct
  grouped := master.distinctPair.carriedTogether
  outputAccepted := master.checkpoint_output_accepted
  outputExact := master.checkpoint_output_exact
  restartCursorExact := fun _ => rfl
  readersExact := fun p => (master.checkpoint p).readersExact.trans
    (congrArg (ProducedContinuation.targetReaders master.reduction) (master.checkpoint_output_exact p))
  advanceAdmission := fun p steps => ⟨ProducedContinuation.advance_admission (master.checkpoint p) steps⟩
  sourceAdvanceAdmission := fun p steps => ⟨ProducedContinuation.source_advance_admission (master.source p) steps⟩
  requestAdmission := fun p requests => ProducedContinuation.requests_admission_iff (master.source p) requests
  sourceAdmissionReturn := fun p {_} witness => ProducedContinuation.requests_source_return (master.source p) witness
  memoryAdmissionReturn := fun p {_} witness => ProducedContinuation.requests_memory_return (master.source p) witness
  inspectAdmission := ProducedContinuation.inspect_admitted_iff
  inspectEvent := fun p query =>
    (ProducedContinuation.inspect_event_exact (master.checkpoint p) query).trans
      (by rw [master.checkpoint_output_exact])
  sourceInspectEvent := fun p query => ProducedContinuation.source_inspect_event_exact (master.source p) query
  runtimeInspectEvent := fun p query =>
    (ProducedContinuation.execute_inspect_exact (master.checkpoint p) query).trans
      (by rw [master.checkpoint_output_exact])
  growthCount := fun extra => (master.grow extra).count_exact
  growthEndpoint := fun extra => (master.grow extra).endpoint_exact
  growthOneRun := fun extra => (master.grow extra).history_is_one_run
  growthReferences := fun extra {_} ref => master.referencesThrough_read (master.grow extra) ref
  referencesInjective := master.references.injective
  growthReferencesInjective := fun {_} growth => (master.referencesThrough growth).injective
  growthReferencesCompose := fun {_ _} _ _ {_} _ => rfl
  growthComposedReads := fun {_ _} one two {_} ref =>
    (master.references.compose (one.referencesThrough two)).reads ref
  growthProfilesCompose := fun {_ _} one two p =>
    CertifiedRoleGrouping.Historical.embedding_composes one.grown.historical two.grown.historical p
  growthObligationsCompose := fun {_ _} one two p =>
    (CertifiedRoleGrouping.Historical.obligation_composes one.grown.historical two.grown.historical p).symm
  arbitraryTracePreserves := master.arbitrary_trace_preserves
  coherentTraces := master.normalizing_trace_coherent
  profileNotRecoverable := master.profile_irrecoverable
  exactFuture := master.future_events_exact
  exactReads := master.future_reads_exact

/-- Scientific package; never stored in the runtime restart memory. -/
structure Certificate (input : Nat) : Type 3 where
  master : Instance input
  facts : Facts master

def certificate (input : Nat) : Certificate input :=
  let master := publicInstance input
  ⟨master, facts master⟩

end ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.publicInstance
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.execution_erases
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.audited_execution_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.all_heads_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.source_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.executed_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.partial_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.carry_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.coDetermination_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.grouping_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.arbitrary_trace_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.normalizing_trace_coherent
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.checkpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.imageTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.producedImageTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.producedImageTransport_carry
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.returned_action_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.checkpoint_output_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.checkpoint_output_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.future_events_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.future_reads_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.distinctPair
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.profile_irrecoverable
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.resource_history_extension
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth.count_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth.endpoint_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.stored_growth_is_one_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth.history_is_one_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth.producedPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.producedPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth.resume
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.endpoint_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.grow
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.referencesThrough
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.referencesThrough_read
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Growth.referencesThrough
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.publicContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.publicGrowth
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.publicGrowthTwice
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.public_growth_composes
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.public_obligations_compose
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.public_growth_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.public_growth_renormalizes
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.family
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.binaryFamily
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.class_carrier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.class_iff_on_master_carrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.class_iff_on_executed_regime
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.checkpoint_is_existing_restart
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.public_execution_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.facts
#print axioms ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.certificate
/- AXIOM_AUDIT_END -/
