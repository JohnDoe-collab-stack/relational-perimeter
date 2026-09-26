import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFeedback

/-!
# Endogenous operational stability

The exact dependent role history constitutes a complete, duplicate-free
carrier of structural obligations.  A source-indexed licensed plan is then
constructed for every member: crossing from a left source requires the complete
executed absorption reduction, whereas a right source uses an independently
typed retention execution.  These plans constitute a singleton operational
carrier.  Deleting the absorption constructor while preserving retained-side
execution makes every left source unreachable and complete singleton coverage
impossible.  The older constant-image collapse and the numerical width trace
remain derived readouts of this proof-relevant construction.  No parallel
trajectory is introduced.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- The singleton frontier from which one executed stage opens. -/
def ThreadedConstitutiveRoleStage.sourceFrontier {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (_roles : ThreadedConstitutiveRoleStage run) :=
  [(constructStage (depth + 1)).operationalRoot]

/-- The two exact children produced by the binary opening of the stage. -/
def ThreadedConstitutiveRoleStage.openedFrontier {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (_roles : ThreadedConstitutiveRoleStage run) :=
  [(constructStage (depth + 1)).operationalRoot.child
      stage.discovery.var false stage.discovery.fresh,
    (constructStage (depth + 1)).operationalRoot.child
      stage.discovery.var true stage.discovery.fresh]

/-- The singleton frontier retained after certified sibling absorption. -/
def ThreadedConstitutiveRoleStage.retainedFrontier {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (_roles : ThreadedConstitutiveRoleStage run) :=
  [(constructStage (depth + 1)).operationalRoot.child
      stage.discovery.var true stage.discovery.fresh]

theorem ThreadedConstitutiveRoleStage.sourceFrontier_length {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.sourceFrontier.length = 1 := by
  rfl

theorem ThreadedConstitutiveRoleStage.openedFrontier_length {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.openedFrontier.length = 2 := by
  rfl

theorem ThreadedConstitutiveRoleStage.retainedFrontier_length {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.retainedFrontier.length = 1 := by
  rfl

/-- The exact opening is also a bidirectional preservation of viability. -/
def ThreadedConstitutiveRoleStage.openingPreservation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      roles.sourceFrontier
      roles.openedFrontier :=
  AcceptedFrontierPreservation.expandHead roles.structuralOpening

/-- Opening followed by the stage's stored absorption is the full stable step. -/
def ThreadedConstitutiveRoleStage.fullOperationalPreservation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      roles.sourceFrontier
      roles.retainedFrontier :=
  roles.openingPreservation.trans roles.operationalAbsorption

/-- The stored reduction is definitionally the one reconstructed from this
stage's executed discovery.  This pins its provenance in the public type. -/
theorem ThreadedConstitutiveRoleStage.operationalAbsorption_from_discovery
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.operationalAbsorption =
      AcceptedFrontierPreservation.absorbFirstIntoSecond
        stage.discovery.relation.toAcceptingTransport :=
  roles.operationalAbsorptionFromDiscovery

theorem ThreadedConstitutiveRoleStage.opened_retained_viable_iff {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    FrontierViable
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        roles.openedFrontier ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        roles.retainedFrontier :=
  roles.operationalAbsorption.viable_iff

theorem ThreadedConstitutiveRoleStage.source_retained_viable_iff {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    FrontierViable
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        roles.sourceFrontier ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        roles.retainedFrontier :=
  roles.fullOperationalPreservation.viable_iff

/-- The absorbed sibling is positively viable at every executed stage.  Its
absorption therefore records dispensability for the criterion, not
impossibility. -/
theorem ThreadedConstitutiveRoleStage.absorbedSiblingViable {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (_roles : ThreadedConstitutiveRoleStage run) :
    FrontierViable
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh] := by
  have sourceExact :
      stage.schedule.entry.source =
        (constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var false stage.discovery.fresh := by
    rw [stage.scheduleExact]
    rfl
  rw [← sourceExact]
  exact ⟨.head stage.sourceContinuation, stage.sourceAccepted⟩

/-- The continuation retained by the complete opening-and-absorption step. -/
def ThreadedConstitutiveRoleStage.retainedContinuation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (_roles : ThreadedConstitutiveRoleStage run) :
    GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh) :=
  (fullStageExecution stage).output

/-- The data-producing complete operation reconstructed from the discovered
relation and applied to the actual parent continuation. -/
def ThreadedConstitutiveRoleStage.materializedRetainedContinuation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (_roles : ThreadedConstitutiveRoleStage run) :
    GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh) :=
  applyFullConstitutiveStep stage.discovery (fullStageExecution stage).parent

/-- Materializing the complete opening-and-absorption operation yields exactly
the retained continuation returned by execution. -/
theorem ThreadedConstitutiveRoleStage.materializedRetainedContinuation_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.materializedRetainedContinuation = roles.retainedContinuation :=
  (fullStageExecution stage).outputExact.symm

/-- The retained choice is read from the continuation materially produced by
the complete discovered operation. -/
theorem ThreadedConstitutiveRoleStage.materializedRetainedContinuation_selected
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.materializedRetainedContinuation.1 stage.discovery.var = true := by
  rw [roles.materializedRetainedContinuation_exact]
  unfold ThreadedConstitutiveRoleStage.retainedContinuation
  rw [(fullStageExecution stage).nextAssignmentExact,
    stage.nextAssignmentExact]
  have entryVar : stage.schedule.entry.var = stage.discovery.var := by
    rw [stage.scheduleExact]
    rfl
  rw [← entryVar]
  exact stage.output_selected

/-- The source continuation of the next search situation, formed from the
state actually produced by the current stage. -/
def ThreadedConstitutiveRoleStage.nextSourceContinuation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    GeneratedStructuralBranchContinuation
      (constructStage ((depth + 1) + 1)).operationalRoot :=
  stageParentContinuation (depth + 1) roles.nextNpState.threadedAssignment

/-- The retained continuation supplies exactly the assignment consumed by the
next source.  The search carriers differ, but their constitutive payload is
transmitted rather than reset. -/
theorem ThreadedConstitutiveRoleStage.retainedContinuation_assignment_eq_nextSource
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    roles.retainedContinuation.1 = roles.nextSourceContinuation.1 := by
  unfold ThreadedConstitutiveRoleStage.retainedContinuation
    ThreadedConstitutiveRoleStage.nextSourceContinuation
    stageParentContinuation
  rw [(fullStageExecution stage).nextAssignmentExact]
  rw [roles.nextNpStateExact]
  exact run.nextRun.assignmentFromExecution.symm

/-- Source continuation read from the state that indexes an authoritative role
history.  Unlike a numerical singleton width, its assignment is part of the
dependent state carried by that exact history. -/
def ThreadedConstitutiveRoleHistory.initialSourceContinuation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (_roles : ThreadedConstitutiveRoleHistory history) :
    GeneratedStructuralBranchContinuation
      (constructStage (depth + 1)).operationalRoot :=
  stageParentContinuation depth state.threadedAssignment

/-- The continuation retained by the head transmits its assignment to the
source of the exact dependent tail, not merely to an arbitrary singleton. -/
theorem ThreadedConstitutiveRoleStage.retainedContinuation_assignment_eq_tailSource
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    roles.retainedContinuation.1 = tailRoles.initialSourceContinuation.1 := by
  rw [roles.retainedContinuation_assignment_eq_nextSource]
  unfold ThreadedConstitutiveRoleStage.nextSourceContinuation
    ThreadedConstitutiveRoleHistory.initialSourceContinuation
  rw [roles.nextNpStateExact]

/-- Proof-relevant raccord from the retained continuation of one stage to the
source continuation of its exact dependent tail. -/
structure RetainedNextConditionRaccord {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {count : Nat}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) : Type 2 where
  retained : GeneratedStructuralBranchContinuation
    ((constructStage (depth + 1)).operationalRoot.child
      stage.discovery.var true stage.discovery.fresh)
  retainedExact : retained = roles.retainedContinuation
  nextSource : GeneratedStructuralBranchContinuation
    (constructStage ((depth + 1) + 1)).operationalRoot
  nextSourceExact : nextSource = tailRoles.initialSourceContinuation
  assignmentTransmitted : retained.1 = nextSource.1

def ThreadedConstitutiveRoleStage.retainedNextConditionRaccord {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {count : Nat}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    RetainedNextConditionRaccord roles tailRoles :=
  { retained := roles.retainedContinuation
    retainedExact := rfl
    nextSource := tailRoles.initialSourceContinuation
    nextSourceExact := rfl
    assignmentTransmitted :=
      roles.retainedContinuation_assignment_eq_tailSource tailRoles }

/-- One complete executed reduction, tied simultaneously to the generated
opening, the relation discovered at that stage, the continuation computed by
the complete operation, criterion preservation, and the exact dependent tail.
None of these links can be replaced independently when this witness is used. -/
structure ExecutedStageOperationalReduction {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {count : Nat}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) : Type 2 where
  openingFromGeneration :
    roles.structuralOpening =
      generatedStructuralSplit
        (constructStage (depth + 1)).operationalRoot
        stage.discovery.var
        stage.discovery.fresh
  absorptionFromDiscovery :
    roles.operationalAbsorption =
      AcceptedFrontierPreservation.absorbFirstIntoSecond
        stage.discovery.relation.toAcceptingTransport
  materializedRetained : GeneratedStructuralBranchContinuation
    ((constructStage (depth + 1)).operationalRoot.child
      stage.discovery.var true stage.discovery.fresh)
  materializedFromDiscoveredOperation :
    materializedRetained = roles.materializedRetainedContinuation
  materializedIsExecuted :
    materializedRetained = roles.retainedContinuation
  materializedSelectsRetained :
    materializedRetained.1 stage.discovery.var = true
  criterionPreservation :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      roles.sourceFrontier
      roles.retainedFrontier
  criterionPreservationFromOpeningAndAbsorption :
    criterionPreservation = roles.fullOperationalPreservation
  absorbedSiblingViable :
    FrontierViable
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh]
  raccord : RetainedNextConditionRaccord roles tailRoles

/-- Canonical complete reduction read from one authoritative role stage. -/
def ThreadedConstitutiveRoleStage.executedStageOperationalReduction {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {count : Nat}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    ExecutedStageOperationalReduction roles tailRoles :=
  { openingFromGeneration := roles.structuralOpeningFromGeneration
    absorptionFromDiscovery := roles.operationalAbsorption_from_discovery
    materializedRetained := roles.materializedRetainedContinuation
    materializedFromDiscoveredOperation := rfl
    materializedIsExecuted := roles.materializedRetainedContinuation_exact
    materializedSelectsRetained :=
      roles.materializedRetainedContinuation_selected
    criterionPreservation := roles.fullOperationalPreservation
    criterionPreservationFromOpeningAndAbsorption := rfl
    absorbedSiblingViable := roles.absorbedSiblingViable
    raccord := roles.retainedNextConditionRaccord tailRoles }

/--
The causal stability layer traverses the authoritative role history.  A step
cannot be constructed without both the exact discovered absorption and the
content-level raccord to the next condition.  It contains no second execution.
-/
inductive CausalOperationalStability :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      CausalOperationalStability
        (ThreadedConstitutiveRoleHistory.nil (state := state))
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      (headRole : ThreadedConstitutiveRoleStage headRun)
      (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
      (reduction : ExecutedStageOperationalReduction headRole tailRoles)
      (tailStability : CausalOperationalStability tailRoles) :
      CausalOperationalStability
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)

/-- Canonical causal certificate extracted from, and only from, the role
history of the authoritative execution. -/
def ThreadedConstitutiveRoleHistory.causalOperationalStability :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      CausalOperationalStability roles
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .step headRole tailRoles =>
      .step headRole tailRoles
        (headRole.executedStageOperationalReduction tailRoles)
        tailRoles.causalOperationalStability

/-- A terminal condition contributes the width of its actual singleton carrier. -/
def singletonFrontierWidth {Carrier : Type u} (state : Carrier) : Nat :=
  [state].length

/-- Canonical numerical form of the stagewise singleton/split trace. -/
def alternatingOperationalWidthTrace : Nat → List Nat
  | 0 => [1]
  | count + 1 => 1 :: 2 :: alternatingOperationalWidthTrace count

/-- Initial width read from the actual head or terminal state of a role history. -/
def ThreadedConstitutiveRoleHistory.initialOperationalWidth :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      ThreadedConstitutiveRoleHistory history → Nat
  | _, _, _, state, _, .nil => singletonFrontierWidth state
  | _, _, _, _, _, .step headRole _ => headRole.sourceFrontier.length

/-- Width trace carried by the causal stability witness itself.  Its `step`
constructor contains the discovered absorption and the content raccord used to
justify proceeding with one retained obligation. -/
def CausalOperationalStability.operationalWidthTrace :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      CausalOperationalStability roles → List Nat
  | _, _, _, state, _, _, .nil => [singletonFrontierWidth state]
  | _, _, _, _, _, _, .step headRole _ _ tailStability =>
      headRole.sourceFrontier.length ::
        headRole.openedFrontier.length ::
          tailStability.operationalWidthTrace

/--
Width trace read only from the authoritative role history.  Each executed head
contributes its actual singleton source and binary opened frontier; the
dependent tail begins from the unique condition produced by that head.
-/
def ThreadedConstitutiveRoleHistory.operationalWidthTrace :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      ThreadedConstitutiveRoleHistory history → List Nat
  | _, _, _, _, _, roles =>
      roles.causalOperationalStability.operationalWidthTrace

/-- The typed trace has exactly the alternating numerical form. -/
theorem ThreadedConstitutiveRoleHistory.operationalWidthTrace_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.operationalWidthTrace = alternatingOperationalWidthTrace count := by
  induction roles with
  | nil => rfl
  | step headRole tailRoles inductionHypothesis =>
      change 1 :: 2 :: tailRoles.operationalWidthTrace =
        1 :: 2 :: alternatingOperationalWidthTrace _
      exact congrArg (fun tail => 1 :: 2 :: tail) inductionHypothesis

/-- The trace has two entries per executed opening and one terminal singleton. -/
theorem ThreadedConstitutiveRoleHistory.operationalWidthTrace_length
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.operationalWidthTrace.length = 2 * count + 1 := by
  induction roles with
  | nil => rfl
  | step headRole tailRoles inductionHypothesis =>
      change (1 :: 2 :: tailRoles.operationalWidthTrace).length = _
      rw [List.length_cons, List.length_cons, inductionHypothesis, Nat.mul_succ]

/-- Every width actually read from the role history is exactly one or two. -/
theorem ThreadedConstitutiveRoleHistory.operationalWidthTrace_value
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (width : Nat) (member : width ∈ roles.operationalWidthTrace) :
    width = 1 ∨ width = 2 := by
  induction roles with
  | nil =>
      cases member with
      | head => exact Or.inl rfl
      | tail _ impossible => cases impossible
  | step headRole tailRoles inductionHypothesis =>
      cases member with
      | head => exact Or.inl rfl
      | tail _ afterOne =>
          cases afterOne with
          | head => exact Or.inr rfl
          | tail _ tailMember => exact inductionHypothesis tailMember

/-- Operational width is uniformly bounded by two, independently of depth. -/
theorem ThreadedConstitutiveRoleHistory.operationalWidth_le_two
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (width : Nat) (member : width ∈ roles.operationalWidthTrace) :
    width ≤ 2 := by
  cases roles.operationalWidthTrace_value width member with
  | inl widthOne =>
      rw [widthOne]
      decide
  | inr widthTwo =>
      rw [widthTwo]
      exact Nat.le_refl 2

/-- One complete structural obligation is one left/right choice at every
opening of the exact authoritative role history.  It indexes structural
multiplicity; it does not pretend that every indexed alternative was executed. -/
inductive IndependentStructuralObligation :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) → Type 2 where
  | terminal {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      IndependentStructuralObligation
        (ThreadedConstitutiveRoleHistory.nil (state := state))
  | left {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      {headRole : ThreadedConstitutiveRoleStage headRun}
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      (tail : IndependentStructuralObligation tailRoles) :
      IndependentStructuralObligation
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)

  | right {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      {headRole : ThreadedConstitutiveRoleStage headRun}
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      (tail : IndependentStructuralObligation tailRoles) :
      IndependentStructuralObligation
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)

/-- The two structural alternatives at one opening remain unequal as
obligations, independently of their later operational classification. -/
theorem IndependentStructuralObligation.left_ne_right
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    {headRole : ThreadedConstitutiveRoleStage headRun}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (tail : IndependentStructuralObligation tailRoles) :
    (IndependentStructuralObligation.left tail :
        IndependentStructuralObligation
          (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) ≠
      IndependentStructuralObligation.right tail := by
  intro impossible
  cases impossible

/-- Read the stage-indexed decisions carried by one structural obligation. -/
def IndependentStructuralObligation.decisions :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      IndependentStructuralObligation roles → List StructuralBranchDecision
  | _, _, _, _, _, _, .terminal => []
  | _, _, _, _, _, _, .left (headRole := headRole) tail =>
      ⟨headRole.executedDecision.var, false⟩ :: tail.decisions
  | _, _, _, _, _, _, .right (headRole := headRole) tail =>
      ⟨headRole.executedDecision.var, true⟩ :: tail.decisions

theorem IndependentStructuralObligation.decisions_length
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (obligation : IndependentStructuralObligation roles) :
    obligation.decisions.length = count := by
  induction obligation with
  | terminal => rfl
  | left tail inductionHypothesis =>
      change Nat.succ tail.decisions.length = Nat.succ _
      exact congrArg Nat.succ inductionHypothesis
  | right tail inductionHypothesis =>
      change Nat.succ tail.decisions.length = Nat.succ _
      exact congrArg Nat.succ inductionHypothesis

/-- Constructive introduction into a mapped list. -/
theorem member_map_forward_constructive {alpha : Type u} {beta : Type v}
    (map : alpha → beta) (value : alpha) :
    ∀ {values : List alpha}, value ∈ values → map value ∈ values.map map
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ prior => .tail _ (member_map_forward_constructive map value prior)

/-- Constructive inversion of membership in a mapped list. -/
theorem member_map_inverse_constructive {alpha : Type u} {beta : Type v}
    (map : alpha → beta) (target : beta) :
    ∀ {values : List alpha}, target ∈ values.map map →
      ∃ source, source ∈ values ∧ map source = target
  | _ :: _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, .tail _ prior =>
      let ⟨source, member, exactTarget⟩ :=
        member_map_inverse_constructive map target prior
      ⟨source, .tail _ member, exactTarget⟩

/-- Constructive introduction into the right side of an append. -/
theorem member_append_right_constructive {alpha : Type u} (value : alpha)
    (left : List alpha) :
    ∀ {right : List alpha}, value ∈ right → value ∈ left ++ right
  | _, member => match left with
      | [] => member
      | head :: tail =>
          .tail head (member_append_right_constructive value tail member)

/-- Constructive elimination of membership in an append. -/
theorem member_append_cases_constructive {alpha : Type u} (value : alpha) :
    ∀ (left right : List alpha), value ∈ left ++ right →
      value ∈ left ∨ value ∈ right
  | [], _, member => Or.inr member
  | _ :: _, _, .head _ => Or.inl (.head _)
  | head :: tail, right, .tail _ prior =>
      match member_append_cases_constructive value tail right prior with
      | .inl inTail => Or.inl (.tail head inTail)
      | .inr inRight => Or.inr inRight

/-- Mapping an injective constructor preserves the absence of duplicates. -/
theorem map_nodup_injective_constructive {alpha : Type u} {beta : Type v}
    (map : alpha → beta)
    (injective : ∀ {left right}, map left = map right → left = right) :
    ∀ {values : List alpha}, values.Nodup → (values.map map).Nodup
  | [], _ => .nil
  | head :: tail, nodup => by
      cases nodup with
      | cons headAbsent tailNodup =>
          apply List.Pairwise.cons
          · intro other mappedMember headImage
            let ⟨source, sourceMember, sourceImage⟩ :=
              member_map_inverse_constructive map other mappedMember
            have headEqualsSource : head = source :=
              injective (Eq.trans headImage sourceImage.symm)
            rw [← headEqualsSource] at sourceMember
            exact (headAbsent head sourceMember) rfl
          · exact map_nodup_injective_constructive map injective tailNodup

/-- Constructive duplicate-freedom for an append whose sides are disjoint. -/
theorem append_nodup_disjoint_constructive {alpha : Type u} :
    ∀ (left right : List alpha), left.Nodup → right.Nodup →
      (∀ value, value ∈ left → value ∈ right → False) →
      (left ++ right).Nodup
  | [], right, _, rightNodup, _ => rightNodup
  | head :: tail, right, leftNodup, rightNodup, disjoint => by
      cases leftNodup with
      | cons headAbsent tailNodup =>
          apply List.Pairwise.cons
          · intro other member same
            cases member_append_cases_constructive other tail right member with
            | inl inTail =>
                rw [← same] at inTail
                exact (headAbsent head inTail) rfl
            | inr inRight =>
                rw [← same] at inRight
                exact disjoint head (.head _) inRight
          · apply append_nodup_disjoint_constructive tail right tailNodup rightNodup
            intro value inTail inRight
            exact disjoint value (.tail head inTail) inRight

/-- Universe-polymorphic constructive length of append. -/
theorem listLengthAppendUniverseConstructive {alpha : Type u} :
    ∀ (left right : List alpha), (left ++ right).length = left.length + right.length := by
  have zeroAdd : ∀ n : Nat, 0 + n = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n inductionHypothesis =>
        change Nat.succ (0 + n) = Nat.succ n
        exact congrArg Nat.succ inductionHypothesis
  have succAdd : ∀ a b : Nat, Nat.succ a + b = Nat.succ (a + b) := by
    intro a b
    induction b with
    | zero => rfl
    | succ b inductionHypothesis =>
        change Nat.succ (Nat.succ a + b) = Nat.succ (Nat.succ (a + b))
        exact congrArg Nat.succ inductionHypothesis
  intro left right
  induction left with
  | nil =>
      change right.length = 0 + right.length
      exact (zeroAdd right.length).symm
  | cons head tail inductionHypothesis =>
      change Nat.succ (tail ++ right).length = Nat.succ tail.length + right.length
      exact Eq.trans (congrArg Nat.succ inductionHypothesis)
        (succAdd tail.length right.length).symm

/-- Universe-polymorphic constructive length of map. -/
theorem listMapLengthUniverseConstructive {alpha : Type u} {beta : Type v}
    (map : alpha → beta) :
    ∀ values : List alpha, (values.map map).length = values.length
  | [] => rfl
  | _ :: tail =>
      congrArg Nat.succ (listMapLengthUniverseConstructive map tail)

/-- Universe-polymorphic introduction into the left side of an append. -/
theorem member_append_left_universe_constructive {alpha : Type u} (value : alpha) :
    ∀ {left : List alpha}, value ∈ left →
      ∀ right : List alpha, value ∈ left ++ right
  | _ :: _, .head _, _ => .head _
  | _ :: _, .tail _ prior, right =>
      .tail _ (member_append_left_universe_constructive value prior right)

/-- The complete structural carrier indexed by the exact role history. -/
def ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      List (IndependentStructuralObligation roles)
  | _, _, _, _, _, .nil => [.terminal]
  | _, _, _, _, _, .step _headRole tailRoles =>
      tailRoles.independentStructuralObligationFrontier.map
          IndependentStructuralObligation.left ++
        tailRoles.independentStructuralObligationFrontier.map
          IndependentStructuralObligation.right

/-- Every obligation over the exact history occurs in its structural carrier. -/
theorem ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier_complete
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (obligation : IndependentStructuralObligation roles) :
    obligation ∈ roles.independentStructuralObligationFrontier := by
  induction obligation with
  | terminal => exact .head _
  | left tail inductionHypothesis =>
      exact member_append_left_universe_constructive _
        (member_map_forward_constructive _ _ inductionHypothesis) _
  | right tail inductionHypothesis =>
      exact member_append_right_constructive _ _
        (member_map_forward_constructive _ _ inductionHypothesis)

/-- The history-indexed structural carrier has exactly `2^n` elements. -/
theorem ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier_length
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.independentStructuralObligationFrontier.length = 2 ^ count := by
  induction roles with
  | nil => rfl
  | step headRole tailRoles inductionHypothesis =>
      unfold ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier
      rw [listLengthAppendUniverseConstructive,
        listMapLengthUniverseConstructive IndependentStructuralObligation.left,
        listMapLengthUniverseConstructive IndependentStructuralObligation.right,
        inductionHypothesis, Nat.pow_succ, Nat.mul_two]

/-- The `2^n` structural carrier contains no duplicated obligation. -/
theorem ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier_nodup
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.independentStructuralObligationFrontier.Nodup := by
  induction roles with
  | nil =>
      apply List.Pairwise.cons
      · intro other member
        cases member
      · exact .nil
  | step headRole tailRoles inductionHypothesis =>
      unfold ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier
      apply append_nodup_disjoint_constructive
      · exact map_nodup_injective_constructive
          IndependentStructuralObligation.left
          (by intro left right same; cases same; rfl)
          inductionHypothesis
      · exact map_nodup_injective_constructive
          IndependentStructuralObligation.right
          (by intro left right same; cases same; rfl)
          inductionHypothesis
      · intro value inLeft inRight
        let ⟨leftTail, _, leftExact⟩ := member_map_inverse_constructive
          IndependentStructuralObligation.left value inLeft
        let ⟨rightTail, _, rightExact⟩ := member_map_inverse_constructive
          IndependentStructuralObligation.right value inRight
        rw [← leftExact] at rightExact
        cases rightExact

/-- One head reduction uses the materially computed retained continuation to
choose the operational branch.  Its impossible `false` case remains explicit
in the computation rather than being erased from the definition. -/
def ExecutedStageOperationalReduction.reduceHeadObligation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    {roles : ThreadedConstitutiveRoleStage run}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (reduction : ExecutedStageOperationalReduction roles tailRoles)
    (tail : IndependentStructuralObligation tailRoles) :
    IndependentStructuralObligation
      (ThreadedConstitutiveRoleHistory.step roles tailRoles) :=
  if reduction.materializedRetained.1 stage.discovery.var = false then
    .left tail
  else
    .right tail

/-- The materialized output of every canonical reduction selects the retained
right obligation. -/
theorem ExecutedStageOperationalReduction.reduceHeadObligation_is_right
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    {roles : ThreadedConstitutiveRoleStage run}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (reduction : ExecutedStageOperationalReduction roles tailRoles)
    (tail : IndependentStructuralObligation tailRoles) :
    reduction.reduceHeadObligation tail = .right tail := by
  unfold ExecutedStageOperationalReduction.reduceHeadObligation
  rw [reduction.materializedSelectsRetained]
  rfl

/-- The operational decision read from the continuation materially produced by
the complete discovered reduction.  Its variable remains the one recorded by
the authoritative role stage; its value is read from the executed output. -/
def ExecutedStageOperationalReduction.retainedDecision
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    {roles : ThreadedConstitutiveRoleStage run}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (reduction : ExecutedStageOperationalReduction roles tailRoles) :
    StructuralBranchDecision :=
  ⟨roles.executedDecision.var,
    reduction.materializedRetained.1 stage.discovery.var⟩

/-- Every canonical reduction materially selects the retained value; this
equation is proved from the output field rather than stipulated by the decision
normalizer below. -/
theorem ExecutedStageOperationalReduction.retainedDecision_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    {roles : ThreadedConstitutiveRoleStage run}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (reduction : ExecutedStageOperationalReduction roles tailRoles) :
    reduction.retainedDecision = ⟨roles.executedDecision.var, true⟩ := by
  unfold ExecutedStageOperationalReduction.retainedDecision
  rw [reduction.materializedSelectsRetained]

/-- The unique obligation retained by the recursively executed reductions. -/
def CausalOperationalStability.retainedOperationalObligation :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      CausalOperationalStability roles → IndependentStructuralObligation roles
  | _, _, _, _, _, _, .nil => .terminal
  | _, _, _, _, _, _, .step _ _ reduction tailStability =>
      reduction.reduceHeadObligation tailStability.retainedOperationalObligation

/-!
## Licensed operational reduction

The numerical fact that a singleton is smaller than a `2^n` carrier does not
by itself justify carrying only that singleton.  The following layer records
the missing constitutive content: every structural obligation must reach the
retained representative through a source-indexed plan.  A left step contains
the generated opening, discovered absorption, materially executed output,
criterion preservation, viability of the absorbed sibling, and exact
dependent-tail raccord.  A right step uses the separately typed retained-side
execution license, whose type and constructor contain no complete absorption
reduction.

The target of the normalization is deliberately allowed to be the same for
many sources.  What varies with the source is the typed reduction witness:
`left` sources use the discovered absorption constructor, whereas `right`
sources use the retained constructor.  Operational co-classification is thus
licensed by executed evidence rather than defined as equality under an
arbitrary constant function.
-/

/-- Evidence needed to keep the already-retained side.  Unlike the complete
`ExecutedStageOperationalReduction` required by `absorbLeft`, this record
contains no absorption and no source-to-retained preservation obtained through
absorption.  It therefore remains available in the ablated grammar below,
where crossing from the left sibling is deliberately impossible. -/
structure RetainedStageExecutionLicense
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) : Type 2 where
  openingFromGeneration :
    roles.structuralOpening =
      generatedStructuralSplit
        (constructStage (depth + 1)).operationalRoot
        stage.discovery.var
        stage.discovery.fresh
  materializedRetained : GeneratedStructuralBranchContinuation
    ((constructStage (depth + 1)).operationalRoot.child
      stage.discovery.var true stage.discovery.fresh)
  materializedFromDiscoveredOperation :
    materializedRetained = roles.materializedRetainedContinuation
  materializedIsExecuted :
    materializedRetained = roles.retainedContinuation
  materializedSelectsRetained :
    materializedRetained.1 stage.discovery.var = true
  raccord : RetainedNextConditionRaccord roles tailRoles

/-- Construct the non-absorptive retained-side evidence directly from the
authoritative role stage.  Its type and construction do not mention
`ExecutedStageOperationalReduction`; deleting the absorption-bearing witness
therefore leaves this operation available. -/
def ThreadedConstitutiveRoleStage.retentionLicense
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    (roles : ThreadedConstitutiveRoleStage run)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    RetainedStageExecutionLicense roles tailRoles :=
  { openingFromGeneration := roles.structuralOpeningFromGeneration
    materializedRetained := roles.materializedRetainedContinuation
    materializedFromDiscoveredOperation := rfl
    materializedIsExecuted := roles.materializedRetainedContinuation_exact
    materializedSelectsRetained :=
      roles.materializedRetainedContinuation_selected
    raccord := roles.retainedNextConditionRaccord tailRoles }

/-- The retained-side operation reads its branch from the materialized output
without requiring an absorption witness. -/
def RetainedStageExecutionLicense.retainHeadObligation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    {roles : ThreadedConstitutiveRoleStage run}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (license : RetainedStageExecutionLicense roles tailRoles)
    (tail : IndependentStructuralObligation tailRoles) :
    IndependentStructuralObligation
      (ThreadedConstitutiveRoleHistory.step roles tailRoles) :=
  if license.materializedRetained.1 stage.discovery.var = false then
    .left tail
  else
    .right tail

/-- The materialized retained-side operation selects the right constructor. -/
theorem RetainedStageExecutionLicense.retainHeadObligation_is_right
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) run.nextRun.next}
    {roles : ThreadedConstitutiveRoleStage run}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (license : RetainedStageExecutionLicense roles tailRoles)
    (tail : IndependentStructuralObligation tailRoles) :
    license.retainHeadObligation tail = .right tail := by
  unfold RetainedStageExecutionLicense.retainHeadObligation
  rw [license.materializedSelectsRetained]
  rfl

/-- Canonical representative constructed solely from non-absorptive
retained-side execution.  It remains defined in the exact ablated grammar. -/
def ThreadedConstitutiveRoleHistory.retentionLicensedOperationalObligation :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      IndependentStructuralObligation roles
  | _, _, _, _, _, .nil => .terminal
  | _, _, _, _, _, .step headRole tailRoles =>
      (headRole.retentionLicense tailRoles).retainHeadObligation
        tailRoles.retentionLicensedOperationalObligation

/-- Compatibility with the earlier complete-reduction representative.  The
new representative is constructed without reading absorption; equality with
the previous one is then proved separately. -/
theorem ThreadedConstitutiveRoleHistory.retentionLicensedOperationalObligation_eq_causal
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.retentionLicensedOperationalObligation =
      roles.causalOperationalStability.retainedOperationalObligation := by
  induction roles with
  | nil => rfl
  | step headRole tailRoles inductionHypothesis =>
      change (headRole.retentionLicense tailRoles).retainHeadObligation
          tailRoles.retentionLicensedOperationalObligation =
        (headRole.executedStageOperationalReduction tailRoles).reduceHeadObligation
          tailRoles.causalOperationalStability.retainedOperationalObligation
      rw [RetainedStageExecutionLicense.retainHeadObligation_is_right,
        ExecutedStageOperationalReduction.reduceHeadObligation_is_right,
        inductionHypothesis]

/-- A source-specific plan whose constructors retain every executed stage
license.  The target is the canonical retained obligation of the same role
history; indexing only by the source avoids identifying sources in order to
classify them. -/
inductive ThreadedConstitutiveRoleHistory.LicensedReductionPlan :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      IndependentStructuralObligation roles → Type 2 where
  | terminal {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      LicensedReductionPlan
        (ThreadedConstitutiveRoleHistory.nil (state := state)) .terminal
  | absorbLeft {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      {headRole : ThreadedConstitutiveRoleStage headRun}
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      {source : IndependentStructuralObligation tailRoles}
      (reduction : ExecutedStageOperationalReduction headRole tailRoles)
      (tailPlan : LicensedReductionPlan tailRoles source) :
      LicensedReductionPlan
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles) (.left source)
  | retainRight {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      {headRole : ThreadedConstitutiveRoleStage headRun}
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      {source : IndependentStructuralObligation tailRoles}
      (license :
        RetainedStageExecutionLicense headRole tailRoles)
      (tailPlan : LicensedReductionPlan tailRoles source) :
      LicensedReductionPlan
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles) (.right source)

/-- Construct the reduction plan directly from the source obligation.  A left
choice necessarily consumes the complete discovered reduction; a right choice
necessarily consumes the retained-side license. -/
def ThreadedConstitutiveRoleHistory.licensedReductionPlan :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      (source : IndependentStructuralObligation roles) →
      roles.LicensedReductionPlan source
  | _, _, _, _, _, _, .terminal => .terminal
  | _, _, _, _, _, _, .left (headRole := headRole) (tailRoles := tailRoles) source =>
      .absorbLeft
        (headRole.executedStageOperationalReduction tailRoles)
        (licensedReductionPlan source)
  | _, _, _, _, _, _, .right (headRole := headRole) (tailRoles := tailRoles) source =>
      .retainRight
        (headRole.retentionLicense tailRoles)
        (licensedReductionPlan source)

/-- Observable record of the source-specific licensed acts. -/
def ThreadedConstitutiveRoleHistory.LicensedReductionPlan.absorptionTrace :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      {source : IndependentStructuralObligation roles} →
      roles.LicensedReductionPlan source → List Bool
  | _, _, _, _, _, _, _, .terminal => []
  | _, _, _, _, _, _, _, .absorbLeft _ tailPlan =>
      true :: tailPlan.absorptionTrace
  | _, _, _, _, _, _, _, .retainRight _ tailPlan =>
      false :: tailPlan.absorptionTrace

/-- The plan trace is computed from the source: left choices are precisely the
stages that require absorption. -/
theorem ThreadedConstitutiveRoleHistory.licensedReductionPlan_trace
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (source : IndependentStructuralObligation roles) :
    (roles.licensedReductionPlan source).absorptionTrace =
      source.decisions.map (fun decision => !decision.value) := by
  induction source with
  | terminal => rfl
  | left tail ih =>
      change true :: _ = true :: _
      rw [ih]
  | right tail ih =>
      change false :: _ = false :: _
      rw [ih]

/-- Sibling sources require observably different licensed acts. -/
theorem ThreadedConstitutiveRoleHistory.siblingReductionPlanTraces_ne
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (source : IndependentStructuralObligation tailRoles) :
    ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
      |>.licensedReductionPlan (.left source)).absorptionTrace ≠
    ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
      |>.licensedReductionPlan (.right source)).absorptionTrace := by
  intro same
  have headSame := congrArg List.head? same
  change some true = some false at headSame
  cases headSame

/-- A positive history exhibits distinct sibling sources, their common
retained representative, and distinct source-indexed license plans. -/
structure ThreadedConstitutiveRoleHistory.SiblingLicenseSeparation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) : Type 2 where
  leftSource : IndependentStructuralObligation
    (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
  rightSource : IndependentStructuralObligation
    (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
  representative : IndependentStructuralObligation
    (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
  sourcesDistinct : leftSource ≠ rightSource
  leftPlan :
    ThreadedConstitutiveRoleHistory.LicensedReductionPlan
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles) leftSource
  rightPlan :
    ThreadedConstitutiveRoleHistory.LicensedReductionPlan
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles) rightSource
  operationalActsDistinct :
    leftPlan.absorptionTrace ≠ rightPlan.absorptionTrace

/-- The first opening constructs the sibling separation from the exact
executed role history. -/
def ThreadedConstitutiveRoleHistory.siblingLicenseSeparation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    ThreadedConstitutiveRoleHistory.SiblingLicenseSeparation
      headRole tailRoles :=
  let tailSource :=
    tailRoles.retentionLicensedOperationalObligation
  { leftSource := .left tailSource
    rightSource := .right tailSource
    representative :=
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
        |>.retentionLicensedOperationalObligation
    sourcesDistinct := IndependentStructuralObligation.left_ne_right _
    leftPlan :=
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
        |>.licensedReductionPlan (.left tailSource)
    rightPlan :=
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
        |>.licensedReductionPlan (.right tailSource)
    operationalActsDistinct :=
      siblingReductionPlanTraces_ne headRole tailRoles tailSource }

/-- A source-indexed normalization retains both the computed representative
and the complete plan licensing it. -/
structure ThreadedConstitutiveRoleHistory.LicensedNormalization
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (source : IndependentStructuralObligation roles) : Type 2 where
  target : IndependentStructuralObligation roles
  targetIsRetained :
    target = roles.retentionLicensedOperationalObligation
  plan : roles.LicensedReductionPlan source

def ThreadedConstitutiveRoleHistory.normalizeWithLicense
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (source : IndependentStructuralObligation roles) :
    roles.LicensedNormalization source :=
  { target := roles.retentionLicensedOperationalObligation
    targetIsRetained := rfl
    plan := roles.licensedReductionPlan source }

/-- Operational co-classification retains two distinct source plans to one
computed representative. -/
structure ThreadedConstitutiveRoleHistory.OperationalCoClassification
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (left right : IndependentStructuralObligation roles) : Type 2 where
  representative : IndependentStructuralObligation roles
  representativeIsRetained :
    representative = roles.retentionLicensedOperationalObligation
  leftPlan : roles.LicensedReductionPlan left
  rightPlan : roles.LicensedReductionPlan right

def ThreadedConstitutiveRoleHistory.coClassify
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (left right : IndependentStructuralObligation roles) :
    roles.OperationalCoClassification left right :=
  { representative :=
      roles.retentionLicensedOperationalObligation
    representativeIsRetained := rfl
    leftPlan := roles.licensedReductionPlan left
    rightPlan := roles.licensedReductionPlan right }

/-- One structural source reaches a representative that is actually carried by
the proposed operational carrier. -/
structure ThreadedConstitutiveRoleHistory.LicensedCoverageOfSource
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (representatives : List (IndependentStructuralObligation roles))
    (source : IndependentStructuralObligation roles) : Type 2 where
  normalization : roles.LicensedNormalization source
  targetMember : normalization.target ∈ representatives

/-- An operational carrier is legitimate only if it contains the computed
representative and every structural source carries its complete license plan. -/
structure ThreadedConstitutiveRoleHistory.LicensedOperationalCarrier
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) : Type 2 where
  representatives : List (IndependentStructuralObligation roles)
  representativesNodup : representatives.Nodup
  representativesStructural :
    ∀ target, target ∈ representatives →
      target ∈ roles.independentStructuralObligationFrontier
  retainedMember :
    roles.retentionLicensedOperationalObligation ∈
      representatives
  covers :
    (source : IndependentStructuralObligation roles) →
      source ∈ roles.independentStructuralObligationFrontier →
        roles.LicensedCoverageOfSource representatives source

/-- The executed reductions and retention licenses construct a legitimate
singleton carrier. -/
def ThreadedConstitutiveRoleHistory.licensedOperationalCarrier
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.LicensedOperationalCarrier :=
  { representatives :=
      [roles.retentionLicensedOperationalObligation]
    representativesNodup := by
      apply List.Pairwise.cons
      · intro other member
        cases member
      · exact .nil
    representativesStructural := by
      intro target member
      cases member with
      | head =>
          exact roles.independentStructuralObligationFrontier_complete _
      | tail _ impossible => cases impossible
    retainedMember := .head _
    covers := by
      intro source _sourceMember
      exact
        { normalization := roles.normalizeWithLicense source
          targetMember := .head _ } }

/-- The exact grammar obtained from `LicensedReductionPlan` by deleting only
`absorbLeft`.  The terminal and retained-side constructors remain, including
the material output and dependent-tail raccord, but no constructor can cross
from a left source.  Unlike an equality-based encoding, the reachable sources
are determined by the constructors themselves. -/
inductive ThreadedConstitutiveRoleHistory.AbsorptionFreeReductionPlan :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      IndependentStructuralObligation roles → Type 2 where
  | terminal {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      AbsorptionFreeReductionPlan
        (ThreadedConstitutiveRoleHistory.nil (state := state)) .terminal
  | retainRight {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      {headRole : ThreadedConstitutiveRoleStage headRun}
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      {source : IndependentStructuralObligation tailRoles}
      (license :
        RetainedStageExecutionLicense headRole tailRoles)
      (tailPlan : AbsorptionFreeReductionPlan tailRoles source) :
      AbsorptionFreeReductionPlan
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles) (.right source)

/-- The constructor grammar itself forces every absorption-free source to be
the recursively retained obligation.  This equality is derived from the plan;
it is not stored as a premise. -/
theorem ThreadedConstitutiveRoleHistory.AbsorptionFreeReductionPlan.sourceIsRetained
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    {source : IndependentStructuralObligation roles}
    (plan : roles.AbsorptionFreeReductionPlan source) :
    source = roles.retentionLicensedOperationalObligation := by
  induction plan with
  | terminal => rfl
  | @retainRight depth count assignment state head headRun tailRun headRole
      tailRoles source license tailPlan inductionHypothesis =>
      change IndependentStructuralObligation.right source =
        (headRole.retentionLicense tailRoles).retainHeadObligation
          tailRoles.retentionLicensedOperationalObligation
      rw [RetainedStageExecutionLicense.retainHeadObligation_is_right]
      exact congrArg IndependentStructuralObligation.right inductionHypothesis

/-- The retained obligation remains executable in the absorption-free grammar;
the ablation removes only the ability to cross from a left source. -/
def ThreadedConstitutiveRoleHistory.absorptionFreeRetainedPlan :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      roles.AbsorptionFreeReductionPlan
        roles.retentionLicensedOperationalObligation
  | _, _, _, _, _, .nil => .terminal
  | _, _, _, _, _, .step headRole tailRoles => by
      change AbsorptionFreeReductionPlan
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
        ((headRole.retentionLicense tailRoles).retainHeadObligation
          tailRoles.retentionLicensedOperationalObligation)
      rw [RetainedStageExecutionLicense.retainHeadObligation_is_right]
      exact .retainRight (headRole.retentionLicense tailRoles)
        tailRoles.absorptionFreeRetainedPlan

/-- Removing the absorption constructor makes every left source unreducible,
even though retained-side execution and every dependent-tail raccord remain. -/
theorem noAbsorptionFreeReductionFromLeft
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (source : IndependentStructuralObligation tailRoles) :
    ¬ Nonempty
        (ThreadedConstitutiveRoleHistory.AbsorptionFreeReductionPlan
          (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
          (.left source)) := by
  rintro ⟨plan⟩
  have impossible := plan.sourceIsRetained
  change IndependentStructuralObligation.left source =
    (headRole.retentionLicense tailRoles).retainHeadObligation
      tailRoles.retentionLicensedOperationalObligation at impossible
  rw [RetainedStageExecutionLicense.retainHeadObligation_is_right]
    at impossible
  cases impossible

/-- A proposed singleton carrier in the exact absorption-free grammar.  It
retains every non-absorptive stage operation but must provide a reduction plan
for every structural source. -/
structure AbsorptionFreeSingletonCoverage
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) : Type 2 where
  representative : IndependentStructuralObligation roles
  representativeIsRetained :
    representative = roles.retentionLicensedOperationalObligation
  covers :
    (source : IndependentStructuralObligation roles) →
      source ∈ roles.independentStructuralObligationFrontier →
        roles.AbsorptionFreeReductionPlan source

/-- At a positive opening, the absorption-free grammar cannot cover the left
sibling and therefore cannot constitute singleton operational coverage. -/
theorem noAbsorptionFreeSingletonCoverage
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    ¬ Nonempty
      (AbsorptionFreeSingletonCoverage
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) := by
  rintro ⟨coverage⟩
  let tailSource :=
    tailRoles.retentionLicensedOperationalObligation
  have leftMember :
      (IndependentStructuralObligation.left tailSource :
        IndependentStructuralObligation
          (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) ∈
        ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
          |>.independentStructuralObligationFrontier) :=
    (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
      |>.independentStructuralObligationFrontier_complete _
  exact noAbsorptionFreeReductionFromLeft headRole tailRoles tailSource
    ⟨coverage.covers (.left tailSource) leftMember⟩

/-- Extensional decision-path normalizer retained for compatibility.  It reads
the executed retained decision at every stage and consumes only the source
tail.  Source-sensitive causal evidence is carried instead by
`LicensedReductionPlan`. -/
def CausalOperationalStability.normalizeDecisionPath :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      CausalOperationalStability roles →
      List StructuralBranchDecision → List StructuralBranchDecision
  | _, _, _, _, _, _, .nil, _ => []
  | _, _, _, _, _, _, .step _ _ reduction tailStability, [] =>
      reduction.retainedDecision :: tailStability.normalizeDecisionPath []
  | _, _, _, _, _, _, .step _ _ reduction tailStability, _ :: sourceTail =>
      reduction.retainedDecision ::
        tailStability.normalizeDecisionPath sourceTail

/-- Constant projection to the retained obligation.  Its singleton image is an
extensional corollary only; causal authorization is supplied separately by the
source-indexed licensed plans and the absorption-free impossibility theorem. -/
def CausalOperationalStability.collapseStructuralObligation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (_obligation : IndependentStructuralObligation roles) :
    IndependentStructuralObligation roles :=
  stability.retainedOperationalObligation

/-- The constant projection has the retained obligation as its exact value. -/
theorem CausalOperationalStability.collapseStructuralObligation_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (obligation : IndependentStructuralObligation roles) :
    stability.collapseStructuralObligation obligation =
      stability.retainedOperationalObligation := by
  rfl

/-- Apply the extensional decision-path normalizer to one complete obligation. -/
def ThreadedConstitutiveRoleHistory.materiallyNormalizedDecisionPath
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (obligation : IndependentStructuralObligation roles) :
    List StructuralBranchDecision :=
  roles.causalOperationalStability.normalizeDecisionPath obligation.decisions

/-- The decision path of the obligation retained by the canonical executed
reduction chain. -/
def ThreadedConstitutiveRoleHistory.retainedOperationalDecisionPath
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    List StructuralBranchDecision :=
  roles.causalOperationalStability.retainedOperationalObligation.decisions

/-- Every complete structural obligation is materially normalized to the path
retained by the canonical chain of executed reductions. -/
theorem ThreadedConstitutiveRoleHistory.materiallyNormalizedDecisionPath_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (obligation : IndependentStructuralObligation roles) :
    roles.materiallyNormalizedDecisionPath obligation =
      roles.retainedOperationalDecisionPath := by
  induction obligation with
  | terminal => rfl
  | left tail inductionHypothesis | right tail inductionHypothesis =>
      rename_i depth0 count0 assignment0 state0 head0 headRun0 tailRun0
        headRole tailRoles
      let reduction := headRole.executedStageOperationalReduction tailRoles
      change
        reduction.retainedDecision ::
            tailRoles.materiallyNormalizedDecisionPath tail =
          (reduction.reduceHeadObligation
            tailRoles.causalOperationalStability.retainedOperationalObligation).decisions
      have reducedDecisions := congrArg
        (fun retained => retained.decisions)
        (reduction.reduceHeadObligation_is_right
          tailRoles.causalOperationalStability.retainedOperationalObligation)
      exact Eq.trans
        (congrArg (List.cons reduction.retainedDecision) inductionHypothesis)
        (Eq.trans
          (congrArg
            (fun decision =>
              decision :: tailRoles.retainedOperationalDecisionPath)
            reduction.retainedDecision_exact)
          reducedDecisions.symm)

/-- Extensional co-classification by decision-path normalization. -/
def ThreadedConstitutiveRoleHistory.MateriallyOperationallyIdentified
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (left right : IndependentStructuralObligation roles) : Prop :=
  roles.materiallyNormalizedDecisionPath left =
    roles.materiallyNormalizedDecisionPath right

/-- Every pair has the same extensional normalized path.  This theorem does not
by itself license the classification; that role belongs to the reduction
plans. -/
theorem ThreadedConstitutiveRoleHistory.allStructuralObligationsMateriallyIdentified
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (left right : IndependentStructuralObligation roles) :
    roles.MateriallyOperationallyIdentified left right := by
  unfold ThreadedConstitutiveRoleHistory.MateriallyOperationallyIdentified
  exact Eq.trans
    (roles.materiallyNormalizedDecisionPath_exact left)
    (roles.materiallyNormalizedDecisionPath_exact right).symm

/-- The canonical obligation-level collapse agrees with material path
normalization on every complete structural obligation. -/
theorem ThreadedConstitutiveRoleHistory.collapseDecisionsFollowMaterialNormalization
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history)
    (obligation : IndependentStructuralObligation roles) :
    (roles.causalOperationalStability.collapseStructuralObligation
      obligation).decisions =
        roles.materiallyNormalizedDecisionPath obligation := by
  exact Eq.trans
    (congrArg IndependentStructuralObligation.decisions
      (roles.causalOperationalStability.collapseStructuralObligation_exact
        obligation))
    (roles.materiallyNormalizedDecisionPath_exact obligation).symm

/-- Extensional equality under the constant retained projection.  This
relation does not identify the structural obligations and is not the causal
license for their co-classification. -/
def CausalOperationalStability.OperationallyIdentified
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (left right : IndependentStructuralObligation roles) : Prop :=
  stability.collapseStructuralObligation left =
    stability.collapseStructuralObligation right

/-- Every pair has the same image under the constant retained projection.
Licensed operational coverage is established separately. -/
theorem CausalOperationalStability.allStructuralObligationsOperationallyIdentified
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (left right : IndependentStructuralObligation roles) :
    stability.OperationallyIdentified left right := by
  unfold CausalOperationalStability.OperationallyIdentified
  rw [stability.collapseStructuralObligation_exact left,
    stability.collapseStructuralObligation_exact right]

/-- Membership in the operational image of the full structural carrier. -/
def CausalOperationalStability.InOperationalImage
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (target : IndependentStructuralObligation roles) : Prop :=
  ∃ source,
    source ∈ roles.independentStructuralObligationFrontier ∧
      stability.collapseStructuralObligation source = target

/-- Singleton image of the extensional retained projection. -/
def CausalOperationalStability.retainedOperationalObligationFrontier
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles) :
    List (IndependentStructuralObligation roles) :=
  [stability.retainedOperationalObligation]

theorem CausalOperationalStability.retainedOperationalObligationFrontier_length
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles) :
    stability.retainedOperationalObligationFrontier.length = 1 := by
  rfl

/-- The retained obligation is one of the obligations constituted by the exact
role history. -/
theorem CausalOperationalStability.retainedOperationalObligation_mem_structural
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles) :
    stability.retainedOperationalObligation ∈
      roles.independentStructuralObligationFrontier :=
  roles.independentStructuralObligationFrontier_complete
    stability.retainedOperationalObligation

/-- The image of the constant retained projection is exactly its singleton. -/
theorem CausalOperationalStability.inOperationalImage_iff_eq_retained
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (target : IndependentStructuralObligation roles) :
    stability.InOperationalImage target ↔
      target = stability.retainedOperationalObligation := by
  constructor
  · intro inImage
    rcases inImage with ⟨source, _sourceMember, sourceExact⟩
    rw [stability.collapseStructuralObligation_exact source] at sourceExact
    exact sourceExact.symm
  · intro targetExact
    rw [targetExact]
    exact
      ⟨stability.retainedOperationalObligation,
        stability.retainedOperationalObligation_mem_structural,
        stability.collapseStructuralObligation_exact
          stability.retainedOperationalObligation⟩

/-- The constant projection sends every structural member into its singleton
image. -/
theorem CausalOperationalStability.collapseStructuralObligation_mem_retained
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles)
    (obligation : IndependentStructuralObligation roles)
    (_member : obligation ∈ roles.independentStructuralObligationFrontier) :
    stability.collapseStructuralObligation obligation ∈
      stability.retainedOperationalObligationFrontier := by
  rw [stability.collapseStructuralObligation_exact obligation]
  exact .head _

/-- Bare numerical comparison between the retained singleton and the `2^n`
structural carrier.  The causal prevention result is the stronger
`CausalExponentialPreventionCertificate` below. -/
theorem CausalOperationalStability.retainedWidth_lt_structuralWidth
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count + 1) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (stability : CausalOperationalStability roles) :
    stability.retainedOperationalObligationFrontier.length <
      roles.independentStructuralObligationFrontier.length := by
  rw [stability.retainedOperationalObligationFrontier_length,
    roles.independentStructuralObligationFrontier_length]
  simpa only [Nat.pow_zero] using
    (Constructive.two_pow_strictly_grows (Nat.zero_lt_succ count))

/-- The causal prevention result is not the bare inequality `1 < 2^n`.
It packages the complete structural carrier, a singleton operational carrier
whose coverage is witnessed source by source by executed reductions and
retention licenses, an observable sibling distinction in the plans, and the constructive
failure of singleton coverage when absorption is unavailable. -/
structure CausalExponentialPreventionCertificate
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) : Type 2 where
  licensedCarrier :
    ThreadedConstitutiveRoleHistory.LicensedOperationalCarrier
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
  licensedCarrierWidthOne : licensedCarrier.representatives.length = 1
  structuralCarrierWidthExponential :
    ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
      |>.independentStructuralObligationFrontier).length =
      2 ^ (count + 1)
  structuralCarrierDistinct :
    ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
      |>.independentStructuralObligationFrontier).Nodup
  absorptionComesFromExecutedDiscovery :
    headRole.operationalAbsorption =
      AcceptedFrontierPreservation.absorbFirstIntoSecond
        head.discovery.relation.toAcceptingTransport
  sourceToRetainedPreservationUsesAbsorption :
    headRole.fullOperationalPreservation =
      headRole.openingPreservation.trans headRole.operationalAbsorption
  retainedMaterialIsExecuted :
    headRole.materializedRetainedContinuation = headRole.retainedContinuation
  absorbedSiblingRemainsViable :
    FrontierViable
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      [(constructStage (depth + 1)).operationalRoot.child
        head.discovery.var false head.discovery.fresh]
  siblingLicensesAreSourceSpecific :
    ThreadedConstitutiveRoleHistory.SiblingLicenseSeparation headRole tailRoles
  retainedSurvivesWithoutAbsorption :
    (ThreadedConstitutiveRoleHistory.step headRole tailRoles)
      |>.AbsorptionFreeReductionPlan
        ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
          |>.retentionLicensedOperationalObligation)
  withoutAbsorptionNoSingletonCoverage :
    ¬ Nonempty (AbsorptionFreeSingletonCoverage
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles))
  licensedWidthStrictlySmaller :
    licensedCarrier.representatives.length <
      ((ThreadedConstitutiveRoleHistory.step headRole tailRoles)
        |>.independentStructuralObligationFrontier).length

/-- Construct the full causal prevention certificate from the authoritative
recursive stability witness.  The construction necessarily exposes a positive
head stage: that stage supplies the absorption reduction whose removal leaves no
singleton coverage. -/
def ThreadedConstitutiveRoleHistory.causalExponentialPreventionCertificate
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    ConstitutiveSearch.EndogenousDecomposition.CausalExponentialPreventionCertificate
      headRole tailRoles :=
  let completeRoles :=
    ThreadedConstitutiveRoleHistory.step headRole tailRoles
  let carrier := completeRoles.licensedOperationalCarrier
  { licensedCarrier := carrier
    licensedCarrierWidthOne := by rfl
    structuralCarrierWidthExponential :=
      completeRoles.independentStructuralObligationFrontier_length
    structuralCarrierDistinct :=
      completeRoles.independentStructuralObligationFrontier_nodup
    absorptionComesFromExecutedDiscovery :=
      headRole.operationalAbsorption_from_discovery
    sourceToRetainedPreservationUsesAbsorption := rfl
    retainedMaterialIsExecuted :=
      headRole.materializedRetainedContinuation_exact
    absorbedSiblingRemainsViable := headRole.absorbedSiblingViable
    siblingLicensesAreSourceSpecific :=
      siblingLicenseSeparation headRole tailRoles
    retainedSurvivesWithoutAbsorption :=
      completeRoles.absorptionFreeRetainedPlan
    withoutAbsorptionNoSingletonCoverage :=
      noAbsorptionFreeSingletonCoverage headRole tailRoles
    licensedWidthStrictlySmaller := by
      exact completeRoles.causalOperationalStability
        |>.retainedWidth_lt_structuralWidth }

/-- Recursive causal prevention evidence aligned with the exact role history.
Every positive constructor contains its local prevention certificate; the
terminal constructor contains no invented opening. -/
inductive CausalExponentialPreventionHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      CausalExponentialPreventionHistory
        (ThreadedConstitutiveRoleHistory.nil (state := state))
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      {headRole : ThreadedConstitutiveRoleStage headRun}
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      (headCertificate :
        CausalExponentialPreventionCertificate headRole tailRoles)
      (tailCertificate : CausalExponentialPreventionHistory tailRoles) :
      CausalExponentialPreventionHistory
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)

/-- Build prevention evidence at every opening, from the same recursive role
history that carries the executed reductions. -/
def ThreadedConstitutiveRoleHistory.causalExponentialPreventionHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      (roles : ThreadedConstitutiveRoleHistory history) →
      CausalExponentialPreventionHistory roles
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .step headRole tailRoles =>
      .step
        (causalExponentialPreventionCertificate headRole tailRoles)
        tailRoles.causalExponentialPreventionHistory

/-- Number of openings for which the recursive prevention evidence carries a
local causal certificate. -/
def CausalExponentialPreventionHistory.stageCount :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : ConstitutiveExecutionHistory (count := count) state} →
      {roles : ThreadedConstitutiveRoleHistory history} →
      CausalExponentialPreventionHistory roles → Nat
  | _, _, _, _, _, _, .nil => 0
  | _, _, _, _, _, _, .step _ tailCertificate =>
      tailCertificate.stageCount + 1

/-- Prevention evidence has one local certificate for every exact opening in
the authoritative role history. -/
theorem CausalExponentialPreventionHistory.stageCount_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (prevention : CausalExponentialPreventionHistory roles) :
    prevention.stageCount = count := by
  induction prevention with
  | nil => rfl
  | step _ tailCertificate inductionHypothesis =>
      change tailCertificate.stageCount + 1 = _
      rw [inductionHypothesis]

/-- Numerical corollary: the retained and next carriers are both singleton.
The proof-relevant raccord is `RetainedNextConditionRaccord`; this equality is
not used as a substitute for it. -/
theorem retainedWidth_eq_nextInitialWidth
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    headRole.retainedFrontier.length = tailRoles.initialOperationalWidth := by
  cases tailRoles <;> rfl

/-- One executed stage has the exact singleton/split/singleton profile. -/
theorem ThreadedConstitutiveRoleHistory.oneStep_operationalWidthTrace
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := 1) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    roles.operationalWidthTrace = [1, 2, 1] :=
  roles.operationalWidthTrace_exact

/--
Integrated certificate: the role index already carries every stagewise
preservation witness, while these fields expose the exact global width facts.
-/
structure OperationalStabilityCertificate
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (history : ConstitutiveExecutionHistory (count := count) state)
    (roles : ThreadedConstitutiveRoleHistory history) : Type 2 where
  causalStability : CausalOperationalStability roles
  causalExponentialPrevention :
    CausalExponentialPreventionHistory roles
  retainedOperationalWidthOne :
    causalStability.retainedOperationalObligationFrontier.length = 1
  structuralWidthExponential :
    roles.independentStructuralObligationFrontier.length = 2 ^ count
  structuralObligationsDistinct :
    roles.independentStructuralObligationFrontier.Nodup
  retainedObligationIsStructural :
    causalStability.retainedOperationalObligation ∈
      roles.independentStructuralObligationFrontier
  causalCollapseIntoRetainedCarrier :
    ∀ obligation,
      obligation ∈ roles.independentStructuralObligationFrontier →
      causalStability.collapseStructuralObligation obligation ∈
        causalStability.retainedOperationalObligationFrontier
  causalCollapseImageExact :
    ∀ target,
      causalStability.InOperationalImage target ↔
        target = causalStability.retainedOperationalObligation
  materialNormalizationExact :
    (obligation : IndependentStructuralObligation roles) →
      roles.materiallyNormalizedDecisionPath obligation =
        roles.retainedOperationalDecisionPath
  materialCollapseFollowsNormalization :
    (obligation : IndependentStructuralObligation roles) →
      (roles.causalOperationalStability.collapseStructuralObligation
        obligation).decisions =
          roles.materiallyNormalizedDecisionPath obligation
  materialOperationalIdentification :
    (left right : IndependentStructuralObligation roles) →
      roles.MateriallyOperationallyIdentified left right
  widthTraceExact :
    roles.operationalWidthTrace = alternatingOperationalWidthTrace count
  widthTraceLength :
    roles.operationalWidthTrace.length = 2 * count + 1
  widthValuesAreOneOrTwo :
    ∀ width, width ∈ roles.operationalWidthTrace → width = 1 ∨ width = 2
  widthUniformlyBounded :
    ∀ width, width ∈ roles.operationalWidthTrace → width ≤ 2

def ThreadedConstitutiveRoleHistory.operationalStabilityCertificate
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory history) :
    OperationalStabilityCertificate history roles :=
  let causal := roles.causalOperationalStability
  { causalStability := causal
    causalExponentialPrevention :=
      roles.causalExponentialPreventionHistory
    retainedOperationalWidthOne :=
      causal.retainedOperationalObligationFrontier_length
    structuralWidthExponential :=
      roles.independentStructuralObligationFrontier_length
    structuralObligationsDistinct :=
      roles.independentStructuralObligationFrontier_nodup
    retainedObligationIsStructural :=
      causal.retainedOperationalObligation_mem_structural
    causalCollapseIntoRetainedCarrier :=
      causal.collapseStructuralObligation_mem_retained
    causalCollapseImageExact :=
      causal.inOperationalImage_iff_eq_retained
    materialNormalizationExact :=
      roles.materiallyNormalizedDecisionPath_exact
    materialCollapseFollowsNormalization :=
      roles.collapseDecisionsFollowMaterialNormalization
    materialOperationalIdentification :=
      roles.allStructuralObligationsMateriallyIdentified
    widthTraceExact := roles.operationalWidthTrace_exact
    widthTraceLength := roles.operationalWidthTrace_length
    widthValuesAreOneOrTwo := roles.operationalWidthTrace_value
    widthUniformlyBounded := roles.operationalWidth_le_two }

/-- On every positive authoritative history, the certificate separates the
single carried operational obligation from the `2^n` carrier that would result
from keeping every binary alternative independent. -/
theorem OperationalStabilityCertificate.preventsExponentialOperationalAccumulation
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : ConstitutiveExecutionHistory (count := count + 1) state}
    {roles : ThreadedConstitutiveRoleHistory history}
    (certificate : OperationalStabilityCertificate history roles) :
    certificate.causalStability.retainedOperationalObligationFrontier.length <
      roles.independentStructuralObligationFrontier.length :=
  certificate.causalStability.retainedWidth_lt_structuralWidth

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.sourceFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.openedFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retainedFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.sourceFrontier_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.openedFrontier_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retainedFrontier_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.openingPreservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.fullOperationalPreservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.operationalAbsorption_from_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.opened_retained_viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.source_retained_viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.absorbedSiblingViable
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retainedContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.materializedRetainedContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.materializedRetainedContinuation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.materializedRetainedContinuation_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.nextSourceContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retainedContinuation_assignment_eq_nextSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.initialSourceContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retainedContinuation_assignment_eq_tailSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.RetainedNextConditionRaccord
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retainedNextConditionRaccord
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.executedStageOperationalReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.causalOperationalStability
#print axioms ConstitutiveSearch.EndogenousDecomposition.singletonFrontierWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.alternatingOperationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.initialOperationalWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.operationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace_value
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidth_le_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentStructuralObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentStructuralObligation.left_ne_right
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentStructuralObligation.decisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentStructuralObligation.decisions_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.member_map_forward_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.member_map_inverse_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.member_append_right_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.member_append_cases_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.map_nodup_injective_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.append_nodup_disjoint_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.listLengthAppendUniverseConstructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.listMapLengthUniverseConstructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.member_append_left_universe_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.independentStructuralObligationFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalReduction.reduceHeadObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalReduction.reduceHeadObligation_is_right
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalReduction.retainedDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalReduction.retainedDecision_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.collapseStructuralObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.retainedOperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.RetainedStageExecutionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.retentionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.RetainedStageExecutionLicense.retainHeadObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.RetainedStageExecutionLicense.retainHeadObligation_is_right
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.retentionLicensedOperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.retentionLicensedOperationalObligation_eq_causal
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.LicensedReductionPlan
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.licensedReductionPlan
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.LicensedReductionPlan.absorptionTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.licensedReductionPlan_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.siblingReductionPlanTraces_ne
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.SiblingLicenseSeparation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.siblingLicenseSeparation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.LicensedNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.normalizeWithLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.OperationalCoClassification
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.coClassify
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.LicensedCoverageOfSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.LicensedOperationalCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.licensedOperationalCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.AbsorptionFreeReductionPlan
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.AbsorptionFreeReductionPlan.sourceIsRetained
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.absorptionFreeRetainedPlan
#print axioms ConstitutiveSearch.EndogenousDecomposition.noAbsorptionFreeReductionFromLeft
#print axioms ConstitutiveSearch.EndogenousDecomposition.AbsorptionFreeSingletonCoverage
#print axioms ConstitutiveSearch.EndogenousDecomposition.noAbsorptionFreeSingletonCoverage
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.normalizeDecisionPath
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.collapseStructuralObligation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.materiallyNormalizedDecisionPath
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.retainedOperationalDecisionPath
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.materiallyNormalizedDecisionPath_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.MateriallyOperationallyIdentified
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.allStructuralObligationsMateriallyIdentified
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.collapseDecisionsFollowMaterialNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.OperationallyIdentified
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.allStructuralObligationsOperationallyIdentified
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.InOperationalImage
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.retainedOperationalObligationFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.retainedOperationalObligationFrontier_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.retainedOperationalObligation_mem_structural
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.inOperationalImage_iff_eq_retained
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.collapseStructuralObligation_mem_retained
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalStability.retainedWidth_lt_structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalExponentialPreventionCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.causalExponentialPreventionCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalExponentialPreventionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.causalExponentialPreventionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalExponentialPreventionHistory.stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalExponentialPreventionHistory.stageCount_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedWidth_eq_nextInitialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.oneStep_operationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalStabilityCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalStabilityCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalStabilityCertificate.preventsExponentialOperationalAccumulation
/- AXIOM_AUDIT_END -/
