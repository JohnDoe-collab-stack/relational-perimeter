import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFeedback

/-!
# Endogenous operational stability

The operational width trace in this module is read from the authoritative
dependent role history.  Every nonterminal role carries the exact binary
opening and the acceptance-preserving absorption reconstructed from that
stage's own discovery.  No parallel trajectory is introduced.
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
  | _, _, _, state, _, .nil => [singletonFrontierWidth state]
  | _, _, _, _, _, .step headRole tailRoles =>
      headRole.sourceFrontier.length ::
        headRole.openedFrontier.length ::
          tailRoles.operationalWidthTrace

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

/-- The retained singleton and the next dependent condition have equal width. -/
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
  { widthTraceExact := roles.operationalWidthTrace_exact
    widthTraceLength := roles.operationalWidthTrace_length
    widthValuesAreOneOrTwo := roles.operationalWidthTrace_value
    widthUniformlyBounded := roles.operationalWidth_le_two }

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
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.opened_retained_viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleStage.source_retained_viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.singletonFrontierWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.alternatingOperationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.initialOperationalWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidthTrace_value
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalWidth_le_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedWidth_eq_nextInitialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.oneStep_operationalWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalStabilityCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveRoleHistory.operationalStabilityCertificate
/- AXIOM_AUDIT_END -/
