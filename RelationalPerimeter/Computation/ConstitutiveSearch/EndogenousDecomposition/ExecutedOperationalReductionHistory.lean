import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReduction

/-!
# Causally threaded operational reductions

The tail of this history is indexed by the exact next state produced by its
head.  Structural profiles keep both positions of every opening.  Operational
profiles use the positions of the frontier actually retained by the executed
reduction.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Proof-only certificate for the reduction computed from one executed run. -/
structure ExecutedOperationalReductionEvidence {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : Type where
  outcomeExact :
    run.discoveryRun.outcome.discovered? = some stage.discovery
  retainedExact :
    (executedSiblingReduction run).retained =
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh]
  leftActionExact :
    ∀ continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh),
      (executedSiblingReduction run).preservation.forward.map
          (.head continuation) =
        .head (stage.discovery.relation.mapContinuation continuation)
  rightActionExact :
    ∀ continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh),
      (executedSiblingReduction run).preservation.forward.map
          (.tail (.head continuation)) = .head continuation
  criterionPreserved :
    ∀ (continuation : GeneratedStructuralBranchContinuation
        ((constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var false stage.discovery.fresh)),
      GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var false stage.discovery.fresh) continuation →
        GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var true stage.discovery.fresh)
          (stage.discovery.relation.mapContinuation continuation)
  sourceSiblingViable :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
      stage.schedule.entry.source
  targetSiblingViable :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
      stage.schedule.entry.target
  siblingsDistinct :
    (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh ≠
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh
  applicationUsesReturnedRelation :
    stage.application.output =
      stage.schedule.entry.relation.mapContinuation stage.sourceContinuation
  outputConstitutesNext :
    stage.application.output.1 =
      run.nextRun.next.threadedAssignment.assignment

/-- Construct the certificate solely from the executed run. -/
def executedOperationalReductionEvidence {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ExecutedOperationalReductionEvidence run :=
  { outcomeExact := executedTransformation_from_discoveryOutcome run
    retainedExact := executedSiblingReduction_retained run
    leftActionExact := executedSiblingReduction_left_eq_discoveredMap run
    rightActionExact := executedSiblingReduction_right_eq_identity run
    criterionPreserved := executedSiblingReduction_preservesAccept run
    sourceSiblingViable := executedSourceSibling_viable run
    targetSiblingViable := executedTargetSibling_viable run
    siblingsDistinct := executedSiblingStates_distinct run
    applicationUsesReturnedRelation := stageApplication_eq_returnedRelationMap run
    outputConstitutesNext := executedOutput_eq_nextOperationalAssignment run }

/--
Dependent certificate history.  Its recursive tail has the type carried by the
authoritative role history, hence is rooted in `headRun.nextRun.next`.
-/
def ExecutedOperationalReductionHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ExecutedOperationalReductionEvidence headRun ×
        ExecutedOperationalReductionHistory tailRoles

/-- Build the unique reduction certificate history from the role history. -/
def buildExecutedOperationalReductionHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      ExecutedOperationalReductionHistory roles
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ⟨executedOperationalReductionEvidence headRun,
        buildExecutedOperationalReductionHistory tailRoles⟩

/-- Number of openings read recursively from the dependent role history. -/
def operationalStageCount :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Nat
  | _, _, _, _, _, .nil => 0
  | _, _, _, _, _, .step _ tail => operationalStageCount tail + 1

/-- The dependent role history contains exactly the openings of its indexed
authoritative execution history. -/
theorem operationalStageCount_eq_historyCount :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      operationalStageCount roles = count
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .step _ tail =>
      congrArg (fun value => value + 1)
        (operationalStageCount_eq_historyCount tail)

/-- One independent left/right role for every constituted opening. -/
def StructuralObligation :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, .step _ tail => Bool × StructuralObligation tail

/-- Pending profiles retain the same two roles at every opening. -/
abbrev PendingOperationalObligation {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :=
  StructuralObligation roles

/-- The unique position of a singleton retained frontier. -/
def executedRetainedPosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    Fin (executedSiblingReduction run).retained.length :=
  ⟨0, by rw [executedSiblingReduction_retained]; exact Nat.zero_lt_succ 0⟩

/-- Operational profiles use the positions of the actually retained lists. -/
def OperationalObligation :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      Fin (executedSiblingReduction headRun).retained.length ×
        OperationalObligation tailRoles

/-- Enumerate every structural role profile constructively. -/
def structuralFrontier :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      List (StructuralObligation roles)
  | _, _, _, _, _, .nil => [()]
  | _, _, _, _, _, .step _ tail =>
      (structuralFrontier tail).map (fun rest => (false, rest)) ++
        (structuralFrontier tail).map (fun rest => (true, rest))

/-- Pending enumeration is the relation-erased structural enumeration. -/
def pendingFrontier {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    List (PendingOperationalObligation roles) :=
  structuralFrontier roles

/-- Enumerate profiles of retained positions from the executed reductions. -/
def operationalFrontier :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      List (OperationalObligation roles)
  | _, _, _, _, _, .nil => [()]
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      (operationalFrontier tailRoles).map
        (fun rest => (executedRetainedPosition headRun, rest))

def structuralWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Nat :=
  (structuralFrontier roles).length

def pendingWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Nat :=
  (pendingFrontier roles).length

def executedWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Nat :=
  (operationalFrontier roles).length

/-- Constructive length preservation for maps, independent of the core theorem. -/
theorem length_map_constructive {α β : Type} (f : α → β) :
    ∀ values : List α, (values.map f).length = values.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (length_map_constructive f tail)

/-- Left zero for natural addition, proved by structural recursion. -/
theorem zero_add_constructive : ∀ value : Nat, 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (zero_add_constructive value)

/-- A successor in the left summand commutes with structural addition. -/
theorem succ_add_constructive (left : Nat) :
    ∀ right : Nat,
      Nat.succ left + right = Nat.succ (left + right)
  | 0 => rfl
  | right + 1 => congrArg Nat.succ (succ_add_constructive left right)

/-- Constructive length of append, independent of the core theorem. -/
theorem length_append_constructive {α : Type} :
    ∀ left right : List α,
      (left ++ right).length = left.length + right.length
  | [], right => (zero_add_constructive right.length).symm
  | _ :: tail, right => Eq.trans
      (congrArg Nat.succ (length_append_constructive tail right))
      (succ_add_constructive tail.length right.length).symm

/-- Combine two equalities under natural-number addition. -/
theorem nat_add_congr {left left' right right' : Nat}
    (hLeft : left = left') (hRight : right = right') :
    left + right = left' + right' := by
  cases hLeft
  cases hRight
  rfl

theorem structuralWidth_eq_two_pow_stageCount :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      structuralWidth roles = 2 ^ operationalStageCount roles
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .step _ tail => by
      change
        ((structuralFrontier tail).map (fun rest => (false, rest)) ++
          (structuralFrontier tail).map (fun rest => (true, rest))).length =
            2 ^ (operationalStageCount tail + 1)
      have tailWidth : (structuralFrontier tail).length =
          2 ^ operationalStageCount tail :=
        structuralWidth_eq_two_pow_stageCount tail
      calc
        ((structuralFrontier tail).map (fun rest => (false, rest)) ++
          (structuralFrontier tail).map (fun rest => (true, rest))).length =
            ((structuralFrontier tail).map
              (fun rest => (false, rest))).length +
            ((structuralFrontier tail).map
              (fun rest => (true, rest))).length :=
                length_append_constructive _ _
        _ = (structuralFrontier tail).length +
            (structuralFrontier tail).length :=
              nat_add_congr
                (length_map_constructive (fun rest => (false, rest)) _)
                (length_map_constructive (fun rest => (true, rest)) _)
        _ = 2 ^ operationalStageCount tail +
            2 ^ operationalStageCount tail :=
              nat_add_congr tailWidth tailWidth
        _ = 2 ^ operationalStageCount tail * 2 :=
              (Nat.mul_two _).symm
        _ = 2 ^ (operationalStageCount tail + 1) :=
              (Nat.pow_succ 2 (operationalStageCount tail)).symm

theorem pendingWidth_eq_structuralWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    pendingWidth roles = structuralWidth roles :=
  rfl

theorem pendingWidth_eq_two_pow_stageCount {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    pendingWidth roles = 2 ^ operationalStageCount roles := by
  exact structuralWidth_eq_two_pow_stageCount roles

theorem executedWidth_eq_one :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      executedWidth roles = 1
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles => by
      change
        ((operationalFrontier tailRoles).map
          (fun rest => (executedRetainedPosition headRun, rest))).length = 1
      have tailWidth : (operationalFrontier tailRoles).length = 1 :=
        executedWidth_eq_one tailRoles
      exact Eq.trans
        (length_map_constructive
          (fun rest => (executedRetainedPosition headRun, rest)) _)
        tailWidth

/-- Constructively transport membership through a list map. -/
theorem mem_map_constructive {α β : Type} (f : α → β) {value : α} :
    ∀ {values : List α}, List.Mem value values →
      List.Mem (f value) (values.map f)
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ prior => .tail _ (mem_map_constructive f prior)

/-- Constructively preserve membership in the left side of an append. -/
theorem mem_append_left_constructive {α : Type} {value : α} :
    ∀ {left : List α} (right : List α), List.Mem value left →
      List.Mem value (left ++ right)
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ prior =>
      .tail _ (mem_append_left_constructive _ prior)

/-- Constructively preserve membership in the right side of an append. -/
theorem mem_append_right_constructive {α : Type} {value : α} :
    ∀ (left : List α) {right : List α}, List.Mem value right →
      List.Mem value (left ++ right)
  | [], _, prior => prior
  | _ :: tail, _, prior =>
      .tail _ (mem_append_right_constructive tail prior)

/-- Recover a constructive source witness from membership in a mapped list. -/
theorem mem_map_preimage_constructive {α β : Type} (f : α → β)
    {target : β} :
    ∀ {values : List α}, List.Mem target (values.map f) →
      ∃ source, List.Mem source values ∧ f source = target
  | _ :: _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, .tail _ prior =>
      let ⟨source, sourceMem, exactValue⟩ :=
        mem_map_preimage_constructive f prior
      ⟨source, .tail _ sourceMem, exactValue⟩

/-- Split membership in an append without propositional extensionality. -/
theorem mem_append_cases_constructive {α : Type} {value : α} :
    ∀ {left right : List α}, List.Mem value (left ++ right) →
      List.Mem value left ∨ List.Mem value right
  | [], _, prior => Or.inr prior
  | _ :: _, _, .head _ => Or.inl (.head _)
  | _ :: tail, _, .tail _ prior =>
      match mem_append_cases_constructive (left := tail) prior with
      | Or.inl inTail => Or.inl (.tail _ inTail)
      | Or.inr inRight => Or.inr inRight

/-- An injective map preserves duplicate-freeness constructively. -/
theorem nodup_map_constructive {α β : Type} (f : α → β)
    (injective : ∀ {left right : α}, f left = f right → left = right) :
    ∀ {values : List α}, values.Nodup → (values.map f).Nodup
  | [], .nil => .nil
  | _head :: _, .cons headFresh tailNodup =>
      .cons
        (fun _mapped mappedMem same =>
          let ⟨source, sourceMem, sourceExact⟩ :=
            mem_map_preimage_constructive f mappedMem
          headFresh source sourceMem
            (injective (Eq.trans same sourceExact.symm)))
        (nodup_map_constructive f injective tailNodup)

/-- Two duplicate-free and disjoint lists append without duplicates. -/
theorem nodup_append_constructive {α : Type} :
    ∀ {left right : List α},
      left.Nodup → right.Nodup →
      (∀ leftValue, List.Mem leftValue left →
        ∀ rightValue, List.Mem rightValue right →
          leftValue ≠ rightValue) →
      (left ++ right).Nodup
  | [], _, .nil, rightNodup, _ => rightNodup
  | head :: _tail, _right, .cons headFresh tailNodup, rightNodup, disjoint =>
      .cons
        (fun value valueMem same =>
          match mem_append_cases_constructive valueMem with
          | .inl inTail => headFresh value inTail same
          | .inr inRight =>
              disjoint head (.head _) value inRight same)
        (nodup_append_constructive tailNodup rightNodup
          (fun leftValue inTail rightValue inRight =>
            disjoint leftValue (.tail _ inTail) rightValue inRight))

/-- Every structural profile occurs in the recursively produced frontier. -/
theorem structuralFrontier_complete :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run)
      (profile : StructuralObligation roles),
      List.Mem profile (structuralFrontier roles)
  | _, _, _, _, _, .nil, profile => by
      change Unit at profile
      cases profile
      exact .head _
  | _, _, _, _, _, .step _ tail, profile => by
      change Bool × StructuralObligation tail at profile
      cases profile with
      | mk choice rest =>
          cases choice with
          | false =>
              exact mem_append_left_constructive _
                (mem_map_constructive (fun value => (false, value))
                  (structuralFrontier_complete tail rest))
          | true =>
              exact mem_append_right_constructive _
                (mem_map_constructive (fun value => (true, value))
                  (structuralFrontier_complete tail rest))

/-- The structural enumeration contains each left/right profile once. -/
theorem structuralFrontier_nodup :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (structuralFrontier roles).Nodup
  | _, _, _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, _, _, .step _ tail => by
      change
        ((structuralFrontier tail).map (fun value => (false, value)) ++
          (structuralFrontier tail).map (fun value => (true, value))).Nodup
      have tailNodup := structuralFrontier_nodup tail
      have leftNodup := nodup_map_constructive
        (fun value => (false, value))
        (fun same => congrArg Prod.snd same)
        tailNodup
      have rightNodup := nodup_map_constructive
        (fun value => (true, value))
        (fun same => congrArg Prod.snd same)
        tailNodup
      exact nodup_append_constructive leftNodup rightNodup
        (fun leftValue leftMem rightValue rightMem same => by
          let ⟨leftSource, _, leftExact⟩ :=
            mem_map_preimage_constructive
              (fun value => (false, value)) leftMem
          let ⟨rightSource, _, rightExact⟩ :=
            mem_map_preimage_constructive
              (fun value => (true, value)) rightMem
          have pairSame : (false, leftSource) = (true, rightSource) :=
            Eq.trans leftExact (Eq.trans same rightExact.symm)
          exact Bool.noConfusion (congrArg Prod.fst pairSame))

/-- The unique index of a retained singleton is its constructed index zero. -/
theorem retainedPosition_eq_executedPosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (position : Fin (executedSiblingReduction run).retained.length) :
    position = executedRetainedPosition run := by
  apply Fin.ext
  have widthOne : (executedSiblingReduction run).retained.length = 1 :=
    executedSiblingReduction_width run
  have positionBelowOne : position.val < 1 :=
    Eq.mp (congrArg (fun width => position.val < width) widthOne) position.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ positionBelowOne)

/-- Every operational profile occurs in the frontier built from retained positions. -/
theorem operationalFrontier_complete :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run)
      (profile : OperationalObligation roles),
      List.Mem profile (operationalFrontier roles)
  | _, _, _, _, _, .nil, profile => by
      change Unit at profile
      cases profile
      exact .head _
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile => by
      change Fin (executedSiblingReduction headRun).retained.length ×
        OperationalObligation tailRoles at profile
      cases profile with
      | mk position rest =>
          have positionExact := retainedPosition_eq_executedPosition headRun position
          cases positionExact
          exact mem_map_constructive
            (fun value => (executedRetainedPosition headRun, value))
            (operationalFrontier_complete tailRoles rest)

/-- The operational enumeration contains each retained-position profile once. -/
theorem operationalFrontier_nodup :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (operationalFrontier roles).Nodup
  | _, _, _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      nodup_map_constructive
        (fun value => (executedRetainedPosition headRun, value))
        (fun same => congrArg Prod.snd same)
        (operationalFrontier_nodup tailRoles)

/-- Accepted local payload selected by one structural left/right role. -/
def LocalAcceptedPayload {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) : Bool → Type
  | false =>
      { continuation : GeneratedStructuralBranchContinuation
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var false stage.discovery.fresh) //
        GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var false stage.discovery.fresh)
          continuation }
  | true =>
      { continuation : GeneratedStructuralBranchContinuation
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var true stage.discovery.fresh) //
        GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var true stage.discovery.fresh)
          continuation }

/-- Accepted payload carried by the sibling retained by the executed reduction. -/
def RetainedAcceptedPayload {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) : Type :=
  { continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh) //
    GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)
      continuation }

/--
Normalize either structural role by the transport of the executed reduction.
The left case consumes the discovered map and its separate preservation proof;
the already retained right case is unchanged.
-/
def normalizeLocalAcceptedPayload {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (choice : Bool) → LocalAcceptedPayload run choice →
      RetainedAcceptedPayload run
  | false, payload =>
      ⟨stage.discovery.relation.mapContinuation payload.1,
        executedSiblingReduction_preservesAccept run payload.1 payload.2⟩
  | true, payload => payload

@[simp] theorem normalizeLocalAcceptedPayload_left_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run false) :
    (normalizeLocalAcceptedPayload run false payload).1 =
      stage.discovery.relation.mapContinuation payload.1 :=
  rfl

@[simp] theorem normalizeLocalAcceptedPayload_right_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run true) :
    (normalizeLocalAcceptedPayload run true payload).1 = payload.1 :=
  rfl

/-- Every structural profile carries accepted local data at every opening. -/
def StructuralAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
    StructuralObligation roles → Type
  | _, _, _, _, _, .nil, _ => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile =>
      LocalAcceptedPayload headRun profile.1 ×
        StructuralAcceptedPayload tailRoles profile.2

/-- Accepted payloads after every structural role has been carried to the
actually retained position of its executed opening. -/
def OperationalAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      RetainedAcceptedPayload headRun ×
        OperationalAcceptedPayload tailRoles

/--
Normalize a complete structural payload profile through the executed transports
of the causally indexed history.
-/
def normalizeStructuralAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
    (profile : StructuralObligation roles) →
      StructuralAcceptedPayload roles profile →
        OperationalAcceptedPayload roles
  | _, _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile, payload =>
      ⟨normalizeLocalAcceptedPayload headRun profile.1 payload.1,
        normalizeStructuralAcceptedPayload tailRoles profile.2 payload.2⟩

/-- Positive accepted payload for every structural role profile. -/
def everyStructuralObligationHasAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
    (profile : StructuralObligation roles) →
      StructuralAcceptedPayload roles profile
  | _, _, _, _, _, .nil, profile => by
      change Unit
      exact ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ headStage headRun _ _ tailRoles, profile => by
      change Bool × StructuralObligation tailRoles at profile
      cases profile with
      | mk choice rest =>
          cases choice with
          | false =>
              exact ⟨⟨_, headStage.sourceAccepted⟩,
                everyStructuralObligationHasAcceptedPayload tailRoles rest⟩
          | true =>
              exact ⟨⟨_, headStage.outputAccepted⟩,
                everyStructuralObligationHasAcceptedPayload tailRoles rest⟩

/-- Width trace of one stage, computed from its actual three frontiers. -/
def executedStageWidthTrace {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : List Nat :=
  [
    [(constructStage (depth + 1)).operationalRoot].length,
    [
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh,
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh
    ].length,
    (executedSiblingReduction run).retained.length
  ]

/-- Full transient trace, recursively read from the executed role history. -/
def executedWidthTrace :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → List Nat
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      executedStageWidthTrace headRun ++ executedWidthTrace tailRoles

/-- A constructive pointwise upper bound on a width trace. -/
inductive WidthTraceAtMost (bound : Nat) : List Nat → Prop where
  | nil : WidthTraceAtMost bound []
  | cons {width tail} : width ≤ bound → WidthTraceAtMost bound tail →
      WidthTraceAtMost bound (width :: tail)

/-- The width trace is definitionally read from frontiers of sizes 1, 2, 1. -/
theorem executedStageWidthTrace_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStageWidthTrace run = [1, 2, 1] :=
  rfl

/-- Every transient width produced by the executed history is at most two. -/
theorem executedWidthTrace_le_two :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      WidthTraceAtMost 2 (executedWidthTrace roles)
  | _, _, _, _, _, .nil => .nil
  | depth, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles => by
      have oneLeTwo : 1 ≤ 2 := Nat.succ_le_succ (Nat.zero_le 1)
      change WidthTraceAtMost 2
        (1 :: 2 :: 1 :: executedWidthTrace tailRoles)
      exact .cons oneLeTwo
        (.cons (Nat.le_refl 2)
          (.cons oneLeTwo (executedWidthTrace_le_two tailRoles)))

/-- Every nonempty executed history actually reaches transient width two. -/
theorem executedWidthTrace_attains_two_of_step {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    {headRole : ThreadedConstitutiveRoleStage headRun}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun} :
    List.Mem 2 (executedWidthTrace
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :=
  .tail _ (.head _)

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalReductionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedOperationalReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStageCount_eq_historyCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.StructuralObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.PendingOperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRetainedPosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.length_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.zero_add_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.succ_add_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.length_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nat_add_congr
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth_eq_two_pow_stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingWidth_eq_structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingWidth_eq_two_pow_stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidth_eq_one
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_left_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_right_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_map_preimage_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_cases_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodup_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodup_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedPosition_eq_executedPosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.LocalAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.RetainedAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeLocalAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeLocalAcceptedPayload_left_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeLocalAcceptedPayload_right_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.StructuralAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeStructuralAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.everyStructuralObligationHasAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.WidthTraceAtMost
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageWidthTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidthTrace_le_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidthTrace_attains_two_of_step
/- AXIOM_AUDIT_END -/
