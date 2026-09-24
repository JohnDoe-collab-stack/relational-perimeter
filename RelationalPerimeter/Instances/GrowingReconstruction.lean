import RelationalPerimeter.Computation.ExecutedReconstruction
import RelationalPerimeter.Computation.OperationalReduction

/-!
# A growing executed reconstruction

At stage `n`, extraction produces `n + 1` pairwise distinct decoys followed by
one useful candidate.  The same executable recursion rejects every decoy and
then constructs the relation witness from the useful candidate.
-/

namespace RelationalPerimeter.Instances.GrowingReconstruction

open RelationalPerimeter.Computation

/-- Parent and two structurally opened alternatives. -/
inductive GrowingState where
  | parent
  | left
  | right
  deriving DecidableEq

/-- Parent continuations are exactly the sum of the two branch carriers. -/
abbrev growingSearchSystem : SearchSystem where
  State := GrowingState
  Continuation := fun state =>
    match state with
    | .parent => Nat ⊕ Nat
    | .left => Nat
    | .right => Nat
  Criterion := fun state continuation =>
    match state with
    | .parent =>
        match continuation with
        | .inl value => 0 < value
        | .inr value => 0 < value
    | .left => 0 < continuation
    | .right => 0 < continuation

/-- The structural opening is the identity on the parent sum carrier. -/
def growingOpening : ExactStructuralOpening
    growingSearchSystem .parent .left .right where
  split := fun continuation => continuation
  merge := fun branch => branch
  split_merge := fun _branch => rfl
  merge_split := fun _continuation => rfl

/-- Positivity is transported exactly through the structural opening. -/
theorem growingCriterionOpening :
    CriterionExactOpening growingSearchSystem growingOpening where
  split_preserves := by
    intro continuation accepted
    cases continuation with
    | inl value => exact accepted
    | inr value => exact accepted
  merge_preserves := by
    intro branch accepted
    cases branch with
    | inl value => exact accepted
    | inr value => exact accepted

/-- Relation reconstructed only from the left alternative to the right one. -/
inductive GrowingRelation : GrowingState → GrowingState → Type
  | absorb (stage : Nat) : GrowingRelation .left .right

/--
Every reconstructed relation acts on an arbitrary left continuation.  The
stage carried by the relation has a visible computational effect.
-/
def growingAction :
    RelationalContinuationAction growingSearchSystem GrowingRelation where
  act := by
    intro source target relation continuation
    cases relation with
    | absorb stage => exact continuation + stage + 1

/-- The action preserves the criterion independently of its definition. -/
theorem growingPreservingAction :
    CriterionPreservingAction
      growingSearchSystem GrowingRelation growingAction where
  preserves := by
    intro source target relation continuation accepted
    cases relation with
    | absorb stage =>
        exact Nat.zero_lt_succ (continuation + stage)

/-- A decoy carries its distinct numeric identity; `useful` is a separate tag. -/
inductive GrowingCandidate where
  | decoy (index : Nat)
  | useful
  deriving DecidableEq, Repr

/-- Descending indices `count - 1, ..., 0`, built by structural recursion. -/
def decoyIndices : Nat → List Nat
  | 0 => []
  | count + 1 => count :: decoyIndices count

/-- Every generated decoy index lies below the structural recursion bound. -/
theorem decoyIndices_member_lt
    {count index : Nat}
    (membership : index ∈ decoyIndices count) :
    index < count := by
  induction count with
  | zero =>
      cases membership
  | succ prior inductionHypothesis =>
      rw [decoyIndices] at membership
      cases membership with
      | head =>
          exact Nat.lt_add_one index
      | tail _ inTail =>
          exact Nat.lt_trans (inductionHypothesis inTail) (Nat.lt_add_one prior)

/-- The descending construction contains no repeated index. -/
theorem decoyIndices_nodup (count : Nat) :
    (decoyIndices count).Nodup := by
  induction count with
  | zero =>
      exact List.Pairwise.nil
  | succ prior inductionHypothesis =>
      apply List.Pairwise.cons
      · intro value membership
        exact Nat.ne_of_gt (decoyIndices_member_lt membership)
      · exact inductionHypothesis

/-- The `n + 1` distinct decoys preceding the useful candidate. -/
def decoys (stage : Nat) : List GrowingCandidate :=
  (decoyIndices (stage + 1)).map GrowingCandidate.decoy

private theorem decoyFreshAfterMap
    (head : Nat) :
    (indices : List Nat) →
    (∀ index, index ∈ indices → head ≠ index) →
    ∀ candidate,
      candidate ∈ indices.map GrowingCandidate.decoy →
      GrowingCandidate.decoy head ≠ candidate
  | [], _fresh, candidate, membership => by
      cases membership
  | index :: rest, fresh, candidate, membership => by
      intro equal
      cases membership with
      | head =>
          exact
            (fresh index (List.Mem.head rest))
              (GrowingCandidate.decoy.inj equal)
      | tail _ inTail =>
          exact
            decoyFreshAfterMap head rest
              (fun value valueMembership =>
                fresh value (List.Mem.tail index valueMembership))
              candidate inTail equal

private theorem mapDecoy_nodup
    (indices : List Nat)
    (distinct : indices.Nodup) :
    (indices.map GrowingCandidate.decoy).Nodup := by
  induction distinct with
  | nil =>
      exact List.Pairwise.nil
  | @cons head tail headFresh tailDistinct inductionHypothesis =>
      apply List.Pairwise.cons
      · exact decoyFreshAfterMap head tail headFresh
      · exact inductionHypothesis

/-- The decoys actually attempted at a stage are pairwise distinct. -/
theorem decoys_nodup (stage : Nat) :
    (decoys stage).Nodup :=
  mapDecoy_nodup
    (decoyIndices (stage + 1))
    (decoyIndices_nodup (stage + 1))

/-- Complete candidate list at one stage. -/
def candidates (stage : Nat) : List GrowingCandidate :=
  decoys stage ++ [.useful]

private theorem decoyFreshAfterMapAppendUseful
    (head : Nat) :
    (indices : List Nat) →
    (∀ index, index ∈ indices → head ≠ index) →
    ∀ candidate,
      candidate ∈
          indices.map GrowingCandidate.decoy ++ [.useful] →
      GrowingCandidate.decoy head ≠ candidate
  | [], _fresh, candidate, membership => by
      intro impossible
      cases membership with
      | head => cases impossible
      | tail _ membershipEmpty => cases membershipEmpty
  | index :: rest, fresh, candidate, membership => by
      intro equal
      cases membership with
      | head =>
          exact
            (fresh index (List.Mem.head rest))
              (GrowingCandidate.decoy.inj equal)
      | tail _ inTail =>
          exact
            decoyFreshAfterMapAppendUseful head rest
              (fun value valueMembership =>
                fresh value (List.Mem.tail index valueMembership))
              candidate inTail equal

private theorem mapDecoyAppendUseful_nodup
    (indices : List Nat)
    (distinct : indices.Nodup) :
    (indices.map GrowingCandidate.decoy ++
      [GrowingCandidate.useful]).Nodup := by
  induction distinct with
  | nil =>
      exact List.Pairwise.cons
        (by intro candidate membership; cases membership)
        List.Pairwise.nil
  | @cons head tail headFresh tailDistinct inductionHypothesis =>
      apply List.Pairwise.cons
      · exact decoyFreshAfterMapAppendUseful head tail headFresh
      · exact inductionHypothesis

/--
The complete extraction is pairwise distinct: the useful constructor cannot
coincide with any of the already distinct decoys.
-/
theorem candidates_nodup (stage : Nat) :
    (candidates stage).Nodup := by
  unfold candidates
  unfold decoys
  exact mapDecoyAppendUseful_nodup
    (decoyIndices (stage + 1))
    (decoyIndices_nodup (stage + 1))

/-- One operational decision reconstructed from a successful relation. -/
structure GrowingDecision where
  relationStage : Nat
  deriving DecidableEq, Repr

/-- The relation determines the decision transmitted to the next situation. -/
def GrowingRelation.toDecision :
    GrowingRelation .left .right → GrowingDecision
  | .absorb stage => ⟨stage⟩

/-- Remove the decoy named by one reconstructed relational decision. -/
def removeDecisionCandidate
    (decision : GrowingDecision) :
    List GrowingCandidate → List GrowingCandidate
  | [] => []
  | .useful :: remaining => .useful :: removeDecisionCandidate decision remaining
  | .decoy index :: remaining =>
      if index = decision.relationStage then remaining
      else .decoy index :: removeDecisionCandidate decision remaining

/--
Retained decisions filter the next extraction by their produced stage labels.
The decision contents, rather than only the number of decisions, are consumed.
-/
def filterCandidatesByDecisions :
    List GrowingDecision → List GrowingCandidate → List GrowingCandidate
  | [], available => available
  | decision :: remaining, available =>
      filterCandidatesByDecisions remaining
        (removeDecisionCandidate decision available)

/-- One stage-labelled decision removes exactly its matching next-stage decoy. -/
theorem singleDecision_filters_nextCandidates (stage : Nat) :
    filterCandidatesByDecisions [⟨stage⟩] (candidates (stage + 1)) =
      GrowingCandidate.decoy (stage + 1) ::
        ((decoyIndices stage).map GrowingCandidate.decoy ++ [.useful]) := by
  unfold filterCandidatesByDecisions candidates decoys
  change
    removeDecisionCandidate ⟨stage⟩
      (GrowingCandidate.decoy (stage + 1) ::
        GrowingCandidate.decoy stage ::
          ((decoyIndices stage).map GrowingCandidate.decoy ++ [.useful])) = _
  rw [removeDecisionCandidate, if_neg (Nat.ne_of_gt (Nat.lt_add_one stage))]
  rw [removeDecisionCandidate, if_pos rfl]

/-- Removing one decision preserves a decoy prefix followed by `useful`. -/
theorem removeDecisionCandidate_preserves_shape
    (decision : GrowingDecision)
    (indices : List Nat) :
    ∃ remaining : List Nat,
      removeDecisionCandidate decision
          (indices.map GrowingCandidate.decoy ++ [.useful]) =
        remaining.map GrowingCandidate.decoy ++ [.useful] := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index rest inductionHypothesis =>
      by_cases sameStage : index = decision.relationStage
      · refine ⟨rest, ?_⟩
        change
          (if index = decision.relationStage then
            rest.map GrowingCandidate.decoy ++ [.useful]
          else
            GrowingCandidate.decoy index ::
              removeDecisionCandidate decision
                (rest.map GrowingCandidate.decoy ++ [.useful])) =
            rest.map GrowingCandidate.decoy ++ [.useful]
        rw [if_pos sameStage]
      · obtain ⟨remaining, exactShape⟩ := inductionHypothesis
        refine ⟨index :: remaining, ?_⟩
        change
          (if index = decision.relationStage then
            rest.map GrowingCandidate.decoy ++ [.useful]
          else
            GrowingCandidate.decoy index ::
              removeDecisionCandidate decision
                (rest.map GrowingCandidate.decoy ++ [.useful])) =
            GrowingCandidate.decoy index ::
              (remaining.map GrowingCandidate.decoy ++ [.useful])
        rw [if_neg sameStage]
        exact congrArg (List.cons (GrowingCandidate.decoy index)) exactShape

/-- Any finite list of decisions preserves that executable candidate shape. -/
theorem filterCandidatesByDecisions_preserves_shape
    (decisions : List GrowingDecision)
    (indices : List Nat) :
    ∃ remaining : List Nat,
      filterCandidatesByDecisions decisions
          (indices.map GrowingCandidate.decoy ++ [.useful]) =
        remaining.map GrowingCandidate.decoy ++ [.useful] := by
  induction decisions generalizing indices with
  | nil => exact ⟨indices, rfl⟩
  | cons decision rest inductionHypothesis =>
      obtain ⟨afterDecision, firstShape⟩ :=
        removeDecisionCandidate_preserves_shape decision indices
      obtain ⟨remaining, finalShape⟩ :=
        inductionHypothesis afterDecision
      exact
        ⟨remaining, by
          unfold filterCandidatesByDecisions
          rw [firstShape]
          exact finalShape⟩

/--
The attempt computes failure for every decoy.  Only the useful tag constructs
the relation witness, and the witness records the stage of this run.
-/
def growingAttempt
    (stage : Nat) :
    GrowingCandidate → Option (GrowingRelation .left .right)
  | .useful => some (.absorb stage)
  | .decoy _index => none

/-- Executable reconstruction over one explicitly supplied extraction. -/
def growingReconstructionFrom
    (stage : Nat)
    (extracted : List GrowingCandidate) :
    ReconstructionSystem
      growingSearchSystem GrowingCandidate GrowingRelation .left .right where
  extract := extracted
  attempt := growingAttempt stage

/-- Executable reconstruction at stage `n`. -/
def growingReconstruction (stage : Nat) :=
  growingReconstructionFrom stage (candidates stage)

/-- Run the reconstruction over one explicitly supplied extraction. -/
def growingRunFrom (stage : Nat) (extracted : List GrowingCandidate) :=
  (growingReconstructionFrom stage extracted).run

/-- Executed left-to-right reconstruction at stage `n`. -/
def growingRun (stage : Nat) :=
  (growingReconstruction stage).run

/-- Every decoy is rejected by the actual attempt function. -/
theorem growingAttempt_decoy_none
    (stage index : Nat) :
    growingAttempt stage (.decoy index) = none :=
  rfl

/-- The useful candidate constructs the stage-indexed relation. -/
theorem growingAttempt_useful_some
    (stage : Nat) :
    growingAttempt stage .useful =
      some (.absorb stage) :=
  rfl

private theorem explore_decoys_tested
    (stage : Nat)
    (indices : List Nat) :
    (exploreCandidates
      (growingReconstruction stage)
      (indices.map GrowingCandidate.decoy ++ [.useful])).testedCandidates =
        indices.map GrowingCandidate.decoy ++ [.useful] := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      change
        (exploreCandidates
            (growingReconstruction stage)
            (GrowingCandidate.decoy index ::
              (rest.map GrowingCandidate.decoy ++ [.useful]))).result.testedCandidates =
          GrowingCandidate.decoy index ::
            (rest.map GrowingCandidate.decoy ++ [.useful])
      rw [exploreCandidates.eq_def]
      change
        (((exploreCandidates
            (growingReconstruction stage)
            (rest.map GrowingCandidate.decoy ++ [.useful])).result.prependFailure
              { candidate := GrowingCandidate.decoy index
                attempt_eq_none := rfl }).testedCandidates) =
          GrowingCandidate.decoy index ::
            (rest.map GrowingCandidate.decoy ++ [.useful])
      rw [ExecutedReconstruction.prependFailure_testedCandidates]
      exact
        congrArg (List.cons (GrowingCandidate.decoy index))
          inductionHypothesis

private theorem explore_decoys_tested_from
    (stage : Nat)
    (extracted : List GrowingCandidate)
    (indices : List Nat) :
    (exploreCandidates
      (growingReconstructionFrom stage extracted)
      (indices.map GrowingCandidate.decoy ++ [.useful])).testedCandidates =
        indices.map GrowingCandidate.decoy ++ [.useful] := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      rw [exploreCandidates.eq_def]
      change
        (((exploreCandidates
            (growingReconstructionFrom stage extracted)
            (rest.map GrowingCandidate.decoy ++ [.useful])).result.prependFailure
              { candidate := GrowingCandidate.decoy index
                attempt_eq_none := rfl }).testedCandidates) =
          GrowingCandidate.decoy index ::
            (rest.map GrowingCandidate.decoy ++ [.useful])
      rw [ExecutedReconstruction.prependFailure_testedCandidates]
      exact
        congrArg (List.cons (GrowingCandidate.decoy index))
          inductionHypothesis

private theorem explore_decoys_failed_exact
    (stage : Nat)
    (indices : List Nat) :
    (exploreCandidates
      (growingReconstruction stage)
      (indices.map GrowingCandidate.decoy ++ [.useful])).result.failedAttempts =
        indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      rw [exploreCandidates.eq_def]
      change
        (((exploreCandidates
            (growingReconstruction stage)
            (rest.map GrowingCandidate.decoy ++ [.useful])).result.prependFailure
              { candidate := GrowingCandidate.decoy index
                attempt_eq_none := rfl }).failedAttempts) =
          Nat.succ rest.length
      rw [ExecutedReconstruction.prependFailure_failedAttempts]
      rw [inductionHypothesis]

/-- Any explicit decoy prefix is executed completely before `useful`. -/
theorem growingRunFrom_decoys_tested_exact
    (stage : Nat)
    (indices : List Nat) :
    (growingRunFrom stage
      (indices.map GrowingCandidate.decoy ++ [.useful])).testedCandidates =
        indices.map GrowingCandidate.decoy ++ [.useful] := by
  change
    (exploreCandidates
      (growingReconstructionFrom stage
        (indices.map GrowingCandidate.decoy ++ [.useful]))
      (indices.map GrowingCandidate.decoy ++ [.useful])).result.testedCandidates =
        indices.map GrowingCandidate.decoy ++ [.useful]
  exact explore_decoys_tested_from stage
    (indices.map GrowingCandidate.decoy ++ [.useful]) indices

/-- The run tests every decoy and then the useful candidate, in that order. -/
theorem growingRun_tested_exact (stage : Nat) :
    (growingRun stage).testedCandidates = candidates stage := by
  exact explore_decoys_tested stage (decoyIndices (stage + 1))

/-- Structural length of the descending index list. -/
theorem decoyIndices_length (count : Nat) :
    (decoyIndices count).length = count := by
  induction count with
  | zero => rfl
  | succ prior inductionHypothesis =>
      change Nat.succ (decoyIndices prior).length = Nat.succ prior
      exact congrArg Nat.succ inductionHypothesis

/-- Mapping the decoy constructor preserves the structurally computed length. -/
theorem mappedDecoys_length (indices : List Nat) :
    (indices.map GrowingCandidate.decoy).length = indices.length := by
  induction indices with
  | nil => rfl
  | cons _index rest inductionHypothesis =>
      change
        Nat.succ (rest.map GrowingCandidate.decoy).length =
          Nat.succ rest.length
      exact congrArg Nat.succ inductionHypothesis

/-- The decoy prefix contains exactly `n + 1` candidates. -/
theorem decoys_length (stage : Nat) :
    (decoys stage).length = stage + 1 := by
  unfold decoys
  exact Eq.trans
    (mappedDecoys_length (decoyIndices (stage + 1)))
    (decoyIndices_length (stage + 1))

/-- Appending the useful candidate adds exactly one position. -/
theorem appendUseful_length (items : List GrowingCandidate) :
    (items ++ [GrowingCandidate.useful]).length = items.length + 1 := by
  induction items with
  | nil => rfl
  | cons _candidate rest inductionHypothesis =>
      change
        Nat.succ (rest ++ [GrowingCandidate.useful]).length =
          Nat.succ (rest.length + 1)
      exact congrArg Nat.succ inductionHypothesis

/-- The complete extracted list contains `n + 2` candidates. -/
theorem candidates_length (stage : Nat) :
    (candidates stage).length = stage + 2 := by
  unfold candidates
  exact Eq.trans
    (appendUseful_length (decoys stage))
    (congrArg (fun length => length + 1) (decoys_length stage))

/-- Exactly `n + 2` attempts are executed at stage `n`. -/
theorem growingRun_attempts_exact (stage : Nat) :
    (growingRun stage).attempts = stage + 2 := by
  change (growingRun stage).testedCandidates.length = stage + 2
  calc
    (growingRun stage).testedCandidates.length =
        (candidates stage).length :=
      congrArg List.length (growingRun_tested_exact stage)
    _ = stage + 2 := candidates_length stage

/-- Every attempt except the final successful one is a recorded failure. -/
theorem growingRun_failedAttempts_exact (stage : Nat) :
    (growingRun stage).failedAttempts = stage + 1 := by
  change
    (exploreCandidates
      (growingReconstruction stage)
      ((decoyIndices (stage + 1)).map GrowingCandidate.decoy ++
        [.useful])).result.failedAttempts = stage + 1
  rw [explore_decoys_failed_exact, decoyIndices_length]

/-- The complete executed trace is the failed prefix followed by one success. -/
theorem growingRun_failures_then_success (stage : Nat) :
    (growingRun stage).failedAttempts + 1 =
      (growingRun stage).attempts := by
  rw [growingRun_failedAttempts_exact, growingRun_attempts_exact]

/-- From stage one onward, failed attempts form a strict majority of the run. -/
theorem growingRun_failures_strictMajority (stage : Nat) :
    (growingRun (stage + 1)).failedAttempts + 1 =
        (growingRun (stage + 1)).attempts ∧
      1 < (growingRun (stage + 1)).failedAttempts := by
  constructor
  · exact growingRun_failures_then_success (stage + 1)
  · rw [growingRun_failedAttempts_exact]
    exact Nat.succ_lt_succ (Nat.zero_lt_succ stage)

private theorem explore_decoys_selected
    (stage : Nat)
    (indices : List Nat) :
    (exploreCandidates
      (growingReconstruction stage)
      (indices.map GrowingCandidate.decoy ++ [.useful])).selectedCandidate? =
        some .useful := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      change
        (exploreCandidates
            (growingReconstruction stage)
            (GrowingCandidate.decoy index ::
              (rest.map GrowingCandidate.decoy ++ [.useful]))).result.selectedCandidate? =
          some .useful
      rw [exploreCandidates.eq_def]
      change
        (((exploreCandidates
            (growingReconstruction stage)
            (rest.map GrowingCandidate.decoy ++ [.useful])).result.prependFailure
              { candidate := GrowingCandidate.decoy index
                attempt_eq_none := rfl }).selectedCandidate?) =
          some .useful
      rw [ExecutedReconstruction.prependFailure_selectedCandidate]
      exact inductionHypothesis

private theorem explore_decoys_relation
    (stage : Nat)
    (indices : List Nat) :
    (exploreCandidates
      (growingReconstruction stage)
      (indices.map GrowingCandidate.decoy ++ [.useful])).relation? =
        some (.absorb stage) := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      change
        (exploreCandidates
            (growingReconstruction stage)
            (GrowingCandidate.decoy index ::
              (rest.map GrowingCandidate.decoy ++ [.useful]))).result.relation? =
          some (.absorb stage)
      rw [exploreCandidates.eq_def]
      change
        (((exploreCandidates
            (growingReconstruction stage)
            (rest.map GrowingCandidate.decoy ++ [.useful])).result.prependFailure
              { candidate := GrowingCandidate.decoy index
                attempt_eq_none := rfl }).relation?) =
          some (.absorb stage)
      rw [ExecutedReconstruction.prependFailure_relation]
      exact inductionHypothesis

private theorem explore_decoys_relation_from
    (stage : Nat)
    (extracted : List GrowingCandidate)
    (indices : List Nat) :
    (exploreCandidates
      (growingReconstructionFrom stage extracted)
      (indices.map GrowingCandidate.decoy ++ [.useful])).relation? =
        some (.absorb stage) := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      rw [exploreCandidates.eq_def]
      change
        (((exploreCandidates
            (growingReconstructionFrom stage extracted)
            (rest.map GrowingCandidate.decoy ++ [.useful])).result.prependFailure
              { candidate := GrowingCandidate.decoy index
                attempt_eq_none := rfl }).relation?) =
          some (.absorb stage)
      rw [ExecutedReconstruction.prependFailure_relation]
      exact inductionHypothesis

/-- The selected candidate is the useful tag, after all decoys. -/
theorem growingRun_selected_exact (stage : Nat) :
    (growingRun stage).selectedCandidate? = some .useful := by
  exact explore_decoys_selected stage (decoyIndices (stage + 1))

/-- The relation in the output is constructed by the successful attempt. -/
theorem growingRun_relation_exact (stage : Nat) :
    (growingRun stage).relation? = some (.absorb stage) := by
  exact explore_decoys_relation stage (decoyIndices (stage + 1))

/-- Any supplied decoy prefix followed by `useful` reconstructs the relation. -/
theorem growingRunFrom_decoys_relation_exact
    (stage : Nat)
    (indices : List Nat) :
    (growingRunFrom stage
      (indices.map GrowingCandidate.decoy ++ [.useful])).relation? =
        some (.absorb stage) := by
  change
    (exploreCandidates
      (growingReconstructionFrom stage
        (indices.map GrowingCandidate.decoy ++ [.useful]))
      (indices.map GrowingCandidate.decoy ++ [.useful])).result.relation? =
        some (.absorb stage)
  exact explore_decoys_relation_from stage
    (indices.map GrowingCandidate.decoy ++ [.useful]) indices

/-- Successive stages execute strictly more candidate attempts. -/
theorem growingRun_attempts_strict (stage : Nat) :
    (growingRun stage).attempts < (growingRun (stage + 1)).attempts := by
  rw [growingRun_attempts_exact, growingRun_attempts_exact]
  exact Nat.lt_add_one (stage + 2)

/-- The two alternatives remain distinct states. -/
theorem left_ne_right : GrowingState.left ≠ GrowingState.right := by
  intro impossible
  cases impossible

/-- The absorbed left alternative still has a positive continuation. -/
def leftContinuation :
    growingSearchSystem.Continuation GrowingState.left :=
  by
    change Nat
    exact 1

/-- The concrete absorbed continuation satisfies the nontrivial criterion. -/
theorem leftContinuation_accepted :
    growingSearchSystem.Criterion GrowingState.left leftContinuation :=
  Nat.zero_lt_succ 0

/-- The concrete criterion is not vacuous: the zero continuation is rejected. -/
theorem zeroLeftContinuation_rejected :
    ¬ growingSearchSystem.Criterion GrowingState.left 0 :=
  Nat.not_lt_zero 0

/-- The reconstructed relation has an observable action on its source. -/
theorem growingAction_exact (stage continuation : Nat) :
    growingAction.act (.absorb stage) continuation =
      continuation + stage + 1 :=
  rfl

/-- The discovered relation reduces every parent continuation to the right. -/
def stageReduction (stage : Nat) :
    growingSearchSystem.Continuation GrowingState.parent →
      growingSearchSystem.Continuation GrowingState.right :=
  OperationalReduction.absorbLeft
    growingAction growingOpening (.absorb stage)

/-- Reduction preserves the criterion without identifying the alternatives. -/
theorem stageReduction_preserves
    (stage : Nat)
    (continuation : growingSearchSystem.Continuation GrowingState.parent)
    (accepted : growingSearchSystem.Criterion GrowingState.parent continuation) :
    growingSearchSystem.Criterion GrowingState.right
      (stageReduction stage continuation) :=
  OperationalReduction.absorbLeft_preserves
    growingPreservingAction growingCriterionOpening
    (.absorb stage) continuation accepted

end RelationalPerimeter.Instances.GrowingReconstruction

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingSearchSystem
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingOpening
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingCriterionOpening
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.GrowingRelation
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingAction
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingPreservingAction
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.GrowingCandidate
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoyIndices
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoyIndices_member_lt
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoyIndices_nodup
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoys
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoys_nodup
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.candidates
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.candidates_nodup
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.GrowingDecision
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.GrowingRelation.toDecision
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.removeDecisionCandidate
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.filterCandidatesByDecisions
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.singleDecision_filters_nextCandidates
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.removeDecisionCandidate_preserves_shape
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.filterCandidatesByDecisions_preserves_shape
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingAttempt
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingReconstructionFrom
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingReconstruction
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRunFrom
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingAttempt_decoy_none
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingAttempt_useful_some
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_tested_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRunFrom_decoys_tested_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoyIndices_length
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.mappedDecoys_length
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.appendUseful_length
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.decoys_length
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.candidates_length
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_attempts_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_failedAttempts_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_failures_then_success
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_failures_strictMajority
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_selected_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_relation_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRunFrom_decoys_relation_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingRun_attempts_strict
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.left_ne_right
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.leftContinuation
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.leftContinuation_accepted
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.zeroLeftContinuation_rejected
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.growingAction_exact
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.stageReduction
#print axioms RelationalPerimeter.Instances.GrowingReconstruction.stageReduction_preserves
/- AXIOM_AUDIT_END -/
