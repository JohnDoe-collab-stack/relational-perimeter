import RelationalPerimeter.Computation.ConstitutiveSearch.FiniteExtensiveAddressing

/-!
# General extensive families constituted by dependent relational roles

This module defines the general class used by the complexity theorem.  A stage
is indexed by the state it receives and the state it produces.  Its role and
occurrences are connected by primitive source, formation, target, and
provenance relations with positive witnesses.  The global extensive carrier is
then derived from a dependent history of such stages; no global frontier,
arity list, or width formula is supplied by the family.
-/

namespace ConstitutiveSearch
namespace RelationalExtensive

open Extensive

/--
One relational opening.  Formation and provenance are proof-relevant data;
the finite frontier enumerates the occurrences already constituted by them.
-/
structure RelationalOpeningStage
    (State : Type) (source next : State) where
  Role : Type
  Occurrence : Type
  Provenance : Type
  SourceRelation : State → Role → Type
  FormationRelation : Role → Occurrence → Type
  TargetRelation : Role → State → Type
  ProvenanceRelation : Provenance → Role → Occurrence → Type
  role : Role
  provenance : Provenance
  sourceWitness : SourceRelation source role
  targetWitness : TargetRelation role next
  occurrenceDecEq : DecidableEq Occurrence
  occurrenceFrontier : List Occurrence
  occurrenceComplete :
    (occurrence : Occurrence) → occurrence ∈ occurrenceFrontier
  occurrenceNodup : occurrenceFrontier.Nodup
  formationWitness :
    (occurrence : Occurrence) → FormationRelation role occurrence
  provenanceWitness :
    (occurrence : Occurrence) →
      ProvenanceRelation provenance role occurrence

/-- Dependent history: the tail starts at the exact state produced by its head. -/
inductive DependentRelationalRoleHistory
    (State : Type) : State → Nat → Type 1 where
  | nil (state : State) : DependentRelationalRoleHistory State state 0
  | step {source next : State} {count : Nat}
      (head : RelationalOpeningStage State source next)
      (tail : DependentRelationalRoleHistory State next count) :
      DependentRelationalRoleHistory State source (count + 1)

/--
One occurrence indexed by the relational stage that constitutes it.  The
stage retains the proof-relevant formation and provenance witnesses in
`Type`; they are recovered constructively below.  They are not hidden behind
a propositional truncation and do not create additional extensive identities.
-/
structure RelationallyConstitutedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) where
  private mk ::
  occurrence : stage.Occurrence

/-- The canonical constituted occurrence supplied by a relational stage. -/
def relationallyConstitutedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) :
    RelationallyConstitutedOccurrence stage :=
  .mk occurrence

/-- Recover the positive formation witness from the constituting stage. -/
def RelationallyConstitutedOccurrence.formationWitness
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) :
    stage.FormationRelation stage.role identity.occurrence :=
  stage.formationWitness identity.occurrence

/-- Recover the positive provenance witness from the constituting stage. -/
def RelationallyConstitutedOccurrence.provenanceWitness
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) :
    stage.ProvenanceRelation stage.provenance stage.role identity.occurrence :=
  stage.provenanceWitness identity.occurrence

/-- Constituted occurrences are equal exactly through their occurrence field. -/
theorem RelationallyConstitutedOccurrence.ext
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    {left right : RelationallyConstitutedOccurrence stage}
    (sameOccurrence : left.occurrence = right.occurrence) :
    left = right := by
  cases left
  cases right
  cases sameOccurrence
  rfl

/-- Decidable equality inherited from the stage occurrence carrier. -/
def relationallyConstitutedOccurrenceDecEq
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    DecidableEq (RelationallyConstitutedOccurrence stage) :=
  fun left right =>
    match stage.occurrenceDecEq left.occurrence right.occurrence with
    | isTrue same => isTrue (RelationallyConstitutedOccurrence.ext same)
    | isFalse different =>
        isFalse (fun same => different (congrArg
          RelationallyConstitutedOccurrence.occurrence same))

/-- A profile of identities constituted at every relational role. -/
def RelationalOccurrenceProfile :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Type
  | _, _, _, .nil _ => Unit
  | _, _, _, .step head tail =>
      RelationallyConstitutedOccurrence head ×
        RelationalOccurrenceProfile tail

/-- Cartesian frontier, defined without replacing occurrences by indices. -/
def productFrontier {Head Tail : Type} :
    List Head → List Tail → List (Head × Tail)
  | [], _ => []
  | head :: rest, tail =>
      tail.map (fun suffix => (head, suffix)) ++ productFrontier rest tail

theorem relational_mem_append_cases {α : Type} {value : α} :
    ∀ {left right : List α}, value ∈ left ++ right →
      value ∈ left ∨ value ∈ right
  | [], _, prior => Or.inr prior
  | _ :: _, _, .head _ => Or.inl (.head _)
  | _ :: tail, _, .tail _ prior =>
      match relational_mem_append_cases (left := tail) prior with
      | .inl inTail => .inl (.tail _ inTail)
      | .inr inRight => .inr inRight

theorem relational_nodup_append {α : Type} :
    ∀ {left right : List α},
      left.Nodup → right.Nodup →
      (∀ leftValue, leftValue ∈ left →
        ∀ rightValue, rightValue ∈ right → leftValue ≠ rightValue) →
      (left ++ right).Nodup
  | [], _, .nil, rightNodup, _ => rightNodup
  | head :: _, _, .cons headFresh tailNodup, rightNodup, disjoint =>
      .cons
        (fun value valueMember same =>
          match relational_mem_append_cases valueMember with
          | .inl inTail => headFresh value inTail same
          | .inr inRight => disjoint head (.head _) value inRight same)
        (relational_nodup_append tailNodup rightNodup
          (fun leftValue inTail rightValue inRight =>
            disjoint leftValue (.tail _ inTail) rightValue inRight))

theorem relational_length_map {α β : Type} (map : α → β) :
    ∀ values : List α, (values.map map).length = values.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (relational_length_map map tail)

theorem relational_zero_add : ∀ value : Nat, 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (relational_zero_add value)

theorem relational_succ_add (left : Nat) :
    ∀ right : Nat, Nat.succ left + right = Nat.succ (left + right)
  | 0 => rfl
  | right + 1 => congrArg Nat.succ (relational_succ_add left right)

theorem relational_length_append {α : Type} :
    ∀ left right : List α,
      (left ++ right).length = left.length + right.length
  | [], right => (relational_zero_add right.length).symm
  | _ :: tail, right => Eq.trans
      (congrArg Nat.succ (relational_length_append tail right))
      (relational_succ_add tail.length right.length).symm

theorem productFrontier_complete
    {Head Tail : Type} {head : Head} {tail : Tail} :
    ∀ {heads : List Head} {tails : List Tail},
      head ∈ heads → tail ∈ tails →
      (head, tail) ∈ productFrontier heads tails
  | _ :: _, _, .head _, tailMember => by
      apply List.mem_append_left
      exact Extensive.mem_map (fun suffix => (head, suffix)) tailMember
  | _ :: rest, tails, .tail _ prior, tailMember => by
      apply List.mem_append_right
      exact productFrontier_complete prior tailMember

theorem productFrontier_length {Head Tail : Type} :
    ∀ (heads : List Head) (tails : List Tail),
      (productFrontier heads tails).length = heads.length * tails.length
  | [], tails => (Nat.zero_mul tails.length).symm
  | _ :: rest, tails => by
      rw [productFrontier, relational_length_append, relational_length_map,
        productFrontier_length rest tails, List.length_cons, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem fst_mem_of_mem_productFrontier
    {Head Tail : Type} {value : Head × Tail} :
    ∀ {heads : List Head} {tails : List Tail},
      value ∈ productFrontier heads tails → value.1 ∈ heads
  | [], _, member => by cases member
  | head :: rest, tails, member => by
      rcases relational_mem_append_cases member with inFirst | inLater
      · rcases Extensive.mem_map_preimage
            (fun suffix => (head, suffix)) inFirst with
          ⟨_, _, exactPair⟩
        exact exactPair ▸ .head _
      · exact .tail _ (fst_mem_of_mem_productFrontier inLater)

theorem productFrontier_nodup
    {Head Tail : Type}
    [DecidableEq Head] [DecidableEq Tail] :
    ∀ {heads : List Head} {tails : List Tail},
      heads.Nodup → tails.Nodup →
      (productFrontier heads tails).Nodup
  | [], _, .nil, tailNodup => by
      exact .nil
  | head :: rest, tails, .cons headFresh restNodup, tailNodup => by
      have mappedNodup :
          (tails.map (fun suffix => (head, suffix))).Nodup :=
        Extensive.nodup_map
          (fun suffix => (head, suffix))
          (fun {_left _right} same => congrArg Prod.snd same)
          tailNodup
      have restProductNodup : (productFrontier rest tails).Nodup :=
        productFrontier_nodup restNodup tailNodup
      exact relational_nodup_append mappedNodup restProductNodup
        (fun leftValue inMapped rightValue inRest same => by
          rcases Extensive.mem_map_preimage
              (fun suffix => (head, suffix)) inMapped with
            ⟨leftTail, _leftMember, leftExact⟩
          have restHeadMember : rightValue.1 ∈ rest :=
            fst_mem_of_mem_productFrontier inRest
          have headSame : head = rightValue.1 := by
            exact congrArg Prod.fst (Eq.trans leftExact same)
          exact headFresh rightValue.1 restHeadMember headSame)

/-- The local frontier after formation and provenance have constituted it. -/
def relationallyConstitutedOccurrenceFrontier
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    List (RelationallyConstitutedOccurrence stage) :=
  stage.occurrenceFrontier.map (relationallyConstitutedOccurrence stage)

theorem relationallyConstitutedOccurrenceFrontier_complete
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    identity ∈ relationallyConstitutedOccurrenceFrontier stage := by
  have canonicalMember := Extensive.mem_map
    (relationallyConstitutedOccurrence stage)
    (stage.occurrenceComplete identity.occurrence)
  have canonicalExact :
      relationallyConstitutedOccurrence stage identity.occurrence = identity :=
    RelationallyConstitutedOccurrence.ext rfl
  exact canonicalExact ▸ canonicalMember

theorem relationallyConstitutedOccurrenceFrontier_nodup
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    (relationallyConstitutedOccurrenceFrontier stage).Nodup :=
  Extensive.nodup_map
    (relationallyConstitutedOccurrence stage)
    (fun {_left _right} same => congrArg
      RelationallyConstitutedOccurrence.occurrence same)
    stage.occurrenceNodup

/-- The unique global frontier of relationally constituted identities. -/
def relationalProfileFrontier :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      List (RelationalOccurrenceProfile history)
  | _, _, _, .nil _ => [()]
  | _, _, _, .step head tail =>
      productFrontier (relationallyConstitutedOccurrenceFrontier head)
        (relationalProfileFrontier tail)

theorem relationalProfileFrontier_complete :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (profile : RelationalOccurrenceProfile history) →
      profile ∈ relationalProfileFrontier history
  | _, _, _, .nil _, profile => by cases profile; exact .head _
  | _, _, _, .step head tail, profile =>
      productFrontier_complete
        (relationallyConstitutedOccurrenceFrontier_complete head profile.1)
        (relationalProfileFrontier_complete tail profile.2)

/-- Constructive equality decision on constituted relational profiles. -/
def relationalOccurrenceProfileDecEq :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      DecidableEq (RelationalOccurrenceProfile history)
  | _, _, _, .nil _ => fun left right =>
      match left, right with
      | (), () => isTrue rfl
  | _, _, _, .step head tail => fun left right =>
      match relationallyConstitutedOccurrenceDecEq head left.1 right.1 with
      | isFalse headDifferent =>
          isFalse (fun same => headDifferent (congrArg Prod.fst same))
      | isTrue headSame =>
          match relationalOccurrenceProfileDecEq tail left.2 right.2 with
          | isFalse tailDifferent =>
              isFalse (fun same => tailDifferent (congrArg Prod.snd same))
          | isTrue tailSame => isTrue (Prod.ext headSame tailSame)

theorem relationalProfileFrontier_nodup :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (relationalProfileFrontier history).Nodup
  | _, _, _, .nil _ =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, .step head tail => by
      letI : DecidableEq (RelationallyConstitutedOccurrence head) :=
        relationallyConstitutedOccurrenceDecEq head
      letI : DecidableEq (RelationalOccurrenceProfile tail) :=
        relationalOccurrenceProfileDecEq tail
      exact productFrontier_nodup
        (relationallyConstitutedOccurrenceFrontier_nodup head)
        (relationalProfileFrontier_nodup tail)

/-- Arity list read from the already realized local occurrence frontiers. -/
def relationalHistoryArities :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → List Nat
  | _, _, _, .nil _ => []
  | _, _, _, .step head tail =>
      head.occurrenceFrontier.length :: relationalHistoryArities tail

/-- Width is a readout of the derived global profile frontier. -/
def relationalProfileWidth
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) : Nat :=
  (relationalProfileFrontier history).length

theorem relationalProfileWidth_eq_arityProduct :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      relationalProfileWidth history = (relationalHistoryArities history).prod
  | _, _, _, .nil _ => rfl
  | _, _, _, .step head tail => by
      change
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
          (relationalProfileFrontier tail)).length =
        head.occurrenceFrontier.length *
          (relationalHistoryArities tail).prod
      calc
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
            (relationalProfileFrontier tail)).length =
            (relationallyConstitutedOccurrenceFrontier head).length *
              (relationalProfileFrontier tail).length :=
          productFrontier_length _ _
        _ = head.occurrenceFrontier.length *
              (relationalProfileFrontier tail).length := by
          rw [relationallyConstitutedOccurrenceFrontier,
            relational_length_map]
        _ = head.occurrenceFrontier.length *
              (relationalHistoryArities tail).prod :=
          congrArg (fun width => head.occurrenceFrontier.length * width)
            (relationalProfileWidth_eq_arityProduct tail)

/-- The finite extensive carrier derived from one relational history. -/
def relationalProfileFiniteCarrier
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) :
    FiniteCarrier :=
  { Identity := RelationalOccurrenceProfile history
    decEq := relationalOccurrenceProfileDecEq history
    frontier := relationalProfileFrontier history
    complete := relationalProfileFrontier_complete history
    nodup := relationalProfileFrontier_nodup history }

/-- The finite carrier and its numerical readout share the same frontier. -/
theorem relationalProfileFiniteCarrier_width
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) :
    (relationalProfileFiniteCarrier history).frontier.length =
      relationalProfileWidth history :=
  rfl

/-- Every realized local opening has one fixed arity. -/
def UniformLocalArity :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Nat → Prop
  | _, _, _, .nil _, _ => True
  | _, _, _, .step head tail, arity =>
      head.occurrenceFrontier.length = arity ∧ UniformLocalArity tail arity

/-- Every realized local opening has at least two occurrences. -/
def AtLeastBinaryLocalArity :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .step head tail =>
      2 ≤ head.occurrenceFrontier.length ∧ AtLeastBinaryLocalArity tail

theorem uniformLocalArity_width :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (arity : Nat) → UniformLocalArity history arity →
      relationalProfileWidth history = arity ^ count
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .step head tail, arity, uniform => by
      change
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
          (relationalProfileFrontier tail)).length = arity ^ (_ + 1)
      calc
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
            (relationalProfileFrontier tail)).length =
            (relationallyConstitutedOccurrenceFrontier head).length *
              relationalProfileWidth tail := productFrontier_length _ _
        _ = head.occurrenceFrontier.length *
              relationalProfileWidth tail := by
          rw [relationallyConstitutedOccurrenceFrontier,
            relational_length_map]
        _ = arity * (arity ^ _) := by
          rw [uniform.1, uniformLocalArity_width tail arity uniform.2]
        _ = arity ^ (_ + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]

theorem atLeastBinaryLocalArity_width_lowerBound :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      AtLeastBinaryLocalArity history →
      2 ^ count ≤ relationalProfileWidth history
  | _, _, _, .nil _, _ => Nat.le_refl 1
  | _, _, _, .step head tail, binary => by
      have tailBound := atLeastBinaryLocalArity_width_lowerBound tail binary.2
      change
        2 ^ (_ + 1) ≤
          (productFrontier (relationallyConstitutedOccurrenceFrontier head)
            (relationalProfileFrontier tail)).length
      rw [productFrontier_length, Nat.pow_succ]
      calc
        2 ^ _ * 2 = 2 * 2 ^ _ := Nat.mul_comm _ _
        _ ≤ (relationallyConstitutedOccurrenceFrontier head).length *
              relationalProfileWidth tail := by
          rw [relationallyConstitutedOccurrenceFrontier,
            relational_length_map]
          exact Nat.mul_le_mul binary.1 tailBound

/--
A nontrivial general class.  Problems produce dependent relational histories;
local nontriviality and unbounded stage counts are properties of those
histories.  No global carrier or cardinality formula is a field.
-/
structure RelationalRoleExtensiveFamily where
  State : Type
  Problem : Nat → Type
  initialState : {index : Nat} → Problem index → State
  stageCount : {index : Nat} → Problem index → Nat
  producedHistory : {index : Nat} → (problem : Problem index) →
    DependentRelationalRoleHistory State
      (initialState problem) (stageCount problem)
  nontrivialOpenings : {index : Nat} → (problem : Problem index) →
    AtLeastBinaryLocalArity (producedHistory problem)
  unboundedIndex : Nat → Nat
  unboundedProblem : (bound : Nat) → Problem (unboundedIndex bound)
  unboundedStages : (bound : Nat) →
    bound ≤ stageCount (unboundedProblem bound)

/--
The general binary subclass. Binary width is not stored in this structure:
it is proved from the already produced relational history of every problem.
-/
structure BinaryRelationalRoleExtensiveFamily extends
    RelationalRoleExtensiveFamily where
  binaryOpenings : {index : Nat} → (problem : Problem index) →
    UniformLocalArity (producedHistory problem) 2

namespace RelationalRoleExtensiveFamily

def sourceCarrier
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) : FiniteCarrier :=
  relationalProfileFiniteCarrier (family.producedHistory problem)

theorem sourceWidth_atLeast_exponential
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) :
    2 ^ family.stageCount problem ≤
      (family.sourceCarrier problem).frontier.length := by
  unfold sourceCarrier
  rw [relationalProfileFiniteCarrier_width]
  exact atLeastBinaryLocalArity_width_lowerBound
    (family.producedHistory problem) (family.nontrivialOpenings problem)

/--
General target theorem: on every problem in every relational extensive family,
full operational width is equivalent to preserving the constituted profile
identities separately.
-/
theorem fullWidth_iff_preservesConstitutedIdentities
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.HasFullExtensiveWidth ↔ PreservesIdentitiesSeparately regime :=
  (preservesIdentitiesSeparately_iff_fullWidth regime).symm

/-- Exact factorized capacity form of the general target theorem. -/
theorem fullWidth_iff_exactRegimeCapacity
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.HasFullExtensiveWidth ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  Iff.trans
    (fullWidth_iff_preservesConstitutedIdentities family problem regime)
    (preservesIdentitiesSeparately_iff_exactRegimeCapacity regime)

end RelationalRoleExtensiveFamily

namespace BinaryRelationalRoleExtensiveFamily

/-- Source carrier inherited from the underlying relational family. -/
def sourceCarrier
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) : FiniteCarrier :=
  family.toRelationalRoleExtensiveFamily.sourceCarrier problem

/-- Every problem in a binary relational family has exact exponential width. -/
theorem sourceWidth_eq_twoPow
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) :
    (family.sourceCarrier problem).frontier.length =
      2 ^ family.stageCount problem := by
  unfold sourceCarrier RelationalRoleExtensiveFamily.sourceCarrier
  rw [relationalProfileFiniteCarrier_width]
  exact uniformLocalArity_width
    (family.producedHistory problem) 2 (family.binaryOpenings problem)

/--
Class-level target theorem. For every problem in every binary relational
extensive family, exact exponential obligation width appears if and only if
the downstream regime preserves the constituted identities separately.
-/
theorem exponentialWidth_iff_preservesConstitutedIdentities
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      PreservesIdentitiesSeparately regime := by
  have sourceWidth := family.sourceWidth_eq_twoPow problem
  constructor
  · intro exponentialWidth
    apply preserves_of_full_width regime
    unfold ObligationRegime.HasFullExtensiveWidth
    exact Eq.trans exponentialWidth sourceWidth.symm
  · intro preserves
    have fullWidth := full_width_of_preserves regime preserves
    unfold ObligationRegime.HasFullExtensiveWidth at fullWidth
    exact Eq.trans fullWidth sourceWidth

/--
The class-level target with the full qualitative wording represented in the
type: identities remain distinct and separately addressable through the
regime itself.
-/
theorem exponentialWidth_iff_distinctSeparateConservation
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        regime :=
  Iff.trans
    (family.exponentialWidth_iff_preservesConstitutedIdentities problem regime)
    (preservesIdentitiesSeparately_iff_distinctSeparateConservation regime)

/-- Exact factorized-capacity form of the class-level exponential `iff`. -/
theorem exponentialWidth_iff_exactRegimeCapacity
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  Iff.trans
    (family.exponentialWidth_iff_preservesConstitutedIdentities problem regime)
    (preservesIdentitiesSeparately_iff_exactRegimeCapacity regime)

end BinaryRelationalRoleExtensiveFamily

/- A concrete variable-arity member proves that the class is not merely the
public binary instance. -/

/-- Constructive finite enumeration avoiding theorem dependencies on quotients. -/
def constructiveFinRange : (size : Nat) → List (Fin size)
  | 0 => []
  | size + 1 =>
      ⟨0, Nat.zero_lt_succ size⟩ ::
        (constructiveFinRange size).map Fin.succ

theorem constructiveFinRange_complete :
    {_size : Nat} → (index : Fin _size) →
      index ∈ constructiveFinRange _size
  | 0, index => Fin.elim0 index
  | _size + 1, ⟨0, _before⟩ => .head _
  | _size + 1, ⟨value + 1, before⟩ =>
      .tail _
        (Extensive.mem_map Fin.succ
          (constructiveFinRange_complete
            ⟨value, Nat.lt_of_succ_lt_succ before⟩))

theorem constructiveFinRange_nodup :
  ∀ size : Nat, (constructiveFinRange size).Nodup
  | 0 => .nil
  | size + 1 => by
      refine .cons ?_ ?_
      · intro value member same
        rcases Extensive.mem_map_preimage Fin.succ member with
          ⟨prior, _priorMember, priorExact⟩
        have impossible : (0 : Nat) = prior.val + 1 :=
          congrArg Fin.val (Eq.trans same priorExact.symm)
        exact Nat.noConfusion impossible
      · exact Extensive.nodup_map Fin.succ
          (fun {_left _right} same => Fin.succ_inj.mp same)
          (constructiveFinRange_nodup size)

theorem constructiveFinRange_length :
    ∀ size : Nat, (constructiveFinRange size).length = size
  | 0 => rfl
  | size + 1 => by
      exact congrArg Nat.succ
        (Eq.trans
          (Extensive.length_map Fin.succ (constructiveFinRange size))
          (constructiveFinRange_length size))

def increasingArityStage (source : Nat) :
    RelationalOpeningStage Nat source (source + 1) :=
  { Role := Unit
    Occurrence := Fin (source + 2)
    Provenance := Nat
    SourceRelation := fun observed _ => PLift (observed = source)
    FormationRelation := fun _ occurrence => PLift (occurrence.val < source + 2)
    TargetRelation := fun _ observed => PLift (observed = source + 1)
    ProvenanceRelation := fun provenance _ occurrence =>
      PLift (provenance = source ∧ occurrence.val < source + 2)
    role := ()
    provenance := source
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨rfl⟩
    occurrenceDecEq := inferInstance
    occurrenceFrontier := constructiveFinRange (source + 2)
    occurrenceComplete := constructiveFinRange_complete
    occurrenceNodup := constructiveFinRange_nodup _
    formationWitness := fun occurrence => ⟨occurrence.isLt⟩
    provenanceWitness := fun occurrence => ⟨⟨rfl, occurrence.isLt⟩⟩ }

def increasingArityHistory :
    (count source : Nat) →
      DependentRelationalRoleHistory Nat source count
  | 0, source => .nil source
  | count + 1, source =>
      .step (increasingArityStage source)
        (increasingArityHistory count (source + 1))

theorem increasingArityHistory_nontrivial :
    (count source : Nat) →
      AtLeastBinaryLocalArity (increasingArityHistory count source)
  | 0, _ => True.intro
  | count + 1, source => by
      constructor
      · change 2 ≤ (constructiveFinRange (source + 2)).length
        rw [constructiveFinRange_length]
        exact Nat.le_add_left 2 source
      · exact increasingArityHistory_nontrivial count (source + 1)

/-- Variable local arities and unbounded histories form a concrete member. -/
def increasingArityRelationalFamily : RelationalRoleExtensiveFamily :=
  { State := Nat
    Problem := fun _ => Unit
    initialState := fun _ => 0
    stageCount := fun {index} _ => index + 1
    producedHistory := fun {index} _ => increasingArityHistory (index + 1) 0
    nontrivialOpenings := fun {index} _ =>
      increasingArityHistory_nontrivial (index + 1) 0
    unboundedIndex := id
    unboundedProblem := fun _ => ()
    unboundedStages := fun bound => Nat.le_succ bound }

theorem increasingArityRelationalFamily_unbounded (bound : Nat) :
    bound ≤ increasingArityRelationalFamily.stageCount
      (increasingArityRelationalFamily.unboundedProblem bound) :=
  increasingArityRelationalFamily.unboundedStages bound

theorem increasingArityRelationalFamily_variable
    (source : Nat) :
    (increasingArityStage source).occurrenceFrontier.length = source + 2 :=
  constructiveFinRange_length _

/-- A binary relational opening independent of the public SAT construction. -/
def abstractBinaryStage (source : Nat) :
    RelationalOpeningStage Nat source (source + 1) :=
  { Role := Nat
    Occurrence := Fin 2
    Provenance := Nat
    SourceRelation := fun observed role => PLift (observed = role)
    FormationRelation := fun role occurrence =>
      PLift (role = source ∧ occurrence.val < 2)
    TargetRelation := fun role observed =>
      PLift (role = source ∧ observed = source + 1)
    ProvenanceRelation := fun provenance role occurrence =>
      PLift (provenance = source ∧ role = source ∧ occurrence.val < 2)
    role := source
    provenance := source
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨rfl, rfl⟩
    occurrenceDecEq := inferInstance
    occurrenceFrontier := constructiveFinRange 2
    occurrenceComplete := constructiveFinRange_complete
    occurrenceNodup := constructiveFinRange_nodup 2
    formationWitness := fun occurrence => ⟨rfl, occurrence.isLt⟩
    provenanceWitness := fun occurrence =>
      ⟨rfl, rfl, occurrence.isLt⟩ }

def abstractBinaryHistory :
    (count source : Nat) →
      DependentRelationalRoleHistory Nat source count
  | 0, source => .nil source
  | count + 1, source =>
      .step (abstractBinaryStage source)
        (abstractBinaryHistory count (source + 1))

theorem abstractBinaryHistory_uniform :
    (count source : Nat) →
      UniformLocalArity (abstractBinaryHistory count source) 2
  | 0, _ => True.intro
  | count + 1, source => by
      constructor
      · exact constructiveFinRange_length 2
      · exact abstractBinaryHistory_uniform count (source + 1)

theorem abstractBinaryHistory_nontrivial :
    (count source : Nat) →
      AtLeastBinaryLocalArity (abstractBinaryHistory count source)
  | 0, _ => True.intro
  | count + 1, source => by
      constructor
      · change 2 ≤ (constructiveFinRange 2).length
        rw [constructiveFinRange_length]
        exact Nat.le_refl 2
      · exact abstractBinaryHistory_nontrivial count (source + 1)

/--
An unbounded binary family distinct from the public SAT family. Its role,
formation, target, and provenance relations are all explicit positive data.
-/
def abstractBinaryRelationalFamily : BinaryRelationalRoleExtensiveFamily :=
  { State := Nat
    Problem := fun _ => Unit
    initialState := fun _ => 0
    stageCount := fun {index} _ => index + 1
    producedHistory := fun {index} _ => abstractBinaryHistory (index + 1) 0
    nontrivialOpenings := fun {index} _ =>
      abstractBinaryHistory_nontrivial (index + 1) 0
    unboundedIndex := id
    unboundedProblem := fun _ => ()
    unboundedStages := fun bound => Nat.le_succ bound
    binaryOpenings := fun {index} _ =>
      abstractBinaryHistory_uniform (index + 1) 0 }

theorem abstractBinaryRelationalFamily_unbounded (bound : Nat) :
    bound ≤ abstractBinaryRelationalFamily.stageCount
      (abstractBinaryRelationalFamily.unboundedProblem bound) :=
  abstractBinaryRelationalFamily.unboundedStages bound

end RelationalExtensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage
#print axioms ConstitutiveSearch.RelationalExtensive.DependentRelationalRoleHistory
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOccurrenceProfile
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrence
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence.formationWitness
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence.provenanceWitness
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrenceFrontier
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFrontier
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFrontier_complete
#print axioms ConstitutiveSearch.RelationalExtensive.relationalOccurrenceProfileDecEq
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFrontier_nodup
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFiniteCarrier
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFiniteCarrier_width
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileWidth_eq_arityProduct
#print axioms ConstitutiveSearch.RelationalExtensive.UniformLocalArity
#print axioms ConstitutiveSearch.RelationalExtensive.AtLeastBinaryLocalArity
#print axioms ConstitutiveSearch.RelationalExtensive.uniformLocalArity_width
#print axioms ConstitutiveSearch.RelationalExtensive.atLeastBinaryLocalArity_width_lowerBound
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily.fullWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily.fullWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.sourceWidth_eq_twoPow
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_distinctSeparateConservation
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange_complete
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange_nodup
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange_length
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityStage
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityHistory
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityRelationalFamily
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityRelationalFamily_unbounded
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityRelationalFamily_variable
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryStage
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryHistory
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryRelationalFamily
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryRelationalFamily_unbounded
/- AXIOM_AUDIT_END -/
