import RelationalPerimeter.Constitution.HeytingArithmetic.ProofCoding

/-!
# Constructive chronology of encoded proof archives

Chronology is stated on the transparent line list, before beta quotation.  The
offset-indexed invariant is stable under reference rebasing and block
concatenation.  It supplies the encoder-side half of the archive discipline;
the checker-side half is already enforced by exposing only the accepted
prefix to every rule.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Every reference in a finite reference list is strictly below `bound`. -/
def ReferencesBefore (bound : Nat) : List Nat -> Prop
  | [] => True
  | reference :: remaining =>
      reference < bound ∧ ReferencesBefore bound remaining

/-- A block is chronological at an absolute starting offset when the first
    line only refers below the offset and every following line may additionally
    refer to the preceding line. -/
def ChronologicalFrom : Nat -> List ProofLine -> Prop
  | _offset, [] => True
  | offset, line :: remaining =>
      ReferencesBefore offset line.premises ∧
        ChronologicalFrom (Nat.succ offset) remaining

/-- Root chronology for a transparent proof archive. -/
def ProofArchive.Chronological (archive : ProofArchive) : Prop :=
  ChronologicalFrom 0 archive.lines

theorem referencesBefore_mono
    {smaller larger : Nat}
    (bounded : smaller <= larger)
    {references : List Nat}
    (before : ReferencesBefore smaller references) :
    ReferencesBefore larger references := by
  induction references with
  | nil => exact True.intro
  | cons reference remaining inductionHypothesis =>
      exact And.intro
        (Nat.lt_of_lt_of_le before.1 bounded)
        (inductionHypothesis before.2)

theorem referencesBefore_rebase
    (delta offset : Nat)
    {references : List Nat}
    (before : ReferencesBefore offset references) :
    ReferencesBefore (delta + offset)
      (references.map (fun reference => delta + reference)) := by
  induction references with
  | nil => exact True.intro
  | cons reference remaining inductionHypothesis =>
      exact And.intro
        (Nat.add_lt_add_left before.1 delta)
        (inductionHypothesis before.2)

theorem chronologicalFrom_rebase
    (delta offset : Nat)
    {lines : List ProofLine}
    (chronological : ChronologicalFrom offset lines) :
    ChronologicalFrom (delta + offset)
      (lines.map (ProofLine.rebase delta)) := by
  induction lines generalizing offset with
  | nil => exact True.intro
  | cons line remaining inductionHypothesis =>
      refine And.intro ?_ ?_
      · exact referencesBefore_rebase delta offset chronological.1
      · have tail := inductionHypothesis (Nat.succ offset) chronological.2
        rw [Nat.add_succ] at tail
        exact tail

theorem chronologicalFrom_append
    (offset : Nat)
    {earlier later : List ProofLine}
    (earlierChronological : ChronologicalFrom offset earlier)
    (laterChronological :
      ChronologicalFrom (offset + earlier.length) later) :
    ChronologicalFrom offset (earlier ++ later) := by
  induction earlier generalizing offset with
  | nil =>
      change ChronologicalFrom (offset + 0) later at laterChronological
      rw [Nat.add_zero] at laterChronological
      exact laterChronological
  | cons line remaining inductionHypothesis =>
      refine And.intro earlierChronological.1 ?_
      apply inductionHypothesis (Nat.succ offset) earlierChronological.2
      change ChronologicalFrom
        (offset + Nat.succ remaining.length) later at laterChronological
      rw [Nat.add_succ] at laterChronological
      rw [Nat.succ_add]
      exact laterChronological

theorem ProofArchive.chronological_rebase
    (archive : ProofArchive)
    (offset : Nat)
    (chronological : archive.Chronological) :
    ChronologicalFrom offset (archive.rebase offset).lines := by
  unfold ProofArchive.Chronological at chronological
  unfold ProofArchive.rebase
  have rebased := chronologicalFrom_rebase offset 0 chronological
  rw [Nat.add_zero] at rebased
  exact rebased

theorem ProofArchive.chronological_appendRebased
    (earlier later : ProofArchive)
    (earlierChronological : earlier.Chronological)
    (laterChronological : later.Chronological) :
    (earlier.appendRebased later).Chronological := by
  unfold ProofArchive.Chronological ProofArchive.appendRebased
  apply chronologicalFrom_append 0 earlierChronological
  have rebased :=
    later.chronological_rebase earlier.lineCount laterChronological
  unfold ProofArchive.lineCount at rebased
  rw [Nat.zero_add]
  exact rebased

theorem ProofArchive.chronological_finish
    (archive : ProofArchive)
    (line : ProofLine)
    (chronological : archive.Chronological)
    (lineReferences : ReferencesBefore archive.lineCount line.premises) :
    (archive.finish line).Chronological := by
  unfold ProofArchive.Chronological ProofArchive.finish
  apply chronologicalFrom_append 0 chronological
  rw [Nat.zero_add]
  unfold ProofArchive.lineCount at lineReferences
  exact And.intro lineReferences True.intro

theorem ProofArchive.lastIndex_lt_lineCount
    (archive : ProofArchive)
    (positive : 0 < archive.lineCount) :
    archive.lastIndex < archive.lineCount := by
  cases countEquation : archive.lineCount with
  | zero =>
      exact (Nat.not_lt_zero 0 (countEquation ▸ positive)).elim
  | succ count =>
      unfold ProofArchive.lastIndex
      rw [countEquation]
      exact Nat.lt_succ_self count

theorem ProofArchive.chronological_singleton
    (line : ProofLine)
    (noReferences : ReferencesBefore 0 line.premises) :
    (ProofArchive.singleton line).Chronological :=
  And.intro noReferences True.intro

theorem referencesBefore_singleton
    {bound reference : Nat}
    (bounded : reference < bound) :
    ReferencesBefore bound [reference] :=
  And.intro bounded True.intro

theorem referencesBefore_pair
    {bound first second : Nat}
    (firstBounded : first < bound)
    (secondBounded : second < bound) :
    ReferencesBefore bound [first, second] :=
  And.intro firstBounded (And.intro secondBounded True.intro)

theorem referencesBefore_triple
    {bound first second third : Nat}
    (firstBounded : first < bound)
    (secondBounded : second < bound)
    (thirdBounded : third < bound) :
    ReferencesBefore bound [first, second, third] :=
  And.intro firstBounded
    (And.intro secondBounded (And.intro thirdBounded True.intro))

theorem ProofArchive.singleton_lineCount_positive
    (line : ProofLine) :
    0 < (ProofArchive.singleton line).lineCount :=
  Nat.zero_lt_succ 0

theorem ProofArchive.finish_lineCount_positive
    (archive : ProofArchive)
    (line : ProofLine) :
    0 < (archive.finish line).lineCount := by
  rw [ProofArchive.lineCount_finish]
  exact Nat.zero_lt_succ _

theorem encodeDerivationWithAxiomParameters_lineCount_positive
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    (axiomParameters :
      {bound : Nat} -> {formula : ScopedFormula bound} ->
        theory.Axiom bound formula -> List Nat)
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation mode theory context conclusion) :
    0 < (encodeDerivationWithAxiomParameters axiomParameters proof).lineCount := by
  cases proof <;>
    unfold encodeDerivationWithAxiomParameters unaryArchive binaryArchive
      ternaryArchive <;>
    first
    | exact ProofArchive.singleton_lineCount_positive _
    | exact ProofArchive.finish_lineCount_positive _ _

theorem unaryArchive_chronological
    (archive : ProofArchive)
    (line : Nat -> ProofLine)
    (chronological : archive.Chronological)
    (positive : 0 < archive.lineCount)
    (premisesEquation :
      (line archive.lastIndex).premises = [archive.lastIndex]) :
    (unaryArchive archive line).Chronological := by
  unfold unaryArchive
  apply archive.chronological_finish
  · exact chronological
  · rw [premisesEquation]
    exact referencesBefore_singleton
      (archive.lastIndex_lt_lineCount positive)

theorem binaryArchive_chronological
    (first second : ProofArchive)
    (line : Nat -> Nat -> ProofLine)
    (firstChronological : first.Chronological)
    (secondChronological : second.Chronological)
    (firstPositive : 0 < first.lineCount)
    (secondPositive : 0 < second.lineCount)
    (premisesEquation :
      (line first.lastIndex
        (first.appendRebased second).lastIndex).premises =
          [first.lastIndex, (first.appendRebased second).lastIndex]) :
    (binaryArchive first second line).Chronological := by
  let combined := first.appendRebased second
  have combinedChronological : combined.Chronological :=
    first.chronological_appendRebased second
      firstChronological secondChronological
  have combinedPositive : 0 < combined.lineCount := by
    unfold combined
    rw [ProofArchive.lineCount_appendRebased]
    exact Nat.add_pos_right first.lineCount secondPositive
  have firstBounded : first.lastIndex < combined.lineCount := by
    apply Nat.lt_of_lt_of_le
      (first.lastIndex_lt_lineCount firstPositive)
    unfold combined
    rw [ProofArchive.lineCount_appendRebased]
    exact Nat.le_add_right first.lineCount second.lineCount
  have combinedBounded : combined.lastIndex < combined.lineCount :=
    combined.lastIndex_lt_lineCount combinedPositive
  unfold binaryArchive
  apply combined.chronological_finish
  · exact combinedChronological
  · rw [premisesEquation]
    exact referencesBefore_pair firstBounded combinedBounded

theorem ternaryArchive_chronological
    (first second third : ProofArchive)
    (line : Nat -> Nat -> Nat -> ProofLine)
    (firstChronological : first.Chronological)
    (secondChronological : second.Chronological)
    (thirdChronological : third.Chronological)
    (firstPositive : 0 < first.lineCount)
    (secondPositive : 0 < second.lineCount)
    (thirdPositive : 0 < third.lineCount)
    (premisesEquation :
      (line first.lastIndex
        (first.appendRebased second).lastIndex
        ((first.appendRebased second).appendRebased third).lastIndex).premises =
          [first.lastIndex,
            (first.appendRebased second).lastIndex,
            ((first.appendRebased second).appendRebased third).lastIndex]) :
    (ternaryArchive first second third line).Chronological := by
  let firstSecond := first.appendRebased second
  let combined := firstSecond.appendRebased third
  have firstSecondChronological : firstSecond.Chronological :=
    first.chronological_appendRebased second
      firstChronological secondChronological
  have combinedChronological : combined.Chronological :=
    firstSecond.chronological_appendRebased third
      firstSecondChronological thirdChronological
  have firstSecondPositive : 0 < firstSecond.lineCount := by
    unfold firstSecond
    rw [ProofArchive.lineCount_appendRebased]
    exact Nat.add_pos_right first.lineCount secondPositive
  have combinedPositive : 0 < combined.lineCount := by
    unfold combined
    rw [ProofArchive.lineCount_appendRebased]
    exact Nat.add_pos_right firstSecond.lineCount thirdPositive
  have firstToFirstSecond :
      first.lineCount <= firstSecond.lineCount := by
    unfold firstSecond
    rw [ProofArchive.lineCount_appendRebased]
    exact Nat.le_add_right first.lineCount second.lineCount
  have combinedCount :
      combined.lineCount =
        firstSecond.lineCount + third.lineCount := by
    unfold combined
    exact ProofArchive.lineCount_appendRebased firstSecond third
  have firstSecondToCombined :
      firstSecond.lineCount <= combined.lineCount := by
    rw [combinedCount]
    exact Nat.le_add_right firstSecond.lineCount third.lineCount
  have firstBounded : first.lastIndex < combined.lineCount := by
    exact Nat.lt_of_lt_of_le
      (first.lastIndex_lt_lineCount firstPositive)
      (Nat.le_trans firstToFirstSecond firstSecondToCombined)
  have firstSecondBounded :
      firstSecond.lastIndex < combined.lineCount := by
    exact Nat.lt_of_lt_of_le
      (firstSecond.lastIndex_lt_lineCount firstSecondPositive)
      firstSecondToCombined
  have combinedBounded : combined.lastIndex < combined.lineCount :=
    combined.lastIndex_lt_lineCount combinedPositive
  unfold ternaryArchive
  apply combined.chronological_finish
  · exact combinedChronological
  · rw [premisesEquation]
    exact referencesBefore_triple
      firstBounded firstSecondBounded combinedBounded

theorem encodeDerivationWithAxiomParameters_chronological
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    (axiomParameters :
      {bound : Nat} -> {formula : ScopedFormula bound} ->
        theory.Axiom bound formula -> List Nat)
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation mode theory context conclusion) :
    (encodeDerivationWithAxiomParameters axiomParameters proof).Chronological := by
  induction proof with
  | theoryAxiom witness =>
      unfold encodeDerivationWithAxiomParameters
      exact ProofArchive.chronological_singleton _ True.intro
  | hypothesis member =>
      unfold encodeDerivationWithAxiomParameters
      exact ProofArchive.chronological_singleton _ True.intro
  | weaken extra premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | implicationIntroduction premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | implicationElimination implication argument
      implicationInduction argumentInduction =>
      unfold encodeDerivationWithAxiomParameters
      apply binaryArchive_chronological
      · exact implicationInduction
      · exact argumentInduction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters implication
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters argument
      · rfl
  | conjunctionIntroduction left right leftInduction rightInduction =>
      unfold encodeDerivationWithAxiomParameters
      apply binaryArchive_chronological
      · exact leftInduction
      · exact rightInduction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters left
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters right
      · rfl
  | conjunctionEliminationLeft premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | conjunctionEliminationRight premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | disjunctionIntroductionLeft premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | disjunctionIntroductionRight premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | disjunctionElimination disjunction leftBranch rightBranch
      disjunctionInduction leftInduction rightInduction =>
      unfold encodeDerivationWithAxiomParameters
      apply ternaryArchive_chronological
      · exact disjunctionInduction
      · exact leftInduction
      · exact rightInduction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters disjunction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters leftBranch
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters rightBranch
      · rfl
  | falsumElimination premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | universalIntroduction premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | universalElimination term premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | existentialIntroduction term premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | existentialElimination existential branch
      existentialInduction branchInduction =>
      unfold encodeDerivationWithAxiomParameters
      apply binaryArchive_chronological
      · exact existentialInduction
      · exact branchInduction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters existential
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters branch
      · rfl
  | equalityReflexivity term =>
      unfold encodeDerivationWithAxiomParameters
      exact ProofArchive.chronological_singleton _ True.intro
  | equalitySymmetry premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | equalityTransitivity first second firstInduction secondInduction =>
      unfold encodeDerivationWithAxiomParameters
      apply binaryArchive_chronological
      · exact firstInduction
      · exact secondInduction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters first
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters second
      · rfl
  | equalitySubstitution body equality premise
      equalityInduction premiseInduction =>
      unfold encodeDerivationWithAxiomParameters
      apply binaryArchive_chronological
      · exact equalityInduction
      · exact premiseInduction
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters equality
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | liftVariables premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | freeInstantiation replacement premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl
  | doubleNegationElimination permission premise inductionHypothesis =>
      unfold encodeDerivationWithAxiomParameters
      apply unaryArchive_chronological
      · exact inductionHypothesis
      · exact encodeDerivationWithAxiomParameters_lineCount_positive
          axiomParameters premise
      · rfl

theorem encodeStandardDerivation_chronological
    {mode : LogicMode}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation mode standardArithmeticTheory context conclusion) :
    (encodeStandardDerivation proof).Chronological :=
  encodeDerivationWithAxiomParameters_chronological
    standardArithmeticAxiomParameters proof

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.ReferencesBefore
#print axioms RelationalPerimeter.HeytingArithmetic.ChronologicalFrom
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchive.Chronological
#print axioms RelationalPerimeter.HeytingArithmetic.chronologicalFrom_rebase
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchive.chronological_appendRebased
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchive.chronological_finish
#print axioms RelationalPerimeter.HeytingArithmetic.encodeDerivationWithAxiomParameters_lineCount_positive
#print axioms RelationalPerimeter.HeytingArithmetic.encodeStandardDerivation_chronological
/- AXIOM_AUDIT_END -/
