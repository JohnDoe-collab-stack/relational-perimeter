import RelationalPerimeter.Constitution.Reals.SequentialCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Executed finite-source grouping

A finite grouping must consume profiles that were actually produced in one
chronological journal, not an arbitrary list of values.  `ExecutedSourceChain`
therefore appends each certified source only after the preceding source
execution has completed.  Its finite selection is projected from those owned
executions.  The batch normalizer then consumes every selected identity with a
rank equal to the number of identities still pending.
-/

namespace RelationalPerimeter.Constitution.Reals

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower

/--
Chronological source executions at one requested precision.  The ending
journal of each constructor is fixed by the actual six-phase execution it
owns.
-/
inductive ExecutedSourceChain
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) :
    OperationJournal ApproximationPayload ->
      OperationJournal ApproximationPayload -> Nat -> Type 1
  | empty (journal : OperationJournal ApproximationPayload) :
      ExecutedSourceChain family precision journal journal 0
  | snoc
      {initial current : OperationJournal ApproximationPayload}
      {size : Nat}
      (prior : ExecutedSourceChain family precision initial current size)
      (source : family.SourceAt precision)
      (execution :
        ExecutedApproximation P current
          (sourcePayload source.index source.readoutPrecision
            (family.sourceCode source))) :
      ExecutedSourceChain family precision initial
        (ExecutedApproximation.completedJournal current
          (sourcePayload source.index source.readoutPrecision
            (family.sourceCode source)))
        (size + 1)

namespace ExecutedSourceChain

/-- Append the next source by executing it from the exact previous journal. -/
def append
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial current : OperationJournal ApproximationPayload}
    {size : Nat}
    (prior : ExecutedSourceChain family precision initial current size)
    (source : family.SourceAt precision) :
    ExecutedSourceChain family precision initial
      (ExecutedApproximation.completedJournal current
        (sourcePayload source.index source.readoutPrecision
          (family.sourceCode source)))
      (size + 1) :=
  .snoc prior source
    (family.executeSource current source.index source.readoutPrecision)

/--
The finite selection is built only from the execution packages owned by the
chain.  No source code or provenance is reconstructed independently.
-/
def selection
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat} :
    ExecutedSourceChain family precision initial final size ->
      HistoricalGrouping.FiniteSelection
        (family.groupingEnvelope precision) size
  | .empty _ =>
      HistoricalGrouping.emptySelection (family.groupingEnvelope precision)
  | .snoc prior source execution =>
      (selection prior).snoc
        { journal := _
          source := source
          execution := execution }

/-- Six journal operations for every source retained by a chain. -/
def operationCount : Nat -> Nat
  | 0 => 0
  | Nat.succ size => operationCount size + 6

theorem finalDepth_exact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    (chain : ExecutedSourceChain family precision initial final size) :
    final.depth = initial.depth + operationCount size := by
  induction chain with
  | empty => rfl
  | snoc prior source execution inductionHypothesis =>
      calc
        (ExecutedApproximation.completedJournal _
          (sourcePayload source.index source.readoutPrecision
            (family.sourceCode source))).depth = _ + 6 :=
          ExecutedApproximation.completedJournal_depth _ _
        _ = (initial.depth + operationCount _) + 6 := by
          rw [inductionHypothesis]
        _ = initial.depth + (operationCount _ + 6) :=
          Nat.add_assoc initial.depth (operationCount _) 6

end ExecutedSourceChain

/--
The complete finite normalization of one chronological executed-source chain.
The exact result field prevents replacing the batch action with an arbitrary
target charge.
-/
structure ExecutedFiniteGrouping
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    (chain : ExecutedSourceChain family precision initial final size) where
  grouped : HistoricalGrouping.BatchCharge chain.selection
  groupedExact :
    grouped = HistoricalGrouping.executeBatch chain.selection
  accepted : HistoricalGrouping.BatchAccepted
    (.target : HistoricalGrouping.BatchState size) grouped
  consumesEverySource : grouped.consumed.length = size
  normalizedTarget :
    (HistoricalGrouping.batchRules chain.selection).normal
      (HistoricalGrouping.initialBatchState chain.selection) = .target

/-- Execute the finite grouping action over every source in the chain. -/
def executeFiniteGrouping
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    (chain : ExecutedSourceChain family precision initial final size) :
    ExecutedFiniteGrouping chain where
  grouped := HistoricalGrouping.executeBatch chain.selection
  groupedExact := rfl
  accepted := HistoricalGrouping.executeBatchAccepted chain.selection
  consumesEverySource :=
    HistoricalGrouping.executeBatch_consumed_length chain.selection
  normalizedTarget :=
    HistoricalGrouping.normal_initialBatchState chain.selection

namespace ExecutedFiniteGrouping

/-- The produced evidence list is exactly the chain selection, oldest first. -/
theorem consumedExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    {chain : ExecutedSourceChain family precision initial final size}
    (grouping : ExecutedFiniteGrouping chain) :
    grouping.grouped.consumed =
      HistoricalGrouping.chargesForIndices chain.selection
        (HistoricalGrouping.initialBatchCharge chain.selection).available
        (HistoricalGrouping.allIndices size) := by
  rw [grouping.groupedExact]
  exact HistoricalGrouping.executeBatch_consumed_exact chain.selection

/-- The finite action returns the constructed limit target exactly. -/
def outputExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    {chain : ExecutedSourceChain family precision initial final size}
    (grouping : ExecutedFiniteGrouping chain) :
    SameValue grouping.grouped.outputCode
      (family.limitApproximation precision) := by
  rw [grouping.groupedExact]
  exact HistoricalGrouping.executeBatch_outputExact chain.selection

end ExecutedFiniteGrouping

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedSourceChain
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedSourceChain.append
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedSourceChain.selection
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedSourceChain.operationCount
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedSourceChain.finalDepth_exact
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedFiniteGrouping
#print axioms RelationalPerimeter.Constitution.Reals.executeFiniteGrouping
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedFiniteGrouping.consumedExact
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedFiniteGrouping.outputExact
/- AXIOM_AUDIT_END -/
