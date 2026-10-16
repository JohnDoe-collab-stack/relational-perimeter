import RelationalPerimeter.Constitution.Reals.LimitProduction

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gödel perimeter and relational-real completeness

This is the terminal generic raccord.  The negative and positive branches use
the exact same presentation produced from the exact same executed Gödel
witness.  The first free continuation is retained as depth one.  Real requests
continue from that depth, and the three distinct Gödel occurrences persist
through the first completed request.

The positive conclusion is effective sequential completeness for every
supplied executed Cauchy family.  It is not a same-regime closure: a total loop
or a closure admission at the first prefix still yields `Empty` by consuming
the truth and non-provability of the same produced diagonal sentence.
-/

namespace StrongPerimetralTurning
namespace GodelRelationalCompleteness

open GodelGroupingTower
open ConstitutiveSearch.OccurrencePersistence
open RelationalPerimeter.Constitution.Reals

universe uFormula uSentence uProof uTruth

/-- One journal operation whose underlying history is the Gödel continuation. -/
def seedJournal
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (code : SignedDyadicCode) :
    OperationJournal ApproximationPayload :=
  .snoc .root
    (fineOperation (limitPayload 0 code) .effectiveContinuation)

theorem seedJournal_depth
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (code : SignedDyadicCode) :
    (seedJournal execution code).depth = 1 :=
  rfl

/-- The seed is not a parallel history: it is definitionally the established H1. -/
theorem seedHistory_is_godelContinuation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (code : SignedDyadicCode) :
    OperationJournal.history
        (godelPerimetralPresentation execution)
        (seedJournal execution code) =
      godelPerimetralContinuation execution :=
  rfl

/-- A total loop is rejected by the exact produced Gödel witness. -/
def totalLoopToEmpty
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (loop : ExecutedGodelTotalLoop execution.witness) : Empty :=
  execution.witness.rejectProducedCompleteness loop.toProducedCompleteness

/-- Same-regime closing data at one exact finite prefix. -/
abbrev SameRegimeAdmissionAt
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (depth : Nat) : Type _ :=
  Sigma fun refinement :
      CircularRefinement (godelPerimetralPresentation execution)
        (ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory
          (godelPerimetralPresentation execution) depth) =>
    PositiveContinuation refinement.extension

/--
A forbidden global closure attempt acts on every finite prefix and preserves
all prior occurrence labels along every depth extension.  It does not contain
a distinguished first-prefix admission: that admission is obtained only by
restricting this coherent total prefix action to depth one.
-/
structure GlobalSameRegimeClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  closePrefix : (depth : Nat) -> SameRegimeAdmissionAt execution depth
  preservesPriorLabels :
    {source target : Nat} ->
      (extension : DepthExtension source target) ->
      (occurrence : History.Occurrence
        (ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory
          (godelPerimetralPresentation execution) source).history) ->
      (closePrefix target).1.label
          (extendOccurrence (godelPerimetralPresentation execution)
            extension occurrence) =
        (closePrefix source).1.label occurrence

/-- Restrict a global closing action to any requested finite prefix. -/
def GlobalSameRegimeClosure.restrict
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution)
    (depth : Nat) : SameRegimeAdmissionAt execution depth :=
  closure.closePrefix depth

/-- Depth one is definitionally the established Gödel continuation. -/
def GlobalSameRegimeClosure.restrictToGodelPrefix
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution) :
    GodelPositiveSameRegimeAdmission execution :=
  closure.restrict 1

/--
The global closure is rejected by restriction, then by the already established
conversion from the exact produced truth witness to a proof of that witness.
-/
def globalSameRegimeClosureToEmpty
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution) : Empty :=
  rejectGodelExplicitAdmissionToEmpty closure.restrictToGodelPrefix

/--
The complete terminal package.  Its family is indexed by the Gödel
presentation itself, so changing the perimeter or witness cannot inhabit this
type.
-/
structure Result
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) where
  correspondence : ExecutedGodelPerimetralCorrespondence execution
  sequentialCompleteness : SequentialCompletenessResult family
  executedSequentialCompleteness : FullyExecutedSequentialCompleteness family
  sequentialCompletenessExact :
    executedSequentialCompleteness.sequential = sequentialCompleteness
  seed : OperationJournal ApproximationPayload
  seedExact :
    seed = seedJournal execution
      (sequentialCompleteness.limit.approximation 0)
  seedHistoryExact :
    OperationJournal.history (godelPerimetralPresentation execution) seed =
      godelPerimetralContinuation execution
  firstLimitProduction : ExecutedLimitProduction family seed 0
  firstLimitProductionExact :
    firstLimitProduction =
      executedSequentialCompleteness.produceLimit seed 0
  persistedThroughSource :
    PersistedGodelOccurrences execution
      firstLimitProduction.source.afterExecutionState.journal.depth
  persistedThroughLimitProduction :
    PersistedGodelOccurrences execution
      firstLimitProduction.completedJournal.depth
  totalLoopRejected : ExecutedGodelTotalLoop execution.witness -> Empty
  globalClosureRejected : GlobalSameRegimeClosure execution -> Empty

/--
Construct the positive limit and the negative closure rejection from the same
executed witness and presentation.
-/
def raccord
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) :
    Result execution family := by
  let correspondence := executedGodelPerimetralCorrespondence execution
  let executedCompleteness := fullyExecutedSequentialCompleteness family
  let completeness := executedCompleteness.sequential
  let seed := seedJournal execution (completeness.limit.approximation 0)
  let firstProduction := executedCompleteness.produceLimit seed 0
  let seedPersisted : PersistedGodelOccurrences execution seed.depth := by
    change PersistedGodelOccurrences execution 1
    exact persistGodelOccurrences execution (.refl 1)
  let sourceStartPersisted :
      PersistedGodelOccurrences execution
        firstProduction.source.journal.depth := by
    rw [firstProduction.sourceJournalExact]
    exact seedPersisted
  let sourcePersisted :=
    persistGodelOccurrencesThroughRequest execution
      firstProduction.source.journal
      (sourcePayload firstProduction.source.source.index
        firstProduction.source.source.readoutPrecision
        (ExecutedCauchyFamily.sourceCode firstProduction.source.source))
      sourceStartPersisted
  let limitPersisted :=
    persistGodelOccurrencesThroughRequest execution
      firstProduction.source.afterExecutionState.journal
      (limitPayload 0 firstProduction.groupedCharge.outputCode)
      sourcePersisted
  exact
  { correspondence := correspondence
    sequentialCompleteness := completeness
    executedSequentialCompleteness := executedCompleteness
    sequentialCompletenessExact := rfl
    seed := seed
    seedExact := rfl
    seedHistoryExact :=
      seedHistory_is_godelContinuation execution
        (completeness.limit.approximation 0)
    firstLimitProduction := firstProduction
    firstLimitProductionExact := rfl
    persistedThroughSource := sourcePersisted
    persistedThroughLimitProduction := limitPersisted
    totalLoopRejected := totalLoopToEmpty
    globalClosureRejected := globalSameRegimeClosureToEmpty }

/--
The first complete production is the precision-zero specialization of the
universal producer retained by the terminal package; it is not reconstructed
beside it.
-/
theorem firstLimitProduction_is_universalSpecialization
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) :
    (raccord execution family).firstLimitProduction =
      (raccord execution family).executedSequentialCompleteness.produceLimit
        (raccord execution family).seed 0 :=
  (raccord execution family).firstLimitProductionExact

/-- The universal specialization is also the canonical complete producer. -/
theorem firstLimitProduction_is_canonicalProducer
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) :
    (raccord execution family).firstLimitProduction =
      executeLimitProduction family (raccord execution family).seed 0 := by
  exact
    (raccord execution family).firstLimitProductionExact.trans
      ((raccord execution family).executedSequentialCompleteness
        |>.produceLimitCanonical (raccord execution family).seed 0)

/-- The source request actually owned by the master reaches depth seven. -/
theorem firstSourceJournal_depth_seven
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) :
    (raccord execution family).firstLimitProduction.source.afterExecutionState.journal.depth =
      7 := by
  have seedDepth : (raccord execution family).seed.depth = 1 := by
    rw [(raccord execution family).seedExact]
    exact seedJournal_depth execution
      ((raccord execution family).sequentialCompleteness.limit.approximation 0)
  calc
    (raccord execution family).firstLimitProduction.source.afterExecutionState.journal.depth =
        (raccord execution family).firstLimitProduction.source.journal.depth + 6 :=
      ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState_depth
        (raccord execution family).firstLimitProduction.source
    _ = (raccord execution family).seed.depth + 6 := by
      rw [(raccord execution family).firstLimitProduction.sourceJournalExact]
    _ = 1 + 6 := congrArg (fun depth => depth + 6) seedDepth
    _ = 7 := rfl

/-- The complete source–grouping–limit program reaches depth thirteen. -/
theorem firstLimitProduction_depth_thirteen
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) :
    (raccord execution family).firstLimitProduction.completedJournal.depth =
      13 := by
  have seedDepth : (raccord execution family).seed.depth = 1 := by
    rw [(raccord execution family).seedExact]
    exact seedJournal_depth execution
      ((raccord execution family).sequentialCompleteness.limit.approximation 0)
  calc
    (raccord execution family).firstLimitProduction.completedJournal.depth =
        (raccord execution family).seed.depth + 12 :=
      (raccord execution family).firstLimitProduction.completedJournal_depth
    _ = 1 + 12 := congrArg (fun depth => depth + 12) seedDepth
    _ = 13 := rfl

/-- Its readout is the constructed limit, after consuming the grouping output. -/
theorem firstLimitProduction_readout_exact
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution)) :
    (raccord execution family).firstLimitProduction.readout =
      (raccord execution family).sequentialCompleteness.limit.approximation 0 :=
  (raccord execution family).firstLimitProduction.readout_is_limitApproximation

end GodelRelationalCompleteness
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.seedJournal
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.seedJournal_depth
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.seedHistory_is_godelContinuation
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.totalLoopToEmpty
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.SameRegimeAdmissionAt
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure.restrict
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure.restrictToGodelPrefix
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.globalSameRegimeClosureToEmpty
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.Result
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.raccord
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstLimitProduction_is_universalSpecialization
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstLimitProduction_is_canonicalProducer
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstSourceJournal_depth_seven
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstLimitProduction_depth_thirteen
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstLimitProduction_readout_exact
/- AXIOM_AUDIT_END -/
