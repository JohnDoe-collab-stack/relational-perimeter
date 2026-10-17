import RelationalPerimeter.Constitution.Godel.RuntimePersistence
import RelationalPerimeter.Constitution.Reals.CommonRealRuntime

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Gödel, operational grouping, and produced relational completeness

This terminal raccord starts exactly from the already produced Gödel
continuation `H1`.  Its authoritative runtime executes a diagonal source and
then a grouping request, stores the exact dependent resources, and obtains its
readout only from that memory.  The same three Gödel occurrences are
transported through all twelve fresh phases.

The positive conclusion is produced sequential completeness for every
supplied executed Cauchy family on that exact presentation.  It is not a
same-regime total closure.  Such a closure is required to act coherently along
actual `DepthExtension`s, and its restriction to the canonical extension
`0 -> 1` is rejected by the same produced Gödel witness.
-/

namespace StrongPerimetralTurning
namespace GodelRelationalCompleteness

open GodelGroupingTower
open GodelRuntimePersistence
open ConstitutiveSearch.OccurrencePersistence
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime
open RelationalPerimeter.Constitution.Reals.ProducedCompleteness
open RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime

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

/-- The positive, proof-relevant extension from depth zero to depth one. -/
def godelPrefixExtension : DepthExtension 0 1 :=
  .step (.refl 0)

/-
A forbidden global closure is an action along supplied positive extensions,
not an unrelated family indexed only by natural numbers.  Its coherence law
uses actual composition and preserves the labels of the exact transported
prior occurrences.
-/
structure GlobalSameRegimeClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  root : SameRegimeAdmissionAt execution 0
  extendOne : (source : Nat) ->
    SameRegimeAdmissionAt execution source ->
      SameRegimeAdmissionAt execution (source + 1)
  preservesPriorLabels :
    (source : Nat) ->
      (admission : SameRegimeAdmissionAt execution source) ->
      (occurrence : History.Occurrence
        (ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory
          (godelPerimetralPresentation execution) source).history) ->
      (extendOne source admission).1.label
          (extendOccurrence (godelPerimetralPresentation execution)
            (.step (.refl source)) occurrence) =
        admission.1.label occurrence

/-- Build closure only by iterating the supplied one-step action from its root. -/
def GlobalSameRegimeClosure.closeAlong
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution) :
    {target : Nat} -> DepthExtension 0 target ->
      SameRegimeAdmissionAt execution target
  | _, .refl _ => closure.root
  | _, .step prior => closure.extendOne _ (closure.closeAlong prior)

/-- Restrict only along a supplied positive extension from the root. -/
def GlobalSameRegimeClosure.restrictAlong
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution)
    {target : Nat}
    (extension : DepthExtension 0 target) :
    SameRegimeAdmissionAt execution target :=
  closure.closeAlong extension

/-- Restriction to `H1` consumes the canonical positive extension `0 -> 1`. -/
def GlobalSameRegimeClosure.restrictToGodelPrefix
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution) :
    GodelPositiveSameRegimeAdmission execution :=
  closure.restrictAlong godelPrefixExtension

/-- The coherent global closure is rejected at its actual Gödel prefix. -/
def globalSameRegimeClosureToEmpty
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    (closure : GlobalSameRegimeClosure execution) : Empty :=
  rejectGodelExplicitAdmissionToEmpty closure.restrictToGodelPrefix

/-!
## One terminal master

The family is indexed by the exact Gödel presentation and by base depth one.
The first limit is extracted from one authoritative singleton run.  The
positive real, universal convergence, finite regrouping producer, persistence,
and negative rejections all remain fields of that one package.
-/

structure Result
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) where
  master : CommonRealRuntime.Completeness family
  masterExact : master = CommonRealRuntime.complete family
  correspondence : ExecutedGodelPerimetralCorrespondence execution
  initial : Runtime family
  initialExact : initial = initialState family
  initialHistoryExact :
    Journal.history initial.journal =
      godelPerimetralContinuation execution
  initialReachable : Reachable family initial
  producedReal : RuntimeProducedRelationalReal family
  producedRealExact : producedReal =
    RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedCauchyFamily.completeViaRuntime
      family
  firstStep : ExecutedStep family initial (.limit 0)
  firstStepExact :
    firstStep = producedReal.produce initial initialReachable 0
  firstRun : ExecutedRun family initial [.limit 0]
  firstRunExact : firstRun = ExecutedRun.singleton firstStep
  firstRunCanonical : firstRun = run family initial [.limit 0]
  finalReachable : Reachable family firstRun.finalState
  firstLimitProduction :
    ExecutedLimitProduction family initial.journal 0
  firstLimitProductionExact :
    firstLimitProduction =
      firstRun.firstStep.response.limitProduction
  finalJournalExact :
    firstRun.finalState.journal = firstLimitProduction.completedJournal
  finalReadoutExact :
    firstRun.finalState.last =
      some
        { stamp := .limit 0
          code := firstLimitProduction.readout }
  producedRealRuntimeExact :
    (state : Runtime family) ->
    (reachable : Reachable family state) -> (precision : Nat) ->
      producedReal.produce state reachable precision =
        perform family state (.limit precision)
  sourceNearProducedLimit :
    (precision : Nat) ->
    {sourceState limitState : Runtime family} ->
    (sourceReachable : Reachable family sourceState) ->
    (sourceAt : family.SourceAt precision) ->
    (sourceStep :
      ExecutedStep family sourceState (.source precision sourceAt)) ->
    (limitReachable : Reachable family limitState) ->
      Near precision sourceStep.response.readout
        (producedReal.produce limitState limitReachable precision).response.readout
  groupFinite :
    {precision : Nat} ->
    {start current : Journal (godelPerimetralPresentation execution) 1} ->
    {size : Nat} ->
    (chain : family.ExecutedSourceChain precision start current size) ->
      family.ExecutedFiniteGrouping chain
  groupFiniteExact :
    {precision : Nat} ->
    {start current : Journal (godelPerimetralPresentation execution) 1} ->
    {size : Nat} ->
    (chain : family.ExecutedSourceChain precision start current size) ->
      groupFinite chain = family.executeFiniteGrouping chain
  initialPersistence :
    PersistedGodelOccurrences execution initial.journal.absoluteDepth
  initialPersistenceExact :
    initialPersistence = persistedAt execution initial.journal
  runPersistence :
    RunPersistence execution family firstRun.traceEvidence initialPersistence
  persistedThroughLimit :
    PersistedGodelOccurrences execution
      firstRun.finalState.journal.absoluteDepth
  persistedThroughLimitExact :
    persistedThroughLimit = runPersistence.terminal
  totalLoopRejected : ExecutedGodelTotalLoop execution.witness -> Empty
  globalClosureRejected : GlobalSameRegimeClosure execution -> Empty

/--
Build the complete positive and negative terminal result from one executed
Gödel witness and one producer-indexed family.
-/
def raccord
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    Result execution family := by
  let initial := initialState family
  let initialReachable : Reachable family initial := .initial
  let master := CommonRealRuntime.complete family
  let producedReal := master.rich.produced
  let firstStep := producedReal.produce initial initialReachable 0
  let firstRun := ExecutedRun.singleton firstStep
  let firstProduction := firstStep.response.limitProduction
  let initialPersisted := persistedAt execution initial.journal
  let runPersistence :=
    persistThroughRunFrom execution family firstRun.traceEvidence
      initialPersisted
  exact
  { master := master
    masterExact := rfl
    correspondence := executedGodelPerimetralCorrespondence execution
    initial := initial
    initialExact := rfl
    initialHistoryExact := rfl
    initialReachable := initialReachable
    producedReal := producedReal
    producedRealExact := rfl
    firstStep := firstStep
    firstStepExact := rfl
    firstRun := firstRun
    firstRunExact := rfl
    firstRunCanonical := rfl
    finalReachable := firstRun.finalReachable initialReachable
    firstLimitProduction := firstProduction
    firstLimitProductionExact := rfl
    finalJournalExact := by
      exact firstStep.next_journal.trans
        firstStep.response.limit_completedJournal
    finalReadoutExact := firstStep.next_last
    producedRealRuntimeExact := producedReal.produceCanonical
    sourceNearProducedLimit := producedReal.sourceNear
    groupFinite := master.rich.groupFinite
    groupFiniteExact := fun _chain => rfl
    initialPersistence := initialPersisted
    initialPersistenceExact := rfl
    runPersistence := runPersistence
    persistedThroughLimit := runPersistence.terminal
    persistedThroughLimitExact := rfl
    totalLoopRejected := totalLoopToEmpty
    globalClosureRejected := globalSameRegimeClosureToEmpty }

/-- The authoritative runtime starts exactly at Gödel depth one. -/
theorem initial_depth_one
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    (raccord execution family).initial.journal.absoluteDepth = 1 := by
  rw [(raccord execution family).initialExact]
  rfl

/-- The source inside the first limit reaches absolute depth seven. -/
theorem firstSource_depth_seven
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    (raccord execution family).firstLimitProduction.source.completedJournal.absoluteDepth =
      7 := by
  rw [(raccord execution family).firstLimitProduction.sourceCompletedDepth]
  rw [initial_depth_one execution family]

/-- The complete source--grouping request reaches absolute depth thirteen. -/
theorem firstLimitProduction_depth_thirteen
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    (raccord execution family).firstLimitProduction.completedJournal.absoluteDepth =
      13 := by
  rw [(raccord execution family).firstLimitProduction.completedDepth]
  rw [initial_depth_one execution family]

/-- The first observation is computed by the producer selected at precision zero. -/
theorem firstLimitProduction_readout_exact
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    (raccord execution family).firstLimitProduction.readout =
      family.producer.calculate (family.diagonalSourceAt 0).request := by
  rw [(raccord execution family).firstLimitProduction.readout_is_source]
  rw [(raccord execution family).firstLimitProduction.source.readout_is_calculated]
  rw [(raccord execution family).firstLimitProduction.sourceAtExact]

/-- The terminal run refines the reduced contract; it is not built from it. -/
theorem firstRun_projects
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    project (raccord execution family).firstRun.finalState =
      reducedRun (family := family)
        (project (raccord execution family).initial)
        [RuntimeRequest.limit (family := family) 0] := by
  rw [(raccord execution family).firstRunCanonical]
  exact run_projects family _ _

end GodelRelationalCompleteness
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.totalLoopToEmpty
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.SameRegimeAdmissionAt
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.godelPrefixExtension
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure.closeAlong
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure.restrictAlong
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.GlobalSameRegimeClosure.restrictToGodelPrefix
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.globalSameRegimeClosureToEmpty
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.Result
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.raccord
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.initial_depth_one
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstSource_depth_seven
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstLimitProduction_depth_thirteen
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstLimitProduction_readout_exact
#print axioms StrongPerimetralTurning.GodelRelationalCompleteness.firstRun_projects
/- AXIOM_AUDIT_END -/
