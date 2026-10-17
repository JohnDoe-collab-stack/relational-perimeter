import RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Persistence of the produced Gödel occurrences through runtime execution

The runtime journal is rooted at depth one, the already produced Gödel
continuation.  This module transports that one established occurrence triple
through every actual semantic phase.  Each phase also proves that all three
transported prior occurrences are distinct from its fresh occurrence.
-/

namespace StrongPerimetralTurning.GodelRuntimePersistence

open GodelGroupingTower
open ConstitutiveSearch.OccurrencePersistence
open RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime
open RelationalPerimeter.Constitution.Reals.ProducedCompleteness
open RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime

universe uRequest uResource

/-- A journal rooted at `H1` carries a positive extension from that exact base. -/
def journalExtension {P : CircularPresentation} (journal : Journal P 1) :
    DepthExtension 1 journal.absoluteDepth :=
  extendDepthBy 1 journal.relativeDepth

/-- The original Gödel triple transported into an exact runtime journal. -/
def persistedAt
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (journal : Journal (godelPerimetralPresentation execution) 1) :
    PersistedGodelOccurrences execution journal.absoluteDepth :=
  persistGodelOccurrences execution (journalExtension journal)

/--
One actual phase transports the same prior triple injectively and separates
each transported occurrence from the phase's actual fresh occurrence.
-/
structure PhasePersistence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {before : Journal (godelPerimetralPresentation execution) 1}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase (godelPerimetralPresentation execution)
      before request phase)
    (prior : PersistedGodelOccurrences execution before.absoluteDepth) where
  persisted : PersistedGodelOccurrences execution executed.after.absoluteDepth
  productionExact :
    persisted.production = executed.transportPrior prior.production
  certificationExact :
    persisted.certification = executed.transportPrior prior.certification
  continuationExact :
    persisted.continuation = executed.transportPrior prior.continuation
  productionFreshDistinct :
    persisted.production ≠ executed.occurrence
  certificationFreshDistinct :
    persisted.certification ≠ executed.occurrence
  continuationFreshDistinct :
    persisted.continuation ≠ executed.occurrence

/-- Construct the exact one-phase persistence package. -/
def persistThroughPhase
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    {before : Journal (godelPerimetralPresentation execution) 1}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase (godelPerimetralPresentation execution)
      before request phase)
    (prior : PersistedGodelOccurrences execution before.absoluteDepth) :
    PhasePersistence execution executed prior :=
  { persisted :=
      { production := executed.transportPrior prior.production
        certification := executed.transportPrior prior.certification
        continuation := executed.transportPrior prior.continuation
        productionCertificationDistinct :=
          fun equality => prior.productionCertificationDistinct
            (executed.transportPrior_injective equality)
        productionContinuationDistinct :=
          fun equality => prior.productionContinuationDistinct
            (executed.transportPrior_injective equality)
        certificationContinuationDistinct :=
          fun equality => prior.certificationContinuationDistinct
            (executed.transportPrior_injective equality) }
    productionExact := rfl
    certificationExact := rfl
    continuationExact := rfl
    productionFreshDistinct := executed.transportPrior_ne_fresh prior.production
    certificationFreshDistinct :=
      executed.transportPrior_ne_fresh prior.certification
    continuationFreshDistinct :=
      executed.transportPrior_ne_fresh prior.continuation }

/--
Persistence evidence for all six phases of one exact executed request.  Every
field depends on the result of the preceding field, so no phase can be skipped
or reconstructed beside the execution.
-/
structure RequestPersistence
    {Request : Type uRequest}
    {program : Program.{uRequest, uResource} Request}
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {journal : Journal (godelPerimetralPresentation execution) 1}
    {request : Request}
    (executed : ExecutedRequest program
      (godelPerimetralPresentation execution) journal request) where
  initial : PersistedGodelOccurrences execution journal.absoluteDepth
  reception : PhasePersistence execution
    executed.memory.continued.authorized.acted.searched.received.phase initial
  search : PhasePersistence execution
    executed.memory.continued.authorized.acted.searched.phase reception.persisted
  action : PhasePersistence execution
    executed.memory.continued.authorized.acted.phase search.persisted
  authorization : PhasePersistence execution
    executed.memory.continued.authorized.phase action.persisted
  continuation : PhasePersistence execution
    executed.memory.continued.phase authorization.persisted
  memory : PhasePersistence execution
    executed.memory.phase continuation.persisted

/-- Transport the original triple through the six actual nested phases. -/
def persistThroughRequestFrom
    {Request : Type uRequest}
    {program : Program.{uRequest, uResource} Request}
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {journal : Journal (godelPerimetralPresentation execution) 1}
    {request : Request}
    (executed : ExecutedRequest program
      (godelPerimetralPresentation execution) journal request)
    (initial : PersistedGodelOccurrences execution journal.absoluteDepth) :
    RequestPersistence execution executed := by
  let reception := persistThroughPhase
    executed.memory.continued.authorized.acted.searched.received.phase initial
  let search := persistThroughPhase
    executed.memory.continued.authorized.acted.searched.phase reception.persisted
  let action := persistThroughPhase
    executed.memory.continued.authorized.acted.phase search.persisted
  let authorization := persistThroughPhase
    executed.memory.continued.authorized.phase action.persisted
  let continuation := persistThroughPhase
    executed.memory.continued.phase authorization.persisted
  let memory := persistThroughPhase executed.memory.phase continuation.persisted
  exact
  { initial := initial
    reception := reception
    search := search
    action := action
    authorization := authorization
    continuation := continuation
    memory := memory }

/-! ## Persistence owned by authoritative runtime steps and traces -/

/--
Persistence through one exact runtime response.  The source case consumes its
six nested phases.  The limit case consumes first the owned source phases and
then the owned grouping phases, sharing the terminal source transport.
-/
inductive StepPersistence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1)
    {state : Runtime family} :
    (request : RuntimeRequest family) ->
    ExecutedStep family state request ->
    PersistedGodelOccurrences execution state.journal.absoluteDepth -> Type _
  | source
      {precision : Nat}
      {sourceAt : family.SourceAt precision}
      (step : ExecutedStep family state (.source precision sourceAt))
      (initial : PersistedGodelOccurrences execution state.journal.absoluteDepth)
      (requestPersistence : RequestPersistence execution
        step.response.sourceProduction.execution)
      (initialExact : requestPersistence.initial = initial)
      (terminalJournalExact :
        step.next.journal =
          step.response.sourceProduction.execution.completedJournal) :
      StepPersistence execution family (.source precision sourceAt) step initial
  | limit
      {precision : Nat}
      (step : ExecutedStep family state (.limit precision))
      (initial : PersistedGodelOccurrences execution state.journal.absoluteDepth)
      (sourcePersistence : RequestPersistence execution
        step.response.limitProduction.source.execution)
      (sourceInitialExact : sourcePersistence.initial = initial)
      (groupingPersistence : RequestPersistence execution
        step.response.limitProduction.execution)
      (groupingInitialExact :
        groupingPersistence.initial = sourcePersistence.memory.persisted)
      (terminalJournalExact :
        step.next.journal =
          step.response.limitProduction.execution.completedJournal) :
      StepPersistence execution family (.limit precision) step initial

namespace StepPersistence

/-- Terminal transport produced by the exact response owned by the step. -/
def terminal
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    {family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1}
    {state : Runtime family}
    {request : RuntimeRequest family}
    {step : ExecutedStep family state request}
    {initial : PersistedGodelOccurrences execution state.journal.absoluteDepth} :
    StepPersistence execution family request step initial ->
      PersistedGodelOccurrences execution step.next.journal.absoluteDepth
  | .source _ _ persistence _ terminalJournalExact => by
      rw [terminalJournalExact]
      exact persistence.memory.persisted
  | .limit _ _ _ _ persistence _ terminalJournalExact => by
      rw [terminalJournalExact]
      exact persistence.memory.persisted

end StepPersistence

/-- Build persistence from the exact resource retained by one runtime step. -/
def persistThroughStepFrom
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1)
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request)
    (initial : PersistedGodelOccurrences execution state.journal.absoluteDepth) :
    StepPersistence execution family request step initial := by
  cases request with
  | source precision sourceAt =>
      let persistence := persistThroughRequestFrom execution
        step.response.sourceProduction.execution initial
      have terminalJournalExact :
          step.next.journal =
            step.response.sourceProduction.execution.completedJournal := by
        exact step.next_journal.trans step.response.source_completedJournal
      exact .source step initial persistence rfl terminalJournalExact
  | limit precision =>
      let production := step.response.limitProduction
      let sourcePersistence := persistThroughRequestFrom execution
        production.source.execution initial
      let groupingPersistence := persistThroughRequestFrom execution
        production.execution sourcePersistence.memory.persisted
      have terminalJournalExact :
          step.next.journal =
            step.response.limitProduction.execution.completedJournal := by
        exact step.next_journal.trans step.response.limit_completedJournal
      exact .limit step initial sourcePersistence rfl groupingPersistence rfl
        terminalJournalExact

/-- Persistence mirrors an exact runtime trace and shares each terminal output. -/
inductive RunPersistence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    {state : Runtime family} ->
    {requests : List (RuntimeRequest family)} ->
    {finalState : Runtime family} ->
    (trace : RunTrace family state requests finalState) ->
    PersistedGodelOccurrences execution state.journal.absoluteDepth -> Type _
  | done
      (state : Runtime family)
      (initial : PersistedGodelOccurrences execution state.journal.absoluteDepth) :
      RunPersistence execution family (.done state) initial
  | step
      {state finalState : Runtime family}
      {request : RuntimeRequest family}
      {remaining : List (RuntimeRequest family)}
      (executed : ExecutedStep family state request)
      (later : RunTrace family executed.next remaining finalState)
      (initial : PersistedGodelOccurrences execution state.journal.absoluteDepth)
      (current : StepPersistence execution family request executed initial)
      (following : RunPersistence execution family later current.terminal) :
      RunPersistence execution family (.step executed later) initial

namespace RunPersistence

def terminal
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation}
    {family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1}
    {state finalState : Runtime family}
    {requests : List (RuntimeRequest family)}
    {trace : RunTrace family state requests finalState}
    {initial : PersistedGodelOccurrences execution state.journal.absoluteDepth} :
    RunPersistence execution family trace initial ->
      PersistedGodelOccurrences execution finalState.journal.absoluteDepth
  | .done _ initial => initial
  | .step _ _ _ _ following => following.terminal

end RunPersistence

/-- Build persistence by consuming the already retained trace, never by replay. -/
def persistThroughRunFrom
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (family : ExecutedCauchyFamily
      (godelPerimetralPresentation execution) 1) :
    {state : Runtime family} ->
    {requests : List (RuntimeRequest family)} ->
    {finalState : Runtime family} ->
    (trace : RunTrace family state requests finalState) ->
    (initial : PersistedGodelOccurrences execution state.journal.absoluteDepth) ->
      RunPersistence execution family trace initial
  | _, [], _, .done state, initial => .done state initial
  | _, _ :: _, _, .step executed later, initial =>
      let current := persistThroughStepFrom execution family executed initial
      .step executed later initial current
        (persistThroughRunFrom execution family later current.terminal)

end StrongPerimetralTurning.GodelRuntimePersistence

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.journalExtension
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.persistedAt
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.PhasePersistence
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.persistThroughPhase
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.RequestPersistence
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.persistThroughRequestFrom
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.StepPersistence
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.StepPersistence.terminal
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.persistThroughStepFrom
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.RunPersistence
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.RunPersistence.terminal
#print axioms StrongPerimetralTurning.GodelRuntimePersistence.persistThroughRunFrom
/- AXIOM_AUDIT_END -/
