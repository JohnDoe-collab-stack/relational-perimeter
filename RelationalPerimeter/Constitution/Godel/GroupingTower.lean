import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence
import RelationalPerimeter.Constitution.PerimeterPersistence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Shared constitutive tower for Gödel and grouping

This module supplies the historical spine used by the later grouping and
relational-real construction.  A public request is decomposed into six fine
operations, in the constitutive order fixed by the repository.  Every fine
operation appends one actual step of the existing free generator, so a journal
at depth `n` is backed by the already established history `iteratedHistory P n`.

No numerical readout and no grouping quotient is introduced here.  In
particular, the operation payload labels a freshly constituted occurrence; it
does not replace that occurrence.  Earlier occurrences are transported through
the common finite index, which preserves their identity and distinctions.
-/

namespace StrongPerimetralTurning
namespace GodelGroupingTower

open ConstitutiveSearch.OccurrencePersistence
open ConstitutiveSearch.PerimeterPersistence.Iterated

universe uPayload uSource uTarget

/-- The six constitutive phases consumed by one admitted public request. -/
inductive ConstitutivePhase : Type
  | receivedContext
  | executedSearch
  | relationalAction
  | authorizationDecomposition
  | effectiveContinuation
  | contractMemory

/-- One fine operation retains both its phase and the shared request payload. -/
structure FineOperation (Payload : Type uPayload) where
  phase : ConstitutivePhase
  payload : Payload

/-- Build the fine operation for one phase without reconstructing its payload. -/
def fineOperation
    {Payload : Type uPayload}
    (payload : Payload)
    (phase : ConstitutivePhase) : FineOperation Payload :=
  { phase := phase, payload := payload }

/-- The fixed constitutive phase order for one request. -/
def phaseSchedule : List ConstitutivePhase :=
  [ .receivedContext,
    .executedSearch,
    .relationalAction,
    .authorizationDecomposition,
    .effectiveContinuation,
    .contractMemory ]

/-- Every phase in a request schedule receives the very same payload value. -/
def schedule
    {Payload : Type uPayload}
    (payload : Payload) : List (FineOperation Payload) :=
  [ fineOperation payload .receivedContext,
    fineOperation payload .executedSearch,
    fineOperation payload .relationalAction,
    fineOperation payload .authorizationDecomposition,
    fineOperation payload .effectiveContinuation,
    fineOperation payload .contractMemory ]

theorem schedule_length
    {Payload : Type uPayload}
    (payload : Payload) : (schedule payload).length = 6 :=
  rfl

theorem schedule_nonempty
    {Payload : Type uPayload}
    (payload : Payload) : schedule payload ≠ [] := by
  intro equality
  cases equality

/--
A journal is a proof-relevant chronological snoc chain.  Its depth therefore
counts fine operations, independently of any precision carried by a payload.
-/
inductive OperationJournal (Payload : Type uPayload) : Type uPayload
  | root
  | snoc (prior : OperationJournal Payload) (operation : FineOperation Payload)

namespace OperationJournal

/-- Number of operations actually appended to a journal. -/
def depth
    {Payload : Type uPayload} : OperationJournal Payload -> Nat
  | .root => 0
  | .snoc prior _ => prior.depth + 1

/-- Chronological list projection of a proof-relevant journal. -/
def operations
    {Payload : Type uPayload} :
    OperationJournal Payload -> List (FineOperation Payload)
  | .root => []
  | .snoc prior operation => prior.operations ++ [operation]

/-- Constructive length law for chronological snoc, proved locally. -/
theorem listLengthSnoc
    {Element : Type uPayload}
    (prior : List Element)
    (last : Element) :
    (prior ++ [last]).length = prior.length + 1 := by
  induction prior with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

theorem operations_length
    {Payload : Type uPayload}
    (journal : OperationJournal Payload) :
    journal.operations.length = journal.depth := by
  induction journal with
  | root => rfl
  | snoc prior operation inductionHypothesis =>
      change (prior.operations ++ [operation]).length = prior.depth + 1
      calc
        (prior.operations ++ [operation]).length =
            prior.operations.length + 1 :=
          listLengthSnoc prior.operations operation
        _ = prior.depth + 1 :=
          congrArg (fun value => value + 1) inductionHypothesis

/-- The one shared generated history underlying this exact operation journal. -/
def history
    {Payload : Type uPayload}
    (P : CircularPresentation)
    (journal : OperationJournal Payload) : RootedGeneratedHistory P :=
  iteratedHistory P journal.depth

/-- Append a chronological list of fine operations. -/
def appendOperations
    {Payload : Type uPayload} :
    OperationJournal Payload ->
      List (FineOperation Payload) -> OperationJournal Payload
  | journal, [] => journal
  | journal, operation :: remaining =>
      appendOperations (.snoc journal operation) remaining

theorem appendOperations_depth
    {Payload : Type uPayload}
    (journal : OperationJournal Payload)
    (operations : List (FineOperation Payload)) :
    (appendOperations journal operations).depth =
      journal.depth + operations.length := by
  induction operations generalizing journal with
  | nil =>
      rfl
  | cons operation remaining inductionHypothesis =>
      change
        (appendOperations
          (OperationJournal.snoc journal operation) remaining).depth =
          journal.depth + (remaining.length + 1)
      calc
        (appendOperations
            (OperationJournal.snoc journal operation) remaining).depth =
            (OperationJournal.snoc journal operation).depth +
              remaining.length :=
          inductionHypothesis (OperationJournal.snoc journal operation)
        _ = (journal.depth + 1) + remaining.length := rfl
        _ = journal.depth + (1 + remaining.length) :=
          Nat.add_assoc journal.depth 1 remaining.length
        _ = journal.depth + (remaining.length + 1) :=
          congrArg (Nat.add journal.depth)
            (Nat.add_comm 1 remaining.length)

/-- A full public request adds exactly six generated operations. -/
theorem appendSchedule_depth
    {Payload : Type uPayload}
    (journal : OperationJournal Payload)
    (payload : Payload) :
    (appendOperations journal (schedule payload)).depth =
      journal.depth + 6 := by
  rw [appendOperations_depth, schedule_length]

/-- Positively extend any existing depth by a supplied finite number of steps. -/
def extendDepthBy :
    (source extra : Nat) -> DepthExtension source (source + extra)
  | source, 0 => .refl source
  | source, Nat.succ extra => .step (extendDepthBy source extra)

/-- The exact six-step depth extension produced by one public request. -/
def requestDepthExtension
    {Payload : Type uPayload}
    (journal : OperationJournal Payload)
    (payload : Payload) :
    DepthExtension journal.depth
      (appendOperations journal (schedule payload)).depth := by
  rw [appendSchedule_depth]
  exact extendDepthBy journal.depth 6

/--
The occurrence produced by an appended operation is the actual last
occurrence of the corresponding successor history.
-/
def freshOccurrence
    {Payload : Type uPayload}
    (P : CircularPresentation)
    (journal : OperationJournal Payload)
    (operation : FineOperation Payload) :
    History.Occurrence (history P (.snoc journal operation)).history :=
  History.Occurrence.last

end OperationJournal

/--
Execution of a schedule records, at every step, the exact fresh occurrence of
the shared generated history.  The tail starts from the journal just produced
by the head; no output is reconstructed independently.
-/
inductive ExecutedSchedule
    {Payload : Type uPayload}
    (P : CircularPresentation) :
    (journal : OperationJournal Payload) ->
      List (FineOperation Payload) -> Type (max uPayload 1)
  | done (journal : OperationJournal Payload) : ExecutedSchedule P journal []
  | step
      {journal : OperationJournal Payload}
      {operation : FineOperation Payload}
      {remaining : List (FineOperation Payload)}
      (occurrence :
        History.Occurrence
          (OperationJournal.history P (.snoc journal operation)).history)
      (occurrenceExact :
        occurrence = OperationJournal.freshOccurrence P journal operation)
      (continuation :
        ExecutedSchedule P (.snoc journal operation) remaining) :
      ExecutedSchedule P journal (operation :: remaining)

/-- Execute any supplied list by consuming the unique fresh occurrence at each step. -/
def executeSchedule
    {Payload : Type uPayload}
    (P : CircularPresentation) :
    (journal : OperationJournal Payload) ->
      (operations : List (FineOperation Payload)) ->
      ExecutedSchedule P journal operations
  | journal, [] => .done journal
  | journal, operation :: remaining =>
      .step
        (OperationJournal.freshOccurrence P journal operation)
        rfl
        (executeSchedule P (.snoc journal operation) remaining)

/-- Execute the fixed six-phase schedule for one shared payload. -/
def executeRequest
    {Payload : Type uPayload}
    (P : CircularPresentation)
    (journal : OperationJournal Payload)
    (payload : Payload) : ExecutedSchedule P journal (schedule payload) :=
  executeSchedule P journal (schedule payload)

/-- The first operation in the canonical request execution is context reception. -/
theorem executeRequest_startsWithReceivedContext
    {Payload : Type uPayload}
    (P : CircularPresentation)
    (journal : OperationJournal Payload)
    (payload : Payload) :
    executeRequest P journal payload =
      .step
        (OperationJournal.freshOccurrence P journal
          (fineOperation payload .receivedContext))
        rfl
        (executeSchedule P
          (.snoc journal (fineOperation payload .receivedContext))
          [ fineOperation payload .executedSearch,
            fineOperation payload .relationalAction,
            fineOperation payload .authorizationDecomposition,
            fineOperation payload .effectiveContinuation,
            fineOperation payload .contractMemory ]) :=
  rfl

/-! ## Canonical extension of actual occurrences through the shared tower -/

/-- Forward maps of exact transports are injective. -/
theorem exactForwardInjective
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.forward := by
  intro first second equality
  calc
    first = transport.backward (transport.forward first) :=
      (transport.forwardBackward first).symm
    _ = transport.backward (transport.forward second) :=
      congrArg transport.backward equality
    _ = second := transport.forwardBackward second

/-- Backward maps of exact transports are injective. -/
theorem exactBackwardInjective
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.backward := by
  intro first second equality
  calc
    first = transport.forward (transport.backward first) :=
      (transport.backwardForward first).symm
    _ = transport.forward (transport.backward second) :=
      congrArg transport.forward equality
    _ = second := transport.backwardForward second

/--
Extend an actual occurrence from one generated history to a supplied later
depth through the unique shared finite index.
-/
def extendOccurrence
    (P : CircularPresentation)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence : History.Occurrence (iteratedHistory P sourceDepth).history) :
    History.Occurrence (iteratedHistory P targetDepth).history :=
  (iteratedOccurrenceSpoke P targetDepth).forward
    (IteratedCarrier.embedFrom depth
      ((iteratedOccurrenceSpoke P sourceDepth).backward occurrence))

/--
Transport an existing occurrence through the exact six-step journal extension
of one executed public request.
-/
def extendOccurrenceThroughRequest
    {Payload : Type uPayload}
    (P : CircularPresentation)
    (journal : OperationJournal Payload)
    (payload : Payload)
    (occurrence : History.Occurrence (OperationJournal.history P journal).history) :
    History.Occurrence
      (OperationJournal.history P
        (OperationJournal.appendOperations journal (schedule payload))).history :=
  extendOccurrence P (OperationJournal.requestDepthExtension journal payload)
    occurrence

theorem extendOccurrence_injective
    (P : CircularPresentation)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth) :
    Function.Injective (extendOccurrence P depth) := by
  intro first second equality
  have embeddedEquality :
      IteratedCarrier.embedFrom depth
          ((iteratedOccurrenceSpoke P sourceDepth).backward first) =
        IteratedCarrier.embedFrom depth
          ((iteratedOccurrenceSpoke P sourceDepth).backward second) :=
    by
      exact exactForwardInjective
        (iteratedOccurrenceSpoke P targetDepth) equality
  have indexedEquality :=
    IteratedCarrier.embedFrom_injective depth embeddedEquality
  exact exactBackwardInjective
    (iteratedOccurrenceSpoke P sourceDepth) indexedEquality

theorem extendOccurrence_ne
    (P : CircularPresentation)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    {first second :
      History.Occurrence (iteratedHistory P sourceDepth).history}
    (distinct : first ≠ second) :
    extendOccurrence P depth first ≠ extendOccurrence P depth second := by
  intro equality
  exact distinct (extendOccurrence_injective P depth equality)

/-- The obstruction at every finite journal endpoint is still the initial one. -/
theorem journal_terminalClosureObstruction_is_initial
    {Payload : Type uPayload}
    (P : CircularPresentation)
    (journal : OperationJournal Payload) :
    (OperationJournal.history P journal).terminalClosureObstruction =
      P.positiveClosureObstruction :=
  RootedGeneratedHistory.terminalClosureObstruction_is_initial _

/-! ## Persistence of the three distinct occurrences produced by Gödel -/

/-- The three established Gödel occurrences, transported into one later depth. -/
structure PersistedGodelOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (targetDepth : Nat) where
  production :
    History.Occurrence
      (iteratedHistory (godelPerimetralPresentation execution) targetDepth).history
  certification :
    History.Occurrence
      (iteratedHistory (godelPerimetralPresentation execution) targetDepth).history
  continuation :
    History.Occurrence
      (iteratedHistory (godelPerimetralPresentation execution) targetDepth).history
  productionCertificationDistinct : production ≠ certification
  productionContinuationDistinct : production ≠ continuation
  certificationContinuationDistinct : certification ≠ continuation

/--
Transport the already produced Gödel occurrences; the construction consumes
the affirmative constitution instead of manufacturing a second triple.
-/
def persistGodelOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    PersistedGodelOccurrences execution targetDepth := by
  let affirmative := godelAffirmativeConstitution execution
  exact
  { production := extendOccurrence
      (godelPerimetralPresentation execution) depth
      affirmative.productionOccurrence
    certification := extendOccurrence
      (godelPerimetralPresentation execution) depth
      affirmative.certificationOccurrence
    continuation := extendOccurrence
      (godelPerimetralPresentation execution) depth
      affirmative.continuationOccurrence
    productionCertificationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        affirmative.productionCertificationDistinct
    productionContinuationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        affirmative.productionContinuationDistinct
    certificationContinuationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        affirmative.certificationContinuationDistinct }

/--
Transport an already persisted Gödel triple through the exact journal
extension of one public request.  The target is indexed by that request's
actual appended journal, rather than merely by an independently chosen depth.
-/
def persistGodelOccurrencesThroughRequest
    {Payload : Type uPayload}
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (journal : OperationJournal Payload)
    (payload : Payload)
    (persisted : PersistedGodelOccurrences execution journal.depth) :
    PersistedGodelOccurrences execution
      (OperationJournal.appendOperations journal (schedule payload)).depth := by
  let depth := OperationJournal.requestDepthExtension journal payload
  exact
  { production :=
      extendOccurrenceThroughRequest
        (godelPerimetralPresentation execution) journal payload
        persisted.production
    certification :=
      extendOccurrenceThroughRequest
        (godelPerimetralPresentation execution) journal payload
        persisted.certification
    continuation :=
      extendOccurrenceThroughRequest
        (godelPerimetralPresentation execution) journal payload
        persisted.continuation
    productionCertificationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        persisted.productionCertificationDistinct
    productionContinuationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        persisted.productionContinuationDistinct
    certificationContinuationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        persisted.certificationContinuationDistinct }

end GodelGroupingTower
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelGroupingTower.ConstitutivePhase
#print axioms StrongPerimetralTurning.GodelGroupingTower.FineOperation
#print axioms StrongPerimetralTurning.GodelGroupingTower.fineOperation
#print axioms StrongPerimetralTurning.GodelGroupingTower.phaseSchedule
#print axioms StrongPerimetralTurning.GodelGroupingTower.schedule
#print axioms StrongPerimetralTurning.GodelGroupingTower.schedule_length
#print axioms StrongPerimetralTurning.GodelGroupingTower.schedule_nonempty
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.depth
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.operations
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.listLengthSnoc
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.operations_length
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.history
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.appendOperations
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.appendOperations_depth
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.appendSchedule_depth
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.extendDepthBy
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.requestDepthExtension
#print axioms StrongPerimetralTurning.GodelGroupingTower.OperationJournal.freshOccurrence
#print axioms StrongPerimetralTurning.GodelGroupingTower.ExecutedSchedule
#print axioms StrongPerimetralTurning.GodelGroupingTower.executeSchedule
#print axioms StrongPerimetralTurning.GodelGroupingTower.executeRequest
#print axioms StrongPerimetralTurning.GodelGroupingTower.executeRequest_startsWithReceivedContext
#print axioms StrongPerimetralTurning.GodelGroupingTower.exactForwardInjective
#print axioms StrongPerimetralTurning.GodelGroupingTower.exactBackwardInjective
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrence
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrenceThroughRequest
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrence_injective
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrence_ne
#print axioms StrongPerimetralTurning.GodelGroupingTower.journal_terminalClosureObstruction_is_initial
#print axioms StrongPerimetralTurning.GodelGroupingTower.PersistedGodelOccurrences
#print axioms StrongPerimetralTurning.GodelGroupingTower.persistGodelOccurrences
#print axioms StrongPerimetralTurning.GodelGroupingTower.persistGodelOccurrencesThroughRequest
/- AXIOM_AUDIT_END -/
