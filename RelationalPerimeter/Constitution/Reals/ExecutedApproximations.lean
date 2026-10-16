import RelationalPerimeter.Constitution.Godel.GroupingTower
import RelationalPerimeter.Constitution.Reals.Precision

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Executed approximation resources

Approximation requests are not identified with natural depths.  A request
carries its own term and precision indices, while its execution appends the
six fine constitutive operations to a journal.  The dyadic code is read only
after the memory phase and the recorded output occurrence is the actual fresh
occurrence of that phase.
-/

namespace RelationalPerimeter.Constitution.Reals

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower

/-- Public requests distinguish source-family data from limit production. -/
inductive ApproximationRequest : Type
  | source (term precision : Nat)
  | limit (precision : Nat)

/-- The one code carried unchanged through all phases of an admitted request. -/
structure ApproximationPayload where
  request : ApproximationRequest
  code : SignedDyadicCode

def sourcePayload
    (term precision : Nat)
    (code : SignedDyadicCode) : ApproximationPayload :=
  { request := .source term precision, code := code }

def limitPayload
    (precision : Nat)
    (code : SignedDyadicCode) : ApproximationPayload :=
  { request := .limit precision, code := code }

namespace ExecutedApproximation

/-- Journal after context reception. -/
def afterReception
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    OperationJournal ApproximationPayload :=
  .snoc journal (fineOperation payload .receivedContext)

/-- The context occurrence at which this request first enters the journal. -/
def receivedOccurrence
    (P : CircularPresentation)
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    History.Occurrence
      (OperationJournal.history P (afterReception journal payload)).history :=
  OperationJournal.freshOccurrence P journal
    (fineOperation payload .receivedContext)

/-- Journal after the executed search. -/
def afterSearch
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    OperationJournal ApproximationPayload :=
  .snoc (afterReception journal payload)
    (fineOperation payload .executedSearch)

/-- Journal after the relational action. -/
def afterAction
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    OperationJournal ApproximationPayload :=
  .snoc (afterSearch journal payload)
    (fineOperation payload .relationalAction)

/-- Journal after authorization and decomposition. -/
def afterAuthorization
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    OperationJournal ApproximationPayload :=
  .snoc (afterAction journal payload)
    (fineOperation payload .authorizationDecomposition)

/-- Journal after effective continuation and immediately before memory. -/
def beforeMemory
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    OperationJournal ApproximationPayload :=
  .snoc (afterAuthorization journal payload)
    (fineOperation payload .effectiveContinuation)

/-- Journal completed by the memory update under contract. -/
def completedJournal
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    OperationJournal ApproximationPayload :=
  .snoc (beforeMemory journal payload)
    (fineOperation payload .contractMemory)

theorem completedJournal_is_appendSchedule
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    completedJournal journal payload =
      OperationJournal.appendOperations journal (schedule payload) :=
  rfl

theorem completedJournal_depth
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    (completedJournal journal payload).depth = journal.depth + 6 := by
  rw [completedJournal_is_appendSchedule]
  exact OperationJournal.appendSchedule_depth journal payload

/-- The output occurrence is exactly the occurrence constituted by memory. -/
def outputOccurrence
    (P : CircularPresentation)
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    History.Occurrence
      (OperationJournal.history P (completedJournal journal payload)).history :=
  OperationJournal.freshOccurrence P (beforeMemory journal payload)
    (fineOperation payload .contractMemory)

end ExecutedApproximation

/--
One executed approximation resource.  Its only execution evidence is the
actual six-phase schedule; the occurrence and readout below are projections of
this same package.
-/
structure ExecutedApproximation
    (P : CircularPresentation)
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) where
  execution : ExecutedSchedule P journal (schedule payload)

/-- Execute a request by the canonical shared schedule. -/
def executeApproximation
    (P : CircularPresentation)
    (journal : OperationJournal ApproximationPayload)
    (payload : ApproximationPayload) :
    ExecutedApproximation P journal payload :=
  { execution := executeRequest P journal payload }

namespace ExecutedApproximation

/--
The provenance exposed by one execution.  The request (and hence its source
index when it is a source request), the received occurrence, the produced
memory occurrence and the constitutive trace are projections of the same
executed package.
-/
structure Provenance
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) where
  request : ApproximationRequest
  receivedAt :
    History.Occurrence
      (OperationJournal.history P (afterReception journal payload)).history
  producedAt :
    History.Occurrence
      (OperationJournal.history P (completedJournal journal payload)).history
  constitutiveTrace : ExecutedSchedule P journal (schedule payload)

/-- Exact provenance of an executed approximation, without re-execution. -/
def provenance
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) :
    Provenance executed :=
  { request := payload.request
    receivedAt := receivedOccurrence P journal payload
    producedAt := outputOccurrence P journal payload
    constitutiveTrace := executed.execution }

theorem provenance_request_exact
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) :
    executed.provenance.request = payload.request :=
  rfl

theorem provenance_trace_is_execution
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) :
    executed.provenance.constitutiveTrace = executed.execution :=
  rfl

/-- The exact occurrence produced by the executed package. -/
def producedAt
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) :
    History.Occurrence
      (OperationJournal.history P (completedJournal journal payload)).history :=
  outputOccurrence P journal payload

/-- Readout happens after execution and returns the code carried by that package. -/
def readout
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) : SignedDyadicCode :=
  payload.code

theorem readout_exact
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) :
    executed.readout = payload.code :=
  rfl

theorem producedAt_is_memoryOccurrence
    {P : CircularPresentation}
    {journal : OperationJournal ApproximationPayload}
    {payload : ApproximationPayload}
    (executed : ExecutedApproximation P journal payload) :
    executed.producedAt =
      OperationJournal.freshOccurrence P (beforeMemory journal payload)
        (fineOperation payload .contractMemory) :=
  rfl

end ExecutedApproximation

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ApproximationRequest
#print axioms RelationalPerimeter.Constitution.Reals.ApproximationPayload
#print axioms RelationalPerimeter.Constitution.Reals.sourcePayload
#print axioms RelationalPerimeter.Constitution.Reals.limitPayload
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.afterReception
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.receivedOccurrence
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.afterSearch
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.afterAction
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.afterAuthorization
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.beforeMemory
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.completedJournal_is_appendSchedule
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.completedJournal_depth
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.outputOccurrence
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation
#print axioms RelationalPerimeter.Constitution.Reals.executeApproximation
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.Provenance
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.provenance
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.provenance_request_exact
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.provenance_trace_is_execution
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.producedAt
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.readout
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.readout_exact
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedApproximation.producedAt_is_memoryOccurrence
/- AXIOM_AUDIT_END -/
