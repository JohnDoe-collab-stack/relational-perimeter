import RelationalPerimeter.Agents.ContinuationSignatures.RoleComposition
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution

/-! The signature operation is executed between the current head production
and the recursive tail. The erased executor is the existing resource executor.
The scientific core is not reduced memory; only the readings are projected. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.ContinuationSignatures
open SAT EndogenousDecomposition

inductive PayloadMode where
  | left | pairedRight | variedLeft
  deriving DecidableEq

def selectSource {state : CausalConstitutiveState} {run : CausalConstitutiveStageExecution state}
    (role : RelationalConstitutiveRoleStage run) : PayloadMode → AcceptedRoleSource role
  | .left => leftSource role
  | .pairedRight => pairedRightSource role
  | .variedLeft => variedLeftSource role

def cursorRole (cursor : MasterResources.Cursor) :=
  relationalConstitutiveRoleStage (causalStageOfThreadedStage cursor.head.run)

def cursorSignature (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    List (Outcome (ULift Unit) Bool) :=
  let run := causalStageOfThreadedStage cursor.head.run
  let role := relationalConstitutiveRoleStage run
  produceRoleSignature role (freeVariable run) (selectSource role mode)

def historySourcesByMode :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → PayloadMode → AcceptedRoleHistory roles
  | _, _, _, .nil, _ => ()
  | _, _, _, .step head rest, mode => (selectSource head mode, historySourcesByMode rest mode)

structure SignatureExecutionResult (count : Nat) (cursor : MasterResources.Cursor) : Type 3 where
  core : CausalOperationalExecutionHistory (_count := count) cursor.state cursor.context × MasterResources.Cursor
  readings : List Bool

def executeSigned : (count : Nat) → (cursor : MasterResources.Cursor) →
    PayloadMode → SignatureExecutionResult count cursor
  | 0, cursor, _ => ⟨(.nil cursor.state cursor.context, cursor), []⟩
  | count + 1, cursor, mode =>
      let resources := cursor.headResources
      let produced := (resources.1.read .here).down
      let run := causalStageOfThreadedStage produced.run
      let role := relationalConstitutiveRoleStage run
      let signature := produceRoleSignature role (freeVariable run) (selectSource role mode)
      let next := (MasterResources.continueWithReferences resources.1 .here
        (.prior (.prior (.prior (.prior cursor.fresh))))).1
      let rest := executeSigned count next mode
      ⟨(.step produced.stage produced.run produced.production rest.core.1, rest.core.2),
        signatureRead signature :: rest.readings⟩

theorem executeSigned_erases (count : Nat) (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    (executeSigned count cursor mode).core = MasterResources.execute count cursor := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
      rw [MasterResources.execute_succ]
      let resources := cursor.headResources
      let produced := (resources.1.read .here).down
      let next := (MasterResources.continueWithReferences resources.1 .here
        (.prior (.prior (.prior (.prior cursor.fresh))))).1
      exact congrArg (fun result =>
        (CausalOperationalExecutionHistory.step produced.stage produced.run
          produced.production result.1, result.2)) (ih next)

theorem executeSigned_readings_length (count : Nat) (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    (executeSigned count cursor mode).readings.length = count := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ (ih _)

/-- The entire head signature, not only its width, is independent of the horizon. -/
theorem executeSigned_head_exact (count : Nat) (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    (executeSigned (count + 1) cursor mode).readings.head? =
      some (signatureRead (cursorSignature cursor mode)) := rfl

theorem executeSigned_head_horizon_independent (first second : Nat)
    (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    (executeSigned (first + 1) cursor mode).readings.head? =
      (executeSigned (second + 1) cursor mode).readings.head? := rfl

theorem executeSigned_pair_readings (count : Nat) (cursor : MasterResources.Cursor) :
    (executeSigned count cursor .left).readings = (executeSigned count cursor .pairedRight).readings := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons _) (ih _)

theorem executeSigned_readings_from_history (count : Nat) (cursor : MasterResources.Cursor)
    (mode : PayloadMode) :
    (executeSigned count cursor mode).readings =
      let roles := (executeSigned count cursor mode).core.1.stagewiseDecomposition.roles
      produceHistoryReadings roles (freeReadResources roles) (historySourcesByMode roles mode) := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons _) (ih _)

theorem executeSigned_varied_head (count : Nat) (cursor : MasterResources.Cursor) :
    (executeSigned (count + 1) cursor .variedLeft).readings.head? ≠
      (executeSigned (count + 1) cursor .left).readings.head? := by
  intro same
  have equalRead := Option.some.inj same
  exact varied_source_separated (cursorRole cursor) equalRead

/-- Data-only consumer. It returns no role history, support, source payload,
or cursor. The rich executor remains the specification witness. -/
def executeReadings : Nat → MasterResources.Cursor → PayloadMode → List Bool
  | 0, _, _ => []
  | count + 1, cursor, mode =>
      let resources := cursor.headResources
      let produced := (resources.1.read .here).down
      let run := causalStageOfThreadedStage produced.run
      let role := relationalConstitutiveRoleStage run
      let signature := produceRoleSignature role (freeVariable run) (selectSource role mode)
      let next := (MasterResources.continueWithReferences resources.1 .here
        (.prior (.prior (.prior (.prior cursor.fresh))))).1
      signatureRead signature :: executeReadings count next mode

theorem executeReadings_exact (count : Nat) (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    executeReadings count cursor mode = (executeSigned count cursor mode).readings := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons _) (ih _)

theorem executeReadings_length (count : Nat) (cursor : MasterResources.Cursor) (mode : PayloadMode) :
    (executeReadings count cursor mode).length = count :=
  (congrArg List.length (executeReadings_exact count cursor mode)).trans
    (executeSigned_readings_length count cursor mode)

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.cursorSignature
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_erases
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_readings_length
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_head_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_head_horizon_independent
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_pair_readings
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_readings_from_history
#print axioms ConstitutiveSearch.ContinuationSignatures.executeSigned_varied_head
#print axioms ConstitutiveSearch.ContinuationSignatures.executeReadings
#print axioms ConstitutiveSearch.ContinuationSignatures.executeReadings_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.executeReadings_length
/- AXIOM_AUDIT_END -/
