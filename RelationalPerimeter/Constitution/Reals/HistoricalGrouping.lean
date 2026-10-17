import RelationalPerimeter.Constitution.Grouping.HistoricalExtension
import RelationalPerimeter.Constitution.Reals.LocalGrouping

set_option autoImplicit false
set_option genInjectivity false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.constructorNameAsVariable false

/-!
# Historical extensions of finite approximation groupings

A fixed local-grouping specification is the global envelope.  A finite
selection exposes only finitely many source identities from that envelope.
Appending one source preserves every old identity through an explicit
embedding and transports each old grouping step to an actual one-step trace in
the extended rules.  The target code is unchanged because both finite views
are projections of the same envelope.
-/

namespace RelationalPerimeter.Constitution.Reals
namespace HistoricalGrouping

open ConstitutiveSearch.Grouping
open LocalGrouping

universe uSource

/-- Constructive index of the sources retained in a finite selection. -/
def PrefixIndex : Nat -> Type
  | 0 => Empty
  | n + 1 => PrefixIndex n ⊕ Unit

/-- A finite view points into one fixed global source envelope. -/
structure FiniteSelection
    (envelope : Specification.{uSource})
    (size : Nat) where
  lookup : PrefixIndex size -> envelope.Source

def emptySelection
    (envelope : Specification.{uSource}) :
    FiniteSelection envelope 0 where
  lookup := fun impossible => nomatch impossible

/-- Append one source while retaining every previous finite identity. -/
def FiniteSelection.snoc
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source) :
    FiniteSelection envelope (size + 1) where
  lookup := fun index =>
    match index with
    | .inl old => selection.lookup old
    | .inr _ => fresh

/-- The grouping specification exposed by one finite selection. -/
def finiteSpecification
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) : Specification where
  Source := PrefixIndex size
  precision := envelope.precision
  sourceCode := fun index => envelope.sourceCode (selection.lookup index)
  targetCode := envelope.targetCode
  sourceNearTarget := fun index =>
    envelope.sourceNearTarget (selection.lookup index)

/-- Embed an old finite grouping state in the view with one appended source. -/
def embedState
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source) :
    LocalGrouping.State (finiteSpecification selection) ->
      LocalGrouping.State (finiteSpecification (selection.snoc fresh))
  | .source index => .source (.inl index)
  | .target => .target

/-- Every old grouping step remains an actual grouping trace after append. -/
def liftStep
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    {source target : LocalGrouping.State (finiteSpecification selection)}
    (step : LocalGrouping.Step (finiteSpecification selection) source target) :
    Trace (LocalGrouping.Step (finiteSpecification (selection.snoc fresh)))
      (embedState selection fresh source)
      (embedState selection fresh target) := by
  cases step with
  | group index =>
      change
        Trace
          (LocalGrouping.Step
            (finiteSpecification (selection.snoc fresh)))
          (LocalGrouping.State.source
            (Sum.inl index : PrefixIndex size ⊕ Unit))
          LocalGrouping.State.target
      exact Trace.one
        (LocalGrouping.Step.group
          (specification := finiteSpecification (selection.snoc fresh))
          (Sum.inl index : PrefixIndex size ⊕ Unit))

/-- Historical extension associated with appending one source. -/
def extension
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source) :
    Extension
      (LocalGrouping.rules (finiteSpecification selection))
      (LocalGrouping.rules (finiteSpecification (selection.snoc fresh))) where
  embedding := embedState selection fresh
  lift := liftStep selection fresh

/-- Transport an old proof-relevant source charge to the appended selection. -/
def liftSourceCharge
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    (identity : PrefixIndex size)
    (charge :
      LocalGrouping.SourceCharge
        (finiteSpecification selection) identity) :
    LocalGrouping.SourceCharge
      (finiteSpecification (selection.snoc fresh)) (.inl identity) :=
  { receivedCode := charge.receivedCode
    receivedCodeExact := charge.receivedCodeExact
    receivedNearTarget := charge.receivedNearTarget }

/-- Two successive appends compose as one historical extension. -/
def twoStepExtension
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (first second : envelope.Source) :
    Extension
      (LocalGrouping.rules (finiteSpecification selection))
      (LocalGrouping.rules
        (finiteSpecification ((selection.snoc first).snoc second))) :=
  (extension selection first).compose
    (extension (selection.snoc first) second)

theorem twoStepExtension_embedding
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (first second : envelope.Source)
    (state : LocalGrouping.State (finiteSpecification selection)) :
    (twoStepExtension selection first second).embedding state =
      (extension (selection.snoc first) second).embedding
        ((extension selection first).embedding state) :=
  rfl

/-- Lifting an old step preserves the exact action output. -/
theorem liftedAction_exact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    (identity : PrefixIndex size)
    (charge :
      LocalGrouping.SourceCharge
        (finiteSpecification selection) identity) :
    (LocalGrouping.acceptanceAction
      (finiteSpecification (selection.snoc fresh))).transport
        ((extension selection fresh).lift
          (LocalGrouping.Step.group
            (specification := finiteSpecification selection)
            identity)) (liftSourceCharge selection fresh identity charge) =
      (LocalGrouping.acceptanceAction
        (finiteSpecification selection)).transport
          (Trace.one
            (LocalGrouping.Step.group
              (specification := finiteSpecification selection)
              identity)) charge := by
  rfl

theorem oldSourceCode_exact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    (index : PrefixIndex size) :
    (finiteSpecification (selection.snoc fresh)).sourceCode (.inl index) =
      (finiteSpecification selection).sourceCode index :=
  rfl

theorem targetCode_exact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source) :
    (finiteSpecification (selection.snoc fresh)).targetCode =
      (finiteSpecification selection).targetCode :=
  rfl

/-- Consume the generic renormalization theorem for the actual old embedding. -/
theorem renormalized
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    (state : LocalGrouping.State (finiteSpecification selection)) :
    (LocalGrouping.rules (finiteSpecification (selection.snoc fresh))).normal
        ((extension selection fresh).embedding
          ((LocalGrouping.rules (finiteSpecification selection)).normal state)) =
      (LocalGrouping.rules (finiteSpecification (selection.snoc fresh))).normal
        ((extension selection fresh).embedding state) :=
  (extension selection fresh).renormalized state

/-! ## Finite batch grouping consumes every retained source -/

/-- Lift an older finite index list into a selection with one extra source. -/
def liftIndices {size : Nat} :
    List (PrefixIndex size) -> List (PrefixIndex (Nat.succ size))
  | [] => []
  | index :: remaining => Sum.inl index :: liftIndices remaining

theorem liftIndices_length {size : Nat}
    (indices : List (PrefixIndex size)) :
    (liftIndices indices).length = indices.length := by
  induction indices with
  | nil => rfl
  | cons index remaining inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- Append one identity after every identity already present. -/
def appendIndex {Identity : Type} :
    List Identity -> Identity -> List Identity
  | [], fresh => [fresh]
  | head :: tail, fresh => head :: appendIndex tail fresh

theorem appendIndex_length {Identity : Type}
    (indices : List Identity)
    (fresh : Identity) :
    (appendIndex indices fresh).length = Nat.succ indices.length := by
  induction indices with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

theorem appendIndex_eq_appendSingleton {Identity : Type}
    (indices : List Identity)
    (fresh : Identity) :
    appendIndex indices fresh = indices ++ [fresh] := by
  induction indices with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

theorem listAppendNil {Identity : Type}
    (indices : List Identity) : indices ++ [] = indices := by
  induction indices with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

theorem listAppendAssoc {Identity : Type}
    (first second third : List Identity) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

/--
Enumerate exactly the identities of a finite selection, oldest first.  The
fresh identity is appended after the lifted historical identities.
-/
def allIndices : (size : Nat) -> List (PrefixIndex size)
  | 0 => []
  | Nat.succ size =>
      appendIndex (liftIndices (allIndices size)) (Sum.inr Unit.unit)

theorem allIndices_length (size : Nat) :
    (allIndices size).length = size := by
  induction size with
  | zero => rfl
  | succ size inductionHypothesis =>
      calc
        (allIndices (Nat.succ size)).length =
            Nat.succ (liftIndices (allIndices size)).length :=
          appendIndex_length (liftIndices (allIndices size))
            (Sum.inr Unit.unit)
        _ = Nat.succ (allIndices size).length :=
          congrArg Nat.succ (liftIndices_length (allIndices size))
        _ = Nat.succ size := congrArg Nat.succ inductionHypothesis

/--
A nonempty chronological cursor, or the exact common target obligation.  There
is no terminal empty-list surrogate for the target.
-/
inductive BatchState (size : Nat) : Type
  | pending (head : PrefixIndex size) (tail : List (PrefixIndex size))
  | target

/-- Turn an enumerated suffix into its exact operational state. -/
def stateOfIndices {size : Nat} :
    List (PrefixIndex size) -> BatchState size
  | [] => .target
  | head :: tail => .pending head tail

/-- One batch step consumes exactly the next retained source identity. -/
inductive BatchStep
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    BatchState size -> BatchState size -> Type
  | consumeLast (head : PrefixIndex size) :
      BatchStep selection (.pending head []) .target
  | consumeMore
      (head next : PrefixIndex size)
      (tail : List (PrefixIndex size)) :
      BatchStep selection (.pending head (next :: tail)) (.pending next tail)

/-- Rank is exactly the number of source identities still to consume. -/
def batchRank
    {size : Nat} :
    BatchState size -> Nat
  | .target => 0
  | .pending _ tail => Nat.succ tail.length

def batchChoices
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (state : BatchState size) ->
      List ((target : BatchState size) ×
        BatchStep selection state target)
  | .target => []
  | .pending head [] => [⟨.target, .consumeLast head⟩]
  | .pending head (next :: tail) =>
      [⟨.pending next tail, .consumeMore head next tail⟩]

def locateBatchStep
    {envelope : Specification.{uSource}}
    {size : Nat}
    {selection : FiniteSelection envelope size}
    {source target : BatchState size}
    (step : BatchStep selection source target) :
    {entry : (next : BatchState size) ×
        BatchStep selection source next //
      entry ∈ batchChoices selection source ∧
        HEq entry
          (⟨target, step⟩ :
            (next : BatchState size) ×
              BatchStep selection source next)} := by
  cases step with
  | consumeLast _ =>
      exact ⟨⟨_, .consumeLast _⟩, List.Mem.head _, HEq.rfl⟩
  | consumeMore _ _ _ =>
      exact ⟨⟨_, .consumeMore _ _ _⟩, List.Mem.head _, HEq.rfl⟩

theorem batchStep_decreases
    {envelope : Specification.{uSource}}
    {size : Nat}
    {selection : FiniteSelection envelope size}
    {source target : BatchState size}
    (step : BatchStep selection source target) :
    batchRank (size := size) target < batchRank (size := size) source := by
  cases step with
  | consumeLast => exact Nat.zero_lt_succ _
  | consumeMore => exact Nat.lt_succ_self _

def batchDiamond
    {envelope : Specification.{uSource}}
    {size : Nat}
    {selection : FiniteSelection envelope size}
    {source left right : BatchState size}
    (first : BatchStep selection source left)
    (second : BatchStep selection source right) :
    Join (BatchStep selection) left right := by
  cases first with
  | consumeLast _ =>
      cases second
      exact ⟨_, .nil _, .nil _⟩
  | consumeMore _ _ _ =>
      cases second
      exact ⟨_, .nil _, .nil _⟩

/--
Finite rules whose rank is the number of retained source identities still to
consume.  Unlike the one-source envelope rules, this rank is not fixed at one.
-/
def batchRules
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) : Rules where
  State := BatchState size
  Step := BatchStep selection
  rank := batchRank
  choices := batchChoices selection
  locate := locateBatchStep
  decreases := batchStep_decreases
  diamond := batchDiamond

/-- Embed an old batch cursor while appending a new historical source. -/
def embedBatchState
    {size : Nat} :
    BatchState size -> BatchState (Nat.succ size)
  | .target => .target
  | .pending head tail =>
      .pending (Sum.inl head) (liftIndices tail)

/-- Every old batch consumption remains an actual consumption after append. -/
def liftBatchStep
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    {source target : BatchState size}
    (step : BatchStep selection source target) :
    Trace (BatchStep (selection.snoc fresh))
      (embedBatchState source) (embedBatchState target) := by
  cases step with
  | consumeLast head =>
      exact Trace.one
        (BatchStep.consumeLast (selection := selection.snoc fresh)
          (Sum.inl head : PrefixIndex size ⊕ Unit))
  | consumeMore head next tail =>
      exact Trace.one
        (BatchStep.consumeMore (selection := selection.snoc fresh)
          (Sum.inl head : PrefixIndex size ⊕ Unit)
          (Sum.inl next : PrefixIndex size ⊕ Unit)
          (liftIndices tail))

/-- Historical extension of the finite batch rules themselves. -/
def batchExtension
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source) :
    Extension (batchRules selection) (batchRules (selection.snoc fresh)) where
  embedding := embedBatchState
  lift := liftBatchStep selection fresh

/-- Two successive finite-batch appends compose without rebuilding a rule. -/
def twoStepBatchExtension
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (first second : envelope.Source) :
    Extension (batchRules selection)
      (batchRules ((selection.snoc first).snoc second)) :=
  (batchExtension selection first).compose
    (batchExtension (selection.snoc first) second)

theorem twoStepBatchExtension_embedding
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (first second : envelope.Source)
    (state : BatchState size) :
    (twoStepBatchExtension selection first second).embedding state =
      (batchExtension (selection.snoc first) second).embedding
        ((batchExtension selection first).embedding state) :=
  rfl

/-- The actual finite selection, in its constructive enumeration order. -/
def initialBatchState
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    BatchState size :=
  stateOfIndices (allIndices size)

theorem initialBatchState_snoc
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source) :
    initialBatchState (selection.snoc fresh) =
      stateOfIndices
        (appendIndex (liftIndices (allIndices size)) (Sum.inr Unit.unit)) :=
  rfl

/-- Consume every identity in a supplied remaining suffix. -/
def consumeTrace
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (remaining : List (PrefixIndex size)) ->
      Trace (BatchStep selection) (stateOfIndices remaining)
        (BatchState.target : BatchState size)
  | [] => .nil (BatchState.target : BatchState size)
  | head :: [] => .one (.consumeLast head)
  | head :: next :: tail =>
      .cons (.consumeMore head next tail)
        (consumeTrace selection (next :: tail))

theorem batchTrace_rank_le
    {envelope : Specification.{uSource}}
    {size : Nat}
    {selection : FiniteSelection envelope size}
    {source target : BatchState size}
    (trace : Trace (BatchStep selection) source target) :
    batchRank (size := size) target ≤ batchRank (size := size) source := by
  induction trace with
  | nil => exact Nat.le_refl _
  | cons step tail inductionHypothesis =>
      exact Nat.le_trans inductionHypothesis (Nat.le_of_lt (batchStep_decreases step))

theorem batchTarget_terminal
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (batchRules selection).Terminal (.target : BatchState size) :=
  (batchRules selection).zero_terminal .target rfl

theorem normal_initialBatchState
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (batchRules selection).normal (initialBatchState selection) = .target :=
  ((batchRules selection).normal_trace
    (consumeTrace selection (allIndices size))).trans
      ((batchRules selection).normal_terminal .target
        (batchTarget_terminal selection))

/-- A proof-relevant source charge retained after its batch consumption. -/
structure ConsumedSourceCharge
    (precision : Nat)
    (targetCode : SignedDyadicCode) where
  code : SignedDyadicCode
  nearTarget : Near precision code targetCode

/--
The batch payload owns a charge for every finite source and records exactly
the charges already consumed.  Its target output remains a separate field.
-/
structure BatchCharge
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) where
  available :
    (index : PrefixIndex size) ->
      LocalGrouping.SourceCharge (finiteSpecification selection) index
  consumed :
    List (ConsumedSourceCharge envelope.precision envelope.targetCode)
  outputCode : SignedDyadicCode
  outputCodeExact : SameValue outputCode envelope.targetCode

/-- The canonical charges follow the same constructive prefix representation as
historical transport.  This is intensional recursion, not function extensionality. -/
def initialSourceCharges
    {envelope : Specification.{uSource}} :
    {size : Nat} -> (selection : FiniteSelection envelope size) ->
      (index : PrefixIndex size) ->
        LocalGrouping.SourceCharge (finiteSpecification selection) index
  | 0, _ => fun impossible => nomatch impossible
  | _ + 1, selection => fun index =>
      match index with
      | .inl old =>
          let previous : FiniteSelection envelope _ := { lookup := fun i => selection.lookup (.inl i) }
          let charge := initialSourceCharges previous old
          { receivedCode := charge.receivedCode
            receivedCodeExact := charge.receivedCodeExact
            receivedNearTarget := charge.receivedNearTarget }
      | .inr _ =>
          LocalGrouping.sourceCharge (finiteSpecification selection) (.inr ())

def initialBatchCharge
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) : BatchCharge selection where
  available := initialSourceCharges selection
  consumed := []
  outputCode := envelope.targetCode
  outputCodeExact := SameValue.refl envelope.targetCode

/--
Lift an old batch payload to the appended selection.  Every old proof-relevant
charge is transported; only the genuinely fresh source receives a new charge.
-/
def liftBatchCharge
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    (charge : BatchCharge selection) : BatchCharge (selection.snoc fresh) where
  available := fun index =>
    match index with
    | .inl old => liftSourceCharge selection fresh old (charge.available old)
    | .inr _ =>
        LocalGrouping.sourceCharge
          (finiteSpecification (selection.snoc fresh)) (.inr Unit.unit)
  consumed := charge.consumed
  outputCode := charge.outputCode
  outputCodeExact := charge.outputCodeExact

theorem liftBatchCharge_initial
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source) :
    liftBatchCharge selection fresh (initialBatchCharge selection) =
      initialBatchCharge (selection.snoc fresh) := by
  rfl

def BatchPayload
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (_state : BatchState size) :=
  BatchCharge selection

/-- Project one retained proof-relevant charge to its consumed evidence. -/
def consumedEvidence
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (head : PrefixIndex size)
    (available :
      (index : PrefixIndex size) ->
        LocalGrouping.SourceCharge (finiteSpecification selection) index) :
    ConsumedSourceCharge envelope.precision envelope.targetCode :=
  { code := (available head).receivedCode
    nearTarget := (available head).receivedNearTarget }

/-- Append one consumed proof to the chronological evidence list. -/
def consumeOne
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (head : PrefixIndex size)
    (charge : BatchCharge selection) : BatchCharge selection where
  available := charge.available
  consumed :=
    appendIndex charge.consumed
      (consumedEvidence selection head charge.available)
  outputCode := charge.outputCode
  outputCodeExact := charge.outputCodeExact

/-- Exact chronological evidence selected by a supplied identity suffix. -/
def chargesForIndices
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (available :
      (index : PrefixIndex size) ->
        LocalGrouping.SourceCharge (finiteSpecification selection) index) :
    List (PrefixIndex size) ->
      List (ConsumedSourceCharge envelope.precision envelope.targetCode)
  | [] => []
  | head :: tail =>
      consumedEvidence selection head available ::
        chargesForIndices selection available tail

def batchAct
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    {source target : BatchState size} :
    BatchStep selection source target ->
      BatchPayload selection source -> BatchPayload selection target
  | .consumeLast head, charge => consumeOne selection head charge
  | .consumeMore head _next _tail, charge => consumeOne selection head charge

def BatchAccepted
    {envelope : Specification.{uSource}}
    {size : Nat}
    {selection : FiniteSelection envelope size}
    (_state : BatchState size)
    (charge : BatchCharge selection) : Prop :=
  Nonempty (SameValue charge.outputCode envelope.targetCode)

theorem batchAct_preserves
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    {source target : BatchState size}
    (step : BatchStep selection source target)
    (charge : BatchPayload selection source) :
    BatchAccepted source charge ->
      BatchAccepted target (batchAct selection step charge) := by
  cases step
  all_goals exact fun accepted => accepted

/-- The finite action consumes one actual retained charge at every step. -/
def batchAcceptanceAction
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    AcceptanceAction (batchRules selection) where
  Payload := BatchPayload selection
  Accept := BatchAccepted
  act := batchAct selection
  preserves := batchAct_preserves selection

theorem initialBatchAccepted
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    BatchAccepted (initialBatchState selection)
      (initialBatchCharge selection) :=
  Nonempty.intro (initialBatchCharge selection).outputCodeExact

/-- Transport a batch charge along an actual finite consumption trace. -/
def transportBatch
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    {source target : BatchState size}
    (trace : Trace (BatchStep selection) source target)
    (charge : BatchCharge selection) : BatchCharge selection :=
  Trace.act
    (D := fun _state => BatchCharge selection)
    (fun step => batchAct selection step) trace charge


/-- Replacing only the executable code keeps the canonical charge interface. -/
def initialBatchChargeFromCode
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (code : SignedDyadicCode)
    (exact : code = envelope.targetCode) : BatchCharge selection where
  available := (initialBatchCharge selection).available
  consumed := []
  outputCode := code
  outputCodeExact := by rw [exact]; exact SameValue.refl _

theorem initialBatchChargeFromCode_exact
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (code : SignedDyadicCode)
    (exact : code = envelope.targetCode) :
    initialBatchChargeFromCode selection code exact = initialBatchCharge selection := by
  cases exact
  rfl

/-- Lifting any old consumption preserves the chronological evidence list. -/
theorem liftedBatchAct_consumed_exact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (fresh : envelope.Source)
    {source target : BatchState size}
    (step : BatchStep selection source target)
    (charge : BatchCharge selection) :
    (transportBatch (selection.snoc fresh)
      ((batchExtension selection fresh).lift step)
      (liftBatchCharge selection fresh charge)).consumed =
        (batchAct selection step charge).consumed := by
  cases step <;> rfl

/-- The complete payload transport commutes with every actual lifted old trace.
Already consumed prefixes need not be executed a second time after append. -/
theorem transportBatch_extension
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source)
    {source target : BatchState size}
    (trace : Trace (BatchStep selection) source target) (charge : BatchCharge selection) :
    transportBatch (selection.snoc fresh) ((batchExtension selection fresh).trace trace)
        (liftBatchCharge selection fresh charge) =
      liftBatchCharge selection fresh (transportBatch selection trace charge) := by
  induction trace generalizing charge with
  | nil => rfl
  | cons step tail ih =>
      cases step <;> exact ih (consumeOne selection _ charge)

theorem batchAction_coherent
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (batchAcceptanceAction selection).Coherent := by
  change
    ∀ {source target : BatchState size}
      (first second : Trace (BatchStep selection) source target)
      (charge : BatchCharge selection),
      transportBatch selection first charge =
        transportBatch selection second charge
  intro source target first
  induction first with
  | nil source =>
      intro second charge
      cases second with
      | nil => rfl
      | cons secondStep secondTail =>
          exact False.elim
            (Nat.not_lt_of_ge
              (batchTrace_rank_le secondTail)
              (batchStep_decreases secondStep))
  | cons step tail inductionHypothesis =>
      intro second charge
      cases second with
      | nil =>
          exact False.elim
            (Nat.not_lt_of_ge
              (batchTrace_rank_le tail)
              (batchStep_decreases step))
      | cons secondStep secondTail =>
          cases step <;> cases secondStep
          all_goals exact inductionHypothesis secondTail _


/-- Normalize one retained source charge with the actual local rules. -/
def normalizeSourceTrace
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (index : PrefixIndex size) :
    Trace (LocalGrouping.Step (finiteSpecification selection)) (.source index) .target := by
  rw [← LocalGrouping.normal_source (finiteSpecification selection) index]
  exact ((LocalGrouping.rules (finiteSpecification selection)).normalize (.source index)).trace

def normalizeSourceCharge
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (index : PrefixIndex size)
    (charge : LocalGrouping.SourceCharge (finiteSpecification selection) index) :
    LocalGrouping.GroupedCharge envelope.precision envelope.targetCode :=
  (LocalGrouping.acceptanceAction (finiteSpecification selection)).transport
    (normalizeSourceTrace selection index) charge

theorem normalizeSourceCharge_exact
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (index : PrefixIndex size)
    (charge : LocalGrouping.SourceCharge (finiteSpecification selection) index) :
    normalizeSourceCharge selection index charge =
      (LocalGrouping.acceptanceAction (finiteSpecification selection)).transport
        (Trace.one (LocalGrouping.Step.group (specification := finiteSpecification selection) index)) charge :=
  LocalGrouping.action_coherent (finiteSpecification selection)
    (normalizeSourceTrace selection index)
    (Trace.one (LocalGrouping.Step.group (specification := finiteSpecification selection) index)) charge

theorem normalizeSourceCharge_consumedNear
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (index : PrefixIndex size)
    (charge : LocalGrouping.SourceCharge (finiteSpecification selection) index) :
    HEq (normalizeSourceCharge selection index charge).consumedNearTarget charge.receivedNearTarget := by
  rw [normalizeSourceCharge_exact]
  rfl

/-- Execute the real finite batch normalization from its enumerated sources. -/
def executeBatch
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) : BatchCharge selection :=
  transportBatch selection
    (consumeTrace selection (allIndices size))
    (initialBatchCharge selection)


/-- The raw code is transported unchanged while all source charges are consumed. -/
theorem transportBatch_outputCode
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    {source target : BatchState size}
    (trace : Trace (BatchStep selection) source target)
    (charge : BatchCharge selection) :
    (transportBatch selection trace charge).outputCode = charge.outputCode := by
  induction trace generalizing charge with
  | nil => rfl
  | cons step tail ih =>
      change (transportBatch selection tail (batchAct selection step charge)).outputCode =
        charge.outputCode
      cases step <;> exact ih _

theorem executeBatch_outputCode
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (executeBatch selection).outputCode = envelope.targetCode :=
  transportBatch_outputCode selection
    (consumeTrace selection (allIndices size)) (initialBatchCharge selection)



/-- Run the actual terminating batch rules, rather than supplying a final state. -/
def normalizationTrace
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) :
    Trace (BatchStep selection) (initialBatchState selection) .target := by
  rw [← normal_initialBatchState selection]
  exact ((batchRules selection).normalize (initialBatchState selection)).trace

def normalizedBatch
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) : BatchCharge selection :=
  transportBatch selection (normalizationTrace selection) (initialBatchCharge selection)

/-- Payload coherence connects the executed rule trace to chronological consumption. -/
theorem normalizedBatch_exact
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) :
    normalizedBatch selection = executeBatch selection :=
  batchAction_coherent selection (normalizationTrace selection)
    (consumeTrace selection (allIndices size)) (initialBatchCharge selection)

/-- Executable chronological fold underlying the rule traces. -/
def consumeIndices
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) :
    List (PrefixIndex size) -> BatchCharge selection -> BatchCharge selection
  | [], charge => charge
  | head :: tail, charge => consumeIndices selection tail (consumeOne selection head charge)

theorem transportConsumeTrace_eq
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (indices : List (PrefixIndex size))
    (charge : BatchCharge selection) :
    transportBatch selection (consumeTrace selection indices) charge =
      consumeIndices selection indices charge := by
  induction indices generalizing charge with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next tail => exact ih (consumeOne selection head charge)

theorem consumeIndices_append
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (first second : List (PrefixIndex size))
    (charge : BatchCharge selection) :
    consumeIndices selection (first ++ second) charge =
      consumeIndices selection second (consumeIndices selection first charge) := by
  induction first generalizing charge with
  | nil => rfl
  | cons head tail ih => exact ih (consumeOne selection head charge)

theorem consumeIndices_lift
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source)
    (indices : List (PrefixIndex size)) (charge : BatchCharge selection) :
    consumeIndices (selection.snoc fresh) (liftIndices indices)
        (liftBatchCharge selection fresh charge) =
      liftBatchCharge selection fresh (consumeIndices selection indices charge) := by
  induction indices generalizing charge with
  | nil => rfl
  | cons head tail ih => exact ih (consumeOne selection head charge)

/-- Normalization of precisely the fresh obligation after an already consumed
historical batch.  Its input is the transported resource, not its readout. -/
def normalizeFreshTrace
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source) :
    Trace (BatchStep (selection.snoc fresh)) (.pending (.inr ()) []) .target := by
  have target : (batchRules (selection.snoc fresh)).normal (.pending (.inr ()) []) = .target :=
    ((batchRules (selection.snoc fresh)).normal_trace
      (Trace.one (BatchStep.consumeLast (selection := selection.snoc fresh)
        (Sum.inr () : PrefixIndex size ⊕ Unit)))).trans
      ((batchRules (selection.snoc fresh)).normal_terminal .target
        (batchTarget_terminal (selection.snoc fresh)))
  rw [← target]
  exact ((batchRules (selection.snoc fresh)).normalize (.pending (.inr ()) [])).trace

def normalizeFresh
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source)
    (transported : BatchCharge (selection.snoc fresh)) : BatchCharge (selection.snoc fresh) :=
  transportBatch (selection.snoc fresh) (normalizeFreshTrace selection fresh) transported

theorem normalizeFresh_exact
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source)
    (transported : BatchCharge (selection.snoc fresh)) :
    normalizeFresh selection fresh transported =
      consumeOne (selection.snoc fresh) (.inr ()) transported :=
  batchAction_coherent (selection.snoc fresh) (normalizeFreshTrace selection fresh)
    (Trace.one (BatchStep.consumeLast (selection := selection.snoc fresh)
      (Sum.inr () : PrefixIndex size ⊕ Unit))) transported

/-- An append owns both the exact transported input and its next normalization.
The result's type records its dependency on the complete previous resource. -/
structure BatchAdvance
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source)
    (previous : BatchCharge selection) where
  private mk ::
  transported : BatchCharge (selection.snoc fresh)
  transportedExact : transported = liftBatchCharge selection fresh previous
  result : BatchCharge (selection.snoc fresh)
  resultFromTransport : result = normalizeFresh selection fresh transported

def advanceBatch
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source)
    (previous : BatchCharge selection) : BatchAdvance selection fresh previous :=
  let transported := liftBatchCharge selection fresh previous
  { transported := transported, transportedExact := rfl,
    result := normalizeFresh selection fresh transported, resultFromTransport := rfl }

theorem advanceBatch_executeBatch
    {envelope : Specification.{uSource}} {size : Nat}
    (selection : FiniteSelection envelope size) (fresh : envelope.Source) :
    (advanceBatch selection fresh (executeBatch selection)).result =
      executeBatch (selection.snoc fresh) := by
  change normalizeFresh selection fresh (liftBatchCharge selection fresh (executeBatch selection)) = _
  rw [normalizeFresh_exact]
  unfold executeBatch
  rw [transportConsumeTrace_eq, transportConsumeTrace_eq]
  change _ = consumeIndices (selection.snoc fresh)
    (appendIndex (liftIndices (allIndices size)) (.inr ())) _
  erw [appendIndex_eq_appendSingleton, consumeIndices_append]
  erw [← liftBatchCharge_initial selection fresh, consumeIndices_lift]
  rfl

theorem BatchAdvance.consumed_exact
    {envelope : Specification.{uSource}} {size : Nat}
    {selection : FiniteSelection envelope size} {fresh : envelope.Source}
    {previous : BatchCharge selection} (advance : BatchAdvance selection fresh previous) :
    advance.result.consumed = appendIndex previous.consumed
      (consumedEvidence (selection.snoc fresh) (.inr ()) advance.transported.available) := by
  rw [advance.resultFromTransport, normalizeFresh_exact]
  change appendIndex advance.transported.consumed _ = _
  rw [advance.transportedExact]
  rfl

theorem BatchAdvance.oldCharge_exact
    {envelope : Specification.{uSource}} {size : Nat}
    {selection : FiniteSelection envelope size} {fresh : envelope.Source}
    {previous : BatchCharge selection} (advance : BatchAdvance selection fresh previous)
    (index : PrefixIndex size) :
    advance.result.available (.inl index) =
      liftSourceCharge selection fresh index (previous.available index) := by
  rw [advance.resultFromTransport, normalizeFresh_exact]
  change advance.transported.available (.inl index) = _
  rw [advance.transportedExact]
  rfl


theorem executeBatchAccepted
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    BatchAccepted (.target : BatchState size) (executeBatch selection) :=
  (batchAcceptanceAction selection).transport_preserves
    (consumeTrace selection (allIndices size))
    (initialBatchCharge selection)
    (initialBatchAccepted selection)

theorem consumeTrace_consumed_length
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (remaining : List (PrefixIndex size))
    (charge : BatchCharge selection) :
    (transportBatch selection
      (consumeTrace selection remaining) charge).consumed.length =
        charge.consumed.length + remaining.length := by
  induction remaining generalizing charge with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          change
            (consumeOne selection head charge).consumed.length =
              charge.consumed.length + 1
          exact appendIndex_length charge.consumed
            { code := (charge.available head).receivedCode
              nearTarget := (charge.available head).receivedNearTarget }
      | cons next tail =>
          change
            (transportBatch selection
              (consumeTrace selection (next :: tail))
              (consumeOne selection head charge)).consumed.length =
                charge.consumed.length + ((next :: tail).length + 1)
          calc
            _ = (consumeOne selection head charge).consumed.length +
                  (next :: tail).length :=
              inductionHypothesis (consumeOne selection head charge)
            _ = (charge.consumed.length + 1) +
                  (next :: tail).length := by
              exact congrArg (fun length => length + (next :: tail).length)
                (appendIndex_length charge.consumed
                  { code := (charge.available head).receivedCode
                    nearTarget := (charge.available head).receivedNearTarget })
            _ = charge.consumed.length + (1 + (next :: tail).length) :=
              Nat.add_assoc charge.consumed.length 1 (next :: tail).length
            _ = charge.consumed.length + ((next :: tail).length + 1) :=
              congrArg (Nat.add charge.consumed.length)
                (Nat.add_comm 1 (next :: tail).length)

/--
Transport records exactly the supplied suffix, in its original chronological
order, after any evidence that had already been consumed.
-/
theorem consumeTrace_consumed_exact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size)
    (remaining : List (PrefixIndex size))
    (charge : BatchCharge selection) :
    (transportBatch selection
      (consumeTrace selection remaining) charge).consumed =
        charge.consumed ++
          chargesForIndices selection charge.available remaining := by
  induction remaining generalizing charge with
  | nil =>
      exact (listAppendNil charge.consumed).symm
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          change
            (consumeOne selection head charge).consumed =
              charge.consumed ++
                [consumedEvidence selection head charge.available]
          exact appendIndex_eq_appendSingleton charge.consumed _
      | cons next tail =>
          change
            (transportBatch selection
              (consumeTrace selection (next :: tail))
              (consumeOne selection head charge)).consumed =
                charge.consumed ++
                  (consumedEvidence selection head charge.available ::
                    chargesForIndices selection charge.available
                      (next :: tail))
          calc
            _ = (consumeOne selection head charge).consumed ++
                  chargesForIndices selection
                    (consumeOne selection head charge).available
                    (next :: tail) :=
              inductionHypothesis (consumeOne selection head charge)
            _ = (charge.consumed ++
                  [consumedEvidence selection head charge.available]) ++
                  chargesForIndices selection charge.available
                    (next :: tail) := by
              exact congrArg
                (fun consumed => consumed ++
                  chargesForIndices selection charge.available
                    (next :: tail))
                (appendIndex_eq_appendSingleton charge.consumed
                  (consumedEvidence selection head charge.available))
            _ = charge.consumed ++
                  ([consumedEvidence selection head charge.available] ++
                    chargesForIndices selection charge.available
                      (next :: tail)) :=
              listAppendAssoc _ _ _
            _ = charge.consumed ++
                  (consumedEvidence selection head charge.available ::
                    chargesForIndices selection charge.available
                      (next :: tail)) :=
              rfl

/-- The batch execution consumes every and only retained finite source. -/
theorem executeBatch_consumed_length
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (executeBatch selection).consumed.length = size := by
  calc
    (executeBatch selection).consumed.length =
        (initialBatchCharge selection).consumed.length +
          (allIndices size).length :=
      consumeTrace_consumed_length selection
        (allIndices size) (initialBatchCharge selection)
    _ = (allIndices size).length := by
      change 0 + (allIndices size).length = (allIndices size).length
      exact Nat.zero_add _
    _ = size := allIndices_length size

/-- The complete batch records every selected charge in oldest-first order. -/
theorem executeBatch_consumed_exact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    (executeBatch selection).consumed =
      chargesForIndices selection (initialBatchCharge selection).available
        (allIndices size) := by
  calc
    (executeBatch selection).consumed =
        (initialBatchCharge selection).consumed ++
          chargesForIndices selection
            (initialBatchCharge selection).available (allIndices size) :=
      consumeTrace_consumed_exact selection (allIndices size)
        (initialBatchCharge selection)
    _ = chargesForIndices selection
          (initialBatchCharge selection).available (allIndices size) :=
      rfl

def executeBatch_outputExact
    {envelope : Specification.{uSource}}
    {size : Nat}
    (selection : FiniteSelection envelope size) :
    SameValue (executeBatch selection).outputCode envelope.targetCode :=
  (executeBatch selection).outputCodeExact

/--
Contract for every next finite future of one fixed envelope.  It returns the
actual rule extension and separately records code preservation.
-/
structure FutureContract
    (envelope : Specification.{uSource}) where
  extend :
    {size : Nat} ->
      (selection : FiniteSelection envelope size) ->
      (fresh : envelope.Source) ->
      Extension
        (LocalGrouping.rules (finiteSpecification selection))
        (LocalGrouping.rules (finiteSpecification (selection.snoc fresh)))
  extendBatch :
    {size : Nat} ->
      (selection : FiniteSelection envelope size) ->
      (fresh : envelope.Source) ->
      Extension (batchRules selection) (batchRules (selection.snoc fresh))
  oldSourceCodePreserved :
    {size : Nat} ->
      (selection : FiniteSelection envelope size) ->
      (fresh : envelope.Source) ->
      (index : PrefixIndex size) ->
      (finiteSpecification (selection.snoc fresh)).sourceCode (.inl index) =
        (finiteSpecification selection).sourceCode index
  targetCodePreserved :
    {size : Nat} ->
      (selection : FiniteSelection envelope size) ->
      (fresh : envelope.Source) ->
      (finiteSpecification (selection.snoc fresh)).targetCode =
        (finiteSpecification selection).targetCode

def futureContract
    (envelope : Specification.{uSource}) : FutureContract envelope where
  extend := extension
  extendBatch := batchExtension
  oldSourceCodePreserved := oldSourceCode_exact
  targetCodePreserved := targetCode_exact

end HistoricalGrouping
end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.PrefixIndex
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.FiniteSelection
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.emptySelection
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.FiniteSelection.snoc
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.finiteSpecification
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.embedState
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftStep
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.extension
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftSourceCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.twoStepExtension
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.twoStepExtension_embedding
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftedAction_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.oldSourceCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.targetCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.renormalized
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftIndices
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftIndices_length
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.appendIndex
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.appendIndex_length
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.appendIndex_eq_appendSingleton
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.listAppendNil
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.listAppendAssoc
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.allIndices
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.allIndices_length
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchState
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.stateOfIndices
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchStep
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.batchRules
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.embedBatchState
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftBatchStep
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.batchExtension
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.twoStepBatchExtension
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.twoStepBatchExtension_embedding
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.initialBatchState_snoc
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeTrace
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.batchTrace_rank_le
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normal_initialBatchState
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.ConsumedSourceCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.initialBatchCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftBatchCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumedEvidence
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeOne
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.chargesForIndices
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftedBatchAct_consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.batchAcceptanceAction
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.initialBatchAccepted
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.transportBatch
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.batchAction_coherent
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.executeBatch
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.executeBatchAccepted
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.executeBatch_consumed_length
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeTrace_consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.executeBatch_consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.executeBatch_outputExact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.FutureContract
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.futureContract
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.transportBatch_outputCode
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.executeBatch_outputCode
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.appendIndex
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.appendIndex_length
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.appendIndex_eq_appendSingleton
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.listAppendNil
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.listAppendAssoc
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeOne
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftSourceCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftBatchCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftedBatchAct_consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumedEvidence
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.chargesForIndices
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeTrace_consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizationTrace
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizedBatch
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizedBatch_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.initialBatchChargeFromCode
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.initialBatchChargeFromCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeSourceCharge
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeSourceCharge_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeSourceCharge_consumedNear
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeSourceTrace
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.initialSourceCharges
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.liftBatchCharge_initial
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeIndices
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.transportConsumeTrace_eq
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeIndices_append
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.consumeIndices_lift
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeFreshTrace
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeFresh
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.normalizeFresh_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchAdvance
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.advanceBatch
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.advanceBatch_executeBatch
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchAdvance.consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchAdvance.oldCharge_exact
#print axioms RelationalPerimeter.Constitution.Reals.HistoricalGrouping.transportBatch_extension
/- AXIOM_AUDIT_END -/
