import RelationalPerimeter.Relativity.Production.RecurringPresentation

/-!
# A local exchange found from the actual used ports

The recognizer returns an old-port instruction or a positively used fresh
port. Its scope is exactly this exchange grammar, not every possible semantic
grouping. The action rearranges stored positive determinations; it does not
execute either producer again. Events, receptions and source occurrences are
transported, not equated. The physical contract and geometry remain open.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure OldInstruction {context : List Kind} {added kind : Kind}
    (instruction : Instruction (added :: context) kind) where
  original : Instruction context kind
  exactInstruction : instruction = original.rename Ref.prior

/-- Inspect the actual input references, not their readings or a future tail. -/
def findOldInstruction {context : List Kind} {added kind : Kind}
    (instruction : Instruction (added :: context) kind) :
    PSum (OldInstruction instruction) (InputPort instruction (Ref.here : Ref (added :: context) added)) := by
  cases instruction with
  | emit reading payload =>
    cases reading with
    | here => exact .inr (.emissionReading _ _)
    | prior reading =>
      cases payload with
      | here => exact .inr (.emissionPayload _ _)
      | prior payload => exact .inl ⟨.emit reading payload, rfl⟩
  | relay signal calibration =>
    cases signal with
    | here => exact .inr (.relaySignal _ _)
    | prior signal =>
      cases calibration with
      | here => exact .inr (.relayCalibration _ _)
      | prior calibration => exact .inl ⟨.relay signal calibration, rfl⟩
  | receive signal =>
    cases signal with
    | here => exact .inr (.receptionSignal _)
    | prior signal => exact .inl ⟨.receive signal, rfl⟩

theorem old_instruction_excludes_fresh {context : List Kind} {added kind}
    {instruction : Instruction (added :: context) kind} (old : OldInstruction instruction)
    (fresh : InputPort instruction (Ref.here : Ref (added :: context) added)) : False := by
  rw [old.exactInstruction] at fresh
  exact fresh.prior_not_fresh old.original

/-- Change only the presentation of a stored role; keep its actual output. -/
def Produces.weaken {context : List Kind} {kind added}
    {values : Values Value context} {instruction : Instruction context kind} {output : Value kind}
    (role : Produces values instruction output) (newOutput : Value added) :
    Produces (context := added :: context) (newOutput, values) (instruction.rename Ref.prior) output := by
  cases role with
  | emitted reading payload => exact .emitted (.prior reading) (.prior payload)
  | relayed signal calibration => exact .relayed (.prior signal) (.prior calibration)
  | received signal => exact .received (.prior signal)

def Produces.returnOld {context : List Kind} {kind added}
    {values : Values Value context} {newOutput : Value added} (instruction : Instruction context kind)
    {output : Value kind}
    (role : Produces (context := added :: context) (newOutput, values) (instruction.rename Ref.prior) output) :
    Produces values instruction output := by
  cases instruction with
  | emit reading payload => cases role; exact .emitted reading payload
  | relay signal calibration => cases role; exact .relayed signal calibration
  | receive signal => cases role; exact .received signal

/-- Read the instruction from the recorded constitutive role itself. -/
def Produces.recordedInstruction {context : List Kind} {kind}
    {values : Values Value context} {instruction : Instruction context kind} {output : Value kind}
    (role : Produces values instruction output) : Instruction context kind := by
  cases role with
  | emitted reading payload => exact .emit reading payload
  | relayed signal calibration => exact .relay signal calibration
  | received signal => exact .receive signal

theorem Produces.recordedInstruction_exact {context : List Kind} {kind}
    {values : Values Value context} {instruction : Instruction context kind} {output : Value kind}
    (role : Produces values instruction output) : role.recordedInstruction = instruction := by
  cases role <;> rfl

/-- The second instruction may really depend on the first fresh output.
Independence is therefore searched, not a premise of this stored prefix. -/
structure StoredPairProduction (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind)
    (second : Instruction (firstKind :: source.kinds) secondKind) where
  firstDetermination : Determination source first
  secondDetermination : Determination (source.extend firstDetermination) second

def produceStoredPair (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind)
    (second : Instruction (firstKind :: source.kinds) secondKind) : StoredPairProduction source first second :=
  let firstDetermination := execute source.values first
  let secondDetermination := execute (source.extend firstDetermination).values second
  ⟨firstDetermination, secondDetermination⟩

def StoredPairProduction.cursor {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) : Cursor :=
  (source.extend pair.firstDetermination).extend pair.secondDetermination

def StoredPairProduction.execution {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) : Execution source :=
  ⟨pair.cursor, .extend (.extend .root ⟨_, first, pair.firstDetermination, rfl⟩)
    ⟨_, second, pair.secondDetermination, rfl⟩⟩

def StoredPairProduction.freshUsedEdge {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second)
    (port : InputPort second (Ref.here : Ref (firstKind :: source.kinds) firstKind)) :
    Used pair.cursor.formation ⟨firstKind, .prior .here⟩ ⟨secondKind, .here⟩ :=
  .produced (source.extend pair.firstDetermination).formation pair.secondDetermination.2 .here port

theorem stored_pair_runner_exact (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind)
    (second : Instruction (firstKind :: source.kinds) secondKind) :
    (produceStoredPair source first second).execution = run source (.step first (.step second .done)) := rfl

def IndependentPairProduction.exchangeStored {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (pair : IndependentPairProduction source first second) : IndependentPairProduction source second first :=
  let secondRole := pair.secondDetermination.2.returnOld second
  let firstRole := pair.firstDetermination.2.weaken pair.secondDetermination.1
  ⟨⟨pair.secondDetermination.1, secondRole⟩, ⟨pair.firstDetermination.1, firstRole⟩⟩

theorem exchanged_outputs_are_cached {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (pair : IndependentPairProduction source first second) :
    pair.exchangeStored.firstDetermination.1 = pair.secondDetermination.1 ∧
      pair.exchangeStored.secondDetermination.1 = pair.firstDetermination.1 := ⟨rfl, rfl⟩

structure DiscoveredStoredExchange {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) where
  old : OldInstruction second
  exchanged : Execution source
  raccord : AddressedRecurringRaccord (.fromCursor pair.cursor) (.fromCursor exchanged.cursor)

def realizeStoredExchange {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) (old : OldInstruction second) : DiscoveredStoredExchange pair := by
  cases old with
  | mk original exactInstruction =>
    cases exactInstruction
    let actual : IndependentPairProduction source first original := ⟨pair.firstDetermination, pair.secondDetermination⟩
    let exchanged := actual.exchangeStored
    exact ⟨⟨original, rfl⟩, exchanged.execution, independentRecurringPair actual exchanged⟩

def searchStoredExchange {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) :
    PSum (DiscoveredStoredExchange pair) (InputPort second (Ref.here : Ref (firstKind :: source.kinds) firstKind)) :=
  match findOldInstruction pair.secondDetermination.2.recordedInstruction with
  | .inl old => .inl (realizeStoredExchange pair (pair.secondDetermination.2.recordedInstruction_exact ▸ old))
  | .inr fresh => .inr (pair.secondDetermination.2.recordedInstruction_exact ▸ fresh)

def exchangeFound {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) : Bool :=
  match searchStoredExchange pair with | .inl _ => true | .inr _ => false

def discoveredExchangeOfFound {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) (yes : exchangeFound pair = true) :
    DiscoveredStoredExchange pair := by
  cases chosen : searchStoredExchange pair with
  | inl found => exact found
  | inr _ => unfold exchangeFound at yes; rw [chosen] at yes; cases yes

def freshPortOfRefusedExchange {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) (no : exchangeFound pair = false) :
    InputPort second (Ref.here : Ref (firstKind :: source.kinds) firstKind) := by
  cases chosen : searchStoredExchange pair with
  | inl _ => unfold exchangeFound at no; rw [chosen] at no; cases no
  | inr fresh => exact fresh

theorem exchange_refusal_excludes_old {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) (refused : exchangeFound pair = false)
    (old : OldInstruction second) : False := by
  unfold exchangeFound at refused
  cases chosen : searchStoredExchange pair with
  | inl found => rw [chosen] at refused; cases refused
  | inr fresh => exact old_instruction_excludes_fresh old fresh

theorem exchange_found_iff_old {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    (pair : StoredPairProduction source first second) : exchangeFound pair = true ↔ Nonempty (OldInstruction second) := by
  constructor
  · intro yes
    unfold exchangeFound at yes
    cases chosen : searchStoredExchange pair with
    | inl found => exact ⟨found.old⟩
    | inr _ => rw [chosen] at yes; cases yes
  · intro ⟨old⟩
    cases chosen : searchStoredExchange pair with
    | inl _ => unfold exchangeFound; rw [chosen]
    | inr fresh => exact False.elim (old_instruction_excludes_fresh old fresh)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.findOldInstruction
#print axioms RelationalPerimeter.Relativity.Production.old_instruction_excludes_fresh
#print axioms RelationalPerimeter.Relativity.Production.Produces.weaken
#print axioms RelationalPerimeter.Relativity.Production.Produces.returnOld
#print axioms RelationalPerimeter.Relativity.Production.Produces.recordedInstruction
#print axioms RelationalPerimeter.Relativity.Production.Produces.recordedInstruction_exact
#print axioms RelationalPerimeter.Relativity.Production.produceStoredPair
#print axioms RelationalPerimeter.Relativity.Production.StoredPairProduction.cursor
#print axioms RelationalPerimeter.Relativity.Production.StoredPairProduction.execution
#print axioms RelationalPerimeter.Relativity.Production.StoredPairProduction.freshUsedEdge
#print axioms RelationalPerimeter.Relativity.Production.stored_pair_runner_exact
#print axioms RelationalPerimeter.Relativity.Production.IndependentPairProduction.exchangeStored
#print axioms RelationalPerimeter.Relativity.Production.exchanged_outputs_are_cached
#print axioms RelationalPerimeter.Relativity.Production.realizeStoredExchange
#print axioms RelationalPerimeter.Relativity.Production.searchStoredExchange
#print axioms RelationalPerimeter.Relativity.Production.exchangeFound
#print axioms RelationalPerimeter.Relativity.Production.discoveredExchangeOfFound
#print axioms RelationalPerimeter.Relativity.Production.freshPortOfRefusedExchange
#print axioms RelationalPerimeter.Relativity.Production.exchange_refusal_excludes_old
#print axioms RelationalPerimeter.Relativity.Production.exchange_found_iff_old
/- AXIOM_AUDIT_END -/
