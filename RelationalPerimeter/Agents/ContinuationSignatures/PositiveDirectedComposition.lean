import RelationalPerimeter.Agents.ContinuationSignatures.Production
import RelationalPerimeter.Constitution.Continuation.ReadoutCorrespondence

/-! A positive non-diagonal instance of directed terminal readout transport.
The same constituted sources collide for the selected read resource while
their positions and active events remain distinct. -/
set_option autoImplicit false
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
open ConstitutiveSearch SAT EndogenousDecomposition

variable {state : CausalConstitutiveState}
  {run : CausalConstitutiveStageExecution state}

variable (role : RelationalConstitutiveRoleStage run)

def positiveDirectedSourceAccepted : AcceptedRoleSource role :=
  variedLeftSource role

def positiveDirectedTargetAccepted : AcceptedRoleSource role :=
  leftSource role

theorem positiveDirectedAcceptedSources_ne :
    positiveDirectedSourceAccepted role ≠ positiveDirectedTargetAccepted role :=
  (three_sources_distinct role).2.1

inductive PositiveDirectedSide where
  | source
  | target
  deriving DecidableEq

inductive PositiveDirectedPhase where
  | active
  | terminal
  deriving DecidableEq

inductive PositiveDirectedRequest where
  | close
  deriving DecidableEq

inductive PositiveDirectedEvent where
  | active (side : PositiveDirectedSide)
  | terminal
  deriving DecidableEq

structure PositiveDirectedSource (role : RelationalConstitutiveRoleStage run) where
  side : PositiveDirectedSide
  phase : PositiveDirectedPhase

def positiveDirectedAcceptedSource : PositiveDirectedSide → AcceptedRoleSource role
  | .source => positiveDirectedSourceAccepted role
  | .target => positiveDirectedTargetAccepted role

theorem positiveDirectedIndexedAcceptedSources_ne :
    positiveDirectedAcceptedSource role .source ≠
      positiveDirectedAcceptedSource role .target :=
  positiveDirectedAcceptedSources_ne role

abbrev positiveDirectedProducedBit (side : PositiveDirectedSide) : Bool :=
  roleRead role run.selected (positiveDirectedAcceptedSource role side)

abbrev PositiveDirectedTerminalReadout (side : PositiveDirectedSide) :=
  { observed : Bool // observed = positiveDirectedProducedBit role side }

def positiveDirectedNext :
    PositiveDirectedSource role → PositiveDirectedRequest → PositiveDirectedSource role
  | ⟨side, .active⟩, .close => ⟨side, .terminal⟩
  | source@⟨_, .terminal⟩, .close => source

def positiveDirectedEvent :
    PositiveDirectedSource role → PositiveDirectedRequest →
      ULift.{1} PositiveDirectedEvent
  | ⟨side, .active⟩, .close => ⟨.active side⟩
  | ⟨_, .terminal⟩, .close => ⟨.terminal⟩

def positiveDirectedRead : PositiveDirectedSource role → Type
  | ⟨_, .active⟩ => PUnit
  | ⟨side, .terminal⟩ => PositiveDirectedTerminalReadout role side

def PositiveDirectedAllow :
    PositiveDirectedSource role → PositiveDirectedRequest → Type
  | ⟨_, .active⟩, .close => PUnit
  | ⟨_, .terminal⟩, .close => Empty

def positiveDirectedDecision
    (source : PositiveDirectedSource role) (request : PositiveDirectedRequest) :
    PSum (PositiveDirectedAllow role source request)
      (PositiveDirectedAllow role source request → False) := by
  cases source with
  | mk side phase =>
      cases phase <;> cases request
      · exact .inl PUnit.unit
      · exact .inr (fun impossible => nomatch impossible)

def positiveDirectedContract :
    FutureContract (PositiveDirectedSource role) PositiveDirectedRequest
      (ULift.{1} PositiveDirectedEvent) (Type) where
  next := positiveDirectedNext role
  event := positiveDirectedEvent role
  read := positiveDirectedRead role
  Allow := PositiveDirectedAllow role
  decision := positiveDirectedDecision role

inductive PositiveDirectedMemory (role : RelationalConstitutiveRoleStage run) where
  | active (side : PositiveDirectedSide)
  | grouped (bit : Bool)

def positiveDirectedMemoryNext :
    PositiveDirectedMemory role → PositiveDirectedRequest → PositiveDirectedMemory role
  | .active side, .close => .grouped (positiveDirectedProducedBit role side)
  | memory@(.grouped _), .close => memory

def positiveDirectedMemoryEvent :
    PositiveDirectedMemory role → PositiveDirectedRequest →
      ULift.{1} PositiveDirectedEvent
  | .active side, .close => ⟨.active side⟩
  | .grouped _, .close => ⟨.terminal⟩

def PositiveDirectedMemoryAllow :
    PositiveDirectedMemory role → PositiveDirectedRequest → Type
  | .active _, .close => PUnit
  | .grouped _, .close => Empty

def positiveDirectedMemoryDecision
    (memory : PositiveDirectedMemory role) (request : PositiveDirectedRequest) :
    PSum (PositiveDirectedMemoryAllow role memory request)
      (PositiveDirectedMemoryAllow role memory request → False) := by
  cases memory with
  | active side => exact .inl PUnit.unit
  | grouped bit => exact .inr (fun impossible => nomatch impossible)

def positiveDirectedMemoryContract :
    OperationalContract (PositiveDirectedMemory role) PositiveDirectedRequest
      (ULift.{1} PositiveDirectedEvent) where
  next := positiveDirectedMemoryNext role
  event := positiveDirectedMemoryEvent role
  Allow := PositiveDirectedMemoryAllow role
  decision := positiveDirectedMemoryDecision role

def positiveDirectedProject :
    PositiveDirectedSource role → PositiveDirectedMemory role
  | ⟨side, .active⟩ => .active side
  | ⟨side, .terminal⟩ => .grouped (positiveDirectedProducedBit role side)

def positiveDirectedRealization :
    OperationalRealization (positiveDirectedContract role)
      (PositiveDirectedMemory role) where
  reduced := positiveDirectedMemoryContract role
  project := positiveDirectedProject role
  forward := by
    intro source request witness
    cases source with
    | mk side phase => cases phase <;> cases request <;> exact witness
  backward := by
    intro source request witness
    cases source with
    | mk side phase => cases phase <;> cases request <;> exact witness
  backward_forward := by
    intro source request witness
    cases source with
    | mk side phase => cases phase <;> cases request <;> rfl
  forward_backward := by
    intro source request witness
    cases source with
    | mk side phase => cases phase <;> cases request <;> rfl
  next_exact := by
    intro source request
    cases source with
    | mk side phase => cases phase <;> cases request <;> rfl
  event_exact := by
    intro source request
    cases source with
    | mk side phase => cases phase <;> cases request <;> rfl

def positiveDirectedSourceInitial : PositiveDirectedSource role :=
  ⟨.source, .active⟩

def positiveDirectedTargetInitial : PositiveDirectedSource role :=
  ⟨.target, .active⟩

def positiveDirectedSourceTerminal : PositiveDirectedSource role :=
  ⟨.source, .terminal⟩

def positiveDirectedTargetTerminal : PositiveDirectedSource role :=
  ⟨.target, .terminal⟩

theorem positiveDirectedInitialSources_ne :
    positiveDirectedSourceInitial role ≠ positiveDirectedTargetInitial role := by
  intro same
  have sides := congrArg PositiveDirectedSource.side same
  cases sides

theorem positiveDirectedTerminals_ne :
    positiveDirectedSourceTerminal role ≠ positiveDirectedTargetTerminal role := by
  intro same
  have sides := congrArg PositiveDirectedSource.side same
  cases sides

theorem positiveDirectedActiveMemories_ne :
    positiveDirectedProject role (positiveDirectedSourceInitial role) ≠
      positiveDirectedProject role (positiveDirectedTargetInitial role) := by
  intro same
  cases same

theorem positiveDirectedCloseChangesPhase (side : PositiveDirectedSide) :
    positiveDirectedNext role ⟨side, .active⟩ .close = ⟨side, .terminal⟩ :=
  rfl

def positiveDirectedSourceRun :
    ExecutedRun (positiveDirectedContract role) (positiveDirectedSourceInitial role)
      [.close] (positiveDirectedSourceTerminal role) [⟨.active .source⟩] :=
  .cons
    (perform (positiveDirectedContract role) (positiveDirectedSourceInitial role)
      .close PUnit.unit)
    (.nil (positiveDirectedSourceTerminal role))

def positiveDirectedTargetRun :
    ExecutedRun (positiveDirectedContract role) (positiveDirectedTargetInitial role)
      [.close] (positiveDirectedTargetTerminal role) [⟨.active .target⟩] :=
  .cons
    (perform (positiveDirectedContract role) (positiveDirectedTargetInitial role)
      .close PUnit.unit)
    (.nil (positiveDirectedTargetTerminal role))

theorem positiveDirectedProducedBitsEqual :
    positiveDirectedProducedBit role .source =
      positiveDirectedProducedBit role .target := by
  change roleRead role run.selected (variedLeftSource role) =
    roleRead role run.selected (leftSource role)
  exact ((produceRoleSignature_exact role run.selected
    (variedLeftSource role) (leftSource role)).mp
      (same_sources_other_resource_agree role)).read

theorem positiveDirectedTerminalProjectionsEqual :
    positiveDirectedProject role (positiveDirectedSourceTerminal role) =
      positiveDirectedProject role (positiveDirectedTargetTerminal role) :=
  congrArg PositiveDirectedMemory.grouped
    (positiveDirectedProducedBitsEqual role)

def positiveDirectedGrouping :
    ExecutedOperationalGrouping (positiveDirectedRealization role)
      (positiveDirectedSourceInitial role) (positiveDirectedTargetInitial role)
      (positiveDirectedSourceTerminal role) (positiveDirectedTargetTerminal role) where
  trace := ⟨.close, []⟩
  leftEvents := [⟨.active .source⟩]
  leftRun := positiveDirectedSourceRun role
  rightEvents := [⟨.active .target⟩]
  rightRun := positiveDirectedTargetRun role
  terminalCollision := by
    change PositiveDirectedMemory.grouped (positiveDirectedProducedBit role .source) =
      PositiveDirectedMemory.grouped (positiveDirectedProducedBit role .target)
    exact congrArg PositiveDirectedMemory.grouped
      (positiveDirectedProducedBitsEqual role)

theorem positiveDirectedEventTracesDistinct :
    (positiveDirectedGrouping role).leftEvents ≠
      (positiveDirectedGrouping role).rightEvents := by
  intro same
  cases same

def encodePositiveDirectedBit : Bool → Nat
  | false => 0
  | true => 1

def decodePositiveDirectedBit : Nat → Bool
  | 0 => false
  | .succ _ => true

theorem decodePositiveDirectedBit_encode (bit : Bool) :
    decodePositiveDirectedBit (encodePositiveDirectedBit bit) = bit := by
  cases bit <;> rfl

def positiveDirectedMemoryRead : PositiveDirectedMemory role → Type
  | .active _ => PUnit
  | .grouped bit => { code : Nat // code = encodePositiveDirectedBit bit }

def positiveDirectedReadoutPreservation :
    DirectedTerminalReadoutPreservation (positiveDirectedRealization role)
      (positiveDirectedSourceTerminal role) (positiveDirectedTargetTerminal role) where
  memoryRead := positiveDirectedMemoryRead role
  sourceForward := fun witness =>
    ⟨encodePositiveDirectedBit witness.1,
      congrArg encodePositiveDirectedBit witness.2⟩
  targetBackward := fun witness =>
    ⟨decodePositiveDirectedBit witness.1,
      (congrArg decodePositiveDirectedBit witness.2).trans
        (decodePositiveDirectedBit_encode
          (positiveDirectedProducedBit role .target))⟩

def positiveDirectedTerminalTransport :
    (positiveDirectedContract role).read (positiveDirectedSourceTerminal role) →
      (positiveDirectedContract role).read (positiveDirectedTargetTerminal role) :=
  (positiveDirectedGrouping role).directedReadout
    (positiveDirectedReadoutPreservation role)

def positiveDirectedSourceWitness :
    (positiveDirectedContract role).read (positiveDirectedSourceTerminal role) :=
  ⟨positiveDirectedProducedBit role .source, rfl⟩

def positiveDirectedTransportedWitness :
    (positiveDirectedContract role).read (positiveDirectedTargetTerminal role) :=
  positiveDirectedTerminalTransport role (positiveDirectedSourceWitness role)

theorem positiveDirectedTransportedWitness_exact :
    (positiveDirectedTransportedWitness role).1 =
      positiveDirectedProducedBit role .target :=
  (positiveDirectedTransportedWitness role).2

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedSide
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedPhase
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedRequest
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedEvent
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedSource
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedSourceAccepted
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTargetAccepted
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedAcceptedSources_ne
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedAcceptedSource
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedIndexedAcceptedSources_ne
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedProducedBit
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedTerminalReadout
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedNext
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedEvent
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedRead
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedAllow
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedDecision
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedContract
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedMemoryNext
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedMemoryEvent
#print axioms ConstitutiveSearch.ContinuationSignatures.PositiveDirectedMemoryAllow
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedMemoryDecision
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedMemoryContract
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedProject
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedSourceInitial
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTargetInitial
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedSourceTerminal
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTargetTerminal
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedInitialSources_ne
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTerminals_ne
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedActiveMemories_ne
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedCloseChangesPhase
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedSourceRun
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTargetRun
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedProducedBitsEqual
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTerminalProjectionsEqual
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedGrouping
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedEventTracesDistinct
#print axioms ConstitutiveSearch.ContinuationSignatures.encodePositiveDirectedBit
#print axioms ConstitutiveSearch.ContinuationSignatures.decodePositiveDirectedBit
#print axioms ConstitutiveSearch.ContinuationSignatures.decodePositiveDirectedBit_encode
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedMemoryRead
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedReadoutPreservation
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTerminalTransport
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedSourceWitness
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTransportedWitness
#print axioms ConstitutiveSearch.ContinuationSignatures.positiveDirectedTransportedWitness_exact
/- AXIOM_AUDIT_END -/
