import Tests.LocalAlignment.DocumentaryAssembledCheckpoint
import Tests.LocalAlignment.DocumentarySequentialCases
import Tests.LocalAlignment.DocumentaryCanonicalAdaptiveRestoration

/-! Concrete source bytes, full-family histories/generations and assembled
typed-master checkpoints. Complete-present byte-only restoration remains open. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.AssembledCases
open Resources EndogenousDecomposition PortableAssignment StatePortable

theorem actual_source :
    StatePortable.restore (StateCapture.save ProgramCases.actual.1.dossier.cursor
      (SequentialCapture.program_ready ProgramCases.actual.2 SequentialCases.initial)) =
      some (⟨ProgramCases.actual.1.dossier.cursor.depth, ProgramCases.actual.1.dossier.cursor.assignment,
        ProgramCases.actual.1.dossier.cursor.state⟩ : StatePortable.Loaded) :=
  StateCapture.restored_exact _ _

theorem unsuitable_source :
    StatePortable.restore (StateCapture.save ProgramCases.wrongActual.1.dossier.cursor
      (SequentialCapture.program_ready ProgramCases.wrongActual.2 SequentialCases.initial)) =
      some (⟨ProgramCases.wrongActual.1.dossier.cursor.depth, ProgramCases.wrongActual.1.dossier.cursor.assignment,
        ProgramCases.wrongActual.1.dossier.cursor.state⟩ : StatePortable.Loaded) :=
  StateCapture.restored_exact _ _

theorem blocked_source :
    StatePortable.restore (StateCapture.save ProgramCases.sourceBlockedActual.1.dossier.cursor
      (SequentialCapture.program_ready ProgramCases.sourceBlockedActual.2 SequentialCases.initial)) =
      some (⟨ProgramCases.sourceBlockedActual.1.dossier.cursor.depth,
        ProgramCases.sourceBlockedActual.1.dossier.cursor.assignment,
        ProgramCases.sourceBlockedActual.1.dossier.cursor.state⟩ : StatePortable.Loaded) :=
  StateCapture.restored_exact _ _

theorem every_memory_source {requests finish} (trace : Memory.Execution MemoryCases.boot requests finish) :
    StatePortable.restore (StateCapture.save finish.session.frame.dossier.cursor
      (SequentialCapture.memory_ready trace SequentialCases.initial)) =
      some (⟨finish.session.frame.dossier.cursor.depth, finish.session.frame.dossier.cursor.assignment,
        finish.session.frame.dossier.cursor.state⟩ : StatePortable.Loaded) :=
  StateCapture.memory trace SequentialCases.initial

def boot := AssembledCheckpoint.capture ControlCodec.natural MemoryCases.boot SequentialCases.initial

theorem boot_restored :
    AssembledCheckpoint.restore Cases.sources Cases.contract DeductionCases.policy
      ControlCodec.natural _ boot = some MemoryCases.boot :=
  AssembledCheckpoint.restored_exact _ _ _ .empty .empty

theorem every_memory_checkpoint {requests finish} (trace : Memory.Execution MemoryCases.boot requests finish) :
    ∃ ready : SequentialCapture.Ready finish.session.frame.dossier.cursor,
      AssembledCheckpoint.restore Cases.sources Cases.contract DeductionCases.policy ControlCodec.natural _
        (AssembledCheckpoint.capture ControlCodec.natural finish ready) = some finish := by
  rcases CanonicalAdaptiveRestoration.memory_execution_formed trace .empty with ⟨store⟩
  rcases PortableMemory.memory_execution_formed trace .empty with ⟨memory⟩
  exact ⟨SequentialCapture.memory_ready trace SequentialCases.initial,
    AssembledCheckpoint.restored_exact _ _ _ store memory⟩

theorem every_checkpoint_future {past finish} (trace : Memory.Execution MemoryCases.boot past finish)
    (requests : List (Memory.Request Nat)) :
    ∃ ready : SequentialCapture.Ready finish.session.frame.dossier.cursor,
      (AssembledCheckpoint.restore Cases.sources Cases.contract DeductionCases.policy ControlCodec.natural _
        (AssembledCheckpoint.capture ControlCodec.natural finish ready)).map
        (fun restored => (Memory.run restored requests).1) =
          some (Memory.run finish requests).1 := by
  rcases every_memory_checkpoint trace with ⟨ready, same⟩
  exact ⟨ready, by rw [same]; rfl⟩

def rootState := initialThreadedConstitutiveState 0
def seed : Record := ⟨0, [], GenerationPortable.capture rootState.generation, rootState.searchSeed, [], []⟩

theorem seed_admitted : (validate seed).isSome = true := rfl
theorem bad_assignment : validate { seed with assignment := [.flip 0] } = none := rfl
theorem bad_search_seed : validate { seed with searchSeed := 99 } = none := rfl
theorem bad_decision_value : validate { seed with decisions := [⟨2, true⟩], provenance := [2] } = none := rfl
theorem bad_provenance : validate { seed with decisions := [⟨2, false⟩], provenance := [1] } = none := rfl
theorem duplicate_compatible_decisions :
    (validate { seed with decisions := [⟨2, false⟩, ⟨2, false⟩], provenance := [2, 2] }).isSome = true := rfl

theorem nonfresh_state_admitted :
    (validate { seed with decisions := [⟨10, false⟩], provenance := [10] }).isSome = true := rfl

theorem nonfresh_next_rejected : StatePortable.restoreForNext
    (ControlCodec.bytes (StatePortable.envelope.words
      { seed with decisions := [⟨10, false⟩], provenance := [10] })) = none := by
  unfold StatePortable.restoreForNext StatePortable.restore
  rw [StatePortable.record_byte_roundtrip]
  rfl

theorem counts_retained :
    ((GenerationPortable.restoreRecord 0
      { GenerationPortable.capture rootState.generation with
        generateCalls := 7, generatedSteps := 8, provenanceUnits := 9, certificatesProduced := 10 }).map
      (fun value => (value.generateCalls, value.generatedSteps, value.provenanceUnits, value.certificatesProduced))) =
        some (7, 8, 9, 10) := rfl

theorem absent_generation : GenerationPortable.restoreRecord 0
    { GenerationPortable.capture rootState.generation with target := .root } = none := rfl
theorem generation_wrong_index : GenerationPortable.restoreRecord 1
    (GenerationPortable.capture rootState.generation) = none := rfl
theorem disconnected_history :
    HistoryPortable.restoreCode StrongPerimetralTurning.Example.examplePresentation
      (.step .root (.formed (.formed .root))) = none := rfl

theorem source_unknown_version : StatePortable.load (ControlCodec.bytes [93, 2]) = none := rfl
theorem source_trailing_words : StatePortable.load
    (ControlCodec.bytes (StatePortable.envelope.words seed ++ [0])) = none := by
  unfold StatePortable.load
  rw [ControlCodec.bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  rw [StatePortable.envelope.exact]

theorem checkpoint_unknown_version : AssembledCheckpoint.loadSections (ControlCodec.bytes [94, 2]) = none := rfl
theorem checkpoint_byte_out_of_range :
    AssembledCheckpoint.octet.read [256] = none := rfl
theorem checkpoint_trailing_words (parts : AssembledCheckpoint.Sections) :
    AssembledCheckpoint.loadSections (ControlCodec.bytes (AssembledCheckpoint.envelope.words parts ++ [0])) = none := by
  unfold AssembledCheckpoint.loadSections
  rw [ControlCodec.bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  rw [AssembledCheckpoint.envelope.exact]

end ConstitutiveSearch.Agent.Local.Documentary.AssembledCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.nonfresh_state_admitted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.nonfresh_next_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.actual_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.unsuitable_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.blocked_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.every_memory_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.boot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.boot_restored
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.every_memory_checkpoint
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.every_checkpoint_future
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.rootState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.seed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.seed_admitted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.bad_assignment
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.bad_search_seed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.bad_decision_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.bad_provenance
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.duplicate_compatible_decisions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.counts_retained
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.absent_generation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.generation_wrong_index
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.disconnected_history
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.source_unknown_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.source_trailing_words
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.checkpoint_unknown_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.checkpoint_byte_out_of_range
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCases.checkpoint_trailing_words
/- AXIOM_AUDIT_END -/
