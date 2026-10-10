import Tests.LocalAlignment.DocumentaryPortableStart
import Tests.LocalAlignment.DocumentaryProgramCases

/-! Closed formation fidelity and restart cases. The source/rule configuration
and original demands are unchanged. The physical client imports the codec alone. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableCases
open Resources Program Portable PortableCheckpoint

theorem same_sources : PortableCheckpoint.sources = Cases.sources := rfl
theorem same_contract : PortableCheckpoint.contract = Cases.contract := rfl
theorem same_rules : PortableCheckpoint.policy = DeductionCases.policy := rfl

def actual := PortableStart.executePrefix ProgramCases.start
def saved : Saved := ⟨1, 1, 4, actual.1.dossier.cursor.depth, record actual.1.store,
  [0, 1, 2, 3], 1⟩

theorem actual_bindings_saved : save actual.1 4 = some saved := rfl
theorem actual_nodes : saved.nodes =
    [.quotation 1 42, .derived 0 1 0 1, .quotation 2 43, .quotation 1 42] := rfl
theorem actual_boundary : saved.round = 4 ∧ saved.depth = 3 := ⟨rfl, rfl⟩

def restoredStore : Deduction.Store PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy :=
  match loadStore PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy saved.nodes with
  | .ok store => store
  | .error _ => ⟨[], Deduction.empty _ _ _⟩

def supportView {context sources contract policy} (store : @Deduction.Store context sources contract policy) :
    (kinds : List Deduction.Kind) × Support Deduction.Value kinds := ⟨store.1, store.2.resources⟩

/-- Equality includes every stored producer and the actual formation tree, not
just the integers or origin labels. This closes fidelity for this actual prefix. -/
theorem actual_formation_recovered : supportView restoredStore = supportView actual.1.store := rfl

def restored : Loaded :=
  ⟨restoredStore, .cons ⟨⟨_, .here⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
    (.cons ⟨⟨_, .prior .here⟩, ⟨rfl, rfl, rfl⟩⟩
      (.cons ⟨⟨_, .prior (.prior .here)⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
        (.cons ⟨⟨_, .prior (.prior (.prior .here))⟩, ⟨rfl, rfl, rfl, rfl⟩⟩ .nil))), 4, 3⟩

theorem loaded_actual_checkpoint : load saved = .ok restored := rfl
theorem byte_codec_actual : decode (encode saved) = some saved := codec_roundtrip saved
def finished := resume restored
def uninterrupted := Program.execute actual.1 PortableStart.remaining

theorem restarted_formation_same : supportView finished.store = supportView uninterrupted.1.store := rfl
theorem restarted_value : finished.store.2.resources.read finished.output.occurrence.2 = 2 := finished.output.meets.1
theorem restarted_origins : finished.output.occurrence.1.origins = [1, 2, 1, 2] := finished.output.meets.2.2
theorem remaining_does_not_advance_master : uninterrupted.1.dossier.cursor.depth = actual.1.dossier.cursor.depth :=
  uninterrupted.2.depth.trans (Nat.add_zero _)

theorem bad_version : load { saved with version := 2 } = .error .version := rfl
theorem bad_task : load { saved with task := 2 } = .error .task := rfl
theorem bad_binding : load { saved with bindings := [0, 0, 2, 3] } = .error .bindings := rfl
theorem bad_value : load { saved with nodes :=
    [.quotation 1 42, .derived 0 1 0 2, .quotation 2 43, .quotation 1 42] } =
    .error (.store .valueChanged) := rfl
theorem forbidden_source : load { saved with nodes :=
    [.quotation 1 42, .derived 0 1 0 1, .quotation 2 43, .quotation 0 42] } = .error (.store .sourceForbidden) := rfl
theorem forbidden_rule : load { saved with nodes :=
    [.quotation 1 42, .derived 2 1 0 1, .quotation 2 43, .quotation 1 42] } = .error (.store .ruleForbidden) := rfl
theorem missing_premise : load { saved with nodes :=
    [.quotation 1 42, .derived 0 9 0 1, .quotation 2 43, .quotation 1 42] } = .error (.store .premiseMissing) := rfl

end ConstitutiveSearch.Agent.Local.Documentary.PortableCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.same_sources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.same_contract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.same_rules
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.saved
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.actual_bindings_saved
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.actual_nodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.actual_boundary
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.restoredStore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.supportView
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.actual_formation_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.restored
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.loaded_actual_checkpoint
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.byte_codec_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.finished
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.uninterrupted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.restarted_formation_same
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.restarted_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.restarted_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.remaining_does_not_advance_master
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.bad_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.bad_task
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.bad_binding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.bad_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.forbidden_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.forbidden_rule
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCases.missing_premise
/- AXIOM_AUDIT_END -/
