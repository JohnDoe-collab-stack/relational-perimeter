import RelationalPerimeter.Computation.Machine.ReconfigurableMachine

/-! Positive, closed assembly of the configured stage and its future contract.
The electrical bank width is NOT the width of the scientific obligation regime.
That regime and its original certificate remain in the unchanged library. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine
open SAT EndogenousDecomposition ContinuationSignatures ConnectedFabric

/-- The stage packet keeps the semantic license on the proof side, and sends
only the compiled machine state to the runtime side. -/
structure StageCertificate (scope : Scope) (live : LiveContinuation.Memory)
    (production : LiveContinuation.Production live) : Type 3 where
  private mk ::
  memory : Memory
  installedExact : memory = install scope production
  frame : Frame
  frameExact : frame = canonicalFrame scope live production
  transitionExact : memory = project scope frame
  acceptedTarget : { result : GeneratedStructuralBranchContinuation
      (causalOpeningRight _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh) //
      GeneratedStructuralBranchAccept
        (causalOpeningRight _ (causalStageOfThreadedStage production.built.run).selected
          (causalStageOfThreadedStage production.built.run).fresh) result }
  acceptedExact : acceptedTarget = canonicalAccepted production
  actionExact : acceptedTarget.1 = production.decomposition.role.completedOutput
  sourceDistinction : production.decomposition.license.transformedOccurrence ≠
    production.decomposition.license.retainedOccurrence
  bankDerived : memory.bank.cells = 1
  futureAgreement : ∀ requests : List (ULift.{3} Request),
    (sourceContract scope).outcome frame requests = (runtimeContract scope).outcome memory requests

def stageCertificate (scope : Scope) (live : LiveContinuation.Memory)
    (production : LiveContinuation.Production live) : StageCertificate scope live production where
  memory := install scope production
  installedExact := rfl
  frame := canonicalFrame scope live production
  frameExact := rfl
  transitionExact := install_exact scope production
  acceptedTarget := canonicalAccepted production
  acceptedExact := rfl
  actionExact := canonicalAccepted_output production
  sourceDistinction := canonical_occurrences_distinct production
  bankDerived := canonical_bank_shared scope production
  futureAgreement requests := by
    rw [install_exact]
    exact all_futures_exact scope _ requests

/-- The runtime entry returns only the data field; no rich certificate is stored. -/
def certifiedAdvance (scope : Scope) (live : LiveContinuation.Memory) : Memory :=
  let production := LiveContinuation.produce live
  (stageCertificate scope live production).memory

theorem certifiedAdvance_exact (scope : Scope) (live : LiveContinuation.Memory) :
    certifiedAdvance scope live = (advance scope live).1 := rfl

theorem differing_observations_cannot_merge (scope : Scope) {one two : Frame}
    (different : (project scope one).view ≠ (project scope two).view)
    {Other : Type 3} (other : ExactRealization (sourceContract scope) Other) :
    other.project one ≠ other.project two := by
  intro same
  exact different (other.equal_memory_same_futures same).read

/- Gate.fire is reversible for a fixed configuration. The runtime does NOT
claim irreversible erasure of the immediate inlet bits: their two outputs
can reconstruct them. What is no longer present is the rich assignment and
history; exactness is relative to the declared query and future language. -/
theorem gate_inverse (gate : Gate) (bit : Bool) : gate.fire (gate.fire bit) = bit := by
  cases gate with
  | mk invert => cases invert <;> cases bit <;> rfl

/-- Every arbitrary shaped pulse really passes through the stored connections. -/
theorem admitted_pulse_exact (scope : Scope) (memory : Memory) (left right : Signals)
    (fits : pulseFits scope left right = true) :
    (perform scope memory (.pulse left right)).1.bank = drive memory.gates left right := by
  dsimp only [perform, pulse]
  rw [fits]
  rfl

theorem admitted_pulse_width (scope : Scope) (memory : Memory) (left right : Signals)
    (fits : pulseFits scope left right = true) :
    (perform scope memory (.pulse left right)).1.bank.cells = 1 ↔ fire memory.gates left = right := by
  rw [admitted_pulse_exact scope memory left right fits]
  exact drive_cells_iff _ _ _

/-- The same nontrivial pair changes its memory organization with the connection. -/
theorem connection_controls_storage (live : LiveContinuation.Memory) :
    let scope := [Channel.singleton 0]
    let inverting : Memory := ⟨live, [⟨true⟩], .separate [false] [true]⟩
    let direct : Memory := ⟨live, [⟨false⟩], .separate [false] [true]⟩
    (perform scope inverting (.pulse [false] [true])).1.bank.cells = 1 ∧
      (perform scope direct (.pulse [false] [true])).1.bank.cells = 2 := by
  constructor <;> rfl

/-- Equal present answers do NOT justify erasing a connection needed by a future pulse. -/
theorem equal_present_different_futures (live : LiveContinuation.Memory) :
    let scope := [Channel.singleton 0]
    let inverting : Memory := ⟨live, [⟨true⟩], .shared [true]⟩
    let direct : Memory := ⟨live, [⟨false⟩], .shared [true]⟩
    inverting.view = direct.view ∧
      ¬ FutureEquivalent (runtimeContract scope) inverting direct := by
  constructor
  · rfl
  · intro same
    have future := (same.next ⟨.pulse [false] [true]⟩).read
    have bit := congrArg (fun view : View => view.2.1.headD false) future
    exact Bool.noConfusion bit

/- This gate-level separator is a calibration, not a second scientific family:
the public path configures these gates from real productions, not by hand. -/

end ConstitutiveSearch.ReconfigurableMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.stageCertificate
#print axioms ConstitutiveSearch.ReconfigurableMachine.certifiedAdvance
#print axioms ConstitutiveSearch.ReconfigurableMachine.certifiedAdvance_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.differing_observations_cannot_merge
#print axioms ConstitutiveSearch.ReconfigurableMachine.gate_inverse
#print axioms ConstitutiveSearch.ReconfigurableMachine.admitted_pulse_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.admitted_pulse_width
#print axioms ConstitutiveSearch.ReconfigurableMachine.connection_controls_storage
#print axioms ConstitutiveSearch.ReconfigurableMachine.equal_present_different_futures
/- AXIOM_AUDIT_END -/
