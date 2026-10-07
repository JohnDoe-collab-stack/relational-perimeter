import RelationalPerimeter.Computation.Machine.Channel

/-! Executable lowering of the actual role action to a bank of connected gates.
The Boolean signals are an electrical interface, not constitutive occurrences.
The rich side still starts from the existing constituted role and formation.
No input assignment or role object is captured by a configured gate. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ConnectedFabric
open SAT EndogenousDecomposition

structure Gate where
  invert : Bool

def Gate.fire (gate : Gate) (input : Bool) : Bool :=
  if gate.invert then !input else input

def configureGate (selected query : Var) : Gate :=
  if query = selected then ⟨true⟩ else ⟨false⟩

def sense (scope : Scope) (assignment : Assignment) : Signals :=
  scope.map (fun channel => assignment channel.query)

def configure (scope : Scope) (selected : Var) : List Gate :=
  scope.map (fun channel => configureGate selected channel.query)

/-- A zipped circuit never evaluates an assignment callback or a query address. -/
def fire (gates : List Gate) (bits : Signals) : Signals :=
  match gates with
  | [] => []
  | gate :: rest => match bits with
    | [] => []
    | bit :: tail => gate.fire bit :: fire rest tail
termination_by structural gates

theorem configureGate_exact (selected query : Var) (assignment : Assignment) :
    (configureGate selected query).fire (assignment query) =
      Assignment.flipAt selected assignment query := by
  by_cases same : query = selected
  · rw [configureGate, if_pos same]
    subst query
    exact (Assignment.flipAt_selected selected assignment).symm
  · rw [configureGate, if_neg same]
    exact (Assignment.flipAt_other selected query assignment same).symm

theorem configure_exact (scope : Scope) (selected : Var) (assignment : Assignment) :
    fire (configure scope selected) (sense scope assignment) =
      sense scope (Assignment.flipAt selected assignment) := by
  induction scope with
  | nil => rfl
  | cons channel rest ih =>
      change (configureGate selected channel.query).fire (assignment channel.query) ::
        fire (configure rest selected) (sense rest assignment) = _
      rw [configureGate_exact, ih]
      rfl

/-- The configured action reads the selected variable of this executed stage. -/
def compile {live : LiveContinuation.Memory}
    (scope : Scope) (production : LiveContinuation.Production live) : List Gate :=
  configure scope (causalStageOfThreadedStage production.built.run).selected

/-- Exact on arbitrary typed continuations, not only the successful input. -/
theorem compile_total_action {live : LiveContinuation.Memory}
    (scope : Scope) (production : LiveContinuation.Production live)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh)) :
    fire (compile scope production) (sense scope continuation.1) =
      sense scope ((compileRoleStageAtom production.decomposition.role).action continuation).1 :=
  configure_exact scope _ continuation.1

/-- Acceptance is separate; the rich obligation needs the real license. -/
def acceptedAction {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh))
    (accepted : GeneratedStructuralBranchAccept
      (causalOpeningLeft _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh) continuation) :
    { result : GeneratedStructuralBranchContinuation
      (causalOpeningRight _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh) //
      GeneratedStructuralBranchAccept
        (causalOpeningRight _ (causalStageOfThreadedStage production.built.run).selected
          (causalStageOfThreadedStage production.built.run).fresh) result } :=
  ⟨(compileRoleStageAtom production.decomposition.role).action continuation,
    production.decomposition.license.preservesCriterion continuation accepted⟩

theorem acceptedAction_circuit {live : LiveContinuation.Memory}
    (scope : Scope) (production : LiveContinuation.Production live)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh))
    (accepted : GeneratedStructuralBranchAccept
      (causalOpeningLeft _ (causalStageOfThreadedStage production.built.run).selected
        (causalStageOfThreadedStage production.built.run).fresh) continuation) :
    fire (compile scope production) (sense scope continuation.1) =
      sense scope (acceptedAction production continuation accepted).1.1 :=
  compile_total_action scope production continuation

inductive Inlet where
  | transformed
  | retained

/-- Sharing is computed from actual signal values. A split cannot be discarded. -/
inductive Bank where
  | shared (signals : Signals)
  | separate (transformed retained : Signals)

def Bank.read : Bank → Inlet → Signals
  | .shared signals, _ => signals
  | .separate left _, .transformed => left
  | .separate _ right, .retained => right

def Bank.cells : Bank → Nat
  | .shared _ => 1
  | .separate _ _ => 2

/-- Structural equality avoids the compiler's generated extensional lemmas. -/
def signalsDecision : (left right : Signals) → Decidable (left = right)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun same => nomatch same)
  | _ :: _, [] => .isFalse (fun same => nomatch same)
  | left :: ls, right :: rs =>
      match Bool.decEq left right with
      | .isFalse different => .isFalse (fun same => different (List.cons.inj same).1)
      | .isTrue head => match signalsDecision ls rs with
        | .isFalse different => .isFalse (fun same => different (List.cons.inj same).2)
        | .isTrue tail => .isTrue (by cases head; cases tail; rfl)

def route (transformed retained : Signals) : Bank :=
  @ite Bank (transformed = retained) (signalsDecision transformed retained)
    (.shared transformed) (.separate transformed retained)

theorem route_reads_transformed (left right : Signals) :
    (route left right).read .transformed = left := by
  unfold route
  split <;> rfl

theorem route_reads_retained (left right : Signals) :
    (route left right).read .retained = right := by
  unfold route
  split
  · assumption
  · rfl

theorem route_shared_iff (left right : Signals) :
    (route left right).cells = 1 ↔ left = right := by
  cases chosen : signalsDecision left right with
  | isTrue same =>
      have routed : route left right = .shared left := by
        unfold route
        rw [chosen]
        rfl
      rw [routed]
      exact ⟨fun _ => same, fun _ => rfl⟩
  | isFalse different =>
      have routed : route left right = .separate left right := by
        unfold route
        rw [chosen]
        rfl
      constructor
      · intro impossible
        rw [routed] at impossible
        exact False.elim (Nat.noConfusion (Nat.succ.inj impossible))
      · intro same
        exact False.elim (different same)

/-- Connection-mediated action, followed by a value-exact memory allocation. -/
def drive (gates : List Gate) (left right : Signals) : Bank :=
  route (fire gates left) right

theorem drive_fibres (gates : List Gate) (left right : Signals) :
    (drive gates left right).read .transformed =
      (drive gates left right).read .retained ↔ fire gates left = right := by
  rw [drive, route_reads_transformed, route_reads_retained]

theorem drive_cells_iff (gates : List Gate) (left right : Signals) :
    (drive gates left right).cells = 1 ↔ fire gates left = right :=
  route_shared_iff _ _

theorem gate_reads_input (gate : Gate) : gate.fire false ≠ gate.fire true := by
  cases gate with
  | mk invert => cases invert <;> decide

theorem gate_reads_connection (input : Bool) :
    (Gate.mk false).fire input ≠ (Gate.mk true).fire input := by
  cases input <;> decide

/-- Without the discovered inversion the same supplied pair stays separated. -/
theorem action_is_necessary_on_selected_port :
    (drive [⟨true⟩] [false] [true]).cells = 1 ∧
      (drive [⟨false⟩] [false] [true]).cells = 2 := by
  constructor <;> rfl

/-- A configured gate does not justify collapsing arbitrary different outputs. -/
theorem nonconvergent_pulse_remains_separate :
    (drive [⟨true⟩] [false] [false]).cells = 2 := rfl

theorem compile_length {live : LiveContinuation.Memory}
    (scope : Scope) (production : LiveContinuation.Production live) :
    (compile scope production).length = scope.length := by
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem fire_sensed_length (scope : Scope) (selected : Var) (assignment : Assignment) :
    (fire (configure scope selected) (sense scope assignment)).length = scope.length := by
  rw [configure_exact]
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

end ConstitutiveSearch.ConnectedFabric
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConnectedFabric.Gate.fire
#print axioms ConstitutiveSearch.ConnectedFabric.configureGate_exact
#print axioms ConstitutiveSearch.ConnectedFabric.configure_exact
#print axioms ConstitutiveSearch.ConnectedFabric.compile
#print axioms ConstitutiveSearch.ConnectedFabric.compile_total_action
#print axioms ConstitutiveSearch.ConnectedFabric.acceptedAction
#print axioms ConstitutiveSearch.ConnectedFabric.acceptedAction_circuit
#print axioms ConstitutiveSearch.ConnectedFabric.route_reads_transformed
#print axioms ConstitutiveSearch.ConnectedFabric.route_reads_retained
#print axioms ConstitutiveSearch.ConnectedFabric.route_shared_iff
#print axioms ConstitutiveSearch.ConnectedFabric.drive
#print axioms ConstitutiveSearch.ConnectedFabric.drive_fibres
#print axioms ConstitutiveSearch.ConnectedFabric.drive_cells_iff
#print axioms ConstitutiveSearch.ConnectedFabric.gate_reads_input
#print axioms ConstitutiveSearch.ConnectedFabric.gate_reads_connection
#print axioms ConstitutiveSearch.ConnectedFabric.action_is_necessary_on_selected_port
#print axioms ConstitutiveSearch.ConnectedFabric.nonconvergent_pulse_remains_separate
#print axioms ConstitutiveSearch.ConnectedFabric.compile_length
#print axioms ConstitutiveSearch.ConnectedFabric.fire_sensed_length
/- AXIOM_AUDIT_END -/
