import RelationalPerimeter.Computation.Machine.LiveSearchFrontier

/-! Lower the actually returned finite transport code, not a predicted selector.
The same lowering acts on public ports and the internal selected-value port. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open SAT EndogenousDecomposition ConnectedFabric

def composeGate (first second : Gate) : Gate := ⟨first.invert != second.invert⟩

theorem composeGate_fire (first second : Gate) (bit : Bool) :
    (composeGate first second).fire bit = second.fire (first.fire bit) := by
  cases first with | mk one =>
    cases second with | mk two => cases one <;> cases two <;> cases bit <;> rfl

def codeGate {root : Cnf} (selected query : Var) :
    {source target : GeneratedStructuralBranchContext root} →
    TransportCode (GeneratedStructuralFlipAtRelation selected) source target → Gate
  | _, _, .identity _ => ⟨false⟩
  | _, _, .atom _ => configureGate selected query
  | _, _, .compose first second => composeGate (codeGate selected query first) (codeGate selected query second)

theorem codeGate_exact {root : Cnf} (selected query : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) :
    (codeGate selected query code).fire (input.1 query) =
      ((code.eval (generatedStructuralFlipAtAction root selected)).map input).1 query := by
  induction code with
  | identity _ => rfl
  | atom relation => exact configureGate_exact selected query input.1
  | compose first second firstIH secondIH =>
      change (composeGate _ _).fire _ = _
      rw [composeGate_fire, firstIH input]
      exact secondIH ((first.eval (generatedStructuralFlipAtAction root selected)).map input)

@[inline]
def scopeCode {root : Cnf} (scope : Scope) (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target) : List Gate :=
  scope.map (fun channel => codeGate selected channel.query code)

theorem scopeCode_length {root : Cnf} (scope : Scope) (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target) :
    (scopeCode scope selected code).length = scope.length := by
  induction scope with
  | nil => rfl
  | cons channel rest ih => exact congrArg Nat.succ ih

theorem scopeCode_exact {root : Cnf} (scope : Scope) (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) :
    fire (scopeCode scope selected code) (sense scope input.1) =
      sense scope ((code.eval (generatedStructuralFlipAtAction root selected)).map input).1 := by
  induction scope with
  | nil => rfl
  | cons channel rest ih =>
      change (codeGate selected channel.query code).fire (input.1 channel.query) ::
        fire (scopeCode rest selected code) (sense rest input.1) = _
      rw [codeGate_exact, ih]
      rfl

theorem gate_involutive (gate : Gate) (bit : Bool) : gate.fire (gate.fire bit) = bit := by
  cases gate with | mk invert => cases invert <;> cases bit <;> rfl

theorem fire_involutive (gates : List Gate) (bits : Signals) (same : gates.length = bits.length) :
    fire gates (fire gates bits) = bits := by
  induction gates generalizing bits with
  | nil => cases bits with | nil => rfl | cons _ _ => cases same
  | cons gate rest ih =>
      cases bits with
      | nil => cases same
      | cons bit tail =>
          change gate.fire (gate.fire bit) :: fire rest (fire rest tail) = _
          rw [gate_involutive, ih tail (Nat.succ.inj same)]

structure LocalAction (front : Frontier) where
  discovery : EndogenousFlipDiscovery (constructStage (front.depth + 1)).operationalRoot
  found : (discover front).outcome.discovered? = some discovery
  execution : ExecutedDiscoverySchedule (validateDiscoverySchedule (scheduleFromDiscovery discovery))

def buildAction (front : Frontier) : LocalAction front :=
  let run := discover front
  match found : run.outcome.discovered? with
  | none => False.elim (discovery_success front found)
  | some discovery =>
      let stored := run.outcome.produceStoredSchedule discovery found
      let validation := validateStoredSchedule stored
      let executed := (executeStoredSchedule validation).execution
      ⟨discovery, found, validation.validated_exact ▸ executed⟩

def LocalAction.selected {front : Frontier} (action : LocalAction front) : Var := action.discovery.var

def LocalAction.gates {front : Frontier} (action : LocalAction front) (scope : Scope) : List Gate :=
  scopeCode scope action.selected action.execution.code

def LocalAction.internalOutput {front : Frontier} (action : LocalAction front) : Bool :=
  (codeGate action.selected action.selected action.execution.code).fire false

def LocalAction.producedSeed {front : Frontier} (action : LocalAction front) : Var :=
  match action.execution.producedState.context.decisions with
  | [] => 0
  | decision :: _ => decision.var

theorem LocalAction.discovery_exact {front : Frontier} (action : LocalAction front) :
    action.discovery = canonicalStageDiscovery (front.depth + 1) := by
  have found := action.found
  rw [discovered_exact, canonicalStageDiscovery_found] at found
  exact (Option.some.inj found).symm

theorem LocalAction.selected_exact {front : Frontier} (action : LocalAction front) :
    action.selected = stageSelectedVar (front.depth + 1) := by
  rw [LocalAction.selected, action.discovery_exact]
  exact canonicalStageDiscovery_var _

theorem LocalAction.gates_exact {front : Frontier} (action : LocalAction front) (scope : Scope) :
    action.gates scope = configure scope action.selected := by
  unfold LocalAction.gates
  rw [executedDiscoverySchedule_code]
  rfl

theorem LocalAction.internalOutput_exact {front : Frontier} (action : LocalAction front) :
    action.internalOutput = true := by
  unfold LocalAction.internalOutput
  rw [executedDiscoverySchedule_code]
  change (configureGate action.selected action.selected).fire false = true
  rw [configureGate, if_pos rfl]
  rfl

theorem LocalAction.producedSeed_exact {front : Frontier} (action : LocalAction front) :
    action.producedSeed = action.selected := by
  unfold LocalAction.producedSeed
  rw [action.execution.producedStateExact]
  rfl

theorem LocalAction.preservesAcceptance {front : Frontier} (action : LocalAction front)
    (input : GeneratedStructuralBranchContinuation (scheduleFromDiscovery action.discovery).entry.source)
    (accepted : GeneratedStructuralBranchAccept (scheduleFromDiscovery action.discovery).entry.source input) :
    GeneratedStructuralBranchAccept (scheduleFromDiscovery action.discovery).entry.target
      ((action.execution.code.eval
        (generatedStructuralFlipAtAction _ action.selected)).map input) :=
  (action.execution.code.eval (generatedStructuralFlipAtAction _ action.selected)).preservesAccept input accepted

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.codeGate
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.codeGate_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.scopeCode_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.scopeCode_length
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.fire_involutive
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.buildAction
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.LocalAction.discovery_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.LocalAction.selected_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.LocalAction.gates_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.LocalAction.internalOutput_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.LocalAction.producedSeed_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.LocalAction.preservesAcceptance
/- AXIOM_AUDIT_END -/
