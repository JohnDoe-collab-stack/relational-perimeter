import Tests.LocalAlignment.DocumentaryControlCompactData

/-! Terminal execution of compact positive traces. The source and final fuels
remain separate. Entry charges precede the sole callback invocation; return
frames retain only the actual event/label/forwarding count. No stale Code or
callback is retained in the positive result. Semantic refinement is erased.
The fixed catalogue and terminal Nat boundary are those of ControlRunner. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution
open Control ControlBindings ControlRunner ControlCompactData
universe u

def chargeFast (amount budget : Nat) : Option Nat :=
  if amount ≤ budget then some (budget - amount) else none

theorem charge_fast_exact (amount budget : Nat) :
    chargeFast amount budget = charge amount budget := by
  induction amount generalizing budget with
  | zero => rw [chargeFast, if_pos (Nat.zero_le budget), Nat.sub_zero]; rfl
  | succ amount previous =>
    cases budget with
    | zero => rw [chargeFast, if_neg (Nat.not_succ_le_zero amount)]; rfl
    | succ budget =>
      rw [chargeFast, charge, Nat.succ_sub_succ_eq_sub]
      change (if amount + 1 ≤ budget + 1 then some (budget - amount) else none) = charge amount budget
      rw [← previous]
      by_cases enough : amount ≤ budget
      · rw [if_pos (Nat.succ_le_succ enough), chargeFast, if_pos enough]
      · rw [if_neg (fun larger => enough (Nat.le_of_succ_le_succ larger)), chargeFast, if_neg enough]

def suffixCost {Value : Type u} (frame : Frame) (output : Option (ControlCompactData.Output Value)) : Nat :=
  match output with
  | none => 1
  | some _ => match frame with | .business _ => 4 | .administrative _ _ => 3

def returnPaid {Value : Type u} (frame : Frame) (child : RawRun Value) : Option (RawRun Value) :=
  (chargeFast (suffixCost frame child.output) child.remaining).map (fun remaining =>
    let restored := returnSource frame child
    ⟨restored.output, restored.path, restored.tape, remaining⟩)

def finish {Value : Type u} (trail : Trail) (child : Option (RawRun Value)) : Option (RawRun Value) :=
  match child with
  | none => none
  | some actual => match trail with
    | [] => some actual
    | frame :: rest => match returnPaid frame actual with
      | none => none
      | some paid => finish (ownedTrail rest) (some paid)
termination_by structural trail

def descend {Value : Type u} (code : Code Label Value) (fuel budget : Nat) (trail : Trail) : Option (RawRun Value) :=
  match code with
  | .done value => match chargeFast 4 budget with
    | none => none
    | some remaining => finish trail (some ⟨some ⟨value, []⟩, .done, doneTape, remaining⟩)
  | .step label next => match fuel with
    | 0 => match chargeFast 2 budget with
      | none => none
      | some remaining => finish trail (some ⟨none, .stop, stopTape, remaining⟩)
    | more + 1 => match chargeFast 4 budget with
      | none => none
      | some remaining => descend (next ()) more remaining (.business label :: trail)
  | .admin event next forwards => match chargeFast (4 + 3 * forwards) budget with
    | none => none
    | some remaining => descend (next ()) fuel remaining (.administrative event forwards :: trail)
termination_by structural code

/-- Recursive semantic specification, used only in erased proofs. The executed
producer is descend/finish, which release each consumed Code before the return. -/
def specification {Value : Type u} (code : Code Label Value) (fuel budget : Nat) : Option (RawRun Value) :=
  match code with
  | .done value => (chargeFast 4 budget).map (fun remaining => ⟨some ⟨value, []⟩, .done, doneTape, remaining⟩)
  | .step label next => match fuel with
    | 0 => (chargeFast 2 budget).map (fun remaining => ⟨none, .stop, stopTape, remaining⟩)
    | more + 1 => (chargeFast 4 budget).bind (fun remaining =>
      (specification (next ()) more remaining).bind (returnPaid (.business label)))
  | .admin event next forwards => (chargeFast (4 + 3 * forwards) budget).bind (fun remaining =>
      (specification (next ()) fuel remaining).bind (returnPaid (.administrative event forwards)))
termination_by structural code

theorem finish_none {Value : Type u} (trail : Trail) : finish trail (none : Option (RawRun Value)) = none := by
  cases trail <;> rfl

theorem finish_cons {Value : Type u} (frame : Frame) (trail : Trail) (child : Option (RawRun Value)) :
    finish (frame :: trail) child = finish trail (child.bind (returnPaid frame)) := by
  cases child with
  | none => rw [Option.bind_none, finish_none, finish_none]
  | some actual =>
    change (match returnPaid frame actual with
      | none => none
      | some paid => finish (ownedTrail trail) (some paid)) =
        finish trail (returnPaid frame actual)
    cases returned : returnPaid frame actual with
    | none => exact (finish_none trail).symm
    | some paid => rfl

theorem descend_exact {Value : Type u} (code : Code Label Value) (fuel budget : Nat) (trail : Trail) :
    descend code fuel budget trail = finish trail (specification code fuel budget) := by
  induction code generalizing fuel budget trail with
  | done value =>
    cases paid : chargeFast 4 budget with
    | none => rw [descend, specification, paid, Option.map_none, finish_none]
    | some remaining => rw [descend, specification, paid]; rfl
  | step label next previous =>
    cases fuel with
    | zero =>
      cases paid : chargeFast 2 budget with
      | none => rw [descend, specification, paid, Option.map_none, finish_none]
      | some remaining => rw [descend, specification, paid]; rfl
    | succ fuel =>
      cases paid : chargeFast 4 budget with
      | none => rw [descend, specification, paid, Option.bind_none, finish_none]
      | some remaining =>
        rw [descend, specification, paid, Option.bind_some]
        change descend (next ()) fuel remaining (.business label :: trail) =
          finish trail ((specification (next ()) fuel remaining).bind (returnPaid (.business label)))
        rw [previous () fuel remaining (.business label :: trail), finish_cons]
  | admin event next forwards previous =>
    cases paid : chargeFast (4 + 3 * forwards) budget with
    | none => rw [descend, specification, paid, Option.bind_none, finish_none]
    | some remaining =>
      rw [descend, specification, paid, Option.bind_some]
      change descend (next ()) fuel remaining (.administrative event forwards :: trail) =
        finish trail ((specification (next ()) fuel remaining).bind (returnPaid (.administrative event forwards)))
      rw [previous () fuel remaining (.administrative event forwards :: trail), finish_cons]

theorem charge_chain (first second budget : Nat) :
    (charge first budget).bind (charge second) = charge (first + second) budget := by
  induction first generalizing budget with
  | zero => rw [Nat.zero_add]; rfl
  | succ first previous =>
    cases budget with
    | zero => rw [Nat.succ_add]; rfl
    | succ budget => rw [Nat.succ_add]; exact previous budget

theorem charge_map_chain {Value : Type u} (first second budget : Nat) (output : Nat → Value) :
    (charge first budget).bind (fun remaining => (charge second remaining).map output) =
    (charge (first + second) budget).map output := by
  induction first generalizing budget with
  | zero => rw [Nat.zero_add]; rfl
  | succ first previous =>
    cases budget with
    | zero => rw [Nat.succ_add]; rfl
    | succ budget => rw [Nat.succ_add]; exact previous budget

theorem charge_three {Value : Type u} (first second third budget : Nat) (output : Nat → Value) :
    (charge first budget).bind (fun remaining =>
      (charge second remaining).bind (fun rest => (charge third rest).map output)) =
    (charge (first + (second + third)) budget).map output := by
  have joined := charge_map_chain first (second + third) budget output
  cases paid : charge first budget with
  | none => rw [paid] at joined; exact joined
  | some remaining =>
    rw [paid] at joined
    change (charge second remaining).bind (fun rest => (charge third rest).map output) = _
    exact (charge_map_chain second third remaining output).trans joined

def restored {Value : Type u} (frame : Frame) (output : Option (ControlCompactData.Output Value))
    (path : Path) (tape : Tape) (remaining : Nat) : RawRun Value :=
  let formed := returnSource frame ⟨output, path, tape, 0⟩
  ⟨formed.output, formed.path, formed.tape, remaining⟩

theorem return_splice {Value : Type u} (frame : Frame) (output : Option (ControlCompactData.Output Value))
    (path : Path) (tape : Tape) (budget : Nat) :
    ((charge tape.cost budget).map (fun remaining => (⟨output, path, tape, remaining⟩ : RawRun Value))).bind
      (returnPaid frame) =
    (charge (tape.cost + suffixCost frame output) budget).map (restored frame output path tape) := by
  have joined := charge_map_chain tape.cost (suffixCost frame output) budget (restored frame output path tape)
  cases paid : charge tape.cost budget with
  | none => rw [paid] at joined; exact joined
  | some remaining =>
    rw [paid] at joined
    change returnPaid frame ⟨output, path, tape, remaining⟩ = _
    rw [returnPaid, charge_fast_exact]
    cases frame <;> cases output <;> exact joined

theorem parent_charge {Value : Type u} (childCode : Code Label Value) (fuel entry : Nat)
    (frame : Frame) (output : Option (ControlCompactData.Output Value)) (path : Path) (tape : Tape)
    (previous : ∀ budget, specification childCode fuel budget =
      (charge tape.cost budget).map (fun remaining => ⟨output, path, tape, remaining⟩)) (budget : Nat) :
    (chargeFast entry budget).bind (fun remaining =>
      (specification childCode fuel remaining).bind (returnPaid frame)) =
    (charge (entry + (tape.cost + suffixCost frame output)) budget).map (restored frame output path tape) := by
  have joined := charge_map_chain entry (tape.cost + suffixCost frame output) budget (restored frame output path tape)
  cases paid : chargeFast entry budget with
  | none =>
    have nativePaid : charge entry budget = none := (charge_fast_exact entry budget).symm.trans paid
    rw [nativePaid] at joined
    exact joined
  | some remaining =>
    have nativePaid : charge entry budget = some remaining := (charge_fast_exact entry budget).symm.trans paid
    rw [nativePaid] at joined
    change (specification childCode fuel remaining).bind (returnPaid frame) = _
    rw [previous remaining, return_splice]
    exact joined

theorem specification_charge {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (realized : Model code fuel output path tape) (budget : Nat) :
    specification code fuel budget =
      (charge tape.cost budget).map (fun remaining => (⟨output, path, tape, remaining⟩ : RawRun Value)) := by
  induction realized generalizing budget with
  | done => rw [specification, charge_fast_exact]; rfl
  | stop => rw [specification, charge_fast_exact]; rfl
  | @businessNone label next fuel path child rest previous =>
    change (chargeFast 4 budget).bind (fun remaining =>
      (specification (next ()) fuel remaining).bind (returnPaid (.business label))) = _
    exact parent_charge (next ()) fuel 4 (.business label) none path child previous budget
  | @businessSome label next fuel path child value labels rest previous =>
    change (chargeFast 4 budget).bind (fun remaining =>
      (specification (next ()) fuel remaining).bind (returnPaid (.business label))) = _
    exact parent_charge (next ()) fuel 4 (.business label) (some ⟨value, labels⟩) path child previous budget
  | @adminNone event next forwards fuel path child rest previous =>
    change (chargeFast (4 + 3 * forwards) budget).bind (fun remaining =>
      (specification (next ()) fuel remaining).bind (returnPaid (.administrative event forwards))) = _
    have joined := parent_charge (next ()) fuel (4 + 3 * forwards) (.administrative event forwards) none path child previous budget
    change _ = (charge ((adminPrefix event forwards).cost + (child.cost + 1)) budget).map _
    rw [admin_prefix_cost]
    exact joined
  | @adminSome event next forwards fuel path child value labels rest previous =>
    change (chargeFast (4 + 3 * forwards) budget).bind (fun remaining =>
      (specification (next ()) fuel remaining).bind (returnPaid (.administrative event forwards))) = _
    have joined := parent_charge (next ()) fuel (4 + 3 * forwards) (.administrative event forwards) (some ⟨value, labels⟩) path child previous budget
    change _ = (charge ((adminPrefix event forwards).cost + (child.cost + 3)) budget).map _
    rw [admin_prefix_cost]
    exact joined

def executeRaw {Value : Type u} (sourceFuel budget : Nat) (code : Code Label Value) : Option (RawRun Value) :=
  descend code sourceFuel budget []

theorem raw_charge {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (realized : Model code fuel output path tape) (budget : Nat) :
    executeRaw fuel budget code =
      (charge tape.cost budget).map (fun remaining => (⟨output, path, tape, remaining⟩ : RawRun Value)) := by
  rw [executeRaw, descend_exact, specification_charge realized]
  cases charge tape.cost budget <;> rfl

theorem raw_sound {Value : Type u} {code : Code Label Value} {fuel budget} {actual : RawRun Value}
    (received : executeRaw fuel budget code = some actual) :
    Model code fuel actual.output actual.path actual.tape ∧ actual.tape.cost + actual.remaining = budget := by
  obtain ⟨output, path, tape, realized⟩ := has_model code fuel
  rw [raw_charge realized] at received
  cases paid : charge tape.cost budget with
  | none => rw [paid] at received; cases received
  | some remaining =>
    rw [paid] at received
    have same : (⟨output, path, tape, remaining⟩ : RawRun Value) = actual := Option.some.inj received
    cases same
    exact ⟨realized, charge_sound _ _ _ paid⟩

structure Run {Value : Type u} (code : Code Label Value) (fuel budget : Nat) extends RawRun Value where
  realized : Model code fuel output path tape
  accounted : tape.cost + remaining = budget

def execute {Value : Type u} (sourceFuel budget : Nat) (code : Code Label Value) : Option (Run code sourceFuel budget) :=
  match received : executeRaw sourceFuel budget code with
  | none => none
  | some actual => some ⟨actual, (raw_sound received).1, (raw_sound received).2⟩

theorem execute_observation {Value : Type u} (sourceFuel budget : Nat) (code : Code Label Value) :
    (execute sourceFuel budget code).map Run.toRawRun = executeRaw sourceFuel budget code := by
  unfold execute
  split
  next absent => exact absent.symm
  next actual received => exact received.symm

theorem complete_data {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (realized : Model code fuel output path tape) (more : Nat) :
    ∃ actual : Run code fuel (tape.cost + more),
      execute fuel (tape.cost + more) code = some actual ∧
      actual.toRawRun = ⟨output, path, tape, more⟩ := by
  have rawActual : executeRaw fuel (tape.cost + more) code = some ⟨output, path, tape, more⟩ := by
    rw [raw_charge realized, charge_add]; rfl
  have observed := execute_observation fuel (tape.cost + more) code
  cases found : execute fuel (tape.cost + more) code with
  | none =>
    rw [found] at observed
    have impossible : (none : Option (RawRun Value)) = some ⟨output, path, tape, more⟩ := observed.trans rawActual
    cases impossible
  | some actual =>
    rw [found] at observed
    exact ⟨actual, rfl, Option.some.inj (observed.trans rawActual)⟩

def runCtl {Value : Type u} (sourceFuel budget : Nat) (code : Code Label Value) :
    Option (Option (ControlCompactData.Output Value) × Path × Tape) :=
  (execute sourceFuel budget code).map (fun actual => (actual.output, actual.path, actual.tape))

theorem ctl_sound {Value : Type u} {code : Code Label Value} {fuel budget output path tape}
    (received : runCtl fuel budget code = some (output, path, tape)) :
    Model code fuel output path tape ∧ tape.cost ≤ budget ∧
      output = observation (Control.execute fuel code) := by
  unfold runCtl at received
  cases found : execute fuel budget code with
  | none => rw [found] at received; cases received
  | some actual =>
    rw [found] at received
    have same : (actual.output, actual.path, actual.tape) = (output, path, tape) := Option.some.inj received
    cases same
    have within : actual.tape.cost ≤ budget := Eq.rec (motive := fun total _ => actual.tape.cost ≤ total)
      (Nat.le_add_right actual.tape.cost actual.remaining) actual.accounted
    exact ⟨actual.realized, within, actual.realized.source_exact⟩

theorem ctl_complete {Value : Type u} {code : Code Label Value} {fuel budget output path tape}
    (realized : Model code fuel output path tape) (within : tape.cost ≤ budget) :
    runCtl fuel budget code = some (output, path, tape) := by
  obtain ⟨more, sameBudget⟩ := ControlRunner.budget_split within
  cases sameBudget
  obtain ⟨actual, found, same⟩ := complete_data realized more
  rw [runCtl, found]
  change some (actual.toRawRun.output, actual.toRawRun.path, actual.toRawRun.tape) = _
  rw [same]

theorem ctl_mono {Value : Type u} {code : Code Label Value} {fuel budget output path tape larger}
    (received : runCtl fuel budget code = some (output, path, tape)) (increase : budget ≤ larger) :
    runCtl fuel larger code = some (output, path, tape) :=
  ctl_complete (ctl_sound received).1 (Nat.le_trans (ctl_sound received).2.1 increase)

theorem fuel_required {Value : Type u} {code : Code Label Value} {fuel budget output path tape}
    (received : runCtl fuel budget code = some (output, path, tape)) : tape.cost ≤ budget :=
  (ctl_sound received).2.1

theorem fuel_short {Value : Type u} {code : Code Label Value} {fuel budget output path tape}
    (realized : Model code fuel output path tape) (short : budget < tape.cost) : runCtl fuel budget code = none := by
  cases found : runCtl fuel budget code with
  | none => rfl
  | some actual =>
    obtain ⟨otherOutput, otherPath, otherTape⟩ := actual
    have received := ctl_sound found
    have sameTape := (realized.unique received.1).2.2
    have impossible : tape.cost ≤ budget := sameTape.symm ▸ received.2.1
    exact False.elim (Nat.not_le_of_lt short impossible)

theorem finite {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    ∃ budget output path tape, runCtl fuel budget code = some (output, path, tape) := by
  obtain ⟨output, path, tape, realized⟩ := has_model code fuel
  exact ⟨tape.cost, output, path, tape, ctl_complete realized (Nat.le_refl _)⟩

structure SourceResult {Value : Type u} (code : Code Label Value) (fuel : Nat) extends ControlCompactData.Output Value where
  path : Path
  tape : Tape
  realized : Model code fuel (some toOutput) path tape

def sourceExecute {Value : Type u} (sourceFuel : Nat) (code : Code Label Value) : Option (SourceResult code sourceFuel) :=
  let actual := sourceDescend code sourceFuel []
  match received : actual.output with
  | none => none
  | some output => some ⟨output, actual.path, actual.tape, received ▸ source_sound code sourceFuel⟩

theorem source_observation {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    (sourceExecute fuel code).map SourceResult.toOutput = (sourceDescend code fuel []).output := by
  unfold sourceExecute
  dsimp only
  split
  next absent => exact absent.symm
  next output received => exact received.symm

theorem source_exact {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    (sourceExecute fuel code).map SourceResult.toOutput = observation (Control.execute fuel code) :=
  (source_observation code fuel).trans (source_sound code fuel).source_exact

end ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.chargeFast
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.charge_fast_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.suffixCost
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.returnPaid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.finish
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.descend
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.specification
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.finish_none
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.finish_cons
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.descend_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.charge_chain
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.charge_map_chain
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.charge_three
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.restored
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.return_splice
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.parent_charge
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.specification_charge
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.executeRaw
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.raw_charge
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.raw_sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.Run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.execute_observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.complete_data
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.runCtl
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.ctl_sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.ctl_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.ctl_mono
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.fuel_required
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.fuel_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.SourceResult
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.sourceExecute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact
/- AXIOM_AUDIT_END -/
