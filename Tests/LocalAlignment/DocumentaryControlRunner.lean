import Tests.LocalAlignment.DocumentaryControlBindings

/-! Direct bounded execution of the actual source code and its retained events.
Source fuel follows the historical business convention. The separate final
budget pays the catalogue below, including constructor inspection, callback,
frame, business trace cons, positive witness, result and fixed allocations.
No callback is invoked before its complete entry block has been paid.
The four original entry operations are followed by three paid operations per
retained forwarding layer: inspection, call and closure/frame allocation.
The compact block keeps that actual count, without rewriting its own events.
The final host boundary implements those terminal fixed blocks and Nat counter
updates; it does not invoke the source interpreter or flatten the audit tree.
Tape.labels is a reporting observation only. Tape.cost is used in proofs only.
A word contains a fixed block; two joins allocate its actual frame/audit tree.
All intrinsic events are consumed by this runner rather than ignored by a
second source interpreter. Allocation is the declared abstract allocation,
not a measurement of the host allocator. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlRunner
open Control ControlBindings
universe u
abbrev Actual {α : Type u} (expected : α) := {value : α // value = expected}
def eventLabel : Event → Label
  | .compose => .controlCompose
  | .call => .controlCall
  | .closure => .controlClosure
  | .frame => .controlFrame
  | .trace => .controlTrace
  | .result => .controlResult
  | .allocation => .formationResources


inductive Tape where
  | word (labels : List Label)
  | join (left right : Tape)
  | adminBlock (event : Event) (forwards : Nat)

def Tape.cost : Tape → Nat
  | .word labels => labels.length
  | .join left right => left.cost + right.cost
  | .adminBlock _ forwards => 4 + 3 * forwards

def forwardingLabels : Nat → List Label
  | 0 => []
  | count + 1 => .controlInspect :: .controlCall :: .controlClosure :: forwardingLabels count

def Tape.labels : Tape → List Label
  | .word labels => labels
  | .join left right => left.labels ++ right.labels
  | .adminBlock event forwards => [.controlInspect, eventLabel event, .controlCall, .controlFrame] ++ forwardingLabels forwards

def doneTape : Tape := .word [.controlInspect, .controlTrace, .controlWitness, .controlResult]
def stopTape : Tape := .word [.controlInspect, .controlResult]
def businessPrefix (label : Label) : Tape := .word [.controlInspect, label, .controlCall, .controlFrame]
def adminPrefix (event : Event) : (forwards : Nat := 0) → Tape
  | 0 => .word [.controlInspect, eventLabel event, .controlCall, .controlFrame]
  | count + 1 => .adminBlock event (count + 1)

theorem admin_prefix_cost (event : Event) (forwards : Nat) :
    (adminPrefix event forwards).cost = 4 + 3 * forwards := by
  cases forwards <;> rfl
def businessSuffix : Tape := .word [.controlFrame, .controlTrace, .controlWitness, .controlResult]
def adminSuffix : Tape := .word [.controlFrame, .controlWitness, .controlResult]
def failureSuffix : Tape := .word [.controlResult]

def combine (front child suffix : Tape) : Tape := .join front (.join child suffix)

def charge : Nat → Nat → Option Nat
  | 0, budget => some budget
  | _ + 1, 0 => none
  | count + 1, budget + 1 => charge count budget

theorem charge_sound (count budget rest : Nat) (actual : charge count budget = some rest) : count + rest = budget := by
  induction count generalizing budget with
  | zero =>
    change some budget = some rest at actual
    simpa only [Nat.zero_add] using (Option.some.inj actual).symm
  | succ count previous =>
    cases budget with
    | zero => cases actual
    | succ budget =>
      change Nat.succ count + rest = Nat.succ budget
      rw [Nat.succ_add]
      exact congrArg Nat.succ (previous budget actual)

theorem charge_add (count rest : Nat) : charge count (count + rest) = some rest := by
  induction count with
  | zero => rw [Nat.zero_add]; rfl
  | succ count previous => rw [Nat.succ_add]; exact previous

def doneResult {Value : Type u} (value : Value) (fuel : Nat) : Result (.done (Label := Label) value) fuel :=
  ⟨value, [], .done, Nat.zero_le _⟩

def businessResult {Value : Type u} (label : Label) (next : Unit → Code Label Value) (fuel : Nat)
    (actual : Result (next ()) fuel) : Result (.step label next) (fuel + 1) :=
  ⟨actual.value, label :: actual.labels, .step actual.trace, Nat.succ_le_succ actual.bounded⟩

def adminResult {Value : Type u} (event : Event) (next : Unit → Code Label Value) (fuel : Nat)
    (actual : Result (next ()) fuel) (forwards : Nat := 0) : Result (.admin event next forwards) fuel :=
  ⟨actual.value, actual.labels, .admin actual.trace, actual.bounded⟩

inductive Trace {Value : Type u} : (code : Code Label Value) → (fuel : Nat) → Option (Result code fuel) → Tape → Type u where
  | done {value fuel} : Trace (.done value) fuel (some (doneResult value fuel)) doneTape
  | stop {label next} : Trace (.step label next) 0 none stopTape
  | businessNone {label next fuel child} (rest : Trace (next ()) fuel none child) :
      Trace (.step label next) (Nat.succ fuel) none (combine (businessPrefix label) child failureSuffix)
  | businessSome {label next fuel child actual} (rest : Trace (next ()) fuel (some actual) child) :
      Trace (.step label next) (Nat.succ fuel) (some (businessResult label next fuel actual))
        (combine (businessPrefix label) child businessSuffix)
  | adminNone {event next forwards fuel child} (rest : Trace (next ()) fuel none child) :
      Trace (.admin event next forwards) fuel none (combine (adminPrefix event forwards) child failureSuffix)
  | adminSome {event next forwards fuel child actual} (rest : Trace (next ()) fuel (some actual) child) :
      Trace (.admin event next forwards) fuel (some (adminResult event next fuel actual forwards))
        (combine (adminPrefix event forwards) child adminSuffix)

theorem Trace.source_exact {Value : Type u} {code : Code Label Value} {fuel output tape}
    (trace : Trace code fuel output tape) : output = Control.execute fuel code := by
  induction trace with
  | done => cases fuel <;> rfl
  | stop => rfl
  | businessNone rest previous => rw [Control.execute, ← previous]
  | businessSome rest previous => rw [Control.execute, ← previous]; rfl
  | adminNone rest previous => rw [Control.execute, ← previous]
  | adminSome rest previous => rw [Control.execute, ← previous]; rfl

structure Run {Value : Type u} (code : Code Label Value) (fuel budget : Nat) where
  output : Actual (Control.execute fuel code)
  tape : Tape
  trace : Trace code fuel output.1 tape
  remaining : Nat
  budgetExact : tape.cost + remaining = budget

theorem combined_budget {front child suffix : Tape} {budget initial middle final : Nat}
    (before : front.cost + initial = budget) (inside : child.cost + middle = initial)
    (after : suffix.cost + final = middle) : (combine front child suffix).cost + final = budget := by
  dsimp only [combine, Tape.cost]
  rw [Nat.add_assoc, Nat.add_assoc, after, inside, before]

def execute {Value : Type u} (sourceFuel budget : Nat) (code : Code Label Value) : Option (Run code sourceFuel budget) :=
  match code with
  | .done value => match paid : charge 4 budget with
    | none => none
    | some remaining => some ⟨⟨some (doneResult value sourceFuel), Trace.source_exact .done⟩,
        doneTape, .done, remaining, charge_sound 4 budget remaining paid⟩
  | .step label next => match sourceFuel with
    | 0 => match paid : charge 2 budget with
      | none => none
      | some remaining => some ⟨⟨none, rfl⟩, stopTape, .stop, remaining, charge_sound 2 budget remaining paid⟩
    | fuel + 1 => match entered : charge 4 budget with
      | none => none
      | some available =>
        let nextCode := next ()
        match execute fuel available nextCode with
        | none => none
        | some child => match received : child.output.1 with
          | none => match returned : charge 1 child.remaining with
            | none => none
            | some remaining =>
              let trace : Trace (.step label next) (fuel + 1) none
                  (combine (businessPrefix label) child.tape failureSuffix) := .businessNone (received ▸ child.trace)
              some ⟨⟨none, trace.source_exact⟩, _, trace, remaining,
                combined_budget (charge_sound 4 budget available entered) child.budgetExact (charge_sound 1 child.remaining remaining returned)⟩
          | some actual => match returned : charge 4 child.remaining with
            | none => none
            | some remaining =>
              let output := businessResult label next fuel actual
              let trace : Trace (.step label next) (fuel + 1) (some output)
                  (combine (businessPrefix label) child.tape businessSuffix) := .businessSome (received ▸ child.trace)
              some ⟨⟨some output, trace.source_exact⟩, _, trace, remaining,
                combined_budget (charge_sound 4 budget available entered) child.budgetExact (charge_sound 4 child.remaining remaining returned)⟩
  | .admin event next forwards => match entered : charge (4 + 3 * forwards) budget with
    | none => none
    | some available =>
      let nextCode := next ()
      match execute sourceFuel available nextCode with
      | none => none
      | some child => match received : child.output.1 with
        | none => match returned : charge 1 child.remaining with
          | none => none
          | some remaining =>
            let trace : Trace (.admin event next forwards) sourceFuel none
                (combine (adminPrefix event forwards) child.tape failureSuffix) := .adminNone (received ▸ child.trace)
            some ⟨⟨none, trace.source_exact⟩, _, trace, remaining,
              combined_budget (by rw [admin_prefix_cost]; exact charge_sound (4 + 3 * forwards) budget available entered) child.budgetExact (charge_sound 1 child.remaining remaining returned)⟩
        | some actual => match returned : charge 3 child.remaining with
          | none => none
          | some remaining =>
            let output := adminResult event next sourceFuel actual forwards
            let trace : Trace (.admin event next forwards) sourceFuel (some output)
                (combine (adminPrefix event forwards) child.tape adminSuffix) := .adminSome (received ▸ child.trace)
            some ⟨⟨some output, trace.source_exact⟩, _, trace, remaining,
              combined_budget (by rw [admin_prefix_cost]; exact charge_sound (4 + 3 * forwards) budget available entered) child.budgetExact (charge_sound 3 child.remaining remaining returned)⟩
termination_by structural code


def Run.observation {Value : Type u} {code : Code Label Value} {fuel budget} (run : Run code fuel budget) :=
  (run.output.1, run.tape, run.remaining)

def runData {Value : Type u} (fuel budget : Nat) (code : Code Label Value) :=
  (execute fuel budget code).map Run.observation

 theorem runData_some {Value : Type u} {code : Code Label Value} {fuel budget output tape remaining}
    (actual : runData fuel budget code = some (output, tape, remaining)) :
    ∃ run : Run code fuel budget, execute fuel budget code = some run ∧
      run.output.1 = output ∧ run.tape = tape ∧ run.remaining = remaining := by
  unfold runData at actual
  cases found : execute fuel budget code with
  | none => rw [found] at actual; cases actual
  | some run =>
    rw [found] at actual
    have same := Option.some.inj actual
    exact ⟨run, rfl, congrArg Prod.fst same,
      congrArg (fun packet => packet.2.1) same, congrArg (fun packet => packet.2.2) same⟩

set_option backward.isDefEq.respectTransparency false in
theorem complete_data {Value : Type u} {code : Code Label Value} {fuel output tape}
    (trace : Trace code fuel output tape) (more : Nat) :
    runData fuel (tape.cost + more) code = some (output, tape, more) := by
  induction trace generalizing more with
  | done =>
    unfold runData
    rw [execute.eq_def]
    try dsimp only
    split
    next absent =>
      have paid : charge 4 (doneTape.cost + more) = some more := charge_add 4 more
      have impossible := absent.symm.trans paid
      cases impossible
    next remaining received =>
      have paid : charge 4 (doneTape.cost + more) = some more := charge_add 4 more
      have same := Option.some.inj (received.symm.trans paid)
      cases same
      rfl
  | stop =>
    unfold runData
    rw [execute.eq_def]
    try dsimp only
    split
    next absent =>
      have paid : charge 2 (stopTape.cost + more) = some more := charge_add 2 more
      have impossible := absent.symm.trans paid
      cases impossible
    next remaining received =>
      have paid : charge 2 (stopTape.cost + more) = some more := charge_add 2 more
      have same := Option.some.inj (received.symm.trans paid)
      cases same
      rfl
  | @businessNone label next fuel child rest previous =>
    obtain ⟨run, received, sameOutput, sameTape, sameRemaining⟩ := runData_some (previous (1 + more))
    have amount : (combine (businessPrefix label) child failureSuffix).cost + more =
        4 + (child.cost + (1 + more)) := by
      change (4 + (child.cost + 1)) + more = 4 + (child.cost + (1 + more))
      exact (Nat.add_assoc 4 (child.cost + 1) more).trans
        (congrArg (fun value => 4 + value) (Nat.add_assoc child.cost 1 more))
    unfold runData
    rw [amount]
    rw [execute.eq_def]
    try dsimp only
    split
    next absent =>
      have impossible := absent.symm.trans (charge_add 4 (child.cost + (1 + more)))
      cases impossible
    next available entered =>
      have sameAvailable := Option.some.inj (entered.symm.trans (charge_add 4 (child.cost + (1 + more))))
      cases sameAvailable
      try dsimp only
      split
      next absent =>
        have impossible := absent.symm.trans received
        cases impossible
      next actualChild got =>
        have sameChild := Option.some.inj (got.symm.trans received)
        cases sameChild
        split
        next outputEq =>
          split
          next absent =>
            have impossible := absent.symm.trans (sameRemaining ▸ charge_add 1 more)
            cases impossible
          next remaining paid =>
            have same := Option.some.inj (paid.symm.trans (sameRemaining ▸ charge_add 1 more))
            cases same
            exact congrArg (fun tape => some (none, combine (businessPrefix label) tape failureSuffix, more)) sameTape
        next actual outputEq =>
          have impossible := outputEq.symm.trans sameOutput
          cases impossible
  | @businessSome label next fuel child actual rest previous =>
    obtain ⟨run, received, sameOutput, sameTape, sameRemaining⟩ := runData_some (previous (4 + more))
    have amount : (combine (businessPrefix label) child businessSuffix).cost + more =
        4 + (child.cost + (4 + more)) := by
      change (4 + (child.cost + 4)) + more = 4 + (child.cost + (4 + more))
      exact (Nat.add_assoc 4 (child.cost + 4) more).trans
        (congrArg (fun value => 4 + value) (Nat.add_assoc child.cost 4 more))
    unfold runData
    rw [amount]
    rw [execute.eq_def]
    try dsimp only
    split
    next absent =>
      have impossible := absent.symm.trans (charge_add 4 (child.cost + (4 + more)))
      cases impossible
    next available entered =>
      have sameAvailable := Option.some.inj (entered.symm.trans (charge_add 4 (child.cost + (4 + more))))
      cases sameAvailable
      try dsimp only
      split
      next absent =>
        have impossible := absent.symm.trans received
        cases impossible
      next actualChild got =>
        have sameChild := Option.some.inj (got.symm.trans received)
        cases sameChild
        split
        next outputEq =>
          have impossible := outputEq.symm.trans sameOutput
          cases impossible
        next actual outputEq =>
          have sameActual := Option.some.inj (outputEq.symm.trans sameOutput)
          cases sameActual
          split
          next absent =>
            have impossible := absent.symm.trans (sameRemaining ▸ charge_add 4 more)
            cases impossible
          next remaining paid =>
            have same := Option.some.inj (paid.symm.trans (sameRemaining ▸ charge_add 4 more))
            cases same
            exact congrArg (fun tape => some (some (businessResult label next fuel actual), combine (businessPrefix label) tape businessSuffix, more)) sameTape
  | @adminNone event next forwards fuel child rest previous =>
    obtain ⟨run, received, sameOutput, sameTape, sameRemaining⟩ := runData_some (previous (1 + more))
    have amount : (combine (adminPrefix event forwards) child failureSuffix).cost + more =
        (4 + 3 * forwards) + (child.cost + (1 + more)) := by
      dsimp only [combine, Tape.cost]
      rw [admin_prefix_cost]
      exact (Nat.add_assoc (4 + 3 * forwards) (child.cost + 1) more).trans
        (congrArg (fun value => (4 + 3 * forwards) + value) (Nat.add_assoc child.cost 1 more))
    unfold runData
    rw [amount]
    rw [execute.eq_def]
    try dsimp only
    split
    next absent =>
      have impossible := absent.symm.trans (charge_add (4 + 3 * forwards) (child.cost + (1 + more)))
      cases impossible
    next available entered =>
      have sameAvailable := Option.some.inj (entered.symm.trans (charge_add (4 + 3 * forwards) (child.cost + (1 + more))))
      cases sameAvailable
      try dsimp only
      split
      next absent =>
        have impossible := absent.symm.trans received
        cases impossible
      next actualChild got =>
        have sameChild := Option.some.inj (got.symm.trans received)
        cases sameChild
        split
        next outputEq =>
          split
          next absent =>
            have impossible := absent.symm.trans (sameRemaining ▸ charge_add 1 more)
            cases impossible
          next remaining paid =>
            have same := Option.some.inj (paid.symm.trans (sameRemaining ▸ charge_add 1 more))
            cases same
            exact congrArg (fun tape => some (none, combine (adminPrefix event forwards) tape failureSuffix, more)) sameTape
        next actual outputEq =>
          have impossible := outputEq.symm.trans sameOutput
          cases impossible
  | @adminSome event next forwards fuel child actual rest previous =>
    obtain ⟨run, received, sameOutput, sameTape, sameRemaining⟩ := runData_some (previous (3 + more))
    have amount : (combine (adminPrefix event forwards) child adminSuffix).cost + more =
        (4 + 3 * forwards) + (child.cost + (3 + more)) := by
      dsimp only [combine, Tape.cost]
      rw [admin_prefix_cost]
      exact (Nat.add_assoc (4 + 3 * forwards) (child.cost + 3) more).trans
        (congrArg (fun value => (4 + 3 * forwards) + value) (Nat.add_assoc child.cost 3 more))
    unfold runData
    rw [amount]
    rw [execute.eq_def]
    try dsimp only
    split
    next absent =>
      have impossible := absent.symm.trans (charge_add (4 + 3 * forwards) (child.cost + (3 + more)))
      cases impossible
    next available entered =>
      have sameAvailable := Option.some.inj (entered.symm.trans (charge_add (4 + 3 * forwards) (child.cost + (3 + more))))
      cases sameAvailable
      try dsimp only
      split
      next absent =>
        have impossible := absent.symm.trans received
        cases impossible
      next actualChild got =>
        have sameChild := Option.some.inj (got.symm.trans received)
        cases sameChild
        split
        next outputEq =>
          have impossible := outputEq.symm.trans sameOutput
          cases impossible
        next actual outputEq =>
          have sameActual := Option.some.inj (outputEq.symm.trans sameOutput)
          cases sameActual
          split
          next absent =>
            have impossible := absent.symm.trans (sameRemaining ▸ charge_add 3 more)
            cases impossible
          next remaining paid =>
            have same := Option.some.inj (paid.symm.trans (sameRemaining ▸ charge_add 3 more))
            cases same
            exact congrArg (fun tape => some (some (adminResult event next fuel actual forwards), combine (adminPrefix event forwards) tape adminSuffix, more)) sameTape


def runCtl {Value : Type u} (sourceFuel budget : Nat) (code : Code Label Value) :=
  (runData sourceFuel budget code).map (fun packet => (packet.1, packet.2.1))

theorem runCtl_some {Value : Type u} {code : Code Label Value} {fuel budget output tape}
    (actual : runCtl fuel budget code = some (output, tape)) :
    ∃ run : Run code fuel budget, execute fuel budget code = some run ∧
      run.output.1 = output ∧ run.tape = tape := by
  unfold runCtl runData at actual
  cases found : execute fuel budget code with
  | none => rw [found] at actual; cases actual
  | some run =>
    rw [found] at actual
    have same := Option.some.inj actual
    exact ⟨run, rfl, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem ctl_sound {Value : Type u} {code : Code Label Value} {fuel budget output tape}
    (actual : runCtl fuel budget code = some (output, tape)) :
    output = Control.execute fuel code ∧
      Nonempty (Trace code fuel output tape) ∧ tape.cost ≤ budget := by
  obtain ⟨run, received, sameOutput, sameTape⟩ := runCtl_some actual
  have within : run.tape.cost ≤ budget :=
    Eq.rec (motive := fun amount _ => run.tape.cost ≤ amount)
      (Nat.le_add_right run.tape.cost run.remaining) run.budgetExact
  have receivedTrace : Trace code fuel output run.tape :=
    Eq.rec (motive := fun result _ => Trace code fuel result run.tape) run.trace sameOutput
  have actualTrace : Trace code fuel output tape :=
    Eq.rec (motive := fun tree _ => Trace code fuel output tree) receivedTrace sameTape
  have paid : tape.cost ≤ budget :=
    Eq.rec (motive := fun tree _ => tree.cost ≤ budget) within sameTape
  exact ⟨sameOutput.symm.trans run.output.2, ⟨actualTrace⟩, paid⟩

theorem budget_split {paid budget : Nat} (within : paid ≤ budget) :
    ∃ more, budget = paid + more := by
  induction within with
  | refl => exact ⟨0, rfl⟩
  | @step budget previous induction =>
    obtain ⟨more, same⟩ := induction
    exact ⟨more + 1, (congrArg Nat.succ same).trans (Nat.add_succ paid more).symm⟩

theorem ctl_complete {Value : Type u} {code : Code Label Value} {fuel output tape}
    (trace : Trace code fuel output tape) {budget : Nat} (within : tape.cost ≤ budget) :
    runCtl fuel budget code = some (output, tape) := by
  obtain ⟨more, same⟩ := budget_split within
  cases same
  unfold runCtl
  rw [complete_data trace more]
  rfl

theorem ctl_mono {Value : Type u} {code : Code Label Value} {fuel budget output tape}
    (actual : runCtl fuel budget code = some (output, tape))
    {more : Nat} (larger : budget ≤ more) : runCtl fuel more code = some (output, tape) := by
  obtain ⟨_, ⟨trace⟩, within⟩ := ctl_sound actual
  exact ctl_complete trace (Nat.le_trans within larger)

theorem has_trace {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    ∃ output tape, Nonempty (Trace code fuel output tape) := by
  induction code generalizing fuel with
  | done value => exact ⟨_, _, ⟨.done⟩⟩
  | step label next previous =>
    cases fuel with
    | zero => exact ⟨_, _, ⟨.stop⟩⟩
    | succ fuel =>
      obtain ⟨output, tape, ⟨child⟩⟩ := previous () fuel
      cases output with
      | none => exact ⟨_, _, ⟨.businessNone child⟩⟩
      | some actual => exact ⟨_, _, ⟨.businessSome child⟩⟩
  | admin event next forwards previous =>
    obtain ⟨output, tape, ⟨child⟩⟩ := previous () fuel
    cases output with
    | none => exact ⟨_, _, ⟨.adminNone child⟩⟩
    | some actual => exact ⟨_, _, ⟨.adminSome child⟩⟩

theorem finite {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    ∃ budget output tape, runCtl fuel budget code = some (output, tape) := by
  obtain ⟨output, tape, ⟨trace⟩⟩ := has_trace code fuel
  exact ⟨tape.cost, output, tape, ctl_complete trace (Nat.le_refl _)⟩


theorem Trace.unique {Value : Type u} {code : Code Label Value} {fuel output tape}
    (first : Trace code fuel output tape) {other otherTape}
    (second : Trace code fuel other otherTape) : output = other ∧ tape = otherTape := by
  have left := complete_data first otherTape.cost
  have right := complete_data second tape.cost
  have common := congrArg (fun budget => runData fuel budget code)
    (Nat.add_comm tape.cost otherTape.cost)
  have same := Option.some.inj (left.symm.trans (common.trans right))
  exact ⟨congrArg Prod.fst same, congrArg (fun packet => packet.2.1) same⟩

theorem fuel_required {Value : Type u} {code : Code Label Value} {fuel output tape}
    (trace : Trace code fuel output tape) {budget other otherTape}
    (actual : runCtl fuel budget code = some (other, otherTape)) : tape.cost ≤ budget := by
  obtain ⟨_, ⟨received⟩, within⟩ := ctl_sound actual
  have same := (trace.unique received).2
  exact Eq.rec (motive := fun tree _ => tree.cost ≤ budget) within same.symm

theorem fuel_short {Value : Type u} {code : Code Label Value} {fuel output tape}
    (trace : Trace code fuel output tape) {budget} (short : budget < tape.cost) :
    runCtl fuel budget code = none := by
  cases found : runCtl fuel budget code with
  | none => rfl
  | some packet =>
    have impossible := Nat.not_le_of_gt short (fuel_required trace found)
    exact False.elim impossible

end ConstitutiveSearch.Agent.Local.Documentary.ControlRunner

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.eventLabel
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Run.observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.runData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.runData_some
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.complete_data
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Tape
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Tape.cost
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Tape.labels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.doneTape
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.stopTape
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.businessPrefix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.adminPrefix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.businessSuffix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.adminSuffix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.failureSuffix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.combine
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.charge
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.charge_sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.charge_add
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.doneResult
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.businessResult
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.adminResult
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Trace.source_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.combined_budget
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.runCtl
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.runCtl_some
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.ctl_sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.ctl_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.ctl_mono
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.has_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.budget_split
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Trace.unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.fuel_required
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.fuel_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.Actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.forwardingLabels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRunner.admin_prefix_cost
/- AXIOM_AUDIT_END -/
