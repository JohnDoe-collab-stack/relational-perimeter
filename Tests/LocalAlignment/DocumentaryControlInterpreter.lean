import Tests.LocalAlignment.DocumentaryRecoveryData

/-! A fuel interpreter with labelled paid transitions and lazy continuations.
Returning a value costs zero. A transition is entered only after one unit has
been available. Labels count this declared abstract machine, not seconds or
the internal work of a library call made inside a transition. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Control
universe u v

inductive Code (Label : Type) (Value : Type u) : Type u where
  | done (value : Value)
  | step (label : Label) (next : Unit → Code Label Value)

inductive Eval {Label : Type} {Value : Type u} : Code Label Value → List Label → Value → Type u where
  | done {value} : Eval (.done value) [] value
  | step {label next labels value} (rest : Eval (next ()) labels value) :
      Eval (.step label next) (label :: labels) value

structure Result {Label : Type} {Value : Type u} (code : Code Label Value) (fuel : Nat) where
  value : Value
  labels : List Label
  trace : Eval code labels value
  bounded : labels.length ≤ fuel

def execute {Label : Type} {Value : Type u} : (fuel : Nat) → (code : Code Label Value) →
    Option (Result code fuel)
  | _, .done value => some ⟨value, [], .done, Nat.zero_le _⟩
  | 0, .step _ _ => none
  | fuel + 1, .step label next =>
      let nextCode := next ()
      match execute fuel nextCode with
      | none => none
      | some actual => some ⟨actual.value, label :: actual.labels, .step actual.trace,
          Nat.succ_le_succ actual.bounded⟩

def Result.observation {Label : Type} {Value : Type u} {code : Code Label Value} {fuel}
    (actual : Result code fuel) : Value × List Label := (actual.value, actual.labels)

def Result.sound {Label : Type} {Value : Type u} {code : Code Label Value} {fuel}
    (actual : Result code fuel) : {_trace : Eval code actual.labels actual.value // actual.labels.length ≤ fuel} :=
  ⟨actual.trace, actual.bounded⟩

def runCtl {Label : Type} {Value : Type u} (fuel : Nat) (code : Code Label Value) :
    Option (Value × List Label) := (execute fuel code).map Result.observation

theorem runCtl_step {Label : Type} {Value : Type u} (fuel : Nat)
    (label : Label) (next : Unit → Code Label Value) :
    runCtl (fuel + 1) (.step label next) =
      (runCtl fuel (next ())).map (fun result => (result.1, label :: result.2)) := by
  unfold runCtl
  rw [execute]
  cases execute fuel (next ()) <;> rfl

theorem ctl_sound {Label : Type} {Value : Type u} (fuel : Nat)
    (code : Code Label Value) (value : Value) (labels : List Label)
    (actual : runCtl fuel code = some (value, labels)) :
    Nonempty {_trace : Eval code labels value // labels.length ≤ fuel} := by
  unfold runCtl at actual
  cases received : execute fuel code with
  | none => rw [received] at actual; cases actual
  | some result =>
      rw [received] at actual
      have same : (result.value, result.labels) = (value, labels) := Option.some.inj actual
      have valueSame := congrArg Prod.fst same
      have labelsSame := congrArg Prod.snd same
      cases valueSame
      cases labelsSame
      exact ⟨result.sound⟩

theorem ctl_complete {Label : Type} {Value : Type u} {code : Code Label Value} {labels value}
    (trace : Eval code labels value) (fuel : Nat) (enough : labels.length ≤ fuel) :
    runCtl fuel code = some (value, labels) := by
  induction trace generalizing fuel with
  | done => cases fuel <;> rfl
  | @step label next labels value rest ih =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero _ enough)
      | succ fuel =>
          rw [runCtl_step]
          rw [ih fuel (Nat.le_of_succ_le_succ enough)]
          rfl

theorem ctl_mono {Label : Type} {Value : Type u} {code : Code Label Value} {value labels}
    (fuel more : Nat) (actual : runCtl fuel code = some (value, labels)) (increase : fuel ≤ more) :
    runCtl more code = some (value, labels) := by
  obtain ⟨executed⟩ := ctl_sound fuel code value labels actual
  exact ctl_complete executed.1 more (Nat.le_trans executed.2 increase)

theorem Eval.unique {Label : Type} {Value : Type u} {code : Code Label Value}
    {leftLabels rightLabels : List Label} {left right : Value}
    (first : Eval code leftLabels left) (second : Eval code rightLabels right) :
    (left, leftLabels) = (right, rightLabels) := by
  induction first generalizing rightLabels right with
  | done => cases second; rfl
  | step rest ih =>
      cases second with
      | step after =>
          have same := ih after
          cases same
          rfl

theorem fuel_required {Label : Type} {Value : Type u} {code : Code Label Value} {value labels}
    (trace : Eval code labels value) (fuel : Nat) {found received}
    (actual : runCtl fuel code = some (found, received)) : labels.length ≤ fuel := by
  obtain ⟨executed⟩ := ctl_sound fuel code found received actual
  have same := trace.unique executed.1
  have labelsSame : labels = received := congrArg Prod.snd same
  exact labelsSame.symm ▸ executed.2

theorem fuel_short {Label : Type} {Value : Type u} {code : Code Label Value} {value labels}
    (trace : Eval code labels value) (fuel : Nat) (short : fuel < labels.length) :
    runCtl fuel code = none := by
  cases actual : runCtl fuel code with
  | none => rfl
  | some result =>
      exact False.elim (Nat.not_lt_of_ge (fuel_required trace fuel actual) short)

def Code.bind {Label : Type} {Value : Type u} {Next : Type v}
    (code : Code Label Value) (continuation : Value → Code Label Next) : Code Label Next :=
  match code with
  | .done value => continuation value
  | .step label next => .step label (fun _ => (next ()).bind continuation)

def Eval.bind {Label : Type} {Value : Type u} {Next : Type v}
    {code : Code Label Value} {continuation : Value → Code Label Next} {firstLabels secondLabels value next}
    (first : Eval code firstLabels value) (second : Eval (continuation value) secondLabels next) :
    Eval (code.bind continuation) (firstLabels ++ secondLabels) next :=
  match first with
  | .done => second
  | .step rest => .step (rest.bind second)

def Finite {Label : Type} {Value : Type u} (code : Code Label Value) : Prop :=
  ∃ (value : Value) (labels : List Label), Nonempty (Eval code labels value)

theorem finite_done {Label : Type} {Value : Type u} (value : Value) :
    Finite (.done (Label := Label) value) := ⟨value, [], ⟨.done⟩⟩

theorem finite_step {Label : Type} {Value : Type u} (label : Label)
    (next : Unit → Code Label Value) (rest : Finite (next ())) :
    Finite (.step label next) := by
  obtain ⟨value, labels, ⟨trace⟩⟩ := rest
  exact ⟨value, label :: labels, ⟨.step trace⟩⟩

theorem finite_bind {Label : Type} {Value : Type u} {Other : Type v}
    {code : Code Label Value} {next : Value → Code Label Other}
    (first : Finite code) (every : (value : Value) → Finite (next value)) :
    Finite (code.bind next) := by
  obtain ⟨value, labels, ⟨trace⟩⟩ := first
  obtain ⟨result, more, ⟨remaining⟩⟩ := every value
  exact ⟨result, labels ++ more, ⟨trace.bind remaining⟩⟩

theorem finite_complete {Label : Type} {Value : Type u} {code : Code Label Value}
    (ends : Finite code) :
    ∃ (fuel : Nat) (value : Value) (labels : List Label),
      runCtl fuel code = some (value, labels) := by
  obtain ⟨value, labels, ⟨trace⟩⟩ := ends
  exact ⟨labels.length, value, labels, ctl_complete trace labels.length (Nat.le_refl _)⟩

def Within {Label : Type} {Value : Type u} (code : Code Label Value) (bound : Nat) : Prop :=
  ∃ (value : Value) (labels : List Label), Nonempty (Eval code labels value) ∧ labels.length ≤ bound

theorem labels_append_length {Label : Type} (first second : List Label) :
    (first ++ second).length = first.length + second.length := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons head tail rest =>
      exact (congrArg Nat.succ rest).trans (Nat.succ_add _ _).symm

theorem within_done {Label : Type} {Value : Type u} (value : Value) :
    Within (.done (Label := Label) value) 0 := ⟨value, [], ⟨.done⟩, Nat.le_refl _⟩

theorem within_step {Label : Type} {Value : Type u} (label : Label)
    (next : Unit → Code Label Value) {bound} (rest : Within (next ()) bound) :
    Within (.step label next) (bound + 1) := by
  obtain ⟨value, labels, ⟨trace⟩, enough⟩ := rest
  exact ⟨value, label :: labels, ⟨.step trace⟩, Nat.succ_le_succ enough⟩

theorem within_weaken {Label : Type} {Value : Type u} {code : Code Label Value} {bound more}
    (first : Within code bound) (increase : bound ≤ more) : Within code more := by
  obtain ⟨value, labels, trace, enough⟩ := first
  exact ⟨value, labels, trace, Nat.le_trans enough increase⟩

theorem within_bind {Label : Type} {Value : Type u} {Other : Type v}
    {code : Code Label Value} {next : Value → Code Label Other} {bound more}
    (first : Within code bound) (every : (value : Value) → Within (next value) more) :
    Within (code.bind next) (bound + more) := by
  obtain ⟨value, labels, ⟨trace⟩, enough⟩ := first
  obtain ⟨result, remaining, ⟨after⟩, paid⟩ := every value
  exact ⟨result, labels ++ remaining, ⟨trace.bind after⟩,
    (labels_append_length labels remaining).symm ▸ Nat.add_le_add enough paid⟩

theorem within_complete {Label : Type} {Value : Type u} {code : Code Label Value} {bound}
    (bounded : Within code bound) : ∃ (value : Value) (labels : List Label),
      runCtl bound code = some (value, labels) := by
  obtain ⟨value, labels, ⟨trace⟩, enough⟩ := bounded
  exact ⟨value, labels, ctl_complete trace bound enough⟩

end ConstitutiveSearch.Agent.Local.Documentary.Control

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Result
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Result.observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Result.sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.runCtl
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.runCtl_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.ctl_sound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.ctl_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.ctl_mono
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Eval.unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.fuel_required
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.fuel_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Code.bind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Eval.bind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.finite_done
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.finite_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.finite_bind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.finite_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.Within
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.labels_append_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.within_done
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.within_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.within_weaken
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.within_bind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Control.within_complete
/- AXIOM_AUDIT_END -/
