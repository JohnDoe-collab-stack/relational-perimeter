import Tests.LocalAlignment.DocumentaryControlRunner

/-! Positive administrative data. Paths retain every actual event and forwarding
count without retaining expired prototype callback wrappers. Constitutive output
data is retained whole. Model is the erased semantic link to the actual source;
its constructive refinement to the original positive Trace is a proof operation,
never a replay required by execution or by its consumer. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData
open Control ControlBindings ControlRunner
universe u

structure Output (Value : Type u) where
  value : Value
  labels : List Label

inductive Path where
  | done | stop
  | business (label : Label) (rest : Path)
  | administrative (event : Event) (forwards : Nat) (rest : Path)

structure RawRun (Value : Type u) where
  output : Option (Output Value)
  path : Path
  tape : Tape
  remaining : Nat

inductive Frame where
  | business (label : Label)
  | administrative (event : Event) (forwards : Nat)

abbrev Trail := List Frame

inductive Model {Value : Type u} :
    Code Label Value → Nat → Option (Output Value) → Path → Tape → Prop where
  | done {value fuel} : Model (.done value) fuel (some ⟨value, []⟩) .done doneTape
  | stop {label next} : Model (.step label next) 0 none .stop stopTape
  | businessNone {label next fuel path child} (rest : Model (next ()) fuel none path child) :
      Model (.step label next) (fuel + 1) none (.business label path)
        (combine (businessPrefix label) child failureSuffix)
  | businessSome {label next fuel path child value labels}
      (rest : Model (next ()) fuel (some ⟨value, labels⟩) path child) :
      Model (.step label next) (fuel + 1) (some ⟨value, label :: labels⟩) (.business label path)
        (combine (businessPrefix label) child businessSuffix)
  | adminNone {event next forwards fuel path child} (rest : Model (next ()) fuel none path child) :
      Model (.admin event next forwards) fuel none (.administrative event forwards path)
        (combine (adminPrefix event forwards) child failureSuffix)
  | adminSome {event next forwards fuel path child value labels}
      (rest : Model (next ()) fuel (some ⟨value, labels⟩) path child) :
      Model (.admin event next forwards) fuel (some ⟨value, labels⟩) (.administrative event forwards path)
        (combine (adminPrefix event forwards) child adminSuffix)

def observation {Value : Type u} {code : Code Label Value} {fuel} (output : Option (Result code fuel)) :=
  output.map (fun result => (⟨result.value, result.labels⟩ : Output Value))

theorem Model.refinement {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (realized : Model code fuel output path tape) :
    ∃ original : Option (Result code fuel), observation original = output ∧ Nonempty (Trace code fuel original tape) := by
  induction realized with
  | done => exact ⟨some (doneResult _ _), rfl, ⟨.done⟩⟩
  | stop => exact ⟨none, rfl, ⟨.stop⟩⟩
  | businessNone rest previous =>
    obtain ⟨original, agreement, ⟨trace⟩⟩ := previous
    cases original with
    | none => exact ⟨none, rfl, ⟨.businessNone trace⟩⟩
    | some actual => cases agreement
  | @businessSome label next fuel path child value labels rest previous =>
    obtain ⟨original, agreement, ⟨trace⟩⟩ := previous
    cases original with
    | none => cases agreement
    | some actual =>
      have same : (⟨actual.value, actual.labels⟩ : Output Value) = ⟨value, labels⟩ := Option.some.inj agreement
      have sameValue : actual.value = value := congrArg Output.value same
      have sameLabels : actual.labels = labels := congrArg Output.labels same
      exact ⟨some (ControlRunner.businessResult label next fuel actual),
        by change some (⟨actual.value, label :: actual.labels⟩ : Output Value) = some (⟨value, label :: labels⟩ : Output Value)
           rw [sameValue, sameLabels], ⟨.businessSome trace⟩⟩
  | adminNone rest previous =>
    obtain ⟨original, agreement, ⟨trace⟩⟩ := previous
    cases original with
    | none => exact ⟨none, rfl, ⟨.adminNone trace⟩⟩
    | some actual => cases agreement
  | @adminSome event next forwards fuel path child value labels rest previous =>
    obtain ⟨original, agreement, ⟨trace⟩⟩ := previous
    cases original with
    | none => cases agreement
    | some actual =>
      exact ⟨some (ControlRunner.adminResult event next fuel actual forwards), agreement, ⟨.adminSome trace⟩⟩

theorem Model.source_exact {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (realized : Model code fuel output path tape) :
    output = observation (Control.execute fuel code) := by
  obtain ⟨original, agreement, ⟨trace⟩⟩ := realized.refinement
  exact agreement.symm.trans (congrArg observation trace.source_exact)


def businessOutput {Value : Type u} (label : Label) (output : Option (Output Value)) : Option (Output Value) :=
  output.map (fun actual => ⟨actual.value, label :: actual.labels⟩)

def returnSource {Value : Type u} (frame : Frame) (child : RawRun Value) : RawRun Value :=
  match frame with
  | .business label =>
    let suffix := match child.output with | none => failureSuffix | some _ => businessSuffix
    ⟨businessOutput label child.output, .business label child.path,
      combine (businessPrefix label) child.tape suffix, child.remaining⟩
  | .administrative event forwards =>
    let suffix := match child.output with | none => failureSuffix | some _ => adminSuffix
    ⟨child.output, .administrative event forwards child.path,
      combine (adminPrefix event forwards) child.tape suffix, child.remaining⟩

@[noinline, export rp_documentary_owned_trail]
def ownedTrail (trail : Trail) : Trail := trail

def finishSource {Value : Type u} (trail : Trail) (child : RawRun Value) : RawRun Value :=
  match trail with
  | [] => child
  | frame :: rest => finishSource (ownedTrail rest) (returnSource frame child)
termination_by structural trail

def sourceDescend {Value : Type u} (code : Code Label Value) (fuel : Nat) (trail : Trail) : RawRun Value :=
  match code with
  | .done value => finishSource trail ⟨some ⟨value, []⟩, .done, doneTape, 0⟩
  | .step label next => match fuel with
    | 0 => finishSource trail ⟨none, .stop, stopTape, 0⟩
    | more + 1 => sourceDescend (next ()) more (.business label :: trail)
  | .admin event next forwards => sourceDescend (next ()) fuel (.administrative event forwards :: trail)
termination_by structural code

theorem source_complete {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (realized : Model code fuel output path tape) (trail : Trail) :
    sourceDescend code fuel trail = finishSource trail ⟨output, path, tape, 0⟩ := by
  induction realized generalizing trail with
  | done => rfl
  | stop => rfl
  | businessNone rest previous => rw [sourceDescend, previous]; rfl
  | businessSome rest previous => rw [sourceDescend, previous]; rfl
  | adminNone rest previous => rw [sourceDescend, previous]; rfl
  | adminSome rest previous => rw [sourceDescend, previous]; rfl

theorem Model.unique {Value : Type u} {code : Code Label Value} {fuel output path tape}
    (first : Model code fuel output path tape) {otherOutput otherPath otherTape}
    (second : Model code fuel otherOutput otherPath otherTape) :
    output = otherOutput ∧ path = otherPath ∧ tape = otherTape := by
  have same : (⟨output, path, tape, 0⟩ : RawRun Value) = ⟨otherOutput, otherPath, otherTape, 0⟩ :=
    (source_complete first []).symm.trans (source_complete second [])
  exact ⟨congrArg RawRun.output same, congrArg RawRun.path same, congrArg RawRun.tape same⟩

theorem has_model {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    ∃ output path tape, Model code fuel output path tape := by
  induction code generalizing fuel with
  | done value => exact ⟨_, _, _, .done⟩
  | step label next previous =>
    cases fuel with
    | zero => exact ⟨_, _, _, .stop⟩
    | succ fuel =>
      obtain ⟨output, path, tape, realized⟩ := previous () fuel
      cases output with
      | none => exact ⟨_, _, _, .businessNone realized⟩
      | some actual => exact ⟨_, _, _, .businessSome realized⟩
  | admin event next forwards previous =>
    obtain ⟨output, path, tape, realized⟩ := previous () fuel
    cases output with
    | none => exact ⟨_, _, _, .adminNone realized⟩
    | some actual => exact ⟨_, _, _, .adminSome realized⟩

theorem source_sound {Value : Type u} (code : Code Label Value) (fuel : Nat) :
    Model code fuel (sourceDescend code fuel []).output (sourceDescend code fuel []).path
      (sourceDescend code fuel []).tape := by
  obtain ⟨output, path, tape, realized⟩ := has_model code fuel
  rw [source_complete realized []]
  exact realized

end ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Path
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.RawRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Trail
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Model
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Model.refinement
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Model.source_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.Model.unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.businessOutput
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.returnSource
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.ownedTrail
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.finishSource
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.sourceDescend
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.source_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.has_model
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactData.source_sound
/- AXIOM_AUDIT_END -/
