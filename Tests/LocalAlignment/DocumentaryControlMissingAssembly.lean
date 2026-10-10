import Tests.LocalAlignment.DocumentaryControlBindings

/-! Missing-input assembly preserves the original failure and whole Step.
Extension, output, frame and packet are separate paid constructions. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly
open Resources Program Snapshot Control ControlBindings
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification}
  {left right : Specification}

def fromParts (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False)
    (extension : Support.Extension before.store.2.resources before.store.2.resources)
    (_extensionActual : extension = Support.Extension.identity before.store.2.resources)
    (output : Option (Occurrence before.store)) (_outputActual : output = none)
    (next : Frame sources contract rules (.conclusion demand :: slots))
    (nextActual : next = assemble before before.dossier before.store extension output) :
    Step before (.conclusion request leftSlot rightSlot demand) := by
  have previous : ∀ {oldSpec} (old : Ref slots oldSpec),
      next.bindings (.prior old) = (before.bindings old).map
        (transport before.store.2 next.store.2 (nextActual.symm ▸ extension)) := by
    cases nextActual; exact fun _ => rfl
  constructor
  · exact previous
  · cases nextActual; exact (Nat.add_zero _).symm
  · exact .missing
  · exact fun _ complete => False.elim (missing complete)

theorem fromParts_actual (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False)
    (extension : Support.Extension before.store.2.resources before.store.2.resources)
    (extensionActual : extension = Support.Extension.identity before.store.2.resources)
    (output : Option (Occurrence before.store)) (outputActual : output = none)
    (next : Frame sources contract rules (.conclusion demand :: slots))
    (nextActual : next = assemble before before.dossier before.store extension output) :
    fromParts before request leftSlot rightSlot demand missing extension extensionActual output outputActual next nextActual =
      missingStep before request leftSlot rightSlot demand missing := by
  cases nextActual; cases extensionActual; cases outputActual; rfl

abbrev Packet (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False) :=
  {step : Step before (.conclusion request leftSlot rightSlot demand) //
    step = missingStep before request leftSlot rightSlot demand missing}

def code (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False) :
    Code Label (Packet before request leftSlot rightSlot demand missing) :=
  .step .missingAssembly (fun _ =>
    .step .assemblyExtension (fun _ =>
      let extension := Support.Extension.identity before.store.2.resources
      .step .assemblyOutput (fun _ =>
        let output : Option (Occurrence before.store) := none
        .step .assemblyFrame (fun _ =>
          let next := assemble before before.dossier before.store extension output
          .step .assemblyPacket (fun _ => .done
            ⟨fromParts before request leftSlot rightSlot demand missing extension rfl output rfl next rfl,
              fromParts_actual before request leftSlot rightSlot demand missing extension rfl output rfl next rfl⟩)))))

theorem bounded (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False) :
    Within (code before request leftSlot rightSlot demand missing) 5 := by
  repeat apply within_step
  exact within_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly.fromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMissingAssembly.bounded
/- AXIOM_AUDIT_END -/
