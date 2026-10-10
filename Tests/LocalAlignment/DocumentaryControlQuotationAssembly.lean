import Tests.LocalAlignment.DocumentaryControlConstitutiveResources

/-! Deposit and assemble the actual quotation packet. The new knowledge uses
the paid support, including its formation; no second quotation is executed. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly
open Resources Program Control ControlBindings ControlConstitutiveResources

variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification}

abbrev Quoted {kinds : List Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (output : Output sources contract) :=
  {after : Deduction.Knowledge sources contract rules (.quotation output.item :: kinds) //
    after = Deduction.quote knowledge output}

def quoteCode {kinds : List Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (output : Output sources contract) :
    Code Label (Quoted knowledge output) :=
  .step .quotationProducer (fun _ =>
    (extendCode knowledge.resources (Deduction.quotationProducer output)
      (fun _ => .step .integerSign (fun _ => .done ⟨Int.ofNat output.item.passage.value, rfl⟩))).bind (fun formed =>
      .step .assemblyKnowledge (fun _ =>
        let after : Deduction.Knowledge sources contract rules (.quotation output.item :: kinds) :=
          ⟨formed.1, by
            obtain ⟨_, actual⟩ := formed; cases actual
            exact fun ref => match ref with
              | .here => .quotation output.item output.evidence
              | .prior old => knowledge.valid old⟩
        .done ⟨after, by obtain ⟨_, actual⟩ := formed; cases actual; rfl⟩)))

theorem quote_finite {kinds : List Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (output : Output sources contract) :
    Finite (quoteCode knowledge output) := by
  apply finite_step
  apply finite_bind (extend_finite _ _ _ (fun _ => finite_step _ _ (finite_done _)))
  intro formed
  exact finite_step _ _ (finite_done _)

def fromParts (before : Frame sources contract rules slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task)
    (after : Deduction.Store sources contract rules)
    (afterActual : after = Deduction.ingest before.store produced.2)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (extensionActual : extension = (afterActual.symm ▸
      (match produced.2 with
      | .complete packet => Support.Extension.produced before.store.2.resources (Deduction.quotationProducer packet.output)
      | .blocked _ _ => Support.Extension.identity before.store.2.resources)))
    (output : Option (Occurrence after))
    (outputActual : output = (afterActual.symm ▸
      (match produced.2 with | .complete _ => some ⟨_, .here⟩ | .blocked _ _ => none)))
    (dossier : Dossier.State sources contract) (dossierActual : dossier = produced.next)
    (next : Frame sources contract rules (.quotation task.demand :: slots))
    (nextActual : next = assemble before dossier after extension output) :
    Step before (.quotation task) := by
  have previous : ∀ {oldSpec} (old : Ref slots oldSpec),
      next.bindings (.prior old) = (before.bindings old).map
        (transport before.store.2 next.store.2 (nextActual.symm ▸ extension)) := by
    cases nextActual; exact fun _ => rfl
  constructor
  · exact previous
  · cases nextActual; cases dossierActual; exact produced.depth
  · exact match produced.2 with | .complete _ => .quoted | .blocked _ _ => .refused
  · intro ready complete
    obtain ⟨stage, decision⟩ := produced
    cases decision with
    | complete packet =>
      have fresh : @Delivery context sources contract rules (.quotation task.demand) after output := by
        cases afterActual; cases outputActual
        exact ⟨⟨_, .here⟩, rfl, rfl, packet_output_meets packet⟩
      exact nextActual.symm ▸ (fun {spec} slot =>
        assemble_complete before dossier after extension output complete fresh slot)
    | blocked leftImpossible rightImpossible =>
      exact match ready with
      | .left permission meets => False.elim (leftImpossible permission meets)
      | .right permission meets => False.elim (rightImpossible permission meets)

theorem fromParts_actual (before : Frame sources contract rules slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task)
    (after : Deduction.Store sources contract rules)
    (afterActual : after = Deduction.ingest before.store produced.2)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (extensionActual : extension = (afterActual.symm ▸
      (match produced.2 with
      | .complete packet => Support.Extension.produced before.store.2.resources (Deduction.quotationProducer packet.output)
      | .blocked _ _ => Support.Extension.identity before.store.2.resources)))
    (output : Option (Occurrence after))
    (outputActual : output = (afterActual.symm ▸
      (match produced.2 with | .complete _ => some ⟨_, .here⟩ | .blocked _ _ => none)))
    (dossier : Dossier.State sources contract) (dossierActual : dossier = produced.next)
    (next : Frame sources contract rules (.quotation task.demand :: slots))
    (nextActual : next = assemble before dossier after extension output) :
    fromParts before task produced after afterActual extension extensionActual output outputActual
      dossier dossierActual next nextActual = quotationStep before task produced := by
  cases nextActual; cases dossierActual
  obtain ⟨stage, decision⟩ := produced
  cases decision <;> cases afterActual <;> cases extensionActual <;> cases outputActual <;> rfl

abbrev Packet (before : Frame sources contract rules slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) :=
  {step : Step before (.quotation task) // step = quotationStep before task produced}

def finishCode (before : Frame sources contract rules slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task)
    (after : Deduction.Store sources contract rules)
    (afterActual : after = Deduction.ingest before.store produced.2)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (extensionActual : extension = (afterActual.symm ▸
      (match produced.2 with
      | .complete packet => Support.Extension.produced before.store.2.resources (Deduction.quotationProducer packet.output)
      | .blocked _ _ => Support.Extension.identity before.store.2.resources)))
    (output : Option (Occurrence after))
    (outputActual : output = (afterActual.symm ▸
      (match produced.2 with | .complete _ => some ⟨_, .here⟩ | .blocked _ _ => none))) :
    Code Label (Packet before task produced) :=
  .step .assemblyDossier (fun _ =>
    let dossier : Dossier.State sources contract := match produced.2 with
      | .complete packet => ⟨produced.1.next, packet.result.1⟩
      | .blocked _ _ => ⟨produced.1.next, before.dossier.memory⟩
    have dossierActual : dossier = produced.next := by
      obtain ⟨stage, decision⟩ := produced
      cases decision <;> rfl
    .step .assemblyFrame (fun _ =>
      let next := assemble before dossier after extension output
      .step .assemblyPacket (fun _ => .done
        ⟨fromParts before task produced after afterActual extension extensionActual output outputActual
            dossier dossierActual next rfl,
          fromParts_actual before task produced after afterActual extension extensionActual output outputActual
            dossier dossierActual next rfl⟩)))

def code (before : Frame sources contract rules slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) : Code Label (Packet before task produced) :=
  match produced with
  | ⟨stage, .complete packet⟩ =>
    (quoteCode before.store.2 packet.output).bind (fun quoted =>
      .step .assemblyKind (fun _ =>
        let kind := Deduction.Kind.quotation packet.output.item
        .step .assemblyKinds (fun _ =>
          let kinds := kind :: before.store.1
          .step .assemblyStore (fun _ =>
            let after : Deduction.Store sources contract rules := ⟨kinds, quoted.1⟩
            have afterActual : after = Deduction.ingest before.store (.complete packet) := by
              obtain ⟨_, actual⟩ := quoted; cases actual; rfl
            .step .assemblyExtension (fun _ =>
              let extension : Support.Extension before.store.2.resources after.2.resources :=
                afterActual.symm ▸ Support.Extension.produced before.store.2.resources
                  (Deduction.quotationProducer packet.output)
              .step .assemblyOutput (fun _ =>
                let output : Option (Occurrence after) := some ⟨kind, .here⟩
                finishCode before task ⟨stage, .complete packet⟩ after afterActual extension rfl output
                  (by obtain ⟨_, actual⟩ := quoted; cases actual; rfl)))))))
  | ⟨stage, .blocked leftImpossible rightImpossible⟩ =>
    .step .assemblyExtension (fun _ =>
      let extension := Support.Extension.identity before.store.2.resources
      .step .assemblyOutput (fun _ =>
        finishCode before task ⟨stage, .blocked leftImpossible rightImpossible⟩ before.store rfl extension rfl none rfl))

theorem finite (before : Frame sources contract rules slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) : Finite (code before task produced) := by
  obtain ⟨stage, decision⟩ := produced
  cases decision with
  | complete packet =>
    apply finite_bind (quote_finite before.store.2 packet.output)
    intro quoted
    repeat apply finite_step
    exact finite_done _
  | blocked _ _ =>
    repeat apply finite_step
    exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.Quoted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.quoteCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.quote_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.fromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.finishCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlQuotationAssembly.finite
/- AXIOM_AUDIT_END -/
