import Tests.LocalAlignment.DocumentaryControlSelection

/-! Actual extraction formation and readout. Paid source cells supply the new
values; the same producer and old formation constitute the new support. The
readout uses the paid source position and a paid read of that formed support. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCitation
open Resources Control ControlBindings

abbrev Action {context} (sources : Support SourceValue context) (origin : Location context) :=
  {action : Extraction sources origin // action = extract sources origin}

def extractCode {context} (sources : Support SourceValue context) (origin : Location context) :
    Code Label (Action sources origin) :=
  .step .citationProducer (fun _ =>
    let producer := extractionProducer origin.2
    (ControlResources.readCode sources.values origin.2).bind (fun readout =>
      .step .formationValues (fun _ =>
        let values : Values SourceValue (origin.1 :: context) := (readout.1, sources.values)
        .step .formationWitness (fun _ =>
          let positive := Formation.produced sources.formation producer
          let alignment : Formation SourceValue
              (context := origin.1 :: context)
              (producer.operation (producer.arguments sources.values), sources.values) =
              Formation SourceValue values := by
            obtain ⟨passage, actual⟩ := readout
            cases actual
            rfl
          let retained := alignment ▸ positive
          .step .formationResources (fun _ =>
            let resources : Support SourceValue (origin.1 :: context) := ⟨values, retained⟩
            .step .quotationProducer (fun _ =>
              .done ⟨extractionFromSupport sources origin resources (by
                  obtain ⟨passage, actual⟩ := readout
                  cases actual
                  rfl), extractionFromSupport_actual sources origin resources (by
                  obtain ⟨passage, actual⟩ := readout
                  cases actual
                  rfl)⟩))))))

def extractBound {context} (sources : Support SourceValue context) (origin : Location context) : Nat :=
  let _ := sources
  (origin.2.position + 1 + 4) + 1

theorem extract_bounded {context} (sources : Support SourceValue context) (origin : Location context) :
    Within (extractCode sources origin) (extractBound sources origin) := by
  apply within_step
  apply within_bind (more := 4) (ControlResources.read_bounded sources.values origin.2)
  intro readout
  apply within_step; apply within_step; apply within_step; apply within_step
  exact within_done _

abbrev Readout {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) := {item : Citation // item = action.citation}

def readoutCode {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : Code Label (Readout action) :=
  (ControlReference.positionCode origin.2).bind (fun position =>
    (ControlResources.readCode action.resources.values Ref.here).bind (fun passage =>
      .step .citationReadout (fun _ => .done ⟨⟨origin.1, position.1, passage.1⟩, by
        obtain ⟨position, actualPosition⟩ := position
        obtain ⟨passage, actualPassage⟩ := passage
        cases actualPosition
        cases actualPassage
        rfl⟩)))

def readoutBound {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : Nat :=
  let _ := action
  ControlReference.positionBound origin.2 + 2

theorem readout_bounded {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : Within (readoutCode action) (readoutBound action) := by
  apply within_bind (ControlReference.position_bounded origin.2)
  intro position
  apply within_bind (more := 1) (ControlResources.read_bounded action.resources.values Ref.here)
  intro passage
  exact within_step _ _ (within_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlCitation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.Action
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.extractCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.extractBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.extract_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.Readout
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.readoutCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.readoutBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCitation.readout_bounded
/- AXIOM_AUDIT_END -/
