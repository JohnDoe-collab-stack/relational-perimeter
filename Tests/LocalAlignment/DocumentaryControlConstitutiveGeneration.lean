import Tests.LocalAlignment.DocumentaryControlMasterData
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalStage

/-! Construct the original free successor from the received positive source.
The inherited obstruction is read recursively; the same paid layer is used
in the target and its positive generation laws. No native whole generator
is used to construct the returned packet. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration
open StrongPerimetralTurning EndogenousDecomposition Control ControlBindings ControlMasterData

def advanceCode {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Code Label (Actual (advanceCursor cursor)) :=
  .step .controlInspect (fun _ => match cursor with
    | .within spine => .step .controlInspect (fun _ => match spine with
      | .boundary _ => .step .formationValues (fun _ => .done ⟨.beyond .first, rfl⟩)
      | .advance _ tail => .step .formationValues (fun _ => .done ⟨.within tail, rfl⟩))
    | .beyond tail => .step .formationValues (fun _ => .done ⟨.beyond (.next tail), rfl⟩))

theorem advance_bounded {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Within (advanceCode cursor) 3 := by
  apply within_step
  cases cursor with
  | within spine =>
    apply within_step
    cases spine <;> exact within_step _ _ (within_done _)
  | beyond tail =>
    exact within_weaken (within_step _ _ (within_done _)) (by decide)

def explicitCode {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Code Label (Actual (explicitAt cursor)) :=
  .step .controlInspect (fun _ => match cursor with
    | .within spine => .step .formationValues (fun _ => .done ⟨.source spine.startNode.explicit, rfl⟩)
    | .beyond tail => .step .formationValues (fun _ => .done ⟨.formed (.beyond tail), rfl⟩))

theorem explicit_bounded {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Within (explicitCode cursor) 2 := by
  apply within_step
  cases cursor <;> exact within_step _ _ (within_done _)

def compatibilityCode {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Code Label (Actual (stepCompatibleAt cursor)) :=
  .step .controlInspect (fun _ => match cursor with
    | .within spine => .step .controlInspect (fun _ => match spine with
      | .boundary node => .step .formationWitness (fun _ => .done ⟨.leaveBoundary node, rfl⟩)
      | .advance compatible _ => .step .formationWitness (fun _ => .done ⟨.source compatible, rfl⟩))
    | .beyond tail => .step .formationWitness (fun _ => .done ⟨.beyondAdvance tail, rfl⟩))

theorem compatibility_bounded {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Within (compatibilityCode cursor) 3 := by
  apply within_step
  cases cursor with
  | within spine =>
    apply within_step
    cases spine <;> exact within_step _ _ (within_done _)
  | beyond tail =>
    exact within_weaken (within_step _ _ (within_done _)) (by decide)

def successorCode {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Code Label (Actual (successorCompatibleExplicitation cursor)) :=
  (advanceCode cursor).bind (fun advanced =>
  (explicitCode advanced.1).bind (fun explicit =>
  (compatibilityCode cursor).bind (fun compatible =>
    .step .formationValues (fun _ =>
      let reading : ReturnedExplicit P := explicit.1
      have same : reading = explicitAt (advanceCursor cursor) := by
        change explicit.1 = _
        rw [explicit.2, advanced.2]
      let witness := Eq.rec (motive := fun e _ => ReturnedCompatible P (implicitAt cursor) e)
        compatible.1 same.symm
      .done ⟨⟨reading, witness⟩, by
        obtain ⟨_, actual⟩ := explicit; cases actual
        obtain ⟨_, actual⟩ := advanced; cases actual
        obtain ⟨_, actual⟩ := compatible; cases actual; rfl⟩))))

theorem successor_bounded {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Within (successorCode cursor) (3 + (2 + (3 + 1))) := by
  apply within_bind (advance_bounded cursor); intro advanced
  apply within_bind (explicit_bounded advanced.1); intro explicit
  apply within_bind (compatibility_bounded cursor); intro compatible
  exact within_step _ _ (within_done _)

def obstructionCode {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → (difference : BoundaryDifferenceCode P cursor) →
    Code Label (Actual difference.inheritedClosureObstruction)
  | _, .initial obstruction => .step .controlInspect (fun _ => .done ⟨obstruction, rfl⟩)
  | _, .afterFormation previous _ _ => .step .controlInspect (fun _ =>
      (obstructionCode previous).bind (fun actual => .done ⟨actual.1, actual.2⟩))

def obstructionBound {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → BoundaryDifferenceCode P cursor → Nat
  | _, .initial _ => 1
  | _, .afterFormation previous _ _ => obstructionBound previous + 1

theorem obstruction_bounded {P : CircularPresentation} {cursor : PerimeterCursor P}
    (difference : BoundaryDifferenceCode P cursor) :
    Within (obstructionCode difference) (obstructionBound difference) := by
  induction difference with
  | initial obstruction => exact within_step _ _ (within_done _)
  | afterFormation previous term same ih =>
    apply within_step
    apply within_weaken
    · exact within_bind (more := 0) ih (fun _ => within_done _)
    · exact Nat.le_of_eq (Nat.add_zero _)

def provenanceCode {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Code Label (Actual (provenanceAtCursor cursor)) :=
  .step .controlInspect (fun _ => match cursor with
    | .within spine => .step .formationWitness (fun _ => .done ⟨.source spine.startNode.provenance, rfl⟩)
    | .beyond tail => .step .formationWitness (fun _ => .done ⟨.free tail, rfl⟩))

theorem provenance_bounded {P : CircularPresentation} (cursor : PerimeterCursor P) :
    Within (provenanceCode cursor) 2 := by
  apply within_step
  cases cursor <;> exact within_step _ _ (within_done _)

def layerCode {P : CircularPresentation} (source : PositiveConstitution P) :
    Code Label (Actual (canonicalFreeLayer source)) :=
  (successorCode source.1).bind (fun successor =>
  (obstructionCode source.2.1.1).bind (fun obstruction =>
  (provenanceCode source.1).bind (fun provenance =>
    .step .formationValues (fun _ =>
      let core : FreeKCore P source.1 source.2.1.1 :=
        { formationTerm := .admissible successor.1
          formationTermIsSuccessor := congrArg FreeKAtom.admissible successor.2
          integratedClosureObstruction := obstruction.1
          integratedClosureObstructionIsCurrent := obstruction.2
          integratedProvenance := provenance.1
          integratedProvenanceIsCurrent := provenance.2 }
      .step .formationWitness (fun _ => .done ⟨⟨core⟩, by
        obtain ⟨_, actual⟩ := provenance; cases actual
        obtain ⟨_, actual⟩ := obstruction; cases actual
        obtain ⟨_, actual⟩ := successor; cases actual; rfl⟩)))))

def layerBound {P : CircularPresentation} (source : PositiveConstitution P) : Nat :=
  (3 + (2 + (3 + 1))) + (obstructionBound source.2.1.1 + (2 + 2))

theorem layer_bounded {P : CircularPresentation} (source : PositiveConstitution P) :
    Within (layerCode source) (layerBound source) := by
  apply within_bind (successor_bounded source.1); intro successor
  apply within_bind (obstruction_bounded source.2.1.1); intro obstruction
  apply within_bind (provenance_bounded source.1); intro provenance
  exact within_step _ _ (within_step _ _ (within_done _))

def targetCode {P : CircularPresentation} (source : PositiveConstitution P)
    (layer : Actual (canonicalFreeLayer source)) : Code Label (Actual (canonicalTarget source)) :=
  (advanceCode source.1).bind (fun advanced =>
    .step .formationValues (fun _ =>
      let difference : BoundaryDifferenceCode P (advanceCursor source.1) :=
        .afterFormation source.2.1.1 layer.1.core.formationTerm layer.1.core.formationTermIsSuccessor
      .step .formationWitness (fun _ =>
        let core := FreeConstitutionCore.formed source.2.1.2 layer.1.core
        .step .formationResources (fun _ =>
          let target : PositiveConstitution P :=
            ⟨advanced.1, Eq.rec (motive := fun cursor _ =>
              Σ data : FreeConstitution P cursor, BoundaryDifference P data)
              ⟨⟨difference, core⟩, .exact⟩ advanced.2.symm⟩
          .done ⟨target, by
            obtain ⟨_, actual⟩ := advanced; cases actual
            obtain ⟨_, actual⟩ := layer; cases actual; rfl⟩))))

theorem target_bounded {P : CircularPresentation} (source : PositiveConstitution P)
    (layer : Actual (canonicalFreeLayer source)) : Within (targetCode source layer) (3 + 3) := by
  apply within_bind (advance_bounded source.1); intro advanced
  exact within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def lawsCode {P : CircularPresentation} (source : PositiveConstitution P)
    (layer : Actual (canonicalFreeLayer source)) : Code Label (Actual (generatedStepOfFreeK source).laws) :=
  (compatibilityCode source.1).bind (fun compatible =>
    .step .formationWitness (fun _ =>
      let preservation : PreservesProvenance source (canonicalTarget source) :=
        { targetIsCanonical := rfl
          integrated := { layer := layer.1, targetIsFormation := by rw [layer.2]; rfl } }
      .step .formationWitness (fun _ =>
        let closure : IntegratesClosureObstruction source := ⟨rfl, rfl⟩
        .step .formationWitness (fun _ =>
          let continuation : ContinuesDifference source := ⟨rfl⟩
          .step .formationValues (fun _ =>
            let record : FormationRecord P (canonicalTarget source).2.1 :=
              Eq.rec (motive := fun layer _ => FormationRecord P
                (FreeConstitution.formed source.2.1 source.2.2 layer))
                (.current (layer := layer.1)) layer.2
            .step .formationWitness (fun _ =>
              let fresh : FreshBoundaryDifference source :=
                { continuation := continuation, freshRecord := record
                  freshRecordIsCurrent := by obtain ⟨_, actual⟩ := layer; cases actual; rfl
                  notPreservedOld := by
                    have same : record = currentRecordInCanonicalTarget source := by
                      obtain ⟨_, actual⟩ := layer; cases actual; rfl
                    rw [same]
                    exact (generatedStepOfFreeK source).laws.freshBoundaryDifference.notPreservedOld }
              .step .masterConstructionReturn (fun _ =>
                let laws : CanonicalGeneratedLaws source :=
                  { compatibility := compatible.1, compatibilityIsCanonical := compatible.2
                    preservesProvenance := preservation, integratesClosureObstruction := closure
                    continuesDifference := continuation, freshBoundaryDifference := fresh }
                .done ⟨laws, by
                  obtain ⟨_, actual⟩ := compatible; cases actual
                  obtain ⟨_, actual⟩ := layer; cases actual; rfl⟩)))))))

theorem laws_bounded {P : CircularPresentation} (source : PositiveConstitution P)
    (layer : Actual (canonicalFreeLayer source)) : Within (lawsCode source layer) (3 + 6) := by
  apply within_bind (compatibility_bounded source.1); intro compatible
  repeat apply within_step
  exact within_done _

def code {P : CircularPresentation} (source : PositiveConstitution P) :
    Code Label (Actual (generate source)) :=
  .step .masterNextStateGeneration (fun _ =>
    (layerCode source).bind (fun layer =>
    (targetCode source layer).bind (fun target =>
    (lawsCode source layer).bind (fun laws =>
      .step .masterConstructionReturn (fun _ => .done
        ⟨⟨target.1, ⟨target.2, laws.1⟩⟩, by
          obtain ⟨_, actual⟩ := laws; cases actual
          obtain ⟨_, actual⟩ := target; cases actual; rfl⟩)))))

def bound {P : CircularPresentation} (source : PositiveConstitution P) : Nat :=
  (layerBound source + ((3 + 3) + ((3 + 6) + 1))) + 1

theorem bounded {P : CircularPresentation} (source : PositiveConstitution P) :
    Within (code source) (bound source) := by
  apply within_step
  apply within_bind (layer_bounded source); intro layer
  apply within_bind (more := 10) (target_bounded source layer); intro target
  apply within_bind (more := 1) (laws_bounded source layer); intro laws
  exact within_step _ _ (within_done _)

def canonicalFromProduced {depth : Nat}
    (source : PositiveConstitution Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint)
    (produced : (target : PositiveConstitution Example.examplePresentation) × GeneratedStep source target)
    (actual : produced = generate source) : CanonicalStageGeneration depth :=
  { target := produced.1
    targetExact := by rw [actual]; cases sourceExact; rfl
    generated := Eq.rec (motive := fun received _ => GeneratedStep received produced.1) produced.2 sourceExact
    generateCalls := 1, generatedSteps := 1, provenanceUnits := 1, certificatesProduced := 1 }

theorem canonical_from_produced_actual {depth : Nat}
    (source : PositiveConstitution Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint)
    (produced : (target : PositiveConstitution Example.examplePresentation) × GeneratedStep source target)
    (actual : produced = generate source) :
    canonicalFromProduced source sourceExact produced actual = generateCanonicalStageFromSource source sourceExact := by
  cases actual; cases sourceExact; rfl

def canonicalCode {depth : Nat}
    (source : PositiveConstitution Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    Code Label (Actual (generateCanonicalStageFromSource source sourceExact)) :=
  (code source).bind (fun produced => .step .masterConstructionReturn (fun _ => .done
    ⟨canonicalFromProduced source sourceExact produced.1 produced.2,
      canonical_from_produced_actual _ _ _ _⟩))

theorem canonical_bounded {depth : Nat}
    (source : PositiveConstitution Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    Within (canonicalCode source sourceExact) (bound source + 1) := by
  apply within_bind (bounded source); intro produced
  exact within_step _ _ (within_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.advanceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.advance_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.explicitCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.explicit_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.compatibilityCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.compatibility_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.successorCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.successor_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.obstructionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.obstructionBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.obstruction_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.provenanceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.provenance_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.layerCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.layerBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.layer_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.targetCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.target_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.lawsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.laws_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.canonicalFromProduced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.canonical_from_produced_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.canonicalCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveGeneration.canonical_bounded
/- AXIOM_AUDIT_END -/
