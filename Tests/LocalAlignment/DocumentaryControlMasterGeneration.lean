import Tests.LocalAlignment.DocumentaryControlMasterData
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.EndogenousDiscovery

/-! Construct the operational root and extract candidates from that same root.
Every recursive cell, list append and counter addition is controlled. -/
set_option genInjectivity false
set_option maxHeartbeats 6000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration
open Resources Control ControlBindings ControlMasterData EndogenousDecomposition SAT

def decoyCode (count : Nat) : Code Label (Actual (constructMeasuredDecoyClause count)) :=
  .step .masterConstructionCell (fun _ => match count with
    | 0 => .done ⟨⟨[], rfl, ⟨1, 0⟩⟩, rfl⟩
    | count + 1 => (decoyCode count).bind (fun tail =>
      .step .masterConstructionReturn (fun _ => .done
        ⟨⟨Literal.positive count :: tail.1.value,
            congrArg (List.cons (Literal.positive count)) tail.1.valueExact, tail.1.work.visit.visit⟩,
          by obtain ⟨_, actual⟩ := tail; cases actual; rfl⟩)))

theorem decoy_finite (count : Nat) : Finite (decoyCode count) := by
  induction count with
  | zero => exact finite_step _ _ (finite_done _)
  | succ count previous =>
    apply finite_step
    apply finite_bind previous
    intro tail
    exact finite_step _ _ (finite_done _)

def formulaCode (index : Nat) : Code Label (Actual (constructMeasuredFormula index)) :=
  (decoyCode (index + 1)).bind (fun decoys =>
    .step .masterConstructionCell (fun _ =>
      let selected := growingDiscoverySplitVar index
      let anchor := growingDiscoveryAnchorVar index
      (consCode (measuredLiteral (.positive anchor)) measuredEmptyList).bind (fun anchorPositive =>
      (consCode (measuredLiteral (.positive selected)) anchorPositive.1).bind (fun positive =>
      (consCode (measuredLiteral (.positive anchor)) measuredEmptyList).bind (fun anchorNegative =>
      (consCode (measuredLiteral (.negative selected)) anchorNegative.1).bind (fun negative =>
      (consCode negative.1 measuredEmptyList).bind (fun cnfNegative =>
      (consCode positive.1 cnfNegative.1).bind (fun cnfPositive =>
      (consCode decoys.1 cnfPositive.1).bind (fun formula => .done
        ⟨formula.1, by
          obtain ⟨_, actual⟩ := formula; cases actual
          obtain ⟨_, actual⟩ := cnfPositive; cases actual
          obtain ⟨_, actual⟩ := cnfNegative; cases actual
          obtain ⟨_, actual⟩ := negative; cases actual
          obtain ⟨_, actual⟩ := anchorNegative; cases actual
          obtain ⟨_, actual⟩ := positive; cases actual
          obtain ⟨_, actual⟩ := anchorPositive; cases actual
          obtain ⟨_, actual⟩ := decoys; cases actual; rfl⟩)))))))))

theorem formula_finite (index : Nat) : Finite (formulaCode index) := by
  apply finite_bind (decoy_finite (index + 1))
  intro decoys
  apply finite_step
  apply finite_bind (cons_finite _ _); intro anchorPositive
  apply finite_bind (cons_finite _ _); intro positive
  apply finite_bind (cons_finite _ _); intro anchorNegative
  apply finite_bind (cons_finite _ _); intro negative
  apply finite_bind (cons_finite _ _); intro cnfNegative
  apply finite_bind (cons_finite _ _); intro cnfPositive
  apply finite_bind (cons_finite _ _); intro formula
  exact finite_done _

def rootCode (index : Nat) : Code Label (Actual (constructMeasuredOperationalRoot index)) :=
  (formulaCode index).bind (fun formula => .step .masterConstructionReturn (fun _ =>
    let root := GeneratedStructuralBranchContext.root formula.1.value
    let indexed := Eq.rec (motive := fun received _ => GeneratedStructuralBranchContext received)
      root formula.1.valueExact
    .done ⟨⟨indexed, by
        obtain ⟨_, actual⟩ := formula; cases actual
        exact (constructMeasuredOperationalRoot index).valueExact, formula.1.work.visit⟩,
      by obtain ⟨_, actual⟩ := formula; cases actual; rfl⟩))

theorem root_finite (index : Nat) : Finite (rootCode index) := by
  apply finite_bind (formula_finite index)
  intro formula
  exact finite_step _ _ (finite_done _)

def clauseCode (clause : Clause) : Code Label (Actual (extractClauseCandidateRun clause)) :=
  .step .masterExtractionCell (fun _ => match clause with
    | [] => .done ⟨⟨[], ⟨0, 0, 0⟩⟩, rfl⟩
    | literal :: rest => (clauseCode rest).bind (fun tail =>
      .step .masterExtractionReturn (fun _ => .done
        ⟨⟨literal.candidateVariable :: tail.1.candidates,
            ⟨0, tail.1.stats.literalVisits + 1, tail.1.stats.candidatesEmitted + 1⟩⟩,
          by obtain ⟨_, actual⟩ := tail; cases actual; rfl⟩)))

theorem clause_finite (clause : Clause) : Finite (clauseCode clause) := by
  induction clause with
  | nil => exact finite_step _ _ (finite_done _)
  | cons literal rest previous =>
    apply finite_step; apply finite_bind previous; intro tail
    exact finite_step _ _ (finite_done _)

def extractionCode (formula : Cnf) : Code Label (Actual (extractCnfCandidateRun formula)) :=
  .step .masterExtractionCell (fun _ => match formula with
    | [] => .done ⟨⟨[], ⟨0, 0, 0⟩⟩, rfl⟩
    | clause :: rest => (clauseCode clause).bind (fun head =>
      (extractionCode rest).bind (fun tail =>
      (appendCode head.1.candidates tail.1.candidates).bind (fun candidates =>
      (ControlArithmetic.addCode head.1.stats.literalVisits tail.1.stats.literalVisits).bind (fun visits =>
      (ControlArithmetic.addCode head.1.stats.candidatesEmitted tail.1.stats.candidatesEmitted).bind (fun emitted =>
        .step .masterExtractionReturn (fun _ => .done
          ⟨⟨candidates.1, ⟨tail.1.stats.clauseVisits + 1, visits.1, emitted.1⟩⟩, by
            obtain ⟨_, actual⟩ := emitted; cases actual
            obtain ⟨_, actual⟩ := visits; cases actual
            obtain ⟨_, actual⟩ := candidates; cases actual
            obtain ⟨_, actual⟩ := tail; cases actual
            obtain ⟨_, actual⟩ := head; cases actual; rfl⟩)))))))

theorem extraction_finite (formula : Cnf) : Finite (extractionCode formula) := by
  induction formula with
  | nil => exact finite_step _ _ (finite_done _)
  | cons clause rest previous =>
    apply finite_step
    apply finite_bind (clause_finite clause); intro head
    apply finite_bind previous; intro tail
    apply finite_bind (append_finite head.1.candidates tail.1.candidates); intro candidates
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded head.1.stats.literalVisits tail.1.stats.literalVisits
      exact ⟨value, labels, trace⟩
    · intro visits
      apply finite_bind
      · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded head.1.stats.candidatesEmitted tail.1.stats.candidatesEmitted
        exact ⟨value, labels, trace⟩
      · intro emitted
        exact finite_step _ _ (finite_done _)

def code {depth : Nat} (generation : CanonicalStageGeneration depth)
    (seed : Nat) (seedActual : seed = generatedSearchSeed generation) :
    Code Label (Actual (measuredGeneratedExtractionFromSeed generation seed seedActual)) :=
  (rootCode seed).bind (fun realized =>
    let seedExact := seedActual.trans (generatedSearchSeed_exact generation)
    let indexed := Eq.rec (motive := fun index _ =>
      GeneratedStructuralBranchContext (distinctGrowingDiscoveryFormula index)) realized.1.value seedExact
    have rootExact : indexed = (constructStage (depth + 1)).operationalRoot := by
      cases seedExact
      exact realized.1.valueExact.trans (constructStage (depth + 1)).operationalRootExact.symm
    (extractionCode indexed.context.formula).bind (fun extracted =>
      .step .masterGeneration (fun _ => .done
        ⟨⟨indexed, rootExact, extracted.1, by
              rw [extracted.2, rootExact]; rfl, realized.1.work⟩, by
          obtain ⟨_, actual⟩ := extracted; cases actual
          obtain ⟨_, actual⟩ := realized; cases actual; rfl⟩)))

theorem finite {depth : Nat} (generation : CanonicalStageGeneration depth)
    (seed : Nat) (seedActual : seed = generatedSearchSeed generation) :
    Finite (code generation seed seedActual) := by
  apply finite_bind (root_finite seed)
  intro realized
  apply finite_bind (extraction_finite _)
  intro extracted
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.decoyCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.decoy_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.formulaCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.formula_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.rootCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.root_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.clauseCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.clause_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.extractionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.extraction_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterGeneration.finite
/- AXIOM_AUDIT_END -/
