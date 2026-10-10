import Tests.LocalAlignment.DocumentaryControlArithmetic
import Tests.LocalAlignment.DocumentaryControlPermission

/-! The actual master's provenance filter: paid natural comparisons, stable
source order, paid list constructors and controlled addition of visit counts.
The complete filter run, including rejected candidates and trace, is retained. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance
open EndogenousDecomposition SAT Control ControlBindings

abbrev Checked (candidate : Var) (provenance : List Var) :=
  {run : CandidateProvenanceCompatibilityRun candidate provenance //
    run = inspectCandidateProvenance candidate provenance}

def inspectCode (candidate : Var) (provenance : List Var) : Code Label (Checked candidate provenance) :=
  .step .masterProvenanceCell (fun _ => match provenance with
    | [] => .done ⟨⟨true, 0⟩, rfl⟩
    | prior :: rest => (ControlPermission.equalCode prior candidate).bind (fun compared =>
        match compared with
        | .isTrue same => .step .masterProvenanceReturn (fun _ => .done
            ⟨⟨false, 1⟩, by rw [inspectCandidateProvenance, if_pos same]⟩)
        | .isFalse different => (inspectCode candidate rest).bind (fun tail =>
            .step .masterProvenanceReturn (fun _ => .done
              ⟨⟨tail.1.compatible, tail.1.visits + 1⟩, by
                rw [inspectCandidateProvenance, if_neg different]
                obtain ⟨_, actual⟩ := tail
                cases actual; rfl⟩))))

def inspectBound (candidate : Var) : List Var → Nat
  | [] => 1
  | prior :: rest => ((ControlPermission.equalLabels prior candidate).length +
      (inspectBound candidate rest + 1)) + 1

theorem inspect_bounded (candidate : Var) (provenance : List Var) :
    Within (inspectCode candidate provenance) (inspectBound candidate provenance) := by
  induction provenance with
  | nil => exact within_step _ _ (within_done _)
  | cons prior rest previous =>
      apply within_step
      apply within_bind ⟨_, _, ⟨ControlPermission.equalTrace prior candidate⟩, Nat.le_refl _⟩
      intro compared
      cases compared with
      | isTrue same =>
          exact within_weaken (within_step _ _ (within_done _))
            (Nat.succ_le_succ (Nat.zero_le _))
      | isFalse different =>
          apply within_bind previous
          intro tail
          exact within_step _ _ (within_done _)

abbrev Filtered (provenance candidates : List Var) :=
  {run : CandidateProvenanceFilterRun provenance candidates //
    run = filterCandidatesByProvenance provenance candidates}

def filterCode (provenance candidates : List Var) : Code Label (Filtered provenance candidates) :=
  .step .masterFilterCell (fun _ => match candidates with
    | [] => .done ⟨⟨[], [], [], 0⟩, rfl⟩
    | candidate :: rest => (inspectCode candidate provenance).bind (fun checked =>
        (filterCode provenance rest).bind (fun tail =>
          (ControlArithmetic.addCode checked.1.visits tail.1.visits).bind (fun visits =>
            .step .masterFilterReturn (fun _ =>
              let produced : CandidateProvenanceFilterRun provenance (candidate :: rest) :=
                if checked.1.compatible then
                  ⟨candidate :: tail.1.retained, tail.1.rejected,
                    (candidate, true) :: tail.1.trace, visits.1⟩
                else
                  ⟨tail.1.retained, candidate :: tail.1.rejected,
                    (candidate, false) :: tail.1.trace, visits.1⟩
              .done ⟨produced, by
                obtain ⟨_, actualVisits⟩ := visits
                cases actualVisits
                obtain ⟨_, actualCheck⟩ := checked
                cases actualCheck
                obtain ⟨_, actualTail⟩ := tail
                cases actualTail
                rfl⟩)))))

theorem filter_finite (provenance candidates : List Var) : Finite (filterCode provenance candidates) := by
  induction candidates with
  | nil => exact finite_step _ _ (finite_done _)
  | cons candidate rest previous =>
      apply finite_step
      apply finite_bind
      · obtain ⟨value, labels, trace, _⟩ := inspect_bounded candidate provenance
        exact ⟨value, labels, trace⟩
      · intro checked
        apply finite_bind previous
        intro tail
        apply finite_bind
        · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded checked.1.visits tail.1.visits
          exact ⟨value, labels, trace⟩
        · intro visits
          exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.Checked
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.inspectCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.inspectBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.inspect_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.Filtered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.filterCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProvenance.filter_finite
/- AXIOM_AUDIT_END -/
