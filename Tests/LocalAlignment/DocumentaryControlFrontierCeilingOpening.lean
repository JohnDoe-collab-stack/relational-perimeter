import Tests.LocalAlignment.DocumentaryControlFrontierCeilingComposition

/-! One opening produces the original entire Opening and its executable
preservation together. Tail, freshness, children and splitter are actually
produced once; the payload follows those same outputs into the next stage. -/
set_option genInjectivity false
set_option maxHeartbeats 15000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOpening
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData ControlFrontierCeilingApplication

structure Produced (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) where
  opening : Actual (VariableMaster.openFrontier formula selected source)
  execution : ExecutablePreservation formula selected source opening.1.frontier
  preservationExact : execution.original.preservation = opening.1.preservation

def code (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Code Label (Produced formula selected source) :=
  .step .frontierCell (fun _ => match source with
    | [] => (identityCode formula selected []).bind (fun preservation =>
        .step .frontierPacket (fun _ =>
          let opening : Actual (VariableMaster.openFrontier formula selected []) :=
            ⟨⟨[], preservation.1.original.preservation⟩, by
              change VariableMaster.Opening.mk [] preservation.1.original.preservation = _
              rw [preservation.2]; rfl⟩
          .done ⟨opening, preservation.1, rfl⟩))
    | parent :: rest => (code formula selected rest).bind (fun tail =>
      (ControlFrontierOpening.freshnessCode selected parent.context.decisions).bind (fun checked =>
        if found : checked.1 = true then
          let fresh := SAT.structuralDecisionsAvoid_of_check_true selected parent.context.decisions
            (checked.2.symm.trans found)
          (ControlFrontierOpening.childCode parent selected false fresh).bind (fun left =>
          (ControlFrontierOpening.childCode parent selected true fresh).bind (fun right =>
          (prependCode (head := parent) tail.execution).bind (fun prefixed =>
          (ControlFrontierOpening.splitCode parent selected fresh left right).bind (fun splitter =>
          (expandCode selected parent fresh left right splitter (rest := tail.opening.1.frontier)).bind (fun expanded =>
          (transCode prefixed.1 expanded.1).bind (fun composed =>
            .step .frontierPacket (fun _ =>
              let opening : Actual (VariableMaster.openFrontier formula selected (parent :: rest)) :=
                ⟨ControlFrontierOpening.fromFresh parent rest tail.opening.1 fresh left right composed.1.original.preservation, by
                  obtain ⟨_, rightActual⟩ := right; cases rightActual
                  obtain ⟨_, leftActual⟩ := left; cases leftActual
                  obtain ⟨_, splitterActual⟩ := splitter; cases splitterActual
                  change VariableMaster.Opening.mk _ composed.1.original.preservation = _
                  rw [composed.2, prefixed.2, expanded.2, tail.preservationExact]
                  obtain ⟨tailOpening, tailExecution, tailPreservation⟩ := tail
                  obtain ⟨_, tailActual⟩ := tailOpening; cases tailActual
                  rw [VariableMaster.openFrontier, dif_pos (checked.2.symm.trans found)]⟩
              .done ⟨opening, composed.1, rfl⟩)))))))
        else
          (prependCode (head := parent) tail.execution).bind (fun prefixed =>
            .step .frontierPacket (fun _ =>
              let opening : Actual (VariableMaster.openFrontier formula selected (parent :: rest)) :=
                ⟨⟨parent :: tail.opening.1.frontier, prefixed.1.original.preservation⟩, by
                  change VariableMaster.Opening.mk _ prefixed.1.original.preservation = _
                  rw [prefixed.2, tail.preservationExact]
                  obtain ⟨tailOpening, tailExecution, tailPreservation⟩ := tail
                  obtain ⟨_, tailActual⟩ := tailOpening; cases tailActual
                  rw [VariableMaster.openFrontier, dif_neg (fun nativeTrue => found (checked.2.trans nativeTrue))]⟩
              .done ⟨opening, prefixed.1, rfl⟩)))))


theorem finite (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Finite (code formula selected source) := by
  induction source with
  | nil =>
      apply finite_step
      apply finite_bind (identity_finite formula selected []); intro preservation
      exact finite_step _ _ (finite_done _)
  | cons parent rest previous =>
      apply finite_step; apply finite_bind previous; intro tail
      apply finite_bind (finite_of_within (ControlFrontierOpening.freshness_bounded _ _)); intro checked
      split
      · apply finite_bind (finite_of_within (ControlFrontierOpening.child_bounded _ _ _ _)); intro left
        apply finite_bind (finite_of_within (ControlFrontierOpening.child_bounded _ _ _ _)); intro right
        apply finite_bind (prepend_finite tail.execution); intro prefixed
        apply finite_bind (finite_of_within (ControlFrontierOpening.split_bounded _ _ _ _ _)); intro splitter
        apply finite_bind (expand_finite _ _ _ _ _ _); intro expanded
        apply finite_bind (trans_finite prefixed.1 expanded.1); intro composed
        exact finite_step _ _ (finite_done _)
      · apply finite_bind (prepend_finite tail.execution); intro prefixed
        exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOpening

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOpening.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOpening.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOpening.finite
/- AXIOM_AUDIT_END -/
