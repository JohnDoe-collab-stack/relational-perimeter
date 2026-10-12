import Tests.LocalAlignment.DocumentaryControlFrontierApplicationSplit

/-! One opening produces the original entire Opening and its executable
preservation together. Tail, freshness, children and splitter are actually
produced once; the payload follows those same outputs into the next stage. -/
set_option genInjectivity false
set_option maxHeartbeats 15000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData ControlFrontierApplication

structure Produced (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) where
  opening : Actual (VariableMaster.openFrontier formula selected source)
  execution : ExecutablePreservation formula selected source opening.1.frontier
  preservationExact : execution.preservation = opening.1.preservation

def code (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Code Label (Produced formula selected source) :=
  .step .frontierCell (fun _ => match source with
    | [] => (identityCode formula selected []).bind (fun preservation =>
        .step .frontierPacket (fun _ =>
          let opening : Actual (VariableMaster.openFrontier formula selected []) :=
            ⟨⟨[], preservation.1.preservation⟩, by
              change VariableMaster.Opening.mk [] preservation.1.preservation = _
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
                ⟨ControlFrontierOpening.fromFresh parent rest tail.opening.1 fresh left right composed.1.preservation, by
                  obtain ⟨_, rightActual⟩ := right; cases rightActual
                  obtain ⟨_, leftActual⟩ := left; cases leftActual
                  obtain ⟨_, splitterActual⟩ := splitter; cases splitterActual
                  change VariableMaster.Opening.mk _ composed.1.preservation = _
                  rw [composed.2, prefixed.2, expanded.2, tail.preservationExact]
                  obtain ⟨tailOpening, tailExecution, tailPreservation⟩ := tail
                  obtain ⟨_, tailActual⟩ := tailOpening; cases tailActual
                  rw [VariableMaster.openFrontier, dif_pos (checked.2.symm.trans found)]⟩
              .done ⟨opening, composed.1, rfl⟩)))))))
        else
          (prependCode (head := parent) tail.execution).bind (fun prefixed =>
            .step .frontierPacket (fun _ =>
              let opening : Actual (VariableMaster.openFrontier formula selected (parent :: rest)) :=
                ⟨⟨parent :: tail.opening.1.frontier, prefixed.1.preservation⟩, by
                  change VariableMaster.Opening.mk _ prefixed.1.preservation = _
                  rw [prefixed.2, tail.preservationExact]
                  obtain ⟨tailOpening, tailExecution, tailPreservation⟩ := tail
                  obtain ⟨_, tailActual⟩ := tailOpening; cases tailActual
                  rw [VariableMaster.openFrontier, dif_neg (fun nativeTrue => found (checked.2.trans nativeTrue))]⟩
              .done ⟨opening, prefixed.1, rfl⟩)))))

def branchBound {formula : Cnf} (parent : GeneratedStructuralBranchContext formula) : Nat :=
  ControlFrontierOpening.childBound parent +
    (ControlFrontierOpening.childBound parent + (7 + (4 + (7 + (7 + 1)))))

def bound (formula : Cnf) (selected : Var) : VariableMaster.States formula → Nat
  | [] => (7 + 1) + 1
  | parent :: rest => (bound formula selected rest +
      (ControlFrontierOpening.freshnessBound parent.context.decisions + branchBound parent)) + 1

theorem bounded (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Within (code formula selected source) (bound formula selected source) := by
  induction source with
  | nil =>
      apply within_step; apply within_bind (more := 1) (identity_bounded formula selected []); intro preservation
      exact within_step _ _ (within_done _)
  | cons parent rest previous =>
      apply within_step; apply within_bind previous; intro tail
      apply within_bind (ControlFrontierOpening.freshness_bounded _ _); intro checked
      split
      · apply within_bind (ControlFrontierOpening.child_bounded _ _ _ _); intro left
        apply within_bind (ControlFrontierOpening.child_bounded _ _ _ _); intro right
        apply within_bind (prepend_bounded tail.execution); intro prefixed
        apply within_bind (ControlFrontierOpening.split_bounded _ _ _ _ _); intro splitter
        apply within_bind (expand_bounded _ _ _ _ _ _); intro expanded
        apply within_bind (more := 1) (trans_bounded prefixed.1 expanded.1); intro composed
        exact within_step _ _ (within_done _)
      · apply within_weaken (bound := 7 + 1)
        · apply within_bind (more := 1) (prepend_bounded tail.execution); intro prefixed
          exact within_step _ _ (within_done _)
        · exact Nat.le_trans (by decide : 8 ≤ 26)
            (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _))

theorem finite (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Finite (code formula selected source) := by
  obtain ⟨value, labels, trace, _⟩ := bounded formula selected source
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening.branchBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierExecutableOpening.finite
/- AXIOM_AUDIT_END -/
