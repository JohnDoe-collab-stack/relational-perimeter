import Tests.LocalAlignment.DocumentaryControlFrontierNormalizationSyntax

/-! The exact finder is opened into actual flips and paid comparisons. Both
directions are executed for classification. Their positive relation witnesses
and exact search equations feed the original certified classification packet. -/
set_option genInjectivity false
set_option maxHeartbeats 7000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch
open SAT Control ControlBindings ControlMasterData ControlFrontierNormalizationSyntax

abbrev Found (formula : Cnf) (selected : Var)
    (source target : GeneratedStructuralBranchContext formula) :=
  Actual ((generatedStructuralFlipAtSearch formula selected).find source target)

def findCode (formula : Cnf) (selected : Var) (source target : GeneratedStructuralBranchContext formula) :
    Code Label (Found formula selected source target) :=
  .step .normalizationSearch (fun _ =>
    (flipCnfCode selected source.context.formula).bind (fun flipped =>
    (cnfCode target.context.formula flipped.1).bind (fun compared => match compared with
      | .isFalse different => .step .normalizationPacket (fun _ => .done ⟨none, by
          change none = if formulaExact : target.context.formula = Cnf.flipAt selected source.context.formula then _ else _
          rw [dif_neg (fun same => different (same.trans flipped.2.symm))]⟩)
      | .isTrue same =>
          (flipHistoryCode selected source.context.decisions).bind (fun history =>
          (historyCode target.context.decisions history.1).bind (fun checked => match checked with
            | .isFalse different => .step .normalizationPacket (fun _ => .done ⟨none, by
                change none = if formulaExact : target.context.formula = Cnf.flipAt selected source.context.formula then _ else _
                rw [dif_pos (same.trans flipped.2)]
                rw [dif_neg (fun exact => different (exact.trans history.2.symm))]⟩)
            | .isTrue historiesSame => .step .formationWitness (fun _ =>
                let relation : GeneratedStructuralFlipAtRelation selected source target :=
                  ⟨same.trans flipped.2, historiesSame.trans history.2⟩
                .step .normalizationPacket (fun _ => .done ⟨some relation, by
                  change some relation = if formulaExact : target.context.formula = Cnf.flipAt selected source.context.formula then _ else _
                  rw [dif_pos (same.trans flipped.2), dif_pos (historiesSame.trans history.2)]⟩)))))))

def findBound {formula : Cnf} (source target : GeneratedStructuralBranchContext formula) : Nat :=
  (flipCnfBound source.context.formula + (cnfBound target.context.formula +
    (flipHistoryBound source.context.decisions + (historyBound target.context.decisions + (1 + 1))))) + 1

theorem find_bounded (formula : Cnf) (selected : Var) (source target : GeneratedStructuralBranchContext formula) :
    Within (findCode formula selected source target) (findBound source target) := by
  apply within_step; apply within_bind (flip_cnf_bounded _ _); intro flipped
  apply within_bind (cnf_bounded _ _); intro compared
  cases compared with
  | isFalse different =>
      apply within_weaken (bound := 1)
      · exact within_step _ _ (within_done _)
      · exact Nat.le_trans (Nat.le_add_left 1 1)
          (Nat.le_trans (Nat.le_add_left 2 _) (Nat.le_add_left _ _))
  | isTrue same =>
      apply within_bind (flip_history_bounded _ _); intro history
      apply within_bind (history_bounded _ _); intro checked
      cases checked with
      | isFalse different =>
          exact within_weaken (within_step _ _ (within_done _)) (Nat.succ_le_succ (Nat.zero_le _))
      | isTrue historiesSame => exact within_step _ _ (within_step _ _ (within_done _))

abbrev Classified (formula : Cnf) (selected : Var)
    (left right : GeneratedStructuralBranchContext formula) :=
  Actual ((generatedStructuralFlipAtSearch formula selected).classifyPairCertified left right)

def fromFound (formula : Cnf) (selected : Var) (left right : GeneratedStructuralBranchContext formula)
    (forward : Found formula selected left right) (backward : Found formula selected right left) :
    CertifiedPairSearchResult (generatedStructuralFlipAtSearch formula selected) left right :=
  match forwardFound : forward.1 with
  | some foundForward =>
      match backwardFound : backward.1 with
      | some foundBackward => .bidirectional foundForward foundBackward
          (forward.2.symm.trans forwardFound) (backward.2.symm.trans backwardFound)
      | none => .forwardOnly foundForward
          (forward.2.symm.trans forwardFound) (backward.2.symm.trans backwardFound)
  | none =>
      match backwardFound : backward.1 with
      | some foundBackward => .backwardOnly foundBackward
          (forward.2.symm.trans forwardFound) (backward.2.symm.trans backwardFound)
      | none => .unresolved (forward.2.symm.trans forwardFound) (backward.2.symm.trans backwardFound)

theorem from_found_actual (formula : Cnf) (selected : Var) (left right : GeneratedStructuralBranchContext formula)
    (forward : Found formula selected left right) (backward : Found formula selected right left) :
    fromFound formula selected left right forward backward =
      (generatedStructuralFlipAtSearch formula selected).classifyPairCertified left right := by
  obtain ⟨_, forwardActual⟩ := forward; cases forwardActual
  obtain ⟨_, backwardActual⟩ := backward; cases backwardActual
  unfold fromFound RelationSearch.classifyPairCertified
  split
  · rename_i forward forwardFound
    split
    · rename_i backward backwardFound
      split
      · rename_i forward' forwardFound'
        split
        · rename_i backward' backwardFound'
          cases Option.some.inj (forwardFound.symm.trans forwardFound')
          cases Option.some.inj (backwardFound.symm.trans backwardFound')
          rfl
        · rename_i backwardFound'
          cases backwardFound.symm.trans backwardFound'
      · rename_i forwardFound'
        cases forwardFound.symm.trans forwardFound'
    · rename_i backwardFound
      split
      · rename_i forward' forwardFound'
        split
        · rename_i backward' backwardFound'
          cases backwardFound.symm.trans backwardFound'
        · rename_i backwardFound'
          cases Option.some.inj (forwardFound.symm.trans forwardFound')
          rfl
      · rename_i forwardFound'
        cases forwardFound.symm.trans forwardFound'
  · rename_i forwardFound
    split
    · rename_i backward backwardFound
      split
      · rename_i forward' forwardFound'
        cases forwardFound.symm.trans forwardFound'
      · rename_i forwardFound'
        split
        · rename_i backward' backwardFound'
          cases Option.some.inj (backwardFound.symm.trans backwardFound')
          rfl
        · rename_i backwardFound'
          cases backwardFound.symm.trans backwardFound'
    · rename_i backwardFound
      split
      · rename_i forward' forwardFound'
        cases forwardFound.symm.trans forwardFound'
      · rename_i forwardFound'
        split
        · rename_i backward' backwardFound'
          cases backwardFound.symm.trans backwardFound'
        · rfl

def classifyCode (formula : Cnf) (selected : Var) (left right : GeneratedStructuralBranchContext formula) :
    Code Label (Classified formula selected left right) :=
  (findCode formula selected left right).bind (fun forward =>
  (findCode formula selected right left).bind (fun backward =>
    .step .normalizationPair (fun _ =>
      .step .formationWitness (fun _ => .done
        ⟨fromFound formula selected left right forward backward,
          from_found_actual formula selected left right forward backward⟩))))

def classifyBound {formula : Cnf} (left right : GeneratedStructuralBranchContext formula) : Nat :=
  findBound left right + (findBound right left + (1 + 1))

theorem classify_bounded (formula : Cnf) (selected : Var) (left right : GeneratedStructuralBranchContext formula) :
    Within (classifyCode formula selected left right) (classifyBound left right) := by
  apply within_bind (find_bounded _ _ _ _); intro forward
  apply within_bind (find_bounded _ _ _ _); intro backward
  exact within_step _ _ (within_step _ _ (within_done _))

def weight {formula : Cnf} (state : GeneratedStructuralBranchContext formula) : Nat :=
  flipCnfBound state.context.formula + (cnfBound state.context.formula +
    (flipHistoryBound state.context.decisions + (historyBound state.context.decisions + 3)))

theorem find_bound_weight {formula : Cnf} (source target : GeneratedStructuralBranchContext formula) :
    findBound source target ≤ weight source + weight target := by
  have historyPart : flipHistoryBound source.context.decisions + 1 ≤
      cnfBound source.context.formula +
        (flipHistoryBound source.context.decisions + (historyBound source.context.decisions + 3)) := by
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_left 1 2)
        (Nat.le_add_left 3 (historyBound source.context.decisions))) _)
      (Nat.le_add_left _ _)
  have sourcePart : flipCnfBound source.context.formula +
      (flipHistoryBound source.context.decisions + 1) ≤ weight source :=
    Nat.add_le_add_left historyPart _
  have targetPart : cnfBound target.context.formula +
      (historyBound target.context.decisions + 2) ≤ weight target := by
    exact Nat.le_trans
      (Nat.add_le_add_left
        (Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left 2 1) _)
          (Nat.le_add_left _ (flipHistoryBound target.context.decisions))) _)
      (Nat.le_add_left _ (flipCnfBound target.context.formula))
  have combined := Nat.add_le_add sourcePart targetPart
  simpa only [findBound, show 2 = 1 + 1 from rfl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

theorem classify_bound_weight {formula : Cnf} (left right : GeneratedStructuralBranchContext formula) :
    classifyBound left right ≤ (weight left + weight right) + ((weight right + weight left) + 2) :=
  Nat.add_le_add (find_bound_weight left right)
    (Nat.add_le_add_right (find_bound_weight right left) 2)

def pairQuota (quota : Nat) : Nat := (quota + quota) + ((quota + quota) + 2)

theorem classify_bound_quota {formula : Cnf} (left right : GeneratedStructuralBranchContext formula)
    (quota : Nat) (leftWithin : weight left ≤ quota) (rightWithin : weight right ≤ quota) :
    classifyBound left right ≤ pairQuota quota :=
  Nat.le_trans (classify_bound_weight left right)
    (Nat.add_le_add (Nat.add_le_add leftWithin rightWithin)
      (Nat.add_le_add_right (Nat.add_le_add rightWithin leftWithin) 2))

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.Found
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.findCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.findBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.find_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.Classified
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.fromFound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.from_found_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.classifyCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.classifyBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.classify_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.weight
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.find_bound_weight
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.classify_bound_weight
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.pairQuota
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalizationSearch.classify_bound_quota
/- AXIOM_AUDIT_END -/
