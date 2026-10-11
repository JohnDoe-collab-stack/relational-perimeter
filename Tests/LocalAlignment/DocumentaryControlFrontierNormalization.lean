import Tests.LocalAlignment.DocumentaryControlFrontierNormalizationSearch

/-! The retained frontier and its complete routing syntax are constructed from
the actual comparison packets and recursive reductions. Each routing constructor
has its own paid formation. Evaluation of the routing syntax remains a later,
distinct invocation. -/
set_option genInjectivity false
set_option maxHeartbeats 7000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization
open SAT Control ControlBindings ControlMasterData

abbrev Inserted (formula : Cnf) (selected : Var) (state : GeneratedStructuralBranchContext formula)
    (rest : List (GeneratedStructuralBranchContext formula))
    (irreducible : SearchIrreducible (generatedStructuralFlipAtSearch formula selected) rest) :=
  Actual (insertAcceptedIntoIrreducible (generatedStructuralFlipAtSearch formula selected)
    (generatedStructuralFlipAtAction formula selected) state rest irreducible)

def insertCode (formula : Cnf) (selected : Var) (state : GeneratedStructuralBranchContext formula) :
    (rest : List (GeneratedStructuralBranchContext formula)) →
    (irreducible : SearchIrreducible (generatedStructuralFlipAtSearch formula selected) rest) →
    Code Label (Inserted formula selected state rest irreducible)
  | [], irreducible => .step .normalizationInsertCell (fun _ =>
      .step .normalizationCode (fun _ =>
        let route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected)
            [state] [state] := AcceptedFrontierCode.identity
              (action := generatedStructuralFlipAtAction formula selected) [state]
        .step .normalizationPacket (fun _ => .done ⟨{
          retained := [state]
          code := route
          irreducible := SearchIrreducible.singleton _ state
          retainedFromSource := fun candidate member => by
            cases member with
            | head => exact Or.inl rfl
            | tail _ impossible => cases impossible }, by rfl⟩)))
  | current :: tail, irreducible => .step .normalizationInsertCell (fun _ =>
      (ControlFrontierNormalizationSearch.classifyCode formula selected state current).bind (fun classification =>
        match classified : classification.1 with
        | .bidirectional forward _ _ _ =>
            .step .normalizationCode (fun _ =>
              let route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected)
                  (state :: current :: tail) (current :: tail) := .absorbFirst forward
              .step .normalizationPacket (fun _ => .done ⟨{
                retained := current :: tail
                code := route
                irreducible := irreducible
                retainedFromSource := fun _ member => Or.inr member }, by
                  unfold insertAcceptedIntoIrreducible
                  rw [← classification.2, classified]⟩))
        | .forwardOnly forward _ _ =>
            .step .normalizationCode (fun _ =>
              let route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected)
                  (state :: current :: tail) (current :: tail) := .absorbFirst forward
              .step .normalizationPacket (fun _ => .done ⟨{
                retained := current :: tail
                code := route
                irreducible := irreducible
                retainedFromSource := fun _ member => Or.inr member }, by
                  unfold insertAcceptedIntoIrreducible
                  rw [← classification.2, classified]⟩))
        | .backwardOnly backward _ _ =>
            (insertCode formula selected state tail irreducible.2).bind (fun recursive =>
              .step .normalizationCode (fun _ =>
                let absorption : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected)
                    (state :: current :: tail) (state :: tail) := .absorbSecond backward
                .step .normalizationCode (fun _ =>
                  let route := AcceptedFrontierCode.compose absorption recursive.1.code
                  .step .normalizationPacket (fun _ => .done ⟨{
                    retained := recursive.1.retained
                    code := route
                    irreducible := recursive.1.irreducible
                    retainedFromSource := fun candidate member => by
                      cases recursive.1.retainedFromSource candidate member with
                      | inl inserted => exact Or.inl inserted
                      | inr tailMember => exact Or.inr (List.mem_cons_of_mem current tailMember) }, by
                        unfold insertAcceptedIntoIrreducible
                        rw [← classification.2, classified]
                        obtain ⟨_, actual⟩ := recursive
                        cases actual
                        rfl⟩))))
        | .unresolved forwardNotFound backwardNotFound =>
            (insertCode formula selected state tail irreducible.2).bind (fun recursive =>
              .step .normalizationCode (fun _ =>
                let swap : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected)
                    (state :: current :: tail) (current :: state :: tail) := .swap
                .step .normalizationCode (fun _ =>
                  let prepended := AcceptedFrontierCode.prepend current recursive.1.code
                  .step .normalizationCode (fun _ =>
                    let route := AcceptedFrontierCode.compose swap prepended
                    .step .normalizationPacket (fun _ => .done ⟨{
                      retained := current :: recursive.1.retained
                      code := route
                      irreducible := ⟨by
                        intro other member
                        cases recursive.1.retainedFromSource other member with
                        | inl inserted =>
                            cases inserted
                            exact ⟨backwardNotFound, forwardNotFound⟩
                        | inr tailMember => exact irreducible.1 other tailMember,
                        recursive.1.irreducible⟩
                      retainedFromSource := fun candidate member => by
                        cases member with
                        | head => exact Or.inr List.mem_cons_self
                        | tail _ recursiveMember =>
                            cases recursive.1.retainedFromSource candidate recursiveMember with
                            | inl inserted => exact Or.inl inserted
                            | inr tailMember => exact Or.inr (List.mem_cons_of_mem current tailMember) }, by
                              unfold insertAcceptedIntoIrreducible
                              rw [← classification.2, classified]
                              obtain ⟨_, actual⟩ := recursive
                              cases actual
                              rfl⟩)))))))

abbrev Normalized (formula : Cnf) (selected : Var)
    (frontier : List (GeneratedStructuralBranchContext formula)) :=
  Actual (normalizeGeneratedStructuralFrontierByFlip formula selected frontier)

def code (formula : Cnf) (selected : Var) :
    (frontier : List (GeneratedStructuralBranchContext formula)) →
    Code Label (Normalized formula selected frontier)
  | [] => .step .normalizationCell (fun _ =>
      .step .normalizationCode (fun _ =>
        let route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) [] [] :=
          .identity []
        .step .normalizationPacket (fun _ => .done ⟨{
          retained := []
          code := route
          irreducible := SearchIrreducible.nil _ }, rfl⟩)))
  | state :: tail => .step .normalizationCell (fun _ =>
      (code formula selected tail).bind (fun tailReduction =>
      (insertCode formula selected state tailReduction.1.retained tailReduction.1.irreducible).bind (fun inserted =>
        .step .normalizationCode (fun _ =>
          let prepended := AcceptedFrontierCode.prepend state tailReduction.1.code
          .step .normalizationCode (fun _ =>
            let route := AcceptedFrontierCode.compose prepended inserted.1.code
            .step .normalizationPacket (fun _ => .done ⟨{
              retained := inserted.1.retained
              code := route
              irreducible := inserted.1.irreducible }, by
                obtain ⟨_, actual⟩ := tailReduction
                cases actual
                obtain ⟨_, actual⟩ := inserted
                cases actual
                rfl⟩))))))

theorem insert_length (formula : Cnf) (selected : Var) (state : GeneratedStructuralBranchContext formula)
    (rest : List (GeneratedStructuralBranchContext formula))
    (irreducible : SearchIrreducible (generatedStructuralFlipAtSearch formula selected) rest) :
    (insertAcceptedIntoIrreducible (generatedStructuralFlipAtSearch formula selected)
      (generatedStructuralFlipAtAction formula selected) state rest irreducible).retained.length ≤ rest.length + 1 := by
  induction rest with
  | nil => exact Nat.le_refl _
  | cons current tail recursive =>
      unfold insertAcceptedIntoIrreducible
      split
      · exact Nat.le_add_right _ 1
      · exact Nat.le_add_right _ 1
      · exact Nat.le_trans (recursive irreducible.2) (Nat.le_add_right _ 1)
      · exact Nat.succ_le_succ (recursive irreducible.2)

theorem retained_from_source (formula : Cnf) (selected : Var)
    (frontier : List (GeneratedStructuralBranchContext formula)) :
    ∀ state, state ∈ (normalizeGeneratedStructuralFrontierByFlip formula selected frontier).retained →
      state ∈ frontier := by
  induction frontier with
  | nil => intro state member; cases member
  | cons head tail recursive =>
      intro state member
      let tailReduction := normalizeGeneratedStructuralFrontierByFlip formula selected tail
      let inserted := insertAcceptedIntoIrreducible (generatedStructuralFlipAtSearch formula selected)
        (generatedStructuralFlipAtAction formula selected) head tailReduction.retained tailReduction.irreducible
      cases inserted.retainedFromSource state member with
      | inl same => cases same; exact List.mem_cons_self
      | inr tailMember => exact List.mem_cons_of_mem head (recursive state tailMember)

theorem retained_length (formula : Cnf) (selected : Var)
    (frontier : List (GeneratedStructuralBranchContext formula)) :
    (normalizeGeneratedStructuralFrontierByFlip formula selected frontier).retained.length ≤ frontier.length := by
  induction frontier with
  | nil => exact Nat.le_refl _
  | cons state tail recursive =>
      exact Nat.le_trans (insert_length formula selected state _ _)
        (Nat.add_le_add_right recursive 1)

def quota {formula : Cnf} : List (GeneratedStructuralBranchContext formula) → Nat
  | [] => 0
  | state :: tail => ControlFrontierNormalizationSearch.weight state + quota tail

theorem weight_within_quota {formula : Cnf} (frontier : List (GeneratedStructuralBranchContext formula)) :
    ∀ state, state ∈ frontier → ControlFrontierNormalizationSearch.weight state ≤ quota frontier := by
  induction frontier with
  | nil => intro state member; cases member
  | cons head tail recursive =>
      intro state member
      cases member with
      | head => exact Nat.le_add_right _ _
      | tail _ tailMember => exact Nat.le_trans (recursive state tailMember) (Nat.le_add_left _ _)

def insertBudget (quota : Nat) : Nat → Nat
  | 0 => 3
  | count + 1 => (ControlFrontierNormalizationSearch.pairQuota quota + (insertBudget quota count + 4)) + 1

theorem insert_budget_step (quota count : Nat) : insertBudget quota count ≤ insertBudget quota (count + 1) :=
  Nat.le_trans (Nat.le_add_right _ 4)
    (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ 1))

theorem insert_budget_mono (quota left right : Nat) (enough : left ≤ right) :
    insertBudget quota left ≤ insertBudget quota right := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step right enough recursive => exact Nat.le_trans recursive (insert_budget_step quota right)

theorem insert_bounded (formula : Cnf) (selected : Var) (state : GeneratedStructuralBranchContext formula)
    (rest : List (GeneratedStructuralBranchContext formula))
    (irreducible : SearchIrreducible (generatedStructuralFlipAtSearch formula selected) rest)
    (limit : Nat) (stateWithin : ControlFrontierNormalizationSearch.weight state ≤ limit)
    (restWithin : ∀ current, current ∈ rest → ControlFrontierNormalizationSearch.weight current ≤ limit) :
    Within (insertCode formula selected state rest irreducible) (insertBudget limit rest.length) := by
  induction rest with
  | nil => exact within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))
  | cons current tail recursive =>
      apply within_step
      apply within_bind (within_weaken (ControlFrontierNormalizationSearch.classify_bounded _ _ _ _)
        (ControlFrontierNormalizationSearch.classify_bound_quota _ _ limit stateWithin
          (restWithin current List.mem_cons_self)))
      intro classification
      split
      · apply within_weaken (bound := 2)
        · exact within_step _ _ (within_step _ _ (within_done _))
        · exact Nat.le_trans (Nat.le_add_left 2 2) (Nat.le_add_left 4 _)
      · apply within_weaken (bound := 2)
        · exact within_step _ _ (within_step _ _ (within_done _))
        · exact Nat.le_trans (Nat.le_add_left 2 2) (Nat.le_add_left 4 _)
      · apply within_bind (recursive irreducible.2 (fun current member =>
          restWithin current (List.mem_cons_of_mem _ member)))
        intro actual
        exact within_weaken (within_step _ _ (within_step _ _ (within_step _ _ (within_done _))))
          (Nat.le_add_right 3 1)
      · apply within_bind (recursive irreducible.2 (fun current member =>
          restWithin current (List.mem_cons_of_mem _ member)))
        intro actual
        exact within_step _ _ (within_step _ _ (within_step _ _ (within_step _ _ (within_done _))))

def budget (quota : Nat) : Nat → Nat
  | 0 => 3
  | count + 1 => (budget quota count + (insertBudget quota count + 3)) + 1

def bound (formula : Cnf) (_selected : Var) (frontier : List (GeneratedStructuralBranchContext formula)) : Nat :=
  budget (quota frontier) frontier.length

theorem bounded_with_quota (formula : Cnf) (selected : Var)
    (frontier : List (GeneratedStructuralBranchContext formula)) (limit : Nat)
    (allWithin : ∀ state, state ∈ frontier → ControlFrontierNormalizationSearch.weight state ≤ limit) :
    Within (code formula selected frontier) (budget limit frontier.length) := by
  induction frontier with
  | nil => exact within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))
  | cons state tail recursive =>
      apply within_step
      apply within_bind (recursive (fun current member => allWithin current (List.mem_cons_of_mem state member)))
      intro tailReduction
      apply within_bind (within_weaken
        (insert_bounded formula selected state tailReduction.1.retained tailReduction.1.irreducible limit
          (allWithin state List.mem_cons_self) (fun current member =>
            allWithin current (List.mem_cons_of_mem state
              (retained_from_source formula selected tail current (tailReduction.2 ▸ member)))))
        (insert_budget_mono limit _ tail.length (tailReduction.2.symm ▸ retained_length formula selected tail)))
      intro inserted
      exact within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

theorem bounded (formula : Cnf) (selected : Var) (frontier : List (GeneratedStructuralBranchContext formula)) :
    Within (code formula selected frontier) (bound formula selected frontier) :=
  bounded_with_quota formula selected frontier (quota frontier) (weight_within_quota frontier)

theorem finite (formula : Cnf) (selected : Var) (frontier : List (GeneratedStructuralBranchContext formula)) :
    Finite (code formula selected frontier) := by
  obtain ⟨value, labels, trace, _⟩ := bounded formula selected frontier
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.Inserted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.insertCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.Normalized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.insert_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.retained_from_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.retained_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.quota
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.weight_within_quota
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.insertBudget
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.insert_budget_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.insert_budget_mono
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.insert_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.budget
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.bounded_with_quota
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierNormalization.finite
/- AXIOM_AUDIT_END -/
