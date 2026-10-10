import Tests.LocalAlignment.DocumentaryControlPermission
import Tests.LocalAlignment.DocumentaryControlResources

/-! Source checks inside the existing quotation master. Permission is searched
before reading the passage. The paid position and actual read feed the citation;
structural comparisons decide its received demand. Producer/search primitives
of the master and physical primitive costs remain separate boundaries. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlSelection
open Resources Control ControlBindings ControlPermission

def conjunction {P Q : Prop} : Decidable P → Decidable Q → Decidable (P ∧ Q)
  | .isTrue one, .isTrue two => .isTrue ⟨one, two⟩
  | .isFalse absent, _ => .isFalse (fun both => absent both.1)
  | _, .isFalse absent => .isFalse (fun both => absent both.2)

def originCode (demand : Demand) (item : Citation) :
    Code Label (Decidable (match demand.origin with
      | none => True | some position => item.position = position)) :=
  .step .citationOrigin (fun _ => match demand.origin with
    | none => .done (.isTrue True.intro)
    | some position => equalCode item.position position)

def originBound (demand : Demand) (item : Citation) : Nat :=
  (match demand.origin with
    | none => 0 | some position => (equalLabels item.position position).length) + 1

theorem origin_bounded (demand : Demand) (item : Citation) :
    Within (originCode demand item) (originBound demand item) := by
  apply within_step
  cases demand.origin with
  | none => exact within_done _
  | some position => exact ⟨_, _, ⟨equalTrace _ _⟩, Nat.le_refl _⟩

def meetsCode (demand : Demand) (item : Citation) : Code Label (Decidable (Meets demand item)) :=
  (equalCode item.passage.key demand.key).bind (fun key =>
    (equalCode item.passage.value demand.value).bind (fun value =>
      (originCode demand item).bind (fun origin =>
        .step .citationCheckResult (fun _ => .done (conjunction key (conjunction value origin))))))

def meetsBound (demand : Demand) (item : Citation) : Nat :=
  (equalLabels item.passage.key demand.key).length +
    ((equalLabels item.passage.value demand.value).length + (originBound demand item + 1))

theorem meets_bounded (demand : Demand) (item : Citation) :
    Within (meetsCode demand item) (meetsBound demand item) := by
  apply within_bind ⟨_, _, ⟨equalTrace _ _⟩, Nat.le_refl _⟩
  intro key
  apply within_bind ⟨_, _, ⟨equalTrace _ _⟩, Nat.le_refl _⟩
  intro value
  apply within_bind (origin_bounded demand item)
  intro origin
  exact within_step _ _ (within_done _)

abbrev Check {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) :=
  {checked : Selection.Checked sources contract demand origin //
    checked = Selection.check sources contract demand origin}

def absent {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context)
    (missing : resolvePermission contract.allowed origin.2.position = none) :
    Check sources contract demand origin :=
  ⟨.rejected (fun permission _ => resolvePermission_none _ _ missing permission), by
    unfold Selection.check
    split
    · rfl
    · rename_i permission found
      cases missing.symm.trans found⟩

def checkedFromDecision {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context)
    (permission : Ref contract.allowed origin.2.position)
    (found : resolvePermission contract.allowed origin.2.position = some permission)
    (decision : Decidable (Meets demand (sourceCitation sources origin))) :
    Check sources contract demand origin :=
  ⟨match decision with
    | .isTrue meets => .permitted permission meets
    | .isFalse wrong => .rejected (fun _ meets => wrong meets), by
    have agreed : decision = meetsDecision demand (sourceCitation sources origin) :=
      Subsingleton.elim _ _
    cases agreed
    unfold Selection.check
    cases meetsDecision demand (sourceCitation sources origin)
    all_goals
      dsimp only
      split
      · rename_i missing
        cases found.symm.trans missing
      · rename_i returned actual
        have same : returned = permission := Option.some.inj (actual.symm.trans found)
        cases same
        rfl⟩

def checkCode {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) : Code Label (Check sources contract demand origin) :=
  (locatedLookup contract.allowed origin.2).bind (fun located =>
    match found : located.2.1 with
    | none => .step .citationCheckResult (fun _ => .done (absent sources contract demand origin
        (located.2.2.symm.trans found)))
    | some permission => (ControlResources.readCode sources.values origin.2).bind (fun readout =>
        .step .citationReadout (fun _ =>
          let item : Citation := ⟨origin.1, located.1.1, readout.1⟩
          have same : item = sourceCitation sources origin := by
            change Citation.mk _ _ _ = Citation.mk _ _ _
            rw [located.1.2, readout.2]
            rfl
          (meetsCode demand item).bind (fun decision =>
            .step .citationCheckResult (fun _ => .done (checkedFromDecision sources contract demand origin
              permission (located.2.2.symm.trans found) (same ▸ decision)))))))

def checkBound {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) : Nat :=
  (ControlReference.positionBound origin.2 + lookupBound contract.allowed origin.2.position) +
    ((origin.2.position + 1) + ((meetsBound demand (sourceCitation sources origin) + 1) + 1))

theorem check_bounded {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) :
    Within (checkCode sources contract demand origin) (checkBound sources contract demand origin) := by
  apply within_bind (located_bounded contract.allowed origin.2)
  intro located
  split
  · exact within_weaken (within_step _ _ (within_done _)) (Nat.le_trans
      (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_add_left _ _))
  · apply within_bind (ControlResources.read_bounded _ _)
    intro readout
    apply within_step
    have same : (Citation.mk origin.1 located.1.1 readout.1) = sourceCitation sources origin := by
      change Citation.mk _ _ _ = Citation.mk _ _ _
      rw [located.1.2, readout.2]
      rfl
    apply within_bind (more := 1)
    · rw [same]
      exact meets_bounded demand _
    · intro decision
      exact within_step _ _ (within_done _)

theorem check_finite {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) : Finite (checkCode sources contract demand origin) := by
  obtain ⟨checked, labels, trace, _⟩ := check_bounded sources contract demand origin
  exact ⟨checked, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlSelection

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.conjunction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.originCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.originBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.origin_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.meetsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.meetsBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.meets_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.Check
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.absent
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.checkedFromDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.checkCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.checkBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.check_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSelection.check_finite
/- AXIOM_AUDIT_END -/
