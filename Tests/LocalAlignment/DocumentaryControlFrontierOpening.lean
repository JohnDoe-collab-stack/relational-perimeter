import Tests.LocalAlignment.DocumentaryControlFrontierSyntax
import Tests.LocalAlignment.DocumentaryControlRoleFormation
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterExecution

/-! Actual frontier opening with its positive preservation retained. The tail
is opened first, freshness is read from the received decision history, and
the two child residuals feed the contexts whose original provenance is extended.
Each forward/backward transport is formed from those produced packets. Closure
formation is paid here; invoking the stored assignment/transport functions is
a separate deferred-execution obligation. No native whole opening is executed.
The syntax-dependent bound is local to this opening, not a D3 master envelope. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

abbrev Freshness (selected : Var) (decisions : List StructuralBranchDecision) :=
  Actual (structuralDecisionsAvoidCheck selected decisions)

def freshnessCode (selected : Var) (decisions : List StructuralBranchDecision) :
    Code Label (Freshness selected decisions) :=
  .step .frontierDecisionCell (fun _ => match decisions with
    | [] => .done ⟨true, rfl⟩
    | decision :: rest => (ControlPermission.equalCode decision.var selected).bind (fun checked =>
      match checked with
      | .isTrue same => .step .masterConstructionReturn (fun _ =>
          .done ⟨false, by rw [structuralDecisionsAvoidCheck, if_pos same]⟩)
      | .isFalse different => (freshnessCode selected rest).bind (fun tail =>
          .step .masterConstructionReturn (fun _ =>
            .done ⟨tail.1, by rw [structuralDecisionsAvoidCheck, if_neg different]; exact tail.2⟩))))

def freshnessBound : List StructuralBranchDecision → Nat
  | [] => 1
  | decision :: rest =>
      (ControlFrontierSyntax.equalBound decision.var + (freshnessBound rest + 1)) + 1

theorem freshness_bounded (selected : Var) (decisions : List StructuralBranchDecision) :
    Within (freshnessCode selected decisions) (freshnessBound decisions) := by
  induction decisions with
  | nil => exact within_step _ _ (within_done _)
  | cons decision rest previous =>
      apply within_step; apply within_bind (ControlFrontierSyntax.equal_bounded _ _)
      intro checked; cases checked with
      | isTrue same =>
          exact within_weaken (within_step _ _ (within_done _))
            (Nat.succ_le_succ (Nat.zero_le _))
      | isFalse different =>
          apply within_bind previous; intro tail
          exact within_step _ _ (within_done _)

def childCode {formula : Cnf} (parent : GeneratedStructuralBranchContext formula)
    (selected : Var) (value : Bool) (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    Code Label (Actual (parent.child selected value fresh)) :=
  (ControlFrontierSyntax.residualCode selected value parent.context.formula).bind (fun residual =>
    .step .formationValues (fun _ =>
      let context : StructuralBranchContext := ⟨residual.1.1, ⟨selected, value⟩ :: parent.context.decisions⟩
      have same : structuralChildContext parent.context selected value = context := by
        change StructuralBranchContext.mk (branchResidual parent.context.formula selected value) _ =
          StructuralBranchContext.mk residual.1.1 _
        rw [congrArg Sigma.fst residual.2]
      .step .formationWitness (fun _ =>
        let generated : StructuralGeneratedFrom formula context :=
          Eq.rec (motive := fun context _ => StructuralGeneratedFrom formula context)
            (.child parent.generated selected value fresh) same
        .step .frontierChild (fun _ => .done
          ⟨⟨context, generated⟩, by obtain ⟨_, actual⟩ := residual; cases actual; rfl⟩))))

def childBound {formula : Cnf} (parent : GeneratedStructuralBranchContext formula) : Nat :=
  ControlFrontierSyntax.residualBound parent.context.formula + (1 + (1 + 1))

theorem child_bounded {formula : Cnf} (parent : GeneratedStructuralBranchContext formula)
    (selected : Var) (value : Bool) (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    Within (childCode parent selected value fresh) (childBound parent) := by
  apply within_bind (ControlFrontierSyntax.residual_bounded _ _ _); intro residual
  repeat apply within_step
  exact within_done _

def identityCode (system : SearchSystem) (frontier : List system.State) :
    Code Label (Actual (AcceptedFrontierPreservation.identity system frontier)) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system frontier frontier :=
      { map := fun continuation => continuation, preservesAccept := fun _ accepted => accepted }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system frontier frontier :=
        { map := fun continuation => continuation, preservesAccept := fun _ accepted => accepted }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, rfl⟩)))

theorem identity_bounded (system : SearchSystem) (frontier : List system.State) :
    Within (identityCode system frontier) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def prependCode {system : SearchSystem} {head : system.State} {source target : List system.State}
    (preservation : AcceptedFrontierPreservation system source target) :
    Code Label (Actual (preservation.prepend (head := head))) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system (head :: source) (head :: target) :=
      { map := fun frontier => match frontier with
          | .head continuation => .head continuation
          | .tail continuation => .tail (preservation.forward.map continuation)
        preservesAccept := preservation.forward.prepend.preservesAccept }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system (head :: target) (head :: source) :=
        { map := fun frontier => match frontier with
            | .head continuation => .head continuation
            | .tail continuation => .tail (preservation.backward.map continuation)
          preservesAccept := preservation.backward.prepend.preservesAccept }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, rfl⟩)))

theorem prepend_bounded {system : SearchSystem} {head : system.State} {source target : List system.State}
    (preservation : AcceptedFrontierPreservation system source target) :
    Within (prependCode (head := head) preservation) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

abbrev Split {formula : Cnf} (parent : GeneratedStructuralBranchContext formula)
    (selected : Var) (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh)) :=
  {splitter : AcceptingExactBinarySplit (generatedStructuralBranchSystem formula) parent left.1 right.1 //
    HEq splitter (generatedStructuralSplit parent selected fresh)}

def splitCode {formula : Cnf} (parent : GeneratedStructuralBranchContext formula)
    (selected : Var) (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh)) :
    Code Label (Split parent selected fresh left right) :=
  .step .controlClosure (fun _ =>
    let split := ControlRoleFormation.splitFunction parent.context selected
    .step .controlClosure (fun _ =>
      let merge := ControlRoleFormation.mergeFunction (parent := parent.context) (selected := selected)
      .step .formationWitness (fun _ =>
        let splitter : AcceptingExactBinarySplit (generatedStructuralBranchSystem formula) parent
            (parent.child selected false fresh) (parent.child selected true fresh) :=
          { split := split, merge := merge
            splitMerge := (generatedStructuralSplit parent selected fresh).splitMerge
            mergeSplit := (generatedStructuralSplit parent selected fresh).mergeSplit
            splitPreservesAccept := (generatedStructuralSplit parent selected fresh).splitPreservesAccept
            mergePreservesAccept := (generatedStructuralSplit parent selected fresh).mergePreservesAccept }
        .step .formationResources (fun _ =>
          let actual : AcceptingExactBinarySplit (generatedStructuralBranchSystem formula) parent left.1 right.1 :=
            left.2.symm ▸ (right.2.symm ▸ splitter)
          .done ⟨actual, by
            obtain ⟨_, leftActual⟩ := left; cases leftActual
            obtain ⟨_, rightActual⟩ := right; cases rightActual
            exact HEq.rfl⟩))))

theorem split_bounded {formula : Cnf} (parent : GeneratedStructuralBranchContext formula)
    (selected : Var) (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh)) :
    Within (splitCode parent selected fresh left right) 4 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_step _ _ (within_done _))))

def expandCode {system : SearchSystem} {parent left right : system.State} {rest : List system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    Code Label (Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter)) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system (parent :: rest) (left :: right :: rest) :=
      { map := fun frontier => match frontier with
          | .head continuation => match splitter.split continuation with
              | .inl continuation => .head continuation
              | .inr continuation => .tail (.head continuation)
          | .tail continuation => .tail (.tail continuation)
        preservesAccept := (AcceptingFrontierTransport.expandHead splitter).preservesAccept }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system (left :: right :: rest) (parent :: rest) :=
        { map := fun frontier => match frontier with
            | .head continuation => .head (splitter.merge (.inl continuation))
            | .tail (.head continuation) => .head (splitter.merge (.inr continuation))
            | .tail (.tail continuation) => .tail continuation
          preservesAccept := (AcceptingFrontierTransport.contractExpandedHead splitter).preservesAccept }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, rfl⟩)))

theorem expand_bounded {system : SearchSystem} {parent left right : system.State} {rest : List system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    Within (expandCode (rest := rest) splitter) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def transCode {system : SearchSystem} {first second third : List system.State}
    (left : AcceptedFrontierPreservation system first second)
    (right : AcceptedFrontierPreservation system second third) :
    Code Label (Actual (left.trans right)) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system first third :=
      { map := fun continuation => right.forward.map (left.forward.map continuation)
        preservesAccept := (left.forward.trans right.forward).preservesAccept }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system third first :=
        { map := fun continuation => left.backward.map (right.backward.map continuation)
          preservesAccept := (right.backward.trans left.backward).preservesAccept }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, rfl⟩)))

theorem trans_bounded {system : SearchSystem} {first second third : List system.State}
    (left : AcceptedFrontierPreservation system first second)
    (right : AcceptedFrontierPreservation system second third) :
    Within (transCode left right) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def fromFresh {formula : Cnf} {selected : Var} (parent : GeneratedStructuralBranchContext formula)
    (rest : VariableMaster.States formula) (tail : VariableMaster.Opening formula rest)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) (parent :: rest)
      (left.1 :: right.1 :: tail.frontier)) :
    VariableMaster.Opening formula (parent :: rest) :=
  { frontier := left.1 :: right.1 :: tail.frontier
    preservation := preservation }

def code (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Code Label (Actual (VariableMaster.openFrontier formula selected source)) :=
  .step .frontierCell (fun _ => match source with
    | [] => (identityCode (generatedStructuralBranchSystem formula) []).bind (fun preservation =>
        .step .frontierPacket (fun _ => .done
          ⟨⟨[], preservation.1⟩, by obtain ⟨_, actual⟩ := preservation; cases actual; rfl⟩))
    | parent :: rest => (code formula selected rest).bind (fun tail =>
      (freshnessCode selected parent.context.decisions).bind (fun checked =>
        if found : checked.1 = true then
          let fresh := SAT.structuralDecisionsAvoid_of_check_true selected parent.context.decisions
            (checked.2.symm.trans found)
          (childCode parent selected false fresh).bind (fun left =>
          (childCode parent selected true fresh).bind (fun right =>
          (prependCode (head := parent) tail.1.preservation).bind (fun prefixed =>
          (splitCode parent selected fresh left right).bind (fun splitter =>
          (expandCode (rest := tail.1.frontier) splitter.1).bind (fun expanded =>
          (transCode prefixed.1 expanded.1).bind (fun composed =>
            .step .frontierPacket (fun _ => .done
              ⟨fromFresh parent rest tail.1 fresh left right composed.1, by
                obtain ⟨_, composedActual⟩ := composed; cases composedActual
                obtain ⟨_, expandedActual⟩ := expanded; cases expandedActual
                obtain ⟨_, prefixedActual⟩ := prefixed; cases prefixedActual
                obtain ⟨_, rightActual⟩ := right; cases rightActual
                obtain ⟨_, leftActual⟩ := left; cases leftActual
                obtain ⟨_, splitterActual⟩ := splitter; cases splitterActual
                obtain ⟨_, tailActual⟩ := tail; cases tailActual
                rw [VariableMaster.openFrontier, dif_pos (checked.2.symm.trans found)]
                rfl⟩)))))))
        else
          (prependCode (head := parent) tail.1.preservation).bind (fun prefixed =>
            .step .frontierPacket (fun _ => .done
              ⟨⟨parent :: tail.1.frontier, prefixed.1⟩, by
                obtain ⟨_, prefixedActual⟩ := prefixed; cases prefixedActual
                obtain ⟨_, tailActual⟩ := tail; cases tailActual
                rw [VariableMaster.openFrontier, dif_neg (fun nativeTrue => found (checked.2.trans nativeTrue))]⟩)))))

def branchBound {formula : Cnf} (parent : GeneratedStructuralBranchContext formula) : Nat :=
  childBound parent + (childBound parent + (3 + (4 + (3 + (3 + 1)))))

def bound (formula : Cnf) (_selected : Var) : VariableMaster.States formula → Nat
  | [] => (3 + 1) + 1
  | parent :: rest => (bound formula _selected rest + (freshnessBound parent.context.decisions + branchBound parent)) + 1

theorem bounded (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Within (code formula selected source) (bound formula selected source) := by
  induction source with
  | nil =>
      apply within_step; apply within_bind (identity_bounded _ _); intro preservation
      exact within_step _ _ (within_done _)
  | cons parent rest previous =>
      apply within_step; apply within_bind previous; intro tail
      apply within_bind (freshness_bounded _ _); intro checked
      split
      · apply within_bind (child_bounded _ _ _ _); intro left
        apply within_bind (child_bounded _ _ _ _); intro right
        apply within_bind (prepend_bounded _); intro prefixed
        apply within_bind (split_bounded _ _ _ _ _); intro splitter
        apply within_bind (expand_bounded _); intro expanded
        apply within_bind (trans_bounded _ _); intro composed
        exact within_step _ _ (within_done _)
      · apply within_weaken (bound := 3 + 1)
        · apply within_bind (prepend_bounded _); intro prefixed
          exact within_step _ _ (within_done _)
        · exact Nat.le_trans (Nat.add_le_add_left (Nat.le_add_right 1 12) 3)
            (Nat.le_add_left _ _)

theorem finite (formula : Cnf) (selected : Var) (source : VariableMaster.States formula) :
    Finite (code formula selected source) := by
  obtain ⟨value, labels, trace, _⟩ := bounded formula selected source
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.Freshness
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.freshnessCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.freshnessBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.freshness_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.childCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.childBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.child_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.identityCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.identity_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.prependCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.prepend_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.Split
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.splitCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.split_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.expandCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.expand_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.transCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.trans_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.fromFresh
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.branchBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierOpening.finite
/- AXIOM_AUDIT_END -/
