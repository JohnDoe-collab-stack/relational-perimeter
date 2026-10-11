import Tests.LocalAlignment.DocumentaryControlFrontierOpening

/-! Evaluate the actual retained routing syntax into the complete original
preservation packet. Both maps and acceptance laws are retained. The paid
closures below are formed here; invoking their frontier maps or deferred
assignment readers is a distinct operation whose cost remains open. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation
open SAT Control ControlBindings ControlMasterData
universe uState uCompletion

/-- One explicit swap closure, instantiated in each direction. Keeping the
generic index order also keeps the original dependent match motive. -/
def swapFunction {system : SearchSystem} {first second : system.State} {rest : List system.State} :
    FrontierContinuation system (first :: second :: rest) →
      FrontierContinuation system (second :: first :: rest) :=
  fun frontier => match frontier with
    | .head received => .tail (.head received)
    | .tail (.head received) => .head received
    | .tail (.tail received) => .tail (.tail received)

def absorbFirstFunction {State : Type uState} {Completion : State → Type uCompletion}
    {first second : State} {rest : List State}
    (transport : ContinuationTransport Completion first second) :
    FrontierCompletion Completion (first :: second :: rest) →
      FrontierCompletion Completion (second :: rest) :=
  fun frontier => match frontier with
    | .head received => .head (transport.map received)
    | .tail received => received

def absorbSecondFunction {State : Type uState} {Completion : State → Type uCompletion}
    {first second : State} {rest : List State}
    (transport : ContinuationTransport Completion second first) :
    FrontierCompletion Completion (first :: second :: rest) →
      FrontierCompletion Completion (first :: rest) :=
  fun frontier => match frontier with
    | .head received => .head received
    | .tail (.head received) => .head (transport.map received)
    | .tail (.tail received) => .tail received

def swapCode {system : SearchSystem} {first second : system.State} {rest : List system.State} :
    Code Label (Actual (AcceptedFrontierPreservation.swapFirstTwo
      (system := system) (first := first) (second := second) (rest := rest))) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system (first :: second :: rest) (second :: first :: rest) :=
      { map := swapFunction (first := first) (second := second)
        preservesAccept := (AcceptingFrontierTransport.swapFirstTwo
          (system := system) (first := first) (second := second) (rest := rest)).preservesAccept }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system (second :: first :: rest) (first :: second :: rest) :=
        { map := swapFunction (first := second) (second := first)
          preservesAccept := (AcceptingFrontierTransport.swapFirstTwo
            (system := system) (first := second) (second := first) (rest := rest)).preservesAccept }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, by rfl⟩)))

theorem swap_bounded {system : SearchSystem} {first second : system.State} {rest : List system.State} :
    Within (swapCode (system := system) (first := first) (second := second) (rest := rest)) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def transportCode {formula : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext formula}
    (relation : GeneratedStructuralFlipAtRelation selected source target) :
    Code Label (Actual relation.toAcceptingTransport) :=
  .step .frontierEvaluationAtom (fun _ =>
    .step .controlClosure (fun _ =>
      let map : GeneratedStructuralBranchContinuation source → GeneratedStructuralBranchContinuation target :=
        fun continuation =>
          let assignment : Assignment := fun query =>
            if query = selected then !(continuation.1 query) else continuation.1 query
          have decisions : StructuralDecisionsHold assignment target.context.decisions :=
            (relation.mapContinuation continuation).2
          ⟨assignment, decisions⟩
      .step .formationWitness (fun _ =>
        let transport : AcceptingContinuationTransport (generatedStructuralBranchSystem formula) source target :=
          { map := map, preservesAccept := relation.mapContinuation_accept }
        .done ⟨transport, rfl⟩)))

theorem transport_bounded {formula : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext formula}
    (relation : GeneratedStructuralFlipAtRelation selected source target) :
    Within (transportCode selected relation) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def absorbFirstCode {system : SearchSystem} {first second : system.State} {rest : List system.State}
    (transport : AcceptingContinuationTransport system first second) :
    Code Label (Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport)) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system (first :: second :: rest) (second :: rest) :=
      { map := absorbFirstFunction ⟨transport.map⟩
        preservesAccept := (AcceptingFrontierTransport.absorbFirstIntoSecond (rest := rest) transport).preservesAccept }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system (second :: rest) (first :: second :: rest) :=
        { map := fun frontier => .tail frontier
          preservesAccept := (AcceptingFrontierTransport.includeAfterAbsorbFirst
            (system := system) (first := first) (second := second) (rest := rest)).preservesAccept }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, by rfl⟩)))

theorem absorb_first_bounded {system : SearchSystem} {first second : system.State} {rest : List system.State}
    (transport : AcceptingContinuationTransport system first second) :
    Within (absorbFirstCode (rest := rest) transport) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def absorbSecondCode {system : SearchSystem} {first second : system.State} {rest : List system.State}
    (transport : AcceptingContinuationTransport system second first) :
    Code Label (Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport)) :=
  .step .controlClosure (fun _ =>
    let forward : AcceptingFrontierTransport system (first :: second :: rest) (first :: rest) :=
      { map := absorbSecondFunction ⟨transport.map⟩
        preservesAccept := (AcceptingFrontierTransport.absorbSecondIntoFirst (rest := rest) transport).preservesAccept }
    .step .controlClosure (fun _ =>
      let backward : AcceptingFrontierTransport system (first :: rest) (first :: second :: rest) :=
        { map := fun frontier => match frontier with
            | .head received => .head received
            | .tail received => .tail (.tail received)
          preservesAccept := (AcceptingFrontierTransport.includeAfterAbsorbSecond
            (system := system) (first := first) (second := second) (rest := rest)).preservesAccept }
      .step .formationResources (fun _ => .done ⟨⟨forward, backward⟩, by rfl⟩)))

theorem absorb_second_bounded {system : SearchSystem} {first second : system.State} {rest : List system.State}
    (transport : AcceptingContinuationTransport system second first) :
    Within (absorbSecondCode (rest := rest) transport) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def code (formula : Cnf) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) →
    Code Label (Actual route.eval)
  | _, _, .identity source => .step .frontierEvaluationCell (fun _ =>
      (ControlFrontierOpening.identityCode (generatedStructuralBranchSystem formula) source).bind (fun actual =>
        .step .frontierEvaluationPacket (fun _ => .done actual)))
  | _, _, .swap => .step .frontierEvaluationCell (fun _ =>
      swapCode.bind (fun actual => .step .frontierEvaluationPacket (fun _ => .done actual)))
  | _, _, .absorbFirst relation => .step .frontierEvaluationCell (fun _ =>
      (transportCode selected relation).bind (fun transport =>
      (absorbFirstCode transport.1).bind (fun preservation =>
        .step .frontierEvaluationPacket (fun _ => .done ⟨preservation.1, by
          obtain ⟨_, actual⟩ := preservation; cases actual
          obtain ⟨_, actual⟩ := transport; cases actual
          rfl⟩))))
  | _, _, .absorbSecond relation => .step .frontierEvaluationCell (fun _ =>
      (transportCode selected relation).bind (fun transport =>
      (absorbSecondCode transport.1).bind (fun preservation =>
        .step .frontierEvaluationPacket (fun _ => .done ⟨preservation.1, by
          obtain ⟨_, actual⟩ := preservation; cases actual
          obtain ⟨_, actual⟩ := transport; cases actual
          rfl⟩))))
  | _, _, .prepend head child => .step .frontierEvaluationCell (fun _ =>
      (code formula selected child).bind (fun childPreservation =>
      (ControlFrontierOpening.prependCode (head := head) childPreservation.1).bind (fun prefixed =>
        .step .frontierEvaluationPacket (fun _ => .done ⟨prefixed.1, by
          obtain ⟨_, actual⟩ := prefixed; cases actual
          obtain ⟨_, actual⟩ := childPreservation; cases actual
          rfl⟩))))
  | _, _, .compose first second => .step .frontierEvaluationCell (fun _ =>
      (code formula selected first).bind (fun firstPreservation =>
      (code formula selected second).bind (fun secondPreservation =>
      (ControlFrontierOpening.transCode firstPreservation.1 secondPreservation.1).bind (fun composed =>
        .step .frontierEvaluationPacket (fun _ => .done ⟨composed.1, by
          obtain ⟨_, actual⟩ := composed; cases actual
          obtain ⟨_, actual⟩ := secondPreservation; cases actual
          obtain ⟨_, actual⟩ := firstPreservation; cases actual
          rfl⟩)))))

def bound (formula : Cnf) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target → Nat
  | _, _, .identity _ => (3 + 1) + 1
  | _, _, .swap => (3 + 1) + 1
  | _, _, .absorbFirst _ => (3 + (3 + 1)) + 1
  | _, _, .absorbSecond _ => (3 + (3 + 1)) + 1
  | _, _, .prepend _ child => (bound formula selected child + (3 + 1)) + 1
  | _, _, .compose first second => (bound formula selected first + (bound formula selected second + (3 + 1))) + 1

theorem bounded (formula : Cnf) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) →
    Within (code formula selected route) (bound formula selected route)
  | _, _, .identity source => by
      apply within_step; apply within_bind (ControlFrontierOpening.identity_bounded _ _); intro actual
      exact within_step _ _ (within_done _)
  | _, _, .swap => by
      apply within_step; apply within_bind swap_bounded; intro actual
      exact within_step _ _ (within_done _)
  | _, _, .absorbFirst relation => by
      apply within_step; apply within_bind (transport_bounded _ _); intro transport
      apply within_bind (more := 1) (absorb_first_bounded transport.1); intro preservation
      exact within_step _ _ (within_done _)
  | _, _, .absorbSecond relation => by
      apply within_step; apply within_bind (transport_bounded _ _); intro transport
      apply within_bind (more := 1) (absorb_second_bounded transport.1); intro preservation
      exact within_step _ _ (within_done _)
  | _, _, .prepend head child => by
      apply within_step; apply within_bind (bounded formula selected child); intro childPreservation
      apply within_bind (more := 1) (ControlFrontierOpening.prepend_bounded childPreservation.1); intro prefixed
      exact within_step _ _ (within_done _)
  | _, _, .compose first second => by
      apply within_step; apply within_bind (bounded formula selected first); intro firstPreservation
      apply within_bind (bounded formula selected second); intro secondPreservation
      apply within_bind (ControlFrontierOpening.trans_bounded firstPreservation.1 secondPreservation.1); intro composed
      exact within_step _ _ (within_done _)

theorem finite (formula : Cnf) (selected : Var)
    {source target : List (GeneratedStructuralBranchContext formula)}
    (route : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) :
    Finite (code formula selected route) := by
  obtain ⟨value, labels, trace, _⟩ := bounded formula selected route
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.swapFunction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.absorbFirstFunction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.absorbSecondFunction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.swapCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.swap_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.transportCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.transport_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.absorbFirstCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.absorb_first_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.absorbSecondCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.absorb_second_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierEvaluation.finite
/- AXIOM_AUDIT_END -/
