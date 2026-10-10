import Tests.LocalAlignment.DocumentaryControlConstitutiveResources
import Tests.LocalAlignment.DocumentaryControlMasterDiscovery
import Tests.LocalAlignment.DocumentaryControlMasterApplication
import Tests.LocalAlignment.DocumentaryControlMasterDecomposition

/-! Open the same master resource chain. Every successor consumes the actual
support produced by its predecessor. Head and continuation share those
productions; the equality is on the whole original MasterHead. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead
open Resources EndogenousDecomposition Control ControlBindings ControlConstitutiveResources

def discoveryOperation {depth : Nat} {assignment : SequentialAssignment depth} {context : List MasterResources.Kind}
    (source : Ref context (.source depth assignment))
    (args : Values MasterResources.Value [.source depth assignment]) :
    Code Label (Operation (MasterResources.discover source) args) :=
  (ControlMasterDiscovery.code args.1.down).bind (fun actual => .done
    ⟨⟨⟨actual.1, actual.2⟩⟩, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩)

theorem discovery_finite {depth : Nat} {assignment : SequentialAssignment depth} {context : List MasterResources.Kind}
    (source : Ref context (.source depth assignment))
    (args : Values MasterResources.Value [.source depth assignment]) :
    Finite (discoveryOperation source args) := by
  apply finite_bind (ControlMasterDiscovery.finite args.1.down)
  intro actual
  exact finite_done _

def applicationOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state))
    (args : Values MasterResources.Value [.discovery state, .fresh state]) :
    Code Label (Operation (MasterResources.applyStage discovery fresh) args) :=
  (ControlMasterApplication.code state args.2.1.down.down args.1.down.1 args.1.down.2).bind
    (fun built => .done ⟨⟨built.1⟩, by obtain ⟨_, actual⟩ := built; cases actual; rfl⟩)

theorem application_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state))
    (args : Values MasterResources.Value [.discovery state, .fresh state]) : Finite (applicationOperation discovery fresh args) := by
  apply finite_bind (ControlMasterApplication.finite _ _ _ _); intro built; exact finite_done _

def decompositionOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state]) :
    Code Label (Operation (MasterResources.decompose past application) args) :=
  (ControlMasterDecomposition.code args.1.down (causalStageOfThreadedStage args.2.1.down.run)).bind
    (fun production => .done ⟨⟨production.1⟩, by obtain ⟨_, actual⟩ := production; cases actual; rfl⟩)

theorem decomposition_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state]) : Finite (decompositionOperation past application args) := by
  apply finite_bind (ControlMasterDecomposition.finite _ _); intro production; exact finite_done _

def assemblyOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {built : ConstructedThreadedStageRun state} {context : List MasterResources.Kind}
    (production : Ref context (.decomposition state past built))
    (args : Values MasterResources.Value [.decomposition state past built]) :
    Code Label (Operation (MasterResources.assemble production) args) :=
  .step .masterAssemble (fun _ => .done ⟨⟨⟨built.stage, built.run, args.1.down⟩⟩, rfl⟩)

def prefixOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (head : Ref context (.head state past)) (args : Values MasterResources.Value [.head state past]) :
    Code Label (Operation (MasterResources.headNextPrefix head) args) :=
  .step .masterNextPrefix (fun _ => .done ⟨⟨args.1.down.production.nextContext⟩, rfl⟩)

def sourceOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (head : Ref context (.head state past)) (args : Values MasterResources.Value [.head state past]) :
    Code Label (Operation (MasterResources.headNextSource head) args) :=
  .step .masterNextSource (fun _ => .done ⟨⟨args.1.down.run.nextRun.next⟩, rfl⟩)

def freshOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (head : Ref context (.head state past)) (fresh : Ref context (.fresh state))
    (args : Values MasterResources.Value [.head state past, .fresh state]) :
    Code Label (Operation (MasterResources.headNextFresh head fresh) args) :=
  .step .masterNextFresh (fun _ => .done ⟨⟨⟨args.1.down.run.nextRun.fresh args.2.1.down.down⟩⟩, rfl⟩)

abbrev Continued {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (fresh : Ref context (.fresh state)) :=
  {next : MasterResources.Cursor // next = (MasterResources.continueWithReferences support head fresh).1}

def continueCode {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (headRef : Ref context (.head state past))
    (freshRef : Ref context (.fresh state)) : Code Label (Continued support headRef freshRef) :=
  (ControlResources.readCode support.values headRef).bind (fun head =>
  .step .masterProducer (fun _ =>
    (extendCode support (MasterResources.headNextPrefix headRef) (prefixOperation headRef)).bind (fun prefixed =>
    .step .masterProducer (fun _ =>
      (extendCode prefixed.1 (MasterResources.headNextSource (.prior headRef))
        (sourceOperation (.prior headRef))).bind (fun sourced =>
      .step .masterProducer (fun _ =>
        (extendCode sourced.1 (MasterResources.headNextFresh (.prior (.prior headRef)) (.prior (.prior freshRef)))
          (freshOperation (.prior (.prior headRef)) (.prior (.prior freshRef)))).bind (fun freshened =>
        .step .masterNextCursor (fun _ =>
          let next : MasterResources.Cursor :=
            ⟨depth + 1, head.1.down.stage.next, _, freshened.1,
              (by obtain ⟨_, actual⟩ := freshened; cases actual
                  obtain ⟨_, actual⟩ := sourced; cases actual
                  obtain ⟨_, actual⟩ := prefixed; cases actual
                  obtain ⟨_, actual⟩ := head; cases actual
                  exact .prior .here),
              (by obtain ⟨_, actual⟩ := freshened; cases actual
                  obtain ⟨_, actual⟩ := sourced; cases actual
                  obtain ⟨_, actual⟩ := prefixed; cases actual
                  obtain ⟨_, actual⟩ := head; cases actual
                  exact .prior (.prior .here)),
              (by obtain ⟨_, actual⟩ := freshened; cases actual
                  obtain ⟨_, actual⟩ := sourced; cases actual
                  obtain ⟨_, actual⟩ := prefixed; cases actual
                  obtain ⟨_, actual⟩ := head; cases actual
                  exact .here)⟩
          .done ⟨next, by
            obtain ⟨_, actual⟩ := freshened; cases actual
            obtain ⟨_, actual⟩ := sourced; cases actual
            obtain ⟨_, actual⟩ := prefixed; cases actual
            obtain ⟨_, actual⟩ := head; cases actual; rfl⟩))))))))

theorem continue_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (fresh : Ref context (.fresh state)) : Finite (continueCode support head fresh) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded support.values head
    exact ⟨value, labels, trace⟩
  · intro head
    apply finite_step
    apply finite_bind (extend_finite _ _ _ (fun _ => finite_step _ _ (finite_done _))); intro prefixed
    apply finite_step
    apply finite_bind (extend_finite _ _ _ (fun _ => finite_step _ _ (finite_done _))); intro sourced
    apply finite_step
    apply finite_bind (extend_finite _ _ _ (fun _ => finite_step _ _ (finite_done _))); intro freshened
    exact finite_step _ _ (finite_done _)

def fromParts (cursor : MasterResources.Cursor)
    (head : CausalOperationalHead cursor.state cursor.context) (actualHead : head = cursor.head)
    (next : MasterResources.Cursor) (actualNext : next = VariableMaster.nextCursor cursor)
    (boundary : next.boundary =
      ⟨cursor.depth + 1, head.stage.next, head.run.nextRun.next, head.production.nextContext⟩) :
    VariableMaster.MasterHead cursor := by
  constructor
  · exact actualHead
  · exact actualNext
  · exact boundary

theorem fromParts_actual (cursor : MasterResources.Cursor)
    (head : CausalOperationalHead cursor.state cursor.context) (actualHead : head = cursor.head)
    (next : MasterResources.Cursor) (actualNext : next = VariableMaster.nextCursor cursor)
    (boundary : next.boundary =
      ⟨cursor.depth + 1, head.stage.next, head.run.nextRun.next, head.production.nextContext⟩) :
    fromParts cursor head actualHead next actualNext boundary = VariableMaster.masterHead cursor := by
  cases actualHead; cases actualNext; rfl

abbrev Head (cursor : MasterResources.Cursor) :=
  {head : VariableMaster.MasterHead cursor // head = VariableMaster.masterHead cursor}

def code (cursor : MasterResources.Cursor) : Code Label (Head cursor) :=
  .step .masterProducer (fun _ =>
    (extendCode cursor.support (MasterResources.discover cursor.source)
      (discoveryOperation cursor.source)).bind (fun discovered =>
    .step .masterProducer (fun _ =>
      (extendCode discovered.1 (MasterResources.applyStage .here (.prior cursor.fresh))
        (applicationOperation .here (.prior cursor.fresh))).bind (fun applied =>
      .step .masterProducer (fun _ =>
        (extendCode applied.1 (MasterResources.decompose (.prior (.prior cursor.past)) .here)
          (decompositionOperation (.prior (.prior cursor.past)) .here)).bind (fun decomposed =>
        .step .masterProducer (fun _ =>
          (extendCode decomposed.1 (MasterResources.assemble .here) (assemblyOperation .here)).bind (fun assembled =>
          (ControlResources.readCode assembled.1.values Ref.here).bind (fun head =>
          have pastExact :
              ((MasterResources.decompose (.prior (.prior cursor.past)) Ref.here).arguments applied.1.values).1.down =
                cursor.context := by
            obtain ⟨_, actual⟩ := applied; cases actual
            obtain ⟨_, actual⟩ := discovered; cases actual
            rfl
          let returnedHead : CausalOperationalHead cursor.state cursor.context :=
            Eq.rec (motive := fun past _ => CausalOperationalHead cursor.state past) head.1.down pastExact
          (continueCode assembled.1 Ref.here (.prior (.prior (.prior (.prior cursor.fresh))))).bind (fun next =>
            have actualHead : returnedHead = cursor.head := by
              obtain ⟨_, actual⟩ := head; cases actual
              obtain ⟨_, actual⟩ := assembled; cases actual
              obtain ⟨_, actual⟩ := decomposed; cases actual
              obtain ⟨_, actual⟩ := applied; cases actual
              obtain ⟨_, actual⟩ := discovered; cases actual; rfl
            have actualNext : next.1 = VariableMaster.nextCursor cursor := by
              obtain ⟨_, actual⟩ := next; cases actual
              obtain ⟨_, actual⟩ := assembled; cases actual
              obtain ⟨_, actual⟩ := decomposed; cases actual
              obtain ⟨_, actual⟩ := applied; cases actual
              obtain ⟨_, actual⟩ := discovered; cases actual; rfl
            have boundary : next.1.boundary =
                ⟨cursor.depth + 1, returnedHead.stage.next,
                  returnedHead.run.nextRun.next, returnedHead.production.nextContext⟩ := by
              rw [actualNext, actualHead]; rfl
            .step .masterHeadPacket (fun _ => .done
              ⟨fromParts cursor returnedHead actualHead next.1 actualNext boundary,
                fromParts_actual cursor returnedHead actualHead next.1 actualNext boundary⟩)))))))))))

theorem finite (cursor : MasterResources.Cursor) : Finite (code cursor) := by
  apply finite_step
  apply finite_bind (extend_finite _ _ _ (discovery_finite _))
  intro discovered
  apply finite_step
  apply finite_bind (extend_finite _ _ _ (application_finite _ _))
  intro applied
  apply finite_step
  apply finite_bind (extend_finite _ _ _ (decomposition_finite _ _))
  intro decomposed
  apply finite_step
  apply finite_bind (extend_finite _ _ _ (fun _ => finite_step _ _ (finite_done _)))
  intro assembled
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded assembled.1.values Ref.here
    exact ⟨value, labels, trace⟩
  · intro head
    apply finite_bind (continue_finite _ _ _)
    intro next
    apply finite_step
    exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.discoveryOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.discovery_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.applicationOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.application_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.decompositionOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.decomposition_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.assemblyOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.prefixOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.sourceOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.freshOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.Continued
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.continueCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.continue_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.fromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.Head
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.finite
/- AXIOM_AUDIT_END -/
