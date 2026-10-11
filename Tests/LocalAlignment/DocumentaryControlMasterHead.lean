import Tests.LocalAlignment.DocumentaryControlConstitutiveResources
import Tests.LocalAlignment.DocumentaryControlMasterDiscovery
import Tests.LocalAlignment.DocumentaryControlMasterApplication
import Tests.LocalAlignment.DocumentaryControlMasterDecomposition

/-! Open the same master resource chain. Every successor consumes the actual
support produced by its predecessor. Head and continuation share those
productions; the equality is on the whole original MasterHead. -/
set_option genInjectivity false
set_option maxHeartbeats 32000000
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
  (ControlRoleFormation.endpointsCode args.2.1.down.run).bind (fun endpoints =>
    (ControlMasterDecomposition.code args.1.down (causalStageOfThreadedStage args.2.1.down.run)
      endpoints.1).bind
      (fun production => .done ⟨⟨production.1⟩, by obtain ⟨_, actual⟩ := production; cases actual; rfl⟩))

theorem decomposition_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state]) : Finite (decompositionOperation past application args) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlRoleFormation.endpoints_bounded args.2.1.down.run
    exact ⟨value, labels, trace⟩
  · intro endpoints
    apply finite_bind (ControlMasterDecomposition.finite _ _ _); intro production; exact finite_done _

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

def discoveryKind {depth : Nat} {assignment : SequentialAssignment depth} {context : List MasterResources.Kind}
    (source : Ref context (.source depth assignment))
    (args : Values MasterResources.Value [.source depth assignment]) :
    Code Label {kind // kind = (MasterResources.discover source).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.discovery args.1.down, rfl⟩)

def applicationKind {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state))
    (args : Values MasterResources.Value [.discovery state, .fresh state]) :
    Code Label {kind // kind = (MasterResources.applyStage discovery fresh).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.application state, rfl⟩)

def decompositionKind {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state]) :
    Code Label {kind // kind = (MasterResources.decompose past application).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.decomposition state args.1.down args.2.1.down, rfl⟩)

def assemblyKind {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {built : ConstructedThreadedStageRun state} {context : List MasterResources.Kind}
    (production : Ref context (.decomposition state past built))
    (args : Values MasterResources.Value [.decomposition state past built]) :
    Code Label {kind // kind = (MasterResources.assemble production).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.head state past, rfl⟩)

def prefixKind {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (head : Ref context (.head state past)) (args : Values MasterResources.Value [.head state past]) :
    Code Label {kind // kind = (MasterResources.headNextPrefix head).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.prefix args.1.down.run.nextRun.next, rfl⟩)

def sourceKind {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (head : Ref context (.head state past)) (args : Values MasterResources.Value [.head state past]) :
    Code Label {kind // kind = (MasterResources.headNextSource head).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.source (depth + 1) args.1.down.stage.next, rfl⟩)

def freshKind {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (head : Ref context (.head state past)) (fresh : Ref context (.fresh state))
    (args : Values MasterResources.Value [.head state past, .fresh state]) :
    Code Label {kind // kind = (MasterResources.headNextFresh head fresh).outputKind args} :=
  .step .producerOutputKind (fun _ => .done ⟨.fresh args.1.down.run.nextRun.next, rfl⟩)

def pastAt (cursor : MasterResources.Cursor)
    (source : Arguments (MasterResources.discover cursor.source).inputs cursor.support.values) :
    Ref cursor.kinds (.prefix source.1.1.down) :=
  retargetRef cursor.past (by rw [source.2]; rfl)

def freshAt (cursor : MasterResources.Cursor)
    (source : Arguments (MasterResources.discover cursor.source).inputs cursor.support.values) :
    Ref cursor.kinds (.fresh source.1.1.down) :=
  retargetRef cursor.fresh (by rw [source.2]; rfl)

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
    (cachedCode support (MasterResources.headNextPrefix headRef)
      (prefixKind headRef) (prefixOperation headRef)).bind (fun prefixed =>
    .step .masterProducer (fun _ =>
      let sourceHead := retainedPrior prefixed.kind headRef
      (cachedCode prefixed.after (MasterResources.headNextSource sourceHead)
        (sourceKind sourceHead) (sourceOperation sourceHead)).bind (fun sourced =>
      .step .masterProducer (fun _ =>
        let freshHead := retainedPrior sourced.kind sourceHead
        let freshInput := retainedPrior sourced.kind (retainedPrior prefixed.kind freshRef)
        (cachedCode sourced.after (MasterResources.headNextFresh freshHead freshInput)
          (freshKind freshHead freshInput) (freshOperation freshHead freshInput)).bind (fun freshened =>
        .step .masterNextCursor (fun _ =>
          have prefixedHead : prefixed.args.1.1 = head.1 :=
            (congrArg Prod.fst prefixed.args.2).trans head.2.symm
          have sourcedHead : sourced.args.1.1 = head.1 :=
            (congrArg Prod.fst sourced.args.2).trans
              ((prefixed.read_prior headRef).trans head.2.symm)
          have freshenedHead : freshened.args.1.1 = head.1 :=
            (congrArg Prod.fst freshened.args.2).trans
              ((sourced.read_prior sourceHead).trans
                ((prefixed.read_prior headRef).trans head.2.symm))
          let actualSource := retainedPrior freshened.kind sourced.here
          let actualPast := retainedPrior freshened.kind (retainedPrior sourced.kind prefixed.here)
          let actualFresh := freshened.here
          have sourceRead : freshened.after.read actualSource =
              (⟨sourced.args.1.1.down.run.nextRun.next⟩ : MasterResources.Value
                (.source (depth + 1) sourced.args.1.1.down.stage.next)) :=
            (freshened.read_prior sourced.here).trans sourced.read_here
          let next : MasterResources.Cursor :=
            ⟨depth + 1, sourced.args.1.1.down.stage.next, _, freshened.after, actualSource,
              retargetRef actualPast (by
                change MasterResources.Kind.prefix prefixed.args.1.1.down.run.nextRun.next =
                  .prefix (freshened.after.read actualSource).down
                rw [sourceRead, prefixedHead, sourcedHead]),
              retargetRef actualFresh (by
                change MasterResources.Kind.fresh freshened.args.1.1.down.run.nextRun.next =
                  .fresh (freshened.after.read actualSource).down
                rw [sourceRead, freshenedHead, sourcedHead])⟩
          .done ⟨next, by
            cases freshened.exact
            cases sourced.exact
            cases prefixed.exact
            obtain ⟨_, ah⟩ := head; cases ah
            rfl⟩))))))))

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
    apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
      (fun _ => finite_step _ _ (finite_done _))); intro prefixed
    apply finite_step
    apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
      (fun _ => finite_step _ _ (finite_done _))); intro sourced
    apply finite_step
    apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
      (fun _ => finite_step _ _ (finite_done _))); intro freshened
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
    (cachedCode cursor.support (MasterResources.discover cursor.source)
      (discoveryKind cursor.source) (discoveryOperation cursor.source)).bind (fun discovered =>
    .step .masterProducer (fun _ =>
      let freshRef := retainedPrior discovered.kind (freshAt cursor discovered.args)
      (cachedCode discovered.after (MasterResources.applyStage discovered.here freshRef)
        (applicationKind discovered.here freshRef)
        (applicationOperation discovered.here freshRef)).bind (fun applied =>
      .step .masterProducer (fun _ =>
        let pastRef := retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))
        (cachedCode applied.after (MasterResources.decompose pastRef applied.here)
          (decompositionKind pastRef applied.here)
          (decompositionOperation pastRef applied.here)).bind (fun decomposed =>
        .step .masterProducer (fun _ =>
          (cachedCode decomposed.after (MasterResources.assemble decomposed.here)
            (assemblyKind decomposed.here) (assemblyOperation decomposed.here)).bind (fun assembled =>
          (ControlResources.readCode assembled.after.values assembled.here).bind (fun head =>
          have headIndices :
              MasterResources.Kind.head discovered.args.1.1.down decomposed.args.1.1.down =
                .head cursor.state cursor.context := by
            cases decomposed.exact
            cases applied.exact
            cases discovered.exact
            rfl
          let returnedHead : CausalOperationalHead cursor.state cursor.context :=
            (Eq.rec (motive := fun kind _ => MasterResources.Value kind) head.1 headIndices).down
          let continuedFresh := retainedPrior assembled.kind (retainedPrior decomposed.kind
            (retainedPrior applied.kind freshRef))
          (continueCode assembled.after assembled.here continuedFresh).bind (fun next =>
            have actualHead : returnedHead = cursor.head := by
              dsimp only [returnedHead]
              obtain ⟨_, actual⟩ := head; cases actual
              cases assembled.exact
              cases decomposed.exact
              cases applied.exact
              cases discovered.exact
              rfl
            have actualNext : next.1 = VariableMaster.nextCursor cursor := by
              dsimp only [continuedFresh]
              obtain ⟨_, actual⟩ := next; cases actual
              cases assembled.exact
              cases decomposed.exact
              cases applied.exact
              cases discovered.exact
              rfl
            have boundary : next.1.boundary =
                ⟨cursor.depth + 1, returnedHead.stage.next,
                  returnedHead.run.nextRun.next, returnedHead.production.nextContext⟩ := by
              rw [actualNext, actualHead]; rfl
            .step .masterHeadPacket (fun _ => .done
              ⟨fromParts cursor returnedHead actualHead next.1 actualNext boundary,
                fromParts_actual cursor returnedHead actualHead next.1 actualNext boundary⟩)))))))))))

theorem finite (cursor : MasterResources.Cursor) : Finite (code cursor) := by
  apply finite_step
  apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _)) (discovery_finite _))
  intro discovered
  apply finite_step
  apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _)) (application_finite _ _))
  intro applied
  apply finite_step
  apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _)) (decomposition_finite _ _))
  intro decomposed
  apply finite_step
  apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
    (fun _ => finite_step _ _ (finite_done _)))
  intro assembled
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded assembled.after.values assembled.here
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
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.discoveryKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.applicationKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.decompositionKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.assemblyKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.prefixKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.sourceKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.freshKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.pastAt
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.freshAt
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.Continued
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.continueCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.continue_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.fromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.Head
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHead.finite
/- AXIOM_AUDIT_END -/
