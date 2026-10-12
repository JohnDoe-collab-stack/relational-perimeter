import Tests.LocalAlignment.DocumentaryControlMasterRootBootstrap
import Tests.LocalAlignment.DocumentaryControlMasterHead
import Tests.LocalAlignment.DocumentaryControlMasterApplicationReader
import Tests.LocalAlignment.DocumentaryControlResourcePayload
import Tests.LocalAlignment.DocumentaryControlCausalContinuation
import Tests.LocalAlignment.DocumentaryControlReceivedDiscovery

/-! The original resource chain keeps the executable measured reader produced
by its actual application. The same paid support feeds head and continuation. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 32000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader
open Resources EndogenousDecomposition Control ControlBindings ControlConstitutiveResources
open ControlMasterHead ControlMeasuredAssignmentReader ControlMasterData

def applicationPayload {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state))
    (_args : Values MasterResources.Value [.discovery state, .fresh state])
    (value : MasterResources.Value ((MasterResources.applyStage discovery fresh).outputKind _args)) :=
  Reader value.down.stage.next.reader

def applicationOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state))
    (reader : Reader assignment.reader)
    (args : Values MasterResources.Value [.discovery state, .fresh state]) :
    Code Label (ControlResourcePayload.OperationPayload (MasterResources.applyStage discovery fresh)
      (applicationPayload discovery fresh) args) :=
  (ControlMasterApplicationReader.code state args.2.1.down.down args.1.down.1 args.1.down.2 reader).bind
    (fun built =>
      let produced : Operation (MasterResources.applyStage discovery fresh) args :=
        ⟨⟨built.built.1⟩, by obtain ⟨_, actual⟩ := built.built; cases actual; rfl⟩
      .done ⟨produced, built.reader⟩)

theorem application_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state))
    (reader : Reader assignment.reader)
    (args : Values MasterResources.Value [.discovery state, .fresh state]) :
    Finite (applicationOperation discovery fresh reader args) := by
  apply finite_bind (ControlMasterApplicationReader.finite _ _ _ _ _); intro built
  exact finite_done _

def decompositionPayload {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state])
    (value : MasterResources.Value ((MasterResources.decompose past application).outputKind args)) :=
  ControlCausalDecomposition.PrefixExecution value.down.nextContext ×
    Actual (constructMeasuredOperationalRoot args.2.1.down.run.nextRun.next.searchSeed)

def decompositionOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state]) :
    Code Label (ControlResourcePayload.OperationPayload (MasterResources.decompose past application)
      (decompositionPayload past application) args) :=
  (ControlCausalProjection.code args.1.down args.2.1.down.run).bind (fun projected =>
    (ControlRoleFormation.endpointsCode args.2.1.down.run).bind (fun endpoints =>
    (ControlMasterDecomposition.actualCode
      (ControlCausalDecomposition.actualPast projected args.1.down) projected.stage
      (ControlCausalDecomposition.castValue (ControlCausalDecomposition.endpoints_type_actual projected).symm
        endpoints.1)).bind (fun production =>
      let original := ControlCausalDecomposition.originalProduction projected args.1.down production
      let produced : Operation (MasterResources.decompose past application) args :=
        ⟨⟨original⟩, congrArg (fun received => (⟨received⟩ : MasterResources.Value
          ((MasterResources.decompose past application).outputKind args)))
          (ControlCausalDecomposition.original_production_actual projected args.1.down production)⟩
      let execution := ControlCausalDecomposition.prefixExecution projected args.1.down production
      .step .controlClosure (fun _ => .step .executionPayload (fun _ => .done ⟨produced, (execution, projected.nextRoot)⟩)))))

theorem decomposition_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List MasterResources.Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state))
    (args : Values MasterResources.Value [.prefix state, .application state]) : Finite (decompositionOperation past application args) := by
  apply finite_bind (ControlCausalProjection.finite _ _); intro projected
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlRoleFormation.endpoints_bounded args.2.1.down.run
    exact ⟨value, labels, trace⟩
  · intro endpoints
    apply finite_bind (ControlMasterDecomposition.actual_finite _ _ _); intro production
    apply finite_step; apply finite_step; exact finite_done _

set_option backward.isDefEq.respectTransparency false in
theorem assembled_prefix_type {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {built : ConstructedThreadedStageRun state} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context)
    (production : Ref context (.decomposition state past built))
    (received : Actual (support.read production))
    (assembled : Cached support (MasterResources.assemble production)) :
    ControlCausalDecomposition.PrefixExecution received.1.down.nextContext =
      ControlCausalDecomposition.PrefixExecution (assembled.after.read assembled.here).down.production.nextContext := by
  cases assembled.exact
  obtain ⟨_, actual⟩ := received; cases actual
  rfl

theorem continued_assignment {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (fresh : Ref context (.fresh state)) (next : Continued support head fresh) :
    HEq next.1.assignment (support.read head).down.stage.next := by
  obtain ⟨_, actual⟩ := next; cases actual; rfl

@[inline] def sequentialRetarget {leftDepth rightDepth : Nat}
    (left : SequentialAssignment leftDepth) (right : SequentialAssignment rightDepth)
    (sameDepth : leftDepth = rightDepth) (same : HEq left right)
    (reader : Reader left.reader) : Reader right.reader := by
  cases sameDepth
  cases eq_of_heq same
  exact reader

structure Produced (cursor : MasterResources.Cursor) where
  head : Head cursor
  reader : Reader head.1.next.assignment.reader
  root : Actual (constructMeasuredOperationalRoot head.1.next.state.searchSeed)

abbrev headIndices (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args))))
    (decomposed : Cached applied.after (MasterResources.decompose
      (retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))) applied.here)) :
    MasterResources.Kind.head discovered.args.1.1.down decomposed.args.1.1.down =
      .head cursor.state cursor.context := by
  cases decomposed.exact; cases applied.exact; cases discovered.exact; rfl

abbrev headFromCache (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args))))
    (decomposed : Cached applied.after (MasterResources.decompose
      (retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))) applied.here))
    (assembled : Cached decomposed.after (MasterResources.assemble decomposed.here))
    (head : ControlResources.Read assembled.after.values assembled.here) : CausalOperationalHead cursor.state cursor.context :=
  (Eq.rec (motive := fun kind _ => MasterResources.Value kind) head.1
    (headIndices cursor discovered applied decomposed)).down

theorem head_actual (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args))))
    (decomposed : Cached applied.after (MasterResources.decompose
      (retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))) applied.here))
    (assembled : Cached decomposed.after (MasterResources.assemble decomposed.here))
    (head : ControlResources.Read assembled.after.values assembled.here) :
    headFromCache cursor discovered applied decomposed assembled head = cursor.head := by
  dsimp only [headFromCache]
  obtain ⟨_, actual⟩ := head; cases actual
  cases assembled.exact; cases decomposed.exact; cases applied.exact; cases discovered.exact; rfl

theorem next_actual (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args))))
    (decomposed : Cached applied.after (MasterResources.decompose
      (retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))) applied.here))
    (assembled : Cached decomposed.after (MasterResources.assemble decomposed.here))
    (next : Continued assembled.after assembled.here (retainedPrior assembled.kind
      (retainedPrior decomposed.kind (retainedPrior applied.kind
        (retainedPrior discovered.kind (freshAt cursor discovered.args)))))) :
    next.1 = VariableMaster.nextCursor cursor := by
  obtain ⟨_, actual⟩ := next; cases actual
  cases assembled.exact; cases decomposed.exact; cases applied.exact; cases discovered.exact; rfl

structure Tail (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args)))) where
  head : Head cursor
  sameAssignment : HEq head.1.next.assignment (applied.after.read applied.here).down.stage.next
  root : Actual (constructMeasuredOperationalRoot (VariableMaster.nextCursor cursor).state.searchSeed)

theorem next_seed_actual (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args))))
    (decomposed : Cached applied.after (MasterResources.decompose
      (retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))) applied.here)) :
    decomposed.args.1.2.1.down.run.nextRun.next.searchSeed = (VariableMaster.nextCursor cursor).state.searchSeed := by
  cases decomposed.exact; cases applied.exact; cases discovered.exact; rfl

def tailCode (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args)))) : Code Label (Tail cursor discovered applied) :=
      .step .masterProducer (fun _ =>
        let pastRef := retainedPrior applied.kind (retainedPrior discovered.kind (pastAt cursor discovered.args))
        (ControlResourcePayload.code applied.after (MasterResources.decompose pastRef applied.here)
          (decompositionPayload pastRef applied.here)
          (decompositionKind pastRef applied.here)
          (decompositionOperation pastRef applied.here)).bind (fun pairedDecomposition =>
        let decomposed := pairedDecomposition.cached
        .step .masterProducer (fun _ =>
          (cachedCode decomposed.after (MasterResources.assemble decomposed.here)
            (assemblyKind decomposed.here) (assemblyOperation decomposed.here)).bind (fun assembled =>
          (ControlResources.readCode assembled.after.values assembled.here).bind (fun head =>
          let returnedHead := headFromCache cursor discovered applied decomposed assembled head
          let continuedFresh := retainedPrior assembled.kind (retainedPrior decomposed.kind
            (retainedPrior applied.kind (retainedPrior discovered.kind (freshAt cursor discovered.args))))
          (ControlCausalContinuation.code assembled.after assembled.here continuedFresh
            (ControlCausalDecomposition.castValue
              (assembled_prefix_type decomposed.after decomposed.here
                ⟨pairedDecomposition.produced.1, pairedDecomposition.produced.2.trans decomposed.read_here.symm⟩ assembled)
              pairedDecomposition.execution.1)).bind (fun next =>
            have actualHead : returnedHead = cursor.head :=
              head_actual cursor discovered applied decomposed assembled head
            have actualNext : next.1 = VariableMaster.nextCursor cursor :=
              next_actual cursor discovered applied decomposed assembled next
            have boundary : next.1.boundary =
                ⟨cursor.depth + 1, returnedHead.stage.next,
                  returnedHead.run.nextRun.next, returnedHead.production.nextContext⟩ := by
              rw [actualNext, actualHead]; rfl
            have headStage : head.1.down.stage.next = decomposed.args.1.2.1.down.stage.next :=
              congrArg (fun value => value.down.stage.next) (head.2.trans assembled.read_here)
            have builtActual : decomposed.args.1.2.1.down = (applied.after.read applied.here).down :=
              congrArg (fun args => args.2.1.down) decomposed.args.2
            have sameAssignment : HEq next.1.assignment (applied.after.read applied.here).down.stage.next :=
              (continued_assignment assembled.after assembled.here continuedFresh next).trans
                (heq_of_eq ((congrArg (fun value => value.down.stage.next) head.2.symm).trans
                  (headStage.trans (congrArg (fun built => built.stage.next) builtActual))))
            .step .masterHeadPacket (fun _ => .done
              ⟨⟨fromParts cursor returnedHead actualHead next.1 actualNext boundary,
                  fromParts_actual cursor returnedHead actualHead next.1 actualNext boundary⟩,
                sameAssignment,
                ControlCausalDecomposition.castValue (congrArg (fun seed => Actual (constructMeasuredOperationalRoot seed))
                  (next_seed_actual cursor discovered applied decomposed)) pairedDecomposition.execution.2⟩)))))))


theorem tail_finite (cursor : MasterResources.Cursor)
    (discovered : Cached cursor.support (MasterResources.discover cursor.source))
    (applied : Cached discovered.after (MasterResources.applyStage discovered.here
      (retainedPrior discovered.kind (freshAt cursor discovered.args)))) : Finite (tailCode cursor discovered applied) := by
  apply finite_step
  apply finite_bind (ControlResourcePayload.finite _ _ _ _ _
    (fun _ => finite_step _ _ (finite_done _)) (decomposition_finite _ _))
  intro pairedDecomposition
  apply finite_step
  apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
    (fun _ => finite_step _ _ (finite_done _))); intro assembled
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded assembled.after.values assembled.here
    exact ⟨value, labels, trace⟩
  · intro head
    apply finite_bind (ControlCausalContinuation.finite _ _ _ _); intro next
    exact finite_step _ _ (finite_done _)

@[inline] def receivedRoot {depth : Nat} {assignment : SequentialAssignment depth} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (source : Ref context (.source depth assignment))
    (root : Actual (constructMeasuredOperationalRoot (support.read source).down.searchSeed))
    (args : Arguments (MasterResources.discover source).inputs support.values) :
    Actual (constructMeasuredOperationalRoot args.1.1.down.searchSeed) :=
  ControlCausalDecomposition.castValue (by obtain ⟨_, actual⟩ := args; cases actual; rfl) root

def receivedDiscovery {depth : Nat} {assignment : SequentialAssignment depth} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (source : Ref context (.source depth assignment))
    (root : Actual (constructMeasuredOperationalRoot (support.read source).down.searchSeed))
    (args : Arguments (MasterResources.discover source).inputs support.values) :
    Code Label (Operation (MasterResources.discover source) args.1) :=
  (ControlReceivedDiscovery.code args.1.1.down (receivedRoot support source root args)).bind (fun actual => .done
    ⟨⟨⟨actual.1, actual.2⟩⟩, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩)

theorem received_discovery_finite {depth : Nat} {assignment : SequentialAssignment depth} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (source : Ref context (.source depth assignment))
    (root : Actual (constructMeasuredOperationalRoot (support.read source).down.searchSeed))
    (args : Arguments (MasterResources.discover source).inputs support.values) :
    Finite (receivedDiscovery support source root args) := by
  apply finite_bind (ControlReceivedDiscovery.finite _ _); intro actual; exact finite_done _

def codeFromRoot (cursor : MasterResources.Cursor) (reader : Reader cursor.assignment.reader)
    (root : Actual (constructMeasuredOperationalRoot cursor.state.searchSeed)) :
    Code Label (Produced cursor) :=
  .step .masterProducer (fun _ =>
    (ControlReceivedResources.code cursor.support (MasterResources.discover cursor.source)
      (discoveryKind cursor.source) (receivedDiscovery cursor.support cursor.source root)).bind (fun discovered =>
    .step .masterProducer (fun _ =>
      let freshRef := retainedPrior discovered.kind (freshAt cursor discovered.args)
      (ControlResourcePayload.code discovered.after (MasterResources.applyStage discovered.here freshRef)
        (applicationPayload discovered.here freshRef)
        (applicationKind discovered.here freshRef)
        (applicationOperation discovered.here freshRef reader)).bind (fun paired =>
      (tailCode cursor discovered paired.cached).bind (fun tail =>
        have same : HEq tail.head.1.next.assignment paired.produced.1.down.stage.next :=
          tail.sameAssignment.trans (heq_of_eq (congrArg (fun value => value.down.stage.next)
            (paired.cached.read_here.trans paired.produced.2.symm)))
        have sameDepth : tail.head.1.next.depth = cursor.depth + 1 :=
          congrArg MasterResources.Cursor.depth tail.head.1.nextExact
        let realized := sequentialRetarget paired.produced.1.down.stage.next tail.head.1.next.assignment
          sameDepth.symm same.symm paired.execution
        .step .executionPayload (fun _ => .done ⟨tail.head, realized, ControlCausalDecomposition.castValue
          (congrArg (fun next => Actual (constructMeasuredOperationalRoot next.state.searchSeed)) tail.head.1.nextExact.symm) tail.root⟩))))))

theorem from_root_finite (cursor : MasterResources.Cursor) (reader : Reader cursor.assignment.reader)
    (root : Actual (constructMeasuredOperationalRoot cursor.state.searchSeed)) :
    Finite (codeFromRoot cursor reader root) := by
  apply finite_step
  apply finite_bind (ControlReceivedResources.finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _)) (received_discovery_finite _ _ root))
  intro discovered
  apply finite_step
  apply finite_bind (ControlResourcePayload.finite _ _ _ _ _
    (fun _ => finite_step _ _ (finite_done _)) (application_finite _ _ reader)); intro paired
  apply finite_bind (tail_finite _ _ _); intro tail
  exact finite_step _ _ (finite_done _)

def code (cursor : MasterResources.Cursor) (reader : Reader cursor.assignment.reader) : Code Label (Produced cursor) :=
  (ControlMasterRootBootstrap.code cursor).bind (fun root => codeFromRoot cursor reader root)

theorem finite (cursor : MasterResources.Cursor) (reader : Reader cursor.assignment.reader) :
    Finite (code cursor reader) := by
  apply finite_bind (ControlMasterRootBootstrap.finite cursor); intro root
  exact from_root_finite cursor reader root

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.applicationPayload
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.applicationOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.application_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.decompositionPayload
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.assembled_prefix_type
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.decompositionOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.decomposition_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.continued_assignment
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.sequentialRetarget
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.headIndices
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.headFromCache
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.head_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.next_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.Tail
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.tailCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.tail_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.next_seed_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.receivedRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.receivedDiscovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.received_discovery_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.codeFromRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterHeadReader.from_root_finite
/- AXIOM_AUDIT_END -/
