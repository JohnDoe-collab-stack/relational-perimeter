import Tests.LocalAlignment.DocumentaryControlMasterHead
import Tests.LocalAlignment.DocumentaryControlCausalDecomposition
import Tests.LocalAlignment.DocumentaryControlReceivedResources

/-! The next prefix consumes its actual causal-stage executor kept by the
same decomposition. Argument receipts retarget the executor without replay. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 32000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation
open Resources EndogenousDecomposition Control ControlBindings ControlConstitutiveResources
open ControlMasterHead ControlCausalDecomposition

@[inline] def prefixForArguments {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (execution : PrefixExecution (support.read head).down.production.nextContext)
    (args : Arguments (MasterResources.headNextPrefix head).inputs support.values) :
    PrefixExecution args.1.1.down.production.nextContext :=
  castValue (by obtain ⟨_, actual⟩ := args; cases actual; rfl) execution

def prefixOperation {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (execution : PrefixExecution (support.read head).down.production.nextContext)
    (args : Arguments (MasterResources.headNextPrefix head).inputs support.values) :
    Code Label (Operation (MasterResources.headNextPrefix head) args.1) :=
  (prefixForArguments support head execution args).code.bind (fun produced =>
    .done ⟨⟨produced.1⟩, by obtain ⟨_, actual⟩ := produced; cases actual; rfl⟩)

theorem prefix_finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (execution : PrefixExecution (support.read head).down.production.nextContext)
    (args : Arguments (MasterResources.headNextPrefix head).inputs support.values) :
    Finite (prefixOperation support head execution args) := by
  apply finite_bind (prefixForArguments support head execution args).finite
  intro produced; exact finite_done _

def code {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (headRef : Ref context (.head state past))
    (freshRef : Ref context (.fresh state))
    (execution : PrefixExecution (support.read headRef).down.production.nextContext) : Code Label (Continued support headRef freshRef) :=
  (ControlResources.readCode support.values headRef).bind (fun head =>
  .step .masterProducer (fun _ =>
    (ControlReceivedResources.code support (MasterResources.headNextPrefix headRef)
      (prefixKind headRef) (prefixOperation support headRef execution)).bind (fun prefixed =>
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

theorem finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List MasterResources.Kind}
    (support : Support MasterResources.Value context) (head : Ref context (.head state past))
    (fresh : Ref context (.fresh state))
    (execution : PrefixExecution (support.read head).down.production.nextContext) : Finite (code support head fresh execution) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded support.values head
    exact ⟨value, labels, trace⟩
  · intro head
    apply finite_step
    apply finite_bind (ControlReceivedResources.finite _ _ _ _
      (fun _ => finite_step _ _ (finite_done _)) (prefix_finite _ _ execution)); intro prefixed
    apply finite_step
    apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
      (fun _ => finite_step _ _ (finite_done _))); intro sourced
    apply finite_step
    apply finite_bind (cached_finite _ _ _ _ (fun _ => finite_step _ _ (finite_done _))
      (fun _ => finite_step _ _ (finite_done _))); intro freshened
    exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation.prefixForArguments
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation.prefixOperation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation.prefix_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalContinuation.finite
/- AXIOM_AUDIT_END -/
