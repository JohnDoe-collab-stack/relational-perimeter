import Tests.LocalAlignment.DocumentaryControlCausalProjection
import Tests.LocalAlignment.DocumentaryControlMasterDecomposition

/-! The decomposition and its next-prefix executor share the same actually
formed causal stage. Only type/proof casts mention the historical projection. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition
open Resources EndogenousDecomposition Control ControlBindings ControlMasterData
open ControlCausalProjection
universe u

@[inline] def castValue {left right : Type u} (same : left = right) (value : left) : right :=
  Eq.rec (motive := fun received _ => received) value same

@[inline] def actualPast {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (projected : ControlCausalProjection.Produced run)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)) :
    ConstitutedOperationalPrefix projected.source.1 :=
  Eq.rec (motive := fun source _ => ConstitutedOperationalPrefix source) past projected.source.2.symm

theorem endpoints_type_actual {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage} (projected : ControlCausalProjection.Produced run) :
    ControlRoleFormation.Endpoints projected.stage = ControlRoleFormation.Endpoints (causalStageOfThreadedStage run) := by
  rcases projected with ⟨⟨_, sourceActual⟩, projected, actual, root⟩
  cases sourceActual
  cases eq_of_heq actual
  rfl

theorem production_type_actual {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage} (projected : ControlCausalProjection.Produced run)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)) :
    ExecutedStageOperationalProduction (actualPast projected past) projected.stage =
      ExecutedStageOperationalProduction past (causalStageOfThreadedStage run) := by
  rcases projected with ⟨⟨_, sourceActual⟩, projected, actual, root⟩
  cases sourceActual
  cases eq_of_heq actual
  rfl

def originalProduction {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage} (projected : ControlCausalProjection.Produced run)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (production : Actual (prefixLocalOperationalProducer (actualPast projected past) projected.stage)) :
    ExecutedStageOperationalProduction past (causalStageOfThreadedStage run) :=
  castValue (production_type_actual projected past) production.1

theorem original_production_actual {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage} (projected : ControlCausalProjection.Produced run)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (production : Actual (prefixLocalOperationalProducer (actualPast projected past) projected.stage)) :
    originalProduction projected past production = prefixLocalOperationalProducer past (causalStageOfThreadedStage run) := by
  rcases projected with ⟨⟨_, sourceActual⟩, projected, actual, root⟩
  cases sourceActual
  cases eq_of_heq actual
  obtain ⟨_, produced⟩ := production
  cases produced
  rfl

structure PrefixExecution {source : CausalConstitutiveState}
    (expected : ConstitutedOperationalPrefix source) where
  code : Code Label (Actual expected)
  finite : Finite code

def prefixCode {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) (stage : CausalConstitutiveStageExecution source)
    (production : ExecutedStageOperationalProduction past stage) :
    Code Label (Actual production.nextContext) :=
  .step .masterNextPrefix (fun _ => .done
    ⟨production.decomposition.role.nextStateExact ▸
      ConstitutedOperationalPrefix.advance production.priorContext stage production.decomposition, rfl⟩)

theorem prefix_finite {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) (stage : CausalConstitutiveStageExecution source)
    (production : ExecutedStageOperationalProduction past stage) : Finite (prefixCode past stage production) :=
  finite_step _ _ (finite_done _)

theorem prefix_execution_type_actual {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage} (projected : ControlCausalProjection.Produced run)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (production : Actual (prefixLocalOperationalProducer (actualPast projected past) projected.stage)) :
    PrefixExecution production.1.nextContext = PrefixExecution (originalProduction projected past production).nextContext := by
  rcases projected with ⟨⟨_, sourceActual⟩, projected, actual, root⟩
  cases sourceActual
  cases eq_of_heq actual
  rfl

def prefixExecution {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage} (projected : ControlCausalProjection.Produced run)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (production : Actual (prefixLocalOperationalProducer (actualPast projected past) projected.stage)) :
    PrefixExecution (originalProduction projected past production).nextContext :=
  let execution : PrefixExecution production.1.nextContext :=
    ⟨prefixCode (actualPast projected past) projected.stage production.1,
      prefix_finite (actualPast projected past) projected.stage production.1⟩
  castValue (prefix_execution_type_actual projected past production) execution

end ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.castValue
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.actualPast
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.endpoints_type_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.production_type_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.originalProduction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.original_production_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.PrefixExecution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.prefixCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.prefix_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.prefix_execution_type_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalDecomposition.prefixExecution
/- AXIOM_AUDIT_END -/
