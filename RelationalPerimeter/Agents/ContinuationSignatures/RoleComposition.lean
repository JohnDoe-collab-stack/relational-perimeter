import RelationalPerimeter.Agents.ContinuationSignatures.Production

/-! Composition on an arbitrary constituted role history. The contract is
read-only on the outputs at the received local query resources. Each head
signature is produced before recursing into its tail. Neither the source
profile frontier nor an image enumeration occurs on this production path. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
open SAT EndogenousDecomposition

def AcceptedRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    RelationalConstitutiveRoleHistory run → Type
  | _, _, _, .nil => Unit
  | _, _, _, .step head rest => AcceptedRoleSource head × AcceptedRoleHistory rest

def RoleReadResources :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    RelationalConstitutiveRoleHistory run → Type
  | _, _, _, .nil => Unit
  | _, _, _, .step _ rest => Var × RoleReadResources rest

def freeReadResources :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → RoleReadResources roles
  | _, _, _, .nil => ()
  | _, _, _, @RelationalConstitutiveRoleHistory.step _ _ head _ _ rest =>
      (freeVariable head, freeReadResources rest)

def signatureRead : List (Outcome (ULift Unit) Bool) → Bool
  | [] => false
  | first :: _ => first.read

def produceHistoryReadings :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → RoleReadResources roles →
    AcceptedRoleHistory roles → List Bool
  | _, _, _, .nil, _, _ => []
  | _, _, _, .step head rest, resources, source =>
      let headSignature := produceRoleSignature head resources.1 source.1
      signatureRead headSignature :: produceHistoryReadings rest resources.2 source.2

theorem produceHistoryReadings_step
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (role : RelationalConstitutiveRoleStage head) (rest : RelationalConstitutiveRoleHistory tail)
    (resources : RoleReadResources (.step role rest)) (source : AcceptedRoleHistory (.step role rest)) :
    produceHistoryReadings (.step role rest) resources source =
      roleRead role resources.1 source.1 :: produceHistoryReadings rest resources.2 source.2 := rfl

theorem produceHistoryReadings_length :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → (resources : RoleReadResources roles) →
    (source : AcceptedRoleHistory roles) → (produceHistoryReadings roles resources source).length = count
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .step _ rest, resources, source =>
      congrArg Nat.succ (produceHistoryReadings_length rest resources.2 source.2)

def historyReadContract {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (resources : RoleReadResources roles) :=
  readOnlyContract (produceHistoryReadings roles resources)

def historyReadBasis {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (resources : RoleReadResources roles) :
    FiniteFutureBasis (historyReadContract roles resources) :=
  readOnlyBasis (produceHistoryReadings roles resources)

def historyReadRealization {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (resources : RoleReadResources roles) :
    ExactRealization (historyReadContract roles resources) (List Bool) :=
  readOnlyRealization (produceHistoryReadings roles resources)

def historyLeftSources :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → AcceptedRoleHistory roles
  | _, _, _, .nil => ()
  | _, _, _, .step head rest => (leftSource head, historyLeftSources rest)

def historyPairedSources :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → AcceptedRoleHistory roles
  | _, _, _, .nil => ()
  | _, _, _, .step head rest => (pairedRightSource head, historyPairedSources rest)

theorem history_pairs_converge :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → (resources : RoleReadResources roles) →
    produceHistoryReadings roles resources (historyLeftSources roles) =
      produceHistoryReadings roles resources (historyPairedSources roles)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .step head rest, resources => by
      change roleRead head resources.1 (leftSource head) :: _ =
        roleRead head resources.1 (pairedRightSource head) :: _
      exact congrArg (List.cons _) (history_pairs_converge rest resources.2)

theorem history_pairs_distinct {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (role : RelationalConstitutiveRoleStage head) (rest : RelationalConstitutiveRoleHistory tail) :
    historyLeftSources (.step role rest) ≠ historyPairedSources (.step role rest) :=
  fun same => paired_sources_distinct role (congrArg Prod.fst same)

theorem history_variant_separated {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (role : RelationalConstitutiveRoleStage head) (rest : RelationalConstitutiveRoleHistory tail) :
    produceHistoryReadings (.step role rest) (freeReadResources (.step role rest))
        (variedLeftSource role, historyLeftSources rest) ≠
      produceHistoryReadings (.step role rest) (freeReadResources (.step role rest))
        (historyLeftSources (.step role rest)) := by
  intro same
  have equalRead := Option.some.inj (congrArg List.head? same)
  exact varied_source_separated role equalRead

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.freeReadResources
#print axioms ConstitutiveSearch.ContinuationSignatures.produceHistoryReadings
#print axioms ConstitutiveSearch.ContinuationSignatures.produceHistoryReadings_step
#print axioms ConstitutiveSearch.ContinuationSignatures.produceHistoryReadings_length
#print axioms ConstitutiveSearch.ContinuationSignatures.historyReadBasis
#print axioms ConstitutiveSearch.ContinuationSignatures.historyReadRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.history_pairs_converge
#print axioms ConstitutiveSearch.ContinuationSignatures.history_pairs_distinct
#print axioms ConstitutiveSearch.ContinuationSignatures.history_variant_separated
/- AXIOM_AUDIT_END -/
