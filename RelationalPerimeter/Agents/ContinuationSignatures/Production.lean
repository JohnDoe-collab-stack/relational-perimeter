import RelationalPerimeter.Agents.ContinuationSignatures.RolePayloadFamily
import RelationalPerimeter.Constitution.Continuation.Composition
import RelationalPerimeter.Constitution.Resources.ConstructedSupport
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleProfileSemantics

/-! Closed local read contract, fixed by a query before classifying sources.
It promises only repeated reads of the produced target at that query. Its
domain is closed under those requests. This is not the full agent contract
and not yet the composed, varying-resource family required by the plan. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
open SAT EndogenousDecomposition
variable {state : CausalConstitutiveState} {run : CausalConstitutiveStageExecution state}

def roleRead (role : RelationalConstitutiveRoleStage run) (query : Var)
    (source : AcceptedRoleSource role) : Bool := (producedOutput role source).1 query

theorem producedOutput_accepted (role : RelationalConstitutiveRoleStage run)
    (source : AcceptedRoleSource role) :
    GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh)
      (producedOutput role source) :=
  RoleSemantics.localPreserves (compileRoleStageAtom role)
    (compileRoleStageAtom role).preservesAccepted source.occurrence source.payload source.accepted

inductive LocalKind where
  | source | query | target | signature

def LocalValue (role : RelationalConstitutiveRoleStage run) : LocalKind → Type
  | .source => AcceptedRoleSource role
  | .query => Var
  | .target => { target : GeneratedStructuralBranchContinuation
        (causalOpeningRight state run.selected run.fresh) //
      GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh) target }
  | .signature => List (Outcome (ULift Unit) Bool)

def actionProducer (role : RelationalConstitutiveRoleStage run) :
    Resources.Producer (LocalValue role) [.query, .source] where
  inputKinds := [.source]
  inputs := .cons (.prior .here) .nil
  outputKind _ := .target
  operation arguments := ⟨producedOutput role arguments.1, producedOutput_accepted role arguments.1⟩

def signatureProducer (role : RelationalConstitutiveRoleStage run) :
    Resources.Producer (LocalValue role) [.target, .query, .source] where
  inputKinds := [.target, .query]
  inputs := .cons .here (.cons (.prior .here) .nil)
  outputKind _ := .signature
  operation arguments := [.stop (arguments.1.1.1 arguments.2.1)]

/-- Rich formation support; only its finite signature is a reduced memory. -/
def localProduction (role : RelationalConstitutiveRoleStage run) (query : Var)
    (source : AcceptedRoleSource role) :
    Resources.Support (LocalValue role) [.signature, .target, .query, .source] :=
  ((Resources.Support.given (Value := LocalValue role) (context := [.query, .source])
    (query, (source, PUnit.unit))).extend (actionProducer role)).extend (signatureProducer role)

def roleReadContract (role : RelationalConstitutiveRoleStage run) (query : Var) :=
  readOnlyContract (roleRead role query)

def roleReadBasis (role : RelationalConstitutiveRoleStage run) (query : Var) :
    FiniteFutureBasis (roleReadContract role query) := readOnlyBasis (roleRead role query)

def produceRoleSignature (role : RelationalConstitutiveRoleStage run) (query : Var)
    (source : AcceptedRoleSource role) := (localProduction role query source).read .here

theorem produceRoleSignature_from_basis (role : RelationalConstitutiveRoleStage run) (query : Var)
    (source : AcceptedRoleSource role) : produceRoleSignature role query source =
      producedSignature (roleReadBasis role query) source := rfl

def roleReadRealization (role : RelationalConstitutiveRoleStage run) (query : Var) :
    ExactRealization (roleReadContract role query) Bool := readOnlyRealization (roleRead role query)

def roleReadDynamics (role : RelationalConstitutiveRoleStage run) (query : Var) :
    SignatureDynamics (roleReadBasis role query) where
  update signature _ := signature
  update_exact _ _ := rfl

theorem produceRoleSignature_exact (role : RelationalConstitutiveRoleStage run) (query : Var)
    (left right : AcceptedRoleSource role) :
    produceRoleSignature role query left = produceRoleSignature role query right ↔
      FutureEquivalent (roleReadContract role query) left right :=
  signature_exact (roleReadBasis role query) left right

theorem produceRoleSignature_minimal (role : RelationalConstitutiveRoleStage run) (query : Var)
    {Memory : Type} (realization : ExactRealization (roleReadContract role query) Memory)
    {left right : AcceptedRoleSource role} (same : realization.project left = realization.project right) :
    produceRoleSignature role query left = produceRoleSignature role query right :=
  minimal_distinctions (roleReadBasis role query) realization same

theorem paired_signatures_equal (role : RelationalConstitutiveRoleStage run) (query : Var) :
    produceRoleSignature role query (leftSource role) =
      produceRoleSignature role query (pairedRightSource role) := rfl

theorem varied_signatures_distinct (role : RelationalConstitutiveRoleStage run) :
    produceRoleSignature role (freeVariable run) (variedLeftSource role) ≠
      produceRoleSignature role (freeVariable run) (leftSource role) := by
  intro same
  have sameRead := (signature_sound (roleReadBasis role (freeVariable run))
    (left := variedLeftSource role) (right := leftSource role) same).read
  exact varied_source_separated role sameRead

theorem three_sources_distinct (role : RelationalConstitutiveRoleStage run) :
    leftSource role ≠ pairedRightSource role ∧
      variedLeftSource role ≠ leftSource role ∧
      variedLeftSource role ≠ pairedRightSource role := by
  refine ⟨paired_sources_distinct role, ?_, ?_⟩
  · intro same
    exact varied_signatures_distinct role
      (congrArg (produceRoleSignature role (freeVariable run)) same)
  · intro same
    exact varied_signatures_distinct role
      ((congrArg (produceRoleSignature role (freeVariable run)) same).trans
        (paired_signatures_equal role _).symm)

theorem same_sources_other_resource_agree (role : RelationalConstitutiveRoleStage run) :
    produceRoleSignature role run.selected (variedLeftSource role) =
      produceRoleSignature role run.selected (leftSource role) := by
  change [Outcome.stop (Assignment.flipAt run.selected
    (Assignment.flipAt (freeVariable run) run.sourceContinuation.1) run.selected)] =
    [Outcome.stop (Assignment.flipAt run.selected run.sourceContinuation.1 run.selected)]
  rw [Assignment.flipAt_selected, Assignment.flipAt_selected,
    Assignment.flipAt_other _ _ _ (freeVariable_selected_ne run).symm]

/-- The same constituted sources merge for one read resource and separate for
another. Neither read resource supplies a partition or a status mask. -/
theorem resources_change_partition (role : RelationalConstitutiveRoleStage run) :
    produceRoleSignature role run.selected (variedLeftSource role) =
        produceRoleSignature role run.selected (leftSource role) ∧
    produceRoleSignature role (freeVariable run) (variedLeftSource role) ≠
        produceRoleSignature role (freeVariable run) (leftSource role) :=
  ⟨same_sources_other_resource_agree role, varied_signatures_distinct role⟩

def varied_separator (role : RelationalConstitutiveRoleStage run) :
    FutureSeparator (roleReadContract role (freeVariable run))
      (variedLeftSource role) (leftSource role) :=
  separate (roleReadBasis role (freeVariable run)) _ _ (varied_signatures_distinct role)

theorem varied_cannot_be_forgotten (role : RelationalConstitutiveRoleStage run)
    {Memory : Type} (realization : ExactRealization (roleReadContract role (freeVariable run)) Memory) :
    realization.project (variedLeftSource role) ≠ realization.project (leftSource role) :=
  fun same => varied_signatures_distinct role
    (produceRoleSignature_minimal role _ realization same)

theorem source_not_recoverable (role : RelationalConstitutiveRoleStage run) (query : Var)
    (recover : Bool → AcceptedRoleSource role) :
    ¬ (∀ source, recover ((roleReadRealization role query).project source) = source) := by
  intro returns
  have equalMemory : (roleReadRealization role query).project (leftSource role) =
      (roleReadRealization role query).project (pairedRightSource role) := rfl
  exact paired_sources_distinct role
    ((returns _).symm.trans ((congrArg recover equalMemory).trans (returns _)))

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.producedOutput_accepted
#print axioms ConstitutiveSearch.ContinuationSignatures.actionProducer
#print axioms ConstitutiveSearch.ContinuationSignatures.signatureProducer
#print axioms ConstitutiveSearch.ContinuationSignatures.localProduction
#print axioms ConstitutiveSearch.ContinuationSignatures.produceRoleSignature_from_basis
#print axioms ConstitutiveSearch.ContinuationSignatures.roleReadContract
#print axioms ConstitutiveSearch.ContinuationSignatures.roleReadBasis
#print axioms ConstitutiveSearch.ContinuationSignatures.roleReadRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.roleReadDynamics
#print axioms ConstitutiveSearch.ContinuationSignatures.produceRoleSignature
#print axioms ConstitutiveSearch.ContinuationSignatures.produceRoleSignature_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.produceRoleSignature_minimal
#print axioms ConstitutiveSearch.ContinuationSignatures.paired_signatures_equal
#print axioms ConstitutiveSearch.ContinuationSignatures.varied_signatures_distinct
#print axioms ConstitutiveSearch.ContinuationSignatures.three_sources_distinct
#print axioms ConstitutiveSearch.ContinuationSignatures.resources_change_partition
#print axioms ConstitutiveSearch.ContinuationSignatures.varied_separator
#print axioms ConstitutiveSearch.ContinuationSignatures.varied_cannot_be_forgotten
#print axioms ConstitutiveSearch.ContinuationSignatures.source_not_recoverable
/- AXIOM_AUDIT_END -/
