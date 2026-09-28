import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalRoleExtensiveFamily

/-!
# Exact public instance of the general relational extensive family

The adapter in this module does not rerun discovery and does not manufacture a
frontier.  It reads the same public causal history and the same relational role
history already projected from the instrumented execution.  Each generic stage
uses the concrete role occurrence type and its concrete occurrence frontier.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open Extensive
open RelationalExtensive

/-- One concrete role viewed as a stage of the general relational interface. -/
def generalOpeningStageOfRole
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    RelationalOpeningStage CausalConstitutiveState source run.next :=
  { Role := RelationalConstitutiveRoleStage run
    Occurrence := RoleOpeningOccurrence role
    Provenance := List Var
    SourceRelation := fun observed candidate =>
      PLift (candidate.searchState = observed)
    FormationRelation := fun candidate occurrence =>
      PLift (candidate = role) ×
        PLift (occurrence.state = occurrence.position.state role)
    TargetRelation := fun candidate observed =>
      PLift (candidate.nextState = observed)
    ProvenanceRelation := fun provenance candidate occurrence =>
      PLift (provenance = source.provenance) ×
        PLift (candidate = role) ×
        PLift (occurrence.state = occurrence.position.state role)
    role := role
    provenance := source.provenance
    sourceWitness := ⟨role.searchStateExact⟩
    targetWitness := ⟨role.nextStateExact⟩
    occurrenceDecEq := roleOpeningOccurrenceDecEq role
    occurrenceFrontier := openingOccurrenceFrontier role
    occurrenceComplete := openingOccurrenceFrontier_complete role
    occurrenceNodup := openingOccurrenceFrontier_nodup role
    formationWitness := fun occurrence => ⟨⟨rfl⟩, ⟨occurrence.formedAt⟩⟩
    provenanceWitness := fun occurrence =>
      ⟨⟨rfl⟩, ⟨⟨rfl⟩, ⟨occurrence.formedAt⟩⟩⟩ }

/-- Structural adapter from the authoritative concrete role history. -/
def generalHistoryOfRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      DependentRelationalRoleHistory CausalConstitutiveState state count
  | _, state, _, .nil => .nil state
  | _, _, _, .step headRole tailRoles =>
      .step (generalOpeningStageOfRole headRole)
        (generalHistoryOfRoleHistory tailRoles)

/--
The exact transport from generic relational identities to the concrete role
occurrences of the authoritative history.  The backward map reinstates the
positive formation and provenance witnesses supplied by each stage.
-/
def generalOpeningOccurrenceTransport
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ExactTypeTransport
      (RelationallyConstitutedOccurrence (generalOpeningStageOfRole role))
      (RoleOpeningOccurrence role) :=
  { forward := RelationallyConstitutedOccurrence.occurrence
    backward := relationallyConstitutedOccurrence
      (generalOpeningStageOfRole role)
    forwardBackward := fun _identity =>
      RelationallyConstitutedOccurrence.ext rfl
    backwardForward := fun _ => rfl }

/-- Exact transport of a product from exact transports of both factors. -/
def productExactTypeTransport
    {SourceHead SourceTail TargetHead TargetTail : Type}
    (head : ExactTypeTransport SourceHead TargetHead)
    (tail : ExactTypeTransport SourceTail TargetTail) :
    ExactTypeTransport
      (SourceHead × SourceTail) (TargetHead × TargetTail) :=
  { forward := fun source =>
      (head.forward source.1, tail.forward source.2)
    backward := fun target =>
      (head.backward target.1, tail.backward target.2)
    forwardBackward := fun source =>
      Prod.ext (head.forwardBackward source.1)
        (tail.forwardBackward source.2)
    backwardForward := fun target =>
      Prod.ext (head.backwardForward target.1)
        (tail.backwardForward target.2) }

def generalConcreteProfileTransport :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      ExactTypeTransport
        (RelationalOccurrenceProfile (generalHistoryOfRoleHistory roles))
        (RoleOccurrenceProfile roles)
  | _, _, _, .nil => ExactTypeTransport.reflexive Unit
  | _, _, _, .step headRole tailRoles => by
      simpa only [generalHistoryOfRoleHistory, RelationalOccurrenceProfile,
        RoleOccurrenceProfile] using
        productExactTypeTransport
          (generalOpeningOccurrenceTransport headRole)
          (generalConcreteProfileTransport tailRoles)

/--
Reindex an obligation regime contravariantly along an exact carrier transport.
The obligation carrier and its frontier are unchanged; only the source through
which `carry` is read is transported, with surjectivity reconstructed from the
explicit inverse.
-/
def reindexObligationRegimeAlongExactTransport
    {source target : Extensive.FiniteCarrier}
    (transport : ExactTypeTransport source.Identity target.Identity)
    (regime : Extensive.ObligationRegime target) :
    Extensive.ObligationRegime source :=
  { Obligation := regime.Obligation
    decEq := regime.decEq
    frontier := regime.frontier
    complete := regime.complete
    nodup := regime.nodup
    carry := fun identity => regime.carry (transport.forward identity)
    carry_surjective := fun obligation =>
      let ⟨targetIdentity, targetExact⟩ := regime.carry_surjective obligation
      ⟨transport.backward targetIdentity, by
        change regime.carry
            (transport.forward (transport.backward targetIdentity)) = obligation
        rw [transport.backwardForward]
        exact targetExact⟩ }

/-- Exact reindexing preserves and reflects injectivity of the carry map. -/
theorem reindexObligationRegime_carry_injective_iff
    {source target : Extensive.FiniteCarrier}
    (transport : ExactTypeTransport source.Identity target.Identity)
    (regime : Extensive.ObligationRegime target) :
    Function.Injective
        (reindexObligationRegimeAlongExactTransport transport regime).carry ↔
      Function.Injective regime.carry := by
  constructor
  · intro reindexedInjective left right sameCarry
    have backwardEqual :
        transport.backward left = transport.backward right :=
      reindexedInjective (by
        change regime.carry
            (transport.forward (transport.backward left)) =
          regime.carry (transport.forward (transport.backward right))
        rw [transport.backwardForward, transport.backwardForward]
        exact sameCarry)
    exact Eq.trans (transport.backwardForward left).symm
      (Eq.trans (congrArg transport.forward backwardEqual)
        (transport.backwardForward right))
  · intro regimeInjective left right sameCarry
    have forwardEqual : transport.forward left = transport.forward right :=
      regimeInjective sameCarry
    exact Eq.trans (transport.forwardBackward left).symm
      (Eq.trans (congrArg transport.backward forwardEqual)
        (transport.forwardBackward right))

theorem generalHistory_is_uniformBinary :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      UniformLocalArity (generalHistoryOfRoleHistory roles) 2
  | _, _, _, .nil => True.intro
  | _, _, _, .step _ tailRoles => by
      exact ⟨rfl, generalHistory_is_uniformBinary tailRoles⟩

theorem generalHistory_is_atLeastBinary :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      AtLeastBinaryLocalArity (generalHistoryOfRoleHistory roles)
  | _, _, _, .nil => True.intro
  | _, _, _, .step _ tailRoles => by
      exact ⟨Nat.le_refl 2, generalHistory_is_atLeastBinary tailRoles⟩

/-- The generic width readout agrees with the concrete binary exponent. -/
theorem generalHistory_width_eq_twoPow
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    relationalProfileWidth (generalHistoryOfRoleHistory roles) = 2 ^ count :=
  uniformLocalArity_width
    (generalHistoryOfRoleHistory roles) 2
    (generalHistory_is_uniformBinary roles)

/-- The public initial state of the already executed causal history. -/
def publicCausalInitialState (input : Nat) : CausalConstitutiveState :=
  causalStateOfThreadedState
    (executeConstitutiveResolution input).threadedInitialState

/-- The exact general history read from the public execution. -/
def publicGeneralRelationalHistory (input : Nat) :
    DependentRelationalRoleHistory CausalConstitutiveState
      (publicCausalInitialState input) (resolutionLength input) :=
  generalHistoryOfRoleHistory (publicRelationalConstitutiveRoles input)

/--
The public run is a nontrivial unbounded member of the general class.  Its
problem parameter is only the external input; all history data is executed and
then projected by the existing public construction.
-/
def publicRelationalRoleExtensiveFamily :
    RelationalRoleExtensiveFamily :=
  { State := CausalConstitutiveState
    Problem := fun _ => Unit
    initialState := fun {index} _ => publicCausalInitialState index
    stageCount := fun {index} _ => resolutionLength index
    producedHistory := fun {index} _ => publicGeneralRelationalHistory index
    nontrivialOpenings := fun {index} _ =>
      generalHistory_is_atLeastBinary (publicRelationalConstitutiveRoles index)
    unboundedIndex := id
    unboundedProblem := fun _ => ()
    unboundedStages := fun bound => Nat.le_succ bound }

/-- The same public execution as a member of the general binary subclass. -/
def publicBinaryRelationalRoleExtensiveFamily :
    BinaryRelationalRoleExtensiveFamily :=
  { toRelationalRoleExtensiveFamily := publicRelationalRoleExtensiveFamily
    binaryOpenings := fun {index} _ =>
      generalHistory_is_uniformBinary
        (publicRelationalConstitutiveRoles index) }

theorem publicGeneralSourceWidth (input : Nat) :
    (publicRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ()).frontier.length = 2 ^ (input + 1) := by
  change (relationalProfileFiniteCarrier
    (publicGeneralRelationalHistory input)).frontier.length = 2 ^ (input + 1)
  rw [relationalProfileFiniteCarrier_width]
  exact generalHistory_width_eq_twoPow
    (publicRelationalConstitutiveRoles input)

/-- Public specialization of the general `iff`, derived rather than restated. -/
theorem publicGeneral_fullWidth_iff_preservesConstitutedIdentities
    (input : Nat)
    (regime : ObligationRegime
      (publicRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.HasFullExtensiveWidth ↔ PreservesIdentitiesSeparately regime :=
  RelationalRoleExtensiveFamily.fullWidth_iff_preservesConstitutedIdentities
    publicRelationalRoleExtensiveFamily () regime

/-- Public factorized-capacity specialization of the general theorem. -/
theorem publicGeneral_fullWidth_iff_exactRegimeCapacity
    (input : Nat)
    (regime : ObligationRegime
      (publicRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.HasFullExtensiveWidth ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (publicRelationalRoleExtensiveFamily.sourceCarrier
            (index := input) ()).frontier.length) :=
  RelationalRoleExtensiveFamily.fullWidth_iff_exactRegimeCapacity
    publicRelationalRoleExtensiveFamily () regime

/--
Public specialization of the class-level target: exact `2^(input+1)` width is
equivalent to separate conservation of the already constituted identities.
-/
theorem publicBinary_exponentialWidth_iff_preservesConstitutedIdentities
    (input : Nat)
    (regime : ObligationRegime
      (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      PreservesIdentitiesSeparately regime :=
  BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
    publicBinaryRelationalRoleExtensiveFamily () regime

/-
The class theorem transported back to the literal carrier of the authoritative
executed roles.  The quantified regime here is not on the general-history
adapter carrier.  Elaboration crosses the complete dependent history adapter,
so this single theorem receives a local heartbeat allowance.
-/
set_option maxHeartbeats 800000 in
theorem publicBinary_exponentialWidth_iff_carry_injective_on_executedCarrier
    (input : Nat)
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective regime.carry := by
  let generalCarrier :=
    publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
      (index := input) ()
  let executedCarrier := publicRoleProfileFiniteCarrier input
  let transport : ExactTypeTransport
      generalCarrier.Identity executedCarrier.Identity :=
    generalConcreteProfileTransport
      (publicRelationalConstitutiveRoles input)
  let reindexed : ObligationRegime generalCarrier :=
    reindexObligationRegimeAlongExactTransport
      (source := generalCarrier) (target := executedCarrier)
      transport regime
  have classIff :=
    publicBinary_exponentialWidth_iff_preservesConstitutedIdentities
      input reindexed
  have injectiveIff :=
    reindexObligationRegime_carry_injective_iff transport regime
  constructor
  · intro widthExact
    exact injectiveIff.mp (classIff.mp widthExact)
  · intro carryInjective
    exact classIff.mpr (injectiveIff.mpr carryInjective)

/-- Exact separately-addressable capacity form of the same public `iff`. -/
theorem publicBinary_exponentialWidth_iff_exactRegimeCapacity
    (input : Nat)
    (regime : ObligationRegime
      (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
            (index := input) ()).frontier.length) :=
  BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_exactRegimeCapacity
    publicBinaryRelationalRoleExtensiveFamily () regime

/-- Program compiled from exactly the same public role history. -/
def publicRoleIndexedProgram (input : Nat) :
    RoleIndexedProgram (publicRelationalConstitutiveRoles input) :=
  compileRoleHistory (publicRelationalConstitutiveRoles input)

theorem publicRoleIndexedProgram_atomCount (input : Nat) :
    (publicRoleIndexedProgram input).atomCount = input + 1 :=
  compileRoleHistory_atomCount_exact
    (publicRelationalConstitutiveRoles input)

theorem publicRoleIndexedProgram_interpretationExact
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) :
    interpretRoleOccurrenceProfile
        (publicRoleIndexedProgram input) profile
        (canonicalRoleProfilePayload
          (publicRelationalConstitutiveRoles input) profile) =
      completedRoleAssignments (publicRelationalConstitutiveRoles input) :=
  interpretCompiledRoleHistory_exact
    (publicRelationalConstitutiveRoles input) profile

/-- Causal reduction of that same compiled public program. -/
def publicExecutedRoleReduction (input : Nat) :
    ExecutedRoleReductionHistory (publicRoleIndexedProgram input) :=
  buildExecutedRoleReductionHistory (publicRelationalConstitutiveRoles input)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalOpeningStageOfRole
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistoryOfRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalOpeningOccurrenceTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.productExactTypeTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalConcreteProfileTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.reindexObligationRegimeAlongExactTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.reindexObligationRegime_carry_injective_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistory_is_uniformBinary
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistory_is_atLeastBinary
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistory_width_eq_twoPow
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalInitialState
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneralRelationalHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinaryRelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneralSourceWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneral_fullWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneral_fullWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinary_exponentialWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinary_exponentialWidth_iff_carry_injective_on_executedCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinary_exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleIndexedProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleIndexedProgram_atomCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleIndexedProgram_interpretationExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicExecutedRoleReduction
/- AXIOM_AUDIT_END -/
