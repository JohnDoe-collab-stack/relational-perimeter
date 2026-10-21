import RelationalPerimeter.Agents.Neural.StableNodeIdentity

/-!
# Finite declared domains and causal intervention bases

The operational contract declares the finite current-input domain and the
finite activation alphabet on which its later checker is complete.  A causal
basis is indexed by both that contract and the exact decoded artifact.  Its
coverage witnesses connect every declared input to an intervention and causal
role of the decoded native execution; they do not quantify over arbitrary
integers or over an independently reconstructed network.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- Positive, computational membership in a finite list. -/
inductive Listed {Value : Type u} (value : Value) : List Value -> Type u where
  | head : Listed value (value :: rest)
  | tail : Listed value rest -> Listed value (other :: rest)

/-- A finite equality decision produces either positive list membership or a
function refuting every such witness. -/
def decideListed
    {Value : Type u}
    (equality : (left right : Value) -> Decidable (left = right))
    (value : Value) :
    (values : List Value) ->
      PSum (Listed value values) (Listed value values -> False)
  | [] => .inr (fun witness => nomatch witness)
  | candidate :: rest =>
      match equality value candidate with
      | .isTrue same => by
          subst candidate
          exact .inl .head
      | .isFalse different =>
          match decideListed equality value rest with
          | .inl witness => .inl (.tail witness)
          | .inr impossible =>
              .inr (fun witness =>
                match witness with
                | .head => different rfl
                | .tail later => impossible later)

/-- A current domain covers the domain declared by the operational contract
when every positive declaration has a positive occurrence in the basis. -/
def CoversDeclaredCurrentDomain
    (contract : ConstitutiveContract)
    (currentInputs : List (RequirementInput contract.family)) : Type :=
  (input : RequirementInput contract.family) ->
    Listed input contract.declaredCurrentInputs ->
      Listed input currentInputs

/-- For one declared input, a listed candidate intervention genuinely carries
a causal role in the proposal produced by the decoded system. -/
structure CausalCandidateCoverage
    {contract : ConstitutiveContract}
    (artifact : DecodedNeuralArtifact contract)
    (naming : StableArtifactNaming artifact)
    (replacements : StableNodeId naming -> List Activation)
    (input : RequirementInput contract.family) : Type where
  node : StableNodeId naming
  role : CausalRole artifact.system input (node.occurrence input)
  replacementListed : Listed role.intervention.replacement (replacements node)
  replacementDeclared :
    Listed role.intervention.replacement contract.declaredReplacementValues

/-- Coverage is relative to the finite domain declared by the contract.  It
requires one executed causal candidate for every positively declared input. -/
def CoversDeclaredCausalCondition
    {contract : ConstitutiveContract}
    (artifact : DecodedNeuralArtifact contract)
    (naming : StableArtifactNaming artifact)
    (replacements : StableNodeId naming -> List Activation) : Type :=
  (input : RequirementInput contract.family) ->
    Listed input contract.declaredCurrentInputs ->
      CausalCandidateCoverage artifact naming replacements input

/-- The checker-facing finite basis.  Both equality procedures are stored
explicitly, so later checkers can decide only the announced finite domain and
activation alphabet. -/
structure FiniteCausalBasis
    (contract : ConstitutiveContract)
    (artifact : DecodedNeuralArtifact contract) : Type 4 where
  currentInputs : List (RequirementInput contract.family)
  currentInputsComplete :
    CoversDeclaredCurrentDomain contract currentInputs
  inputEquality :
    (left right : RequirementInput contract.family) -> Decidable (left = right)
  naming : StableArtifactNaming artifact
  replacements : StableNodeId naming -> List Activation
  replacementCoverage :
    CoversDeclaredCausalCondition artifact naming replacements
  replacementEquality :
    (left right : Activation) -> Decidable (left = right)

def FiniteCausalBasis.decideCurrentInput
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (basis : FiniteCausalBasis contract artifact)
    (input : RequirementInput contract.family) :
    PSum (Listed input basis.currentInputs)
      (Listed input basis.currentInputs -> False) :=
  decideListed basis.inputEquality input basis.currentInputs

def FiniteCausalBasis.decideReplacement
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (basis : FiniteCausalBasis contract artifact)
    (node : StableNodeId basis.naming)
    (replacement : Activation) :
    PSum (Listed replacement (basis.replacements node))
      (Listed replacement (basis.replacements node) -> False) :=
  decideListed basis.replacementEquality replacement (basis.replacements node)

/-- Reflection for a positive executable input decision.  It remains data in
`Type`, so the membership witness is not erased before a later checker uses
it. -/
def FiniteCausalBasis.currentInputDecision_positive
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (basis : FiniteCausalBasis contract artifact)
    (input : RequirementInput contract.family)
    (witness : Listed input basis.currentInputs)
    (_exact : basis.decideCurrentInput input = .inl witness) :
    Listed input basis.currentInputs := by
  exact witness

/-- Reflection for a positive executable replacement decision. -/
def FiniteCausalBasis.replacementDecision_positive
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (basis : FiniteCausalBasis contract artifact)
    (node : StableNodeId basis.naming)
    (replacement : Activation)
    (witness : Listed replacement (basis.replacements node))
    (_exact : basis.decideReplacement node replacement = .inl witness) :
    Listed replacement (basis.replacements node) := by
  exact witness

/-! ## Closed public basis -/

def publicRequirementInputEquality
    (left right : PublicRequirementInput) : Decidable (left = right) := by
  cases left with
  | mk leftRequirement leftContext =>
      cases right with
      | mk rightRequirement rightContext =>
          cases leftRequirement <;> cases rightRequirement <;>
            cases leftContext <;> cases rightContext <;>
              first
              | exact .isTrue rfl
              | exact .isFalse (fun same => nomatch same)

def publicActivationEquality
    (left right : Activation) : Decidable (left = right) :=
  Int.decEq left right

def publicCausalReplacements
    (node : StableNodeId publicInitialStableNaming) : List Activation :=
  match node with
  | .receivedInput _ => [2, 3]
  | .neuron _ => [0, 1]

def publicCausalCoverage : CoversDeclaredCausalCondition
    publicDecodedRequirementArtifact publicInitialStableNaming
      publicCausalReplacements := by
  intro input declared
  cases input with
  | mk requirement context =>
      cases requirement <;> cases context
      · exact
          { node := .receivedInput publicRequirementPort
            role := publicRequirementCausalRole
              (RequirementInput.mk .scopeZero .direct)
            replacementListed := .tail .head
            replacementDeclared := .tail (.tail (.tail .head)) }
      · exact
          { node := .receivedInput publicRequirementPort
            role := publicRequirementCausalRole
              (RequirementInput.mk .scopeZero .reversed)
            replacementListed := .head
            replacementDeclared := .tail (.tail .head) }
      · exact
          { node := .receivedInput publicRequirementPort
            role := publicRequirementCausalRole
              (RequirementInput.mk .scopeOne .direct)
            replacementListed := .head
            replacementDeclared := .tail (.tail .head) }
      · exact
          { node := .receivedInput publicRequirementPort
            role := publicRequirementCausalRole
              (RequirementInput.mk .scopeOne .reversed)
            replacementListed := .tail .head
            replacementDeclared := .tail (.tail (.tail .head)) }

def publicFiniteCausalBasis : FiniteCausalBasis
    PublicInitialOperationalContract publicDecodedRequirementArtifact where
  currentInputs := publicDeclaredCurrentInputs
  currentInputsComplete := fun _ witness => witness
  inputEquality := publicRequirementInputEquality
  naming := publicInitialStableNaming
  replacements := publicCausalReplacements
  replacementCoverage := publicCausalCoverage
  replacementEquality := publicActivationEquality

def publicFirstDeclaredInput : PublicRequirementInput :=
  RequirementInput.mk .scopeZero .direct

theorem publicFirstDeclaredInput_is_decided :
    Nonempty (Listed publicFirstDeclaredInput
      publicFiniteCausalBasis.currentInputs) :=
  ⟨.head⟩

theorem publicFirstDeclaredInput_decision_exact :
    publicFiniteCausalBasis.decideCurrentInput publicFirstDeclaredInput =
      .inl (.head : Listed publicFirstDeclaredInput
        publicFiniteCausalBasis.currentInputs) :=
  rfl

theorem publicInputReplacement_is_decided :
    Nonempty (Listed (3 : Activation)
      (publicFiniteCausalBasis.replacements
        (.receivedInput publicRequirementPort))) :=
  ⟨.tail .head⟩

theorem publicInputReplacement_decision_exact :
    publicFiniteCausalBasis.decideReplacement
        (.receivedInput publicRequirementPort) 3 =
      .inl (.tail .head : Listed (3 : Activation)
        (publicFiniteCausalBasis.replacements
          (.receivedInput publicRequirementPort))) :=
  rfl

/-! ## Closed reconfigured reference basis -/

def publicReconfiguredRequirementNode :
    StableNodeId publicReconfiguredStableNaming :=
  .receivedInput publicReconfigurationRequirementPort

def publicReconfiguredCausalReplacements
    (_node : StableNodeId publicReconfiguredStableNaming) :
    List Activation :=
  [publicReconfigurationRequirementReplacement publicSubstantiveNext]

def publicReconfiguredCausalCoverage : CoversDeclaredCausalCondition
    publicDecodedReconfiguredArtifact publicReconfiguredStableNaming
      publicReconfiguredCausalReplacements := by
  intro input declared
  cases declared with
  | head =>
      exact
        { node := publicReconfiguredRequirementNode
          role := publicReconfigurationRequirementCausalRoleFrom
            publicRequirementSystem publicSubstantiveSource
            publicSubstantiveNext
          replacementListed := .head
          replacementDeclared := .tail (.tail .head) }
  | tail impossible => nomatch impossible

def publicReconfiguredFiniteCausalBasis : FiniteCausalBasis
    PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact where
  currentInputs := [publicSubstantiveNext]
  currentInputsComplete := fun _ witness => witness
  inputEquality := publicRequirementInputEquality
  naming := publicReconfiguredStableNaming
  replacements := publicReconfiguredCausalReplacements
  replacementCoverage := publicReconfiguredCausalCoverage
  replacementEquality := publicActivationEquality

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Listed
#print axioms ConstitutiveSearch.NeuralAgent.decideListed
#print axioms ConstitutiveSearch.NeuralAgent.CoversDeclaredCurrentDomain
#print axioms ConstitutiveSearch.NeuralAgent.CausalCandidateCoverage
#print axioms ConstitutiveSearch.NeuralAgent.CoversDeclaredCausalCondition
#print axioms ConstitutiveSearch.NeuralAgent.FiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.FiniteCausalBasis.decideCurrentInput
#print axioms ConstitutiveSearch.NeuralAgent.FiniteCausalBasis.decideReplacement
#print axioms ConstitutiveSearch.NeuralAgent.FiniteCausalBasis.currentInputDecision_positive
#print axioms ConstitutiveSearch.NeuralAgent.FiniteCausalBasis.replacementDecision_positive
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementInputEquality
#print axioms ConstitutiveSearch.NeuralAgent.publicActivationEquality
#print axioms ConstitutiveSearch.NeuralAgent.publicCausalReplacements
#print axioms ConstitutiveSearch.NeuralAgent.publicCausalCoverage
#print axioms ConstitutiveSearch.NeuralAgent.publicFiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.publicFirstDeclaredInput_is_decided
#print axioms ConstitutiveSearch.NeuralAgent.publicFirstDeclaredInput_decision_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicInputReplacement_is_decided
#print axioms ConstitutiveSearch.NeuralAgent.publicInputReplacement_decision_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredRequirementNode
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredCausalReplacements
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredCausalCoverage
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredFiniteCausalBasis
/- AXIOM_AUDIT_END -/
