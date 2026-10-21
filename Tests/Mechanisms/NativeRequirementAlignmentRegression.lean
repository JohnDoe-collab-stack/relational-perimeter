import RelationalPerimeter.Agents.Neural.PublicRequirementAlignment

set_option genInjectivity false
namespace Tests.Mechanisms.NativeRequirementAlignmentRegression
open ConstitutiveSearch.NativeMechanism ConstitutiveSearch.NeuralAgent

def denyInput : PublicRequirementInput :=
  { requirement := .deny, context := () }

def allowInput : PublicRequirementInput :=
  { requirement := .allow, context := () }

theorem deny_requirement_scope :
    denyInput.receivedRequirement.scope = [0] := rfl

theorem allow_requirement_scope :
    allowInput.receivedRequirement.scope = [1] := rfl

theorem deny_encoding_exact :
    (publicRequirementSystem.run denyInput).inputs.read
      publicRequirementEncoding.port = publicRequirementEncoding.code .deny :=
  encoded_requirement_exact publicRequirementEncoding denyInput

theorem allow_encoding_exact :
    (publicRequirementSystem.run allowInput).inputs.read
      publicRequirementEncoding.port = publicRequirementEncoding.code .allow :=
  encoded_requirement_exact publicRequirementEncoding allowInput

def deny_executed_path :=
  incorporated_requirement_has_executed_path
    (publicRequirementIncorporation denyInput)

def allow_executed_path :=
  incorporated_requirement_has_executed_path
    (publicRequirementIncorporation allowInput)

def deny_causal_role :
    CausalRole publicRequirementSystem denyInput
      (.receivedInput publicRequirementEncoding.port) :=
  publicRequirementCausalRole denyInput

def allow_causal_role :
    CausalRole publicRequirementSystem allowInput
      (.receivedInput publicRequirementEncoding.port) :=
  publicRequirementCausalRole allowInput

theorem deny_changes_executed_proposal :
    ChangesProposal publicRequirementSystem denyInput
      (publicRequirementIntervention denyInput) :=
  publicRequirementProposalChange denyInput

theorem allow_changes_executed_proposal :
    ChangesProposal publicRequirementSystem allowInput
      (publicRequirementIntervention allowInput) :=
  publicRequirementProposalChange allowInput

def deny_signal_path := publicRequirementSignalPath denyInput
def allow_signal_path := publicRequirementSignalPath allowInput

theorem deny_proposal_aligned :
    publicRequirementSystem.proposal denyInput = false :=
  public_proposal_aligned denyInput

theorem allow_proposal_aligned :
    publicRequirementSystem.proposal allowInput = true :=
  public_proposal_aligned allowInput

theorem requirements_are_not_collapsed :
    denyInput.receivedRequirement ≠ allowInput.receivedRequirement :=
  public_received_requirements_distinct

theorem encodings_are_not_constant :
    publicRequirementEncoding.code .deny ≠
      publicRequirementEncoding.code .allow :=
  public_requirement_codes_distinct

theorem executed_proposals_are_not_constant :
    publicRequirementSystem.proposal denyInput ≠
      publicRequirementSystem.proposal allowInput :=
  public_executed_proposals_distinct

end Tests.Mechanisms.NativeRequirementAlignmentRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_requirement_scope
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_requirement_scope
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_encoding_exact
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_encoding_exact
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_executed_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_executed_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_causal_role
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_causal_role
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_changes_executed_proposal
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_changes_executed_proposal
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_signal_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_signal_path
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.deny_proposal_aligned
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.allow_proposal_aligned
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.requirements_are_not_collapsed
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.encodings_are_not_constant
#print axioms Tests.Mechanisms.NativeRequirementAlignmentRegression.executed_proposals_are_not_constant
/- AXIOM_AUDIT_END -/
