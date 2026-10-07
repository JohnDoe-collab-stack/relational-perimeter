import Lean
import Tests.ContinuationSignatureBehavior
import Tests.ContinuationSignatureMinimality
import Tests.ContinuationSignatureProduction
import Tests.ContinuationSignatureReachableAgent

/-! Independent coverage of every constant in the newly added signature lot.
The repository-wide audit remains mandatory and is not relaxed here. -/
set_option maxHeartbeats 0
open Lean

run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleText := env.header.moduleNames[index.toNat]!.toString
    unless moduleText.startsWith "RelationalPerimeter.Constitution.Continuation." ||
        moduleText.startsWith "RelationalPerimeter.Agents.ContinuationSignatures." ||
        moduleText.startsWith "Tests.ContinuationSignature" do continue
    checked := checked + 1
    let dependencies ← Lean.collectAxioms name
    unless dependencies.isEmpty do
      throwError "Signature constant audit rejected {name}: {dependencies}"
  logInfo m!"SIGNATURE_CONSTANTS_OK constants={checked} axiomUsers=0"

namespace Tests.ContinuationSignatureAxiomCoverage
theorem runtime_exact (input : Nat) (mode : ConstitutiveSearch.ContinuationSignatures.PayloadMode) :
    ConstitutiveSearch.ContinuationSignatures.publicSignatureMemory input mode =
      (ConstitutiveSearch.ContinuationSignatures.publicSignedExecution input mode).readings :=
  ConstitutiveSearch.ContinuationSignatures.publicSignatureMemory_exact input mode
end Tests.ContinuationSignatureAxiomCoverage
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ContinuationSignatureAxiomCoverage.runtime_exact
/- AXIOM_AUDIT_END -/
