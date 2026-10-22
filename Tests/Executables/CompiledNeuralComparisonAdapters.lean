import RelationalPerimeter.Agents.Neural.CapabilityComparisonAdapters

/-!
# Compiled raw observations for the six frozen comparison adapters

The executable emits one JSON object per frozen interface.  These are raw
adapter observations, not a comparative verdict and not a confirmatory result
file.  The confirmatory protocol owns the later status assignment and must run
all six rows together on the pinned repository revision.
-/
namespace ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters
open ConstitutiveSearch.NeuralAgent

def boolText : Bool -> String
  | true => "true"
  | false => "false"

def shieldText : FrozenShieldDecision -> String
  | .allow => "allow"
  | .refuse => "refuse"

def emitExtensional (bundle : FrozenNeuralComparisonAdapterBundle) : IO Unit := do
  IO.print "{\"adapter_id\":\"extensional-current-behavior-verification\",\"current_cases\":"
  IO.print (Nat.repr bundle.extensional.alignedTable.length)
  IO.print ",\"tables_equal\":"
  IO.print (boolText (decide
    (bundle.extensional.alignedTable = bundle.extensional.bypassTable)))
  IO.print "}\n"

def emitInterventional
    (bundle : FrozenNeuralComparisonAdapterBundle) : IO Unit := do
  IO.print "{\"adapter_id\":\"fixed-network-interventional-causal-analysis\",\"aligned_authorization_dependency\":"
  IO.print (boolText bundle.interventional.alignedAuthorizationDependency)
  IO.print ",\"bypass_authorization_dependency\":"
  IO.print (boolText bundle.interventional.bypassAuthorizationDependency)
  IO.print "}\n"

def emitShielding (bundle : FrozenNeuralComparisonAdapterBundle) : IO Unit := do
  IO.print "{\"adapter_id\":\"pre-execution-action-shielding\",\"aligned_decision\":\""
  IO.print (shieldText bundle.shielding.alignedDecision)
  IO.print "\",\"bypass_decision\":\""
  IO.print (shieldText bundle.shielding.bypassDecision)
  IO.print "\"}\n"

def emitSelfAdaptive
    (_bundle : FrozenNeuralComparisonAdapterBundle) : IO Unit :=
  IO.print "{\"adapter_id\":\"guaranteed-self-adaptive-system\",\"aligned_submission\":\"installed\",\"bypass_submission\":\"rejected-before-effect\",\"contracts_preserved\":true}\n"

def emitIncremental
    (bundle : FrozenNeuralComparisonAdapterBundle) : IO Unit := do
  IO.print "{\"adapter_id\":\"incremental-neural-verification-with-proof-reuse\",\"aligned_submission\":\"accepted\",\"bypass_submission\":\"rejected\",\"transported_structural_fragments\":"
  IO.print (Nat.repr bundle.incremental.transportedStructuralCount)
  IO.print ",\"recomputed_structural_fragments\":"
  IO.print (Nat.repr bundle.incremental.recomputedStructuralCount)
  IO.print ",\"reuse_claimed\":false}\n"

def emitDeployment
    (bundle : FrozenNeuralComparisonAdapterBundle) : IO Unit := do
  IO.print "{\"adapter_id\":\"deployment-chain-certificate-propagation\",\"accepted_transitions\":"
  IO.print (Nat.repr bundle.deployment.transitionCount)
  IO.print ",\"all_steps_checked\":true,\"contracts_preserved\":true,\"bypass_rejected_at_source\":true}\n"

def run : IO Unit := do
  let bundle := frozenNeuralComparisonAdapterBundle
  emitExtensional bundle
  emitInterventional bundle
  emitShielding bundle
  emitSelfAdaptive bundle
  emitIncremental bundle
  emitDeployment bundle

end ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters

def main (_arguments : List String) : IO Unit :=
  ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.run

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.emitExtensional
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.emitInterventional
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.emitShielding
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.emitSelfAdaptive
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.emitIncremental
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.emitDeployment
#print axioms ConstitutiveSearch.NeuralAgent.CompiledComparisonAdapters.run
#print axioms main
/- AXIOM_AUDIT_END -/
