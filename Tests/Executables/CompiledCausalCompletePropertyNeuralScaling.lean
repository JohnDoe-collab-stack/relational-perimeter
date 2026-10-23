import RelationalPerimeter.Agents.Neural.CausalCompletePropertyScalingMeasurement

/-!
# Executable driver for causal complete-property scaling

Each iteration times two independently invoked compiled paths from the same
checked source and proof-free command.  Both certify the successor produced by
the source-consuming action/effect chain.  The trace then continues from the
incremental successor itself.  Output is raw observation only; the frozen
external protocol owns aggregation and any gain decision.
-/
namespace ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling
open ConstitutiveSearch.NeuralAgent

def versionText : ScalingArtifactVersion -> String
  | .source => "source"
  | .local => "local"
  | .extended => "extended"

def errorText : ScalingCheckerError -> String
  | .initial => "initial"
  | .target => "target"
  | .transition => "transition"
  | .structuralAssembly => "structural-assembly"
  | .structuralMismatch => "structural-mismatch"

structure ParsedNat where
  accepted : Bool
  value : Nat

def decimalCode (code : Nat) : ParsedNat :=
  if 48 <= code then
    if code <= 57 then
      { accepted := true, value := code - 48 }
    else
      { accepted := false, value := 0 }
  else
    { accepted := false, value := 0 }

def parseNatBytes (bytes : ByteArray) : Nat -> Nat -> Nat -> ParsedNat
  | 0, _, accumulated => { accepted := true, value := accumulated }
  | remaining + 1, index, accumulated =>
      if within : index < bytes.size then
        let digit := decimalCode (bytes[index]'within).toNat
        if digit.accepted then
          parseNatBytes bytes remaining (index + 1)
            (accumulated * 10 + digit.value)
        else
          { accepted := false, value := 0 }
      else
        { accepted := false, value := 0 }

def parseNat (value : String) : ParsedNat :=
  let bytes := value.toUTF8
  if bytes.size = 0 then
    { accepted := false, value := 0 }
  else
    parseNatBytes bytes bytes.size 0 0

/-- Force source, action, effect and successor data.  This checksum is not a
complexity estimate; it prevents timings from observing an unforced shell. -/
def transitionChecksum
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) : Nat :=
  let production := analysis.production.production
  current.state.memory.register.length +
    production.action.result.1.register.length +
    production.action.result.2.productions.length +
    production.effect.successor.register.length +
    production.effect.event.productions.length +
    production.target.memory.register.length + 1

def emitObservation
    (size step initialNanoseconds incrementalNanoseconds fullNanoseconds
      initialCertificateEntries initialSemanticChecksum transitionForce : Nat)
    (version : ScalingArtifactVersion)
    (metrics : ScalingPairMetrics)
    (cost : ScalingCompleteCost)
    (incrementalSemanticChecksum fullSemanticChecksum sourceRegisterLength
      targetRegisterLength : Nat) : IO Unit := do
  IO.print "{\"family_id\":\"compiled-causal-complete-property-scaling-v12\","
  IO.print "\"status\":\"accepted\",\"size\":"
  IO.print (Nat.repr size)
  IO.print ",\"step\":"
  IO.print (Nat.repr step)
  IO.print ",\"version\":\""
  IO.print (versionText version)
  IO.print "\",\"initial_nanoseconds\":"
  IO.print (Nat.repr initialNanoseconds)
  IO.print ",\"incremental_nanoseconds\":"
  IO.print (Nat.repr incrementalNanoseconds)
  IO.print ",\"full_recheck_nanoseconds\":"
  IO.print (Nat.repr fullNanoseconds)
  IO.print ",\"neural_nodes\":"
  IO.print (Nat.repr metrics.neuralNodeCount)
  IO.print ",\"profile_width\":"
  IO.print (Nat.repr metrics.profileWidth)
  IO.print ",\"causal_graph_nodes\":"
  IO.print (Nat.repr metrics.causalGraphNodeCount)
  IO.print ",\"causal_graph_edges\":"
  IO.print (Nat.repr metrics.causalGraphEdgeCount)
  IO.print ",\"affected_cone\":"
  IO.print (Nat.repr metrics.affectedConeCount)
  IO.print ",\"transported_fragments\":"
  IO.print (Nat.repr metrics.transportedFragmentCount)
  IO.print ",\"recomputed_fragments\":"
  IO.print (Nat.repr metrics.recomputedFragmentCount)
  IO.print ",\"other_necessary_calculations\":"
  IO.print (Nat.repr metrics.otherNecessaryCalculationCount)
  IO.print ",\"source_register_length\":"
  IO.print (Nat.repr sourceRegisterLength)
  IO.print ",\"target_register_length\":"
  IO.print (Nat.repr targetRegisterLength)
  IO.print ",\"transition_force_checksum\":"
  IO.print (Nat.repr transitionForce)
  IO.print ",\"initial_certificate_entries\":"
  IO.print (Nat.repr initialCertificateEntries)
  IO.print ",\"initial_semantic_checksum\":"
  IO.print (Nat.repr initialSemanticChecksum)
  IO.print ",\"incremental_semantic_checksum\":"
  IO.print (Nat.repr incrementalSemanticChecksum)
  IO.print ",\"full_semantic_checksum\":"
  IO.print (Nat.repr fullSemanticChecksum)
  IO.print ",\"conversion_units\":"; IO.print (Nat.repr cost.conversionUnits)
  IO.print ",\"initialization_units\":"; IO.print (Nat.repr cost.initializationUnits)
  IO.print ",\"construction_units\":"; IO.print (Nat.repr cost.constructionUnits)
  IO.print ",\"verification_units\":"; IO.print (Nat.repr cost.verificationUnits)
  IO.print ",\"assembly_units\":"; IO.print (Nat.repr cost.assemblyUnits)
  IO.print ",\"installation_units\":"; IO.print (Nat.repr cost.installationUnits)
  IO.print ",\"execution_units\":"; IO.print (Nat.repr cost.executionUnits)
  IO.print ",\"full_conversion_units\":"; IO.print (Nat.repr cost.fullConversionUnits)
  IO.print ",\"full_initialization_units\":"; IO.print (Nat.repr cost.fullInitializationUnits)
  IO.print ",\"full_construction_units\":"; IO.print (Nat.repr cost.fullConstructionUnits)
  IO.print ",\"full_verification_units\":"; IO.print (Nat.repr cost.fullVerificationUnits)
  IO.print ",\"full_assembly_units\":"; IO.print (Nat.repr cost.fullAssemblyUnits)
  IO.print ",\"full_installation_units\":"; IO.print (Nat.repr cost.fullInstallationUnits)
  IO.print ",\"full_execution_units\":"; IO.print (Nat.repr cost.fullExecutionUnits)
  IO.print ",\"complete_obligations\":"; IO.print (Nat.repr cost.completeObligationCount)
  IO.print ",\"future_trace_length\":"; IO.print (Nat.repr cost.futureTraceLength)
  IO.print ",\"certificate_serialized_bytes\":"; IO.print (Nat.repr cost.targetCertificateBytes)
  IO.print ",\"delta_serialized_bytes\":"; IO.print (Nat.repr cost.deltaBytes)
  IO.print ",\"transported_serialized_bytes\":"; IO.print (Nat.repr cost.transportedBytes)
  IO.print ",\"recomputed_serialized_bytes\":"; IO.print (Nat.repr cost.recomputedBytes)
  IO.print ",\"timing_status\":\"raw-observation-not-a-theorem\"}\n"

def runTrace
    (size initialNanoseconds initialCertificateEntries initialSemanticChecksum : Nat)
    (current : CheckedAgent causalScalingMetaContract ()) :
    (step remaining : Nat) -> IO Unit
  | _, 0 => pure ()
  | step, remaining + 1 => do
      let version := scalingVersionAt step
      let update : CausalScalingReceivedArtifact := { size := size, version := version }
      let futureLength := step + 1
      let incrementalStarted <- IO.monoNanosNow
      match checkGenericIncrementalUpdate
          (causalScalingIncrementalCheckerEngine current) update with
      | .error problem => throw (IO.userError (errorText problem))
      | .ok incremental =>
          let incrementalSemanticChecksum := scalingSemanticCertificateChecksum
            incremental.checked.next.certificate futureLength
          let transitionForce := transitionChecksum incremental.analysis
          if incrementalSemanticChecksum = 0 || transitionForce = 0 then
            throw (IO.userError "unforced incremental causal certificate")
          else
            let incrementalFinished <- IO.monoNanosNow
            let fullStarted <- IO.monoNanosNow
            match checkFullUpdate (causalScalingFullRecheckEngine current) update with
            | .error problem => throw (IO.userError (errorText problem))
            | .ok full =>
                let fullSemanticChecksum := scalingSemanticCertificateChecksum
                  full.checked.next.certificate futureLength
                if fullSemanticChecksum = 0 then
                  throw (IO.userError "unforced full causal certificate")
                else if incrementalSemanticChecksum != fullSemanticChecksum then
                  throw (IO.userError "paired causal certificates disagree")
                else
                  let fullFinished <- IO.monoNanosNow
                  let metrics := causalScalingPairMetrics incremental.analysis
                  let cost := causalScalingCompleteCost futureLength
                    initialCertificateEntries incremental.analysis
                  emitObservation size step initialNanoseconds
                    (incrementalFinished - incrementalStarted)
                    (fullFinished - fullStarted) initialCertificateEntries
                    initialSemanticChecksum transitionForce version metrics cost
                    incrementalSemanticChecksum fullSemanticChecksum
                    current.state.memory.register.length
                    incremental.checked.next.state.memory.register.length
                  runTrace size initialNanoseconds initialCertificateEntries
                    initialSemanticChecksum incremental.checked.next
                    (step + 1) remaining

def run (size traceLength : Nat) : IO Unit := do
  let initialStarted <- IO.monoNanosNow
  let initial := causalScalingInitialAgent size
  let initialCertificateEntries :=
    structuralObservationSnapshot initial.certificate |>.length
  let initialSemanticChecksum := scalingSemanticCertificateChecksum
    initial.certificate 1
  if initialCertificateEntries = 0 || initialSemanticChecksum = 0 then
    throw (IO.userError "unforced initial causal certificate")
  else
    let initialFinished <- IO.monoNanosNow
    runTrace size (initialFinished - initialStarted) initialCertificateEntries
      initialSemanticChecksum initial 0 traceLength

def runParsed (sizeText traceText : String) : IO Unit :=
  let size := parseNat sizeText
  let traceLength := parseNat traceText
  if size.accepted && traceLength.accepted then
    run size.value traceLength.value
  else
    throw (IO.userError "expected natural size and trace length")

def runAfterSize (sizeText : String) : List String -> IO Unit
  | [] => throw (IO.userError
      "usage: compiled_causal_complete_property_neural_scaling SIZE TRACE_LENGTH")
  | traceText :: _ => runParsed sizeText traceText

end ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [] => throw (IO.userError
      "usage: compiled_causal_complete_property_neural_scaling SIZE TRACE_LENGTH")
  | sizeText :: remaining =>
      ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.runAfterSize
        sizeText remaining

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.transitionChecksum
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.emitObservation
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.runTrace
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.run
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.runParsed
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCausalCompletePropertyScaling.runAfterSize
#print axioms main
/- AXIOM_AUDIT_END -/
