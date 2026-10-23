import RelationalPerimeter.Agents.Neural.ParameterizedCompiledCheckerFamily

/-!
# Executable driver for the parameterized compiled checker family

The driver emits raw paired observations.  It invokes the library's generic
incremental and full-reference engines on the same generated target at every
step.  It does not interpret the observations and is not, by itself, a
confirmatory protocol or a complexity claim.
-/
namespace ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily
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

def emitObservation
    (size step initialNanoseconds incrementalNanoseconds
      fullNanoseconds initialCertificateEntries : Nat)
    (version : ScalingArtifactVersion)
    (metrics : ScalingPairMetrics) : IO Unit := do
  IO.print "{\"family_id\":\"compiled-parameterized-constitutive-checker-v1\","
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
  IO.print ",\"initial_certificate_entries\":"
  IO.print (Nat.repr initialCertificateEntries)
  IO.print ",\"certificate_delta_entries\":"
  IO.print (Nat.repr
    (metrics.transportedFragmentCount + metrics.recomputedFragmentCount))
  IO.print ",\"execution_units\":"
  IO.print (Nat.repr metrics.neuralNodeCount)
  IO.print ",\"verification_units\":"
  IO.print (Nat.repr
    (metrics.causalGraphNodeCount + metrics.causalGraphEdgeCount))
  IO.print ",\"timing_status\":\"raw-observation-not-a-theorem\"}\n"

def runTrace
    (size initialNanoseconds initialCertificateEntries : Nat)
    (current : CheckedAgent scalingMetaContract ()) :
    (step remaining : Nat) -> IO Unit
  | _, 0 => pure ()
  | step, remaining + 1 => do
      let version := scalingVersionAt step
      let target := scalingTargetArtifact size version
      let incrementalStarted <- IO.monoNanosNow
      let incrementalResult := checkGenericIncrementalUpdate
        (scalingIncrementalCheckerEngine current) target
      match incrementalResult with
      | .error problem =>
          throw (IO.userError (errorText problem))
      | .ok incremental =>
          let metrics := scalingPairMetrics incremental.analysis
          let metricChecksum := metrics.causalGraphNodeCount +
            metrics.causalGraphEdgeCount + metrics.affectedConeCount +
            metrics.transportedFragmentCount + metrics.recomputedFragmentCount
          if metricChecksum = 0 then
            throw (IO.userError "unforced incremental observation")
          else
            let incrementalFinished <- IO.monoNanosNow
            let fullStarted <- IO.monoNanosNow
            let fullResult := checkFullUpdate
              (scalingFullRecheckEngine current) target
            match fullResult with
            | .error problem =>
                throw (IO.userError (errorText problem))
            | .ok full =>
                have _successorExact :
                    incremental.checked.next = full.checked.next := by
                  rfl
                let fullChecksum :=
                  structuralObservationSnapshot
                    full.checked.next.certificate |>.length
                if fullChecksum = 0 then
                  throw (IO.userError "unforced full observation")
                else
                  let fullFinished <- IO.monoNanosNow
                  emitObservation size step initialNanoseconds
                    (incrementalFinished - incrementalStarted)
                    (fullFinished - fullStarted) initialCertificateEntries
                    version metrics
                  runTrace size initialNanoseconds initialCertificateEntries
                    incremental.checked.next (step + 1) remaining

def run (size traceLength : Nat) : IO Unit := do
  let initialStarted <- IO.monoNanosNow
  let initialized := checkScalingInitial size
  match initialized with
  | .error _ => throw (IO.userError "initial checker rejected")
  | .ok success =>
      let initialCertificateEntries :=
        structuralObservationSnapshot success.checkedAgent.certificate |>.length
      if initialCertificateEntries = 0 then
        throw (IO.userError "unforced initial observation")
      else
        let initialFinished <- IO.monoNanosNow
        runTrace size (initialFinished - initialStarted)
          initialCertificateEntries success.checkedAgent 0 traceLength

def runParsed (sizeText traceText : String) : IO Unit :=
  let size := parseNat sizeText
  let traceLength := parseNat traceText
  if size.accepted && traceLength.accepted then
    run size.value traceLength.value
  else
    throw (IO.userError "expected natural size and trace length")

def runAfterSize (sizeText : String) : List String -> IO Unit
  | [] =>
      throw (IO.userError
        "usage: compiled_parameterized_neural_checker FAMILY_SIZE TRACE_LENGTH")
  | traceText :: _ => runParsed sizeText traceText

end ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [] =>
      throw (IO.userError
        "usage: compiled_parameterized_neural_checker FAMILY_SIZE TRACE_LENGTH")
  | sizeText :: remaining =>
      ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.runAfterSize
        sizeText remaining

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.versionText
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.errorText
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.ParsedNat
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.decimalCode
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.parseNatBytes
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.parseNat
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.emitObservation
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.runTrace
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.run
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.runParsed
#print axioms ConstitutiveSearch.NeuralAgent.CompiledParameterizedFamily.runAfterSize
#print axioms main
/- AXIOM_AUDIT_END -/
