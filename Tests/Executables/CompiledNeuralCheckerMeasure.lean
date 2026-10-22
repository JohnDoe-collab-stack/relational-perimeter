import RelationalPerimeter.Agents.Neural.IncrementalReferenceEquivalence

/-!
# Measurement entry point for the compiled neural checkers

This executable calls the public incremental checker and the complete
reference checker defined by the library.  It does not reproduce either
algorithm in a measurement script.  Its scope is deliberately the exact
public update: elapsed times are observations for that fixed artifact, not a
scaling theorem.
-/
namespace ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure
open ConstitutiveSearch.NeuralAgent

def warmupCount : Nat := 50

def measuredCount : Nat := 1000

structure IncrementalObservation where
  accepted : Bool
  affected : Nat
  transported : Nat
  recomputed : Nat
  assembled : Nat
  checksum : Nat

structure ReferenceObservation where
  accepted : Bool
  checksum : Nat

def observeIncremental
    (update : IncrementalNeuralUpdate) : IncrementalObservation :=
  match checkIncrementalUpdate update with
  | .error _ =>
      { accepted := false
        affected := 0
        transported := 0
        recomputed := 0
        assembled := 0
        checksum := 0 }
  | .ok checked =>
      let affected := checked.affectedCone.length
      let transported := checked.transportedCount
      let recomputed := checked.recomputedCount
      let assembled := checked.assembledStructuralFragments.length
      { accepted := true
        affected := affected
        transported := transported
        recomputed := recomputed
        assembled := assembled
        checksum := affected + transported + recomputed + assembled + 1 }

def observeReference
    (update : FullReferenceNeuralUpdate) : ReferenceObservation :=
  match checkReferenceUpdate update with
  | .error _ => { accepted := false, checksum := 0 }
  | .ok _ => { accepted := true, checksum := 1 }

def warmIncremental (update : IncrementalNeuralUpdate) : Nat -> IO Unit
  | 0 => pure ()
  | count + 1 => do
      let observation := observeIncremental update
      if observation.accepted then
        warmIncremental update count
      else
        throw (IO.userError "incremental checker rejected during warmup")

def warmReference (update : FullReferenceNeuralUpdate) : Nat -> IO Unit
  | 0 => pure ()
  | count + 1 => do
      let observation := observeReference update
      if observation.accepted then
        warmReference update count
      else
        throw (IO.userError "reference checker rejected during warmup")

def runIncremental (update : IncrementalNeuralUpdate) :
    Nat -> Nat -> IO (Nat × IncrementalObservation)
  | 0, checksum =>
      pure (checksum, observeIncremental update)
  | count + 1, checksum => do
      let observation := observeIncremental update
      if observation.accepted then
        runIncremental update count (checksum + observation.checksum)
      else
        throw (IO.userError "incremental checker rejected during measurement")

def runReference (update : FullReferenceNeuralUpdate) :
    Nat -> Nat -> IO (Nat × ReferenceObservation)
  | 0, checksum =>
      pure (checksum, observeReference update)
  | count + 1, checksum => do
      let observation := observeReference update
      if observation.accepted then
        runReference update count (checksum + observation.checksum)
      else
        throw (IO.userError "reference checker rejected during measurement")

structure TimedIncremental where
  elapsedNanoseconds : Nat
  checksum : Nat
  observation : IncrementalObservation

structure TimedReference where
  elapsedNanoseconds : Nat
  checksum : Nat
  observation : ReferenceObservation

def measureIncremental (update : IncrementalNeuralUpdate) :
    IO TimedIncremental := do
  warmIncremental update warmupCount
  let started <- IO.monoNanosNow
  let result <- runIncremental update measuredCount 0
  let finished <- IO.monoNanosNow
  pure
    { elapsedNanoseconds := finished - started
      checksum := result.1
      observation := result.2 }

def measureReference (update : FullReferenceNeuralUpdate) :
    IO TimedReference := do
  warmReference update warmupCount
  let started <- IO.monoNanosNow
  let result <- runReference update measuredCount 0
  let finished <- IO.monoNanosNow
  pure
    { elapsedNanoseconds := finished - started
      checksum := result.1
      observation := result.2 }

def boolText (value : Bool) : String :=
  if value then "true" else "false"

def emitResult
    (incremental : TimedIncremental)
    (reference : TimedReference) : IO Unit := do
  IO.print "{\"measurement_id\":\"compiled-neural-checker-v5\","
  IO.print "\"scope\":\"fixed-public-update\",\"warmup_count\":"
  IO.print (Nat.repr warmupCount)
  IO.print ",\"measured_count\":"
  IO.print (Nat.repr measuredCount)
  IO.print ",\"incremental\":{\"accepted\":"
  IO.print (boolText incremental.observation.accepted)
  IO.print ",\"elapsed_nanoseconds\":"
  IO.print (Nat.repr incremental.elapsedNanoseconds)
  IO.print ",\"checksum\":"
  IO.print (Nat.repr incremental.checksum)
  IO.print ",\"affected_cone_size\":"
  IO.print (Nat.repr incremental.observation.affected)
  IO.print ",\"transported_fragments\":"
  IO.print (Nat.repr incremental.observation.transported)
  IO.print ",\"recomputed_fragments\":"
  IO.print (Nat.repr incremental.observation.recomputed)
  IO.print ",\"assembled_fragments\":"
  IO.print (Nat.repr incremental.observation.assembled)
  IO.print "},\"reference\":{\"accepted\":"
  IO.print (boolText reference.observation.accepted)
  IO.print ",\"elapsed_nanoseconds\":"
  IO.print (Nat.repr reference.elapsedNanoseconds)
  IO.print ",\"checksum\":"
  IO.print (Nat.repr reference.checksum)
  IO.print "},\"exact_result_theorem\":true,"
  IO.print "\"timing_status\":\"observational-not-a-theorem\"}\n"

theorem measuredChecksExact :
    eraseIncrementalCheckResult
        (checkIncrementalUpdate publicIncrementalNeuralUpdate) =
      checkReferenceUpdate publicFullReferenceNeuralUpdate :=
  publicIncrementalAndReferenceChecks_exact

def selectedIncrementalUpdate (selector : String) : IncrementalNeuralUpdate :=
  if selector == "public-update-v1" then
    publicIncrementalNeuralUpdate
  else
    publicIncorrectIncrementalUpdate

def run (selector : String) : IO Unit := do
  let update := selectedIncrementalUpdate selector
  let incremental <- measureIncremental update
  let reference <- measureReference update.toFullReferenceUpdate
  emitResult incremental reference

end ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure

def main (arguments : List String) : IO Unit := do
  let selector := match arguments with
    | head :: _ => head
    | [] => ""
  ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.run selector

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.observeIncremental
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.observeReference
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.warmIncremental
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.runIncremental
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.measureIncremental
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.emitResult
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.measuredChecksExact
#print axioms ConstitutiveSearch.NeuralAgent.CompiledCheckerMeasure.run
#print axioms main
/- AXIOM_AUDIT_END -/
