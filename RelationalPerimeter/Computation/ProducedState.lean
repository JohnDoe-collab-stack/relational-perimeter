import Init

/-!
# Operational state produced by an executed run

The values transmitted to the next situation are explicit data.  A separate
origin witness records that each field is exactly the value computed from the
run, rather than an externally supplied replacement.
-/

namespace RelationalPerimeter.Computation

universe u

/-- Data retained after one operational run. -/
structure ProducedOperationalState
    (Output Provenance TraceItem Seed : Type u) where
  output : Output
  provenance : List Provenance
  retainedTrace : List TraceItem
  nextSeed : Seed

/-- The four readouts calculated from a run. -/
structure OperationalStateProducer
    (Run Output Provenance TraceItem Seed : Type u) where
  outputOf : Run → Output
  provenanceOf : Run → List Provenance
  retainedTraceOf : Run → List TraceItem
  nextSeedOf : Run → Seed

namespace OperationalStateProducer

/-- Construct the transmitted state directly from the run readouts. -/
def produce
    {Run Output Provenance TraceItem Seed : Type u}
    (producer : OperationalStateProducer
      Run Output Provenance TraceItem Seed)
    (run : Run) :
    ProducedOperationalState Output Provenance TraceItem Seed :=
  { output := producer.outputOf run
    provenance := producer.provenanceOf run
    retainedTrace := producer.retainedTraceOf run
    nextSeed := producer.nextSeedOf run }

end OperationalStateProducer

/-- Proof that a transmitted state was obtained from one specified run. -/
structure ProducedFrom
    {Run Output Provenance TraceItem Seed : Type u}
    (producer : OperationalStateProducer
      Run Output Provenance TraceItem Seed)
    (run : Run)
    (state : ProducedOperationalState Output Provenance TraceItem Seed) : Prop where
  output_exact : state.output = producer.outputOf run
  provenance_exact : state.provenance = producer.provenanceOf run
  retainedTrace_exact : state.retainedTrace = producer.retainedTraceOf run
  nextSeed_exact : state.nextSeed = producer.nextSeedOf run

/-- The canonical produced state carries all four origin equations. -/
theorem OperationalStateProducer.produce_exact
    {Run Output Provenance TraceItem Seed : Type u}
    (producer : OperationalStateProducer
      Run Output Provenance TraceItem Seed)
    (run : Run) :
    ProducedFrom producer run (producer.produce run) :=
  { output_exact := rfl
    provenance_exact := rfl
    retainedTrace_exact := rfl
    nextSeed_exact := rfl }

end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.ProducedOperationalState
#print axioms RelationalPerimeter.Computation.OperationalStateProducer
#print axioms RelationalPerimeter.Computation.OperationalStateProducer.produce
#print axioms RelationalPerimeter.Computation.ProducedFrom
#print axioms RelationalPerimeter.Computation.OperationalStateProducer.produce_exact
/- AXIOM_AUDIT_END -/
