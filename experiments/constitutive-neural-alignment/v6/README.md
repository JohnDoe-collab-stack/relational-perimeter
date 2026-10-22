# Frozen capability-comparison adapters (v6)

Version 6 preserves the historical v4 protocol and replaces it for future
confirmatory comparison because the shared Lean material changed while its
constitutive interfaces were corrected.  It freezes six compiled, typed
adapters over one private `FrozenNeuralComparisonMaterial` package.

No comparison result is present and no confirmatory command has been run.
The adapters are content-addressed now; a stable repository commit still has
to be recorded before the one permitted confirmatory execution.

The compiled command is:

```text
lake exe compiled_neural_comparison_adapters
```

It emits six raw NDJSON observations.  Raw observations are not verdicts.
Capability statuses must later be produced under the frozen decision rules and
validated against `comparison-result-schema.json`.  The learned incremental
row reports its actual zero transported fragments and does not claim local
reuse on this particular material.

Validate the frozen package without running the adapters:

```text
python3 scripts/check-neural-comparison-adapters-v6.py
```
