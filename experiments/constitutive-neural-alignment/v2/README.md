# Final mutation and scaling campaign (v2)

This directory is a frozen confirmatory campaign. It does not replace the
constructive Lean theorems.

`final-negative-mutations.json` maps the eight mandatory mutations to fixtures
whose exact Lean error class, line, column, and scientific obligation are
enforced by `scripts/expected_failure_diagnostics.py`.

`scaling-protocol.json` was frozen before `scaling-results.json` was produced.
The generated family grows the relevant chronological neural chain. The same
target well-formedness property is checked by both paths: the complete checker
starts from zero, while the incremental checker compares every reused prefix
fragment and checks the entire affected suffix. Deterministic checked-unit
counts are primary; timings are machine-dependent observations.

Reproduce the recorded run with the command frozen in the protocol. Validate
the protocol, evidence, fragment accounting, and mutation coverage with:

```text
py -3 scripts/check-final-neural-campaign.py
```
