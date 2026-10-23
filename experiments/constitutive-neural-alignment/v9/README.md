# Constitutive neural alignment v9

This directory freezes the inputs for the next joint learned-instance
comparison. It contains no confirmatory result.

`learning-transformation-protocol.json` fixes provenance, reuse rights,
deterministic learning inputs, parameters, commands and the three exact
candidate transformations. `comparison-protocol.json` fixes the common typed
material, six adapter classes, R1--R8, the relational method, the reference
combination, the independent full recheck, P1--P8 and S1--S8.

`manifest.json` records input hashes before any new confirmatory production.
Both reserved result paths must remain absent until a stable repository commit
is recorded and `scripts/check-neural-joint-protocol-v9.py` passes. The frozen
runner `scripts/run-neural-joint-confirmatory-v9.py` then retains all six raw
NDJSON rows and writes a separate post-run record containing the raw output
hash. This avoids an impossible self-hashing result file. Development and
smoke executions remain exploratory. A changed protocol requires a new
version; neither confirmatory output is ever overwritten.
