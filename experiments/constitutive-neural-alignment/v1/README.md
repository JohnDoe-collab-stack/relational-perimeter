# Frozen comparison protocol and independent learned artifact

This directory is a pre-confirmatory scientific input, not an experimental
result. `comparison-protocol.json` freezes the six comparison classes, their
interfaces, the common material, and the eight capabilities that later runs
must report separately. A missing adapter is never counted as a negative
result.

`training-data.json` is the complete locally defined synthetic domain of two
requirements, two contexts, and two authorization states. The deterministic
learner searches integer threshold neurons and emits a three-version artifact:
the initial learned network and two successive learned transformations. The
network exposes an authorization-sensitive output, the authorization
observation, and an explicit bypass observation. No external data or weights
are stored in the repository, and no learned weight is edited by hand.

Reproduce and verify from the repository root with:

```text
python3 scripts/check-independent-neural-artifact.py
```

The verifier checks every recorded SHA-256 hash, reruns the learner in a fresh
temporary directory, and requires byte-for-byte equality of the JSON artifact,
the generated Lean source, and the manifest. Confirmatory comparison remains
forbidden until the later aligned/bypass adapters and their common trace have
been frozen.
