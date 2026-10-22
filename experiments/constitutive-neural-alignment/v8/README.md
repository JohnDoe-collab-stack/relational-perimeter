# Compiled parameterized checker scaling campaign (v8)

Version 8 follows the immutable v7 failure at size 160. It keeps the same Lean
family, compiled executable, six-step schedule, five measured repetitions,
metrics, resource budget and practical-gain rule. Its sole scope correction is
to freeze the confirmatory sizes at 0, 2, 5, 10, 20, 40 and 80, all of which
completed within the v7 resource budget before the v7 run was rejected as a
whole.

The v8 runner reuses the frozen v7 measurement engine through a versioned
wrapper. Both files and the complete Lean source tree are content-addressed.

Confirmatory command:

```text
py -3 scripts/run-compiled-parameterized-neural-scaling-v8.py --protocol experiments/constitutive-neural-alignment/v8/scaling-protocol.json --output experiments/constitutive-neural-alignment/v8/scaling-results.json
```

The result is observational evidence, not a Lean complexity theorem.
