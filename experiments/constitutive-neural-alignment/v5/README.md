# Compiled neural checker measurement v5

This campaign closes the measurement-to-checker connection.  The measured
program is a Lake executable whose Lean source imports the public checker
modules and calls `checkIncrementalUpdate` and `checkReferenceUpdate` directly.
The Python runner only freezes hashes, builds that executable, launches it and
records its JSON output.  It contains no checker algorithm.

The measured reference input is derived from the same runtime-selected
incremental input through `IncrementalNeuralUpdate.toFullReferenceUpdate`.
The library theorem `publicIncrementalAndReferenceChecks_exact` proves that the
two public successful results are exactly equal after erasing incremental
accounting.  The executable also reports the affected cone and the transported,
recomputed and assembled fragment counts returned by the compiled incremental
checker.

The confirmatory command was frozen before the run in
`measurement-protocol.json`; it produced the immutable reference
`measurement-results.json`.  Do not overwrite that file.  A reproduction must
write to a distinct untracked path, for example:

```powershell
py -3 scripts/run-compiled-neural-checker-measurement.py --protocol experiments/constitutive-neural-alignment/v5/measurement-protocol.json --output reproduced-compiled-neural-checker-v5.json
```

The executable selects its update from a runtime argument.  The frozen valid
selector must succeed; a distinct selector selects the malformed control and
must terminate with a nonzero exit.  This prevents the compiler from replacing
the measured checker call by a precomputed closed observation.

## Scientific boundary

This version measures one fixed public artifact.  Its elapsed times do not
establish a growth law, and it records neither peak memory nor allocations.
The deterministic evidence is the acceptance result, the exact result theorem,
the affected-cone and fragment counts, and rejection of the invalid control.
Timing is retained only as an environmental observation.

The v2 and v3 campaigns remain unchanged historical artifacts.  Because their
Python programs implement separate models, their timing and checked-unit rows
must not be cited as measurements of the compiled Lean checker.
