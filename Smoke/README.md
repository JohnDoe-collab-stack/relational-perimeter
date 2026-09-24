# Executable smoke trace

`EndogenousOperationalTrace.lean` exposes one closed stage-three computation.
It is deliberately separated from the proof modules and is **not** presented
as a scientific proof or a confirmatory experiment.  The corresponding
general statements are proved in Lean and checked in `Tests/`.

The frozen observation is versioned as
`endogenous-operational-trace-v1.expected`.

- command: `lake env lean Smoke/EndogenousOperationalTrace.lean`;
- parameters: `stage = 3`, absorbed continuation `7`, retained continuation
  `8`, feedback comparison at stage `0`;
- random seeds: none;
- source and expected-output fingerprints: recorded by `MANIFEST.sha256`;
- repository revision: the Git revision containing these files.

Run `scripts/verify-smoke.ps1` on PowerShell or
`bash scripts/verify-smoke.sh` on a POSIX shell to execute the computation and
compare its tagged output with the frozen observation.

The eight values are, in order: candidate count, attempt count, failure count,
reconstructed-relation flag, absorbed-left result, retained-right result, next
attempts with the produced decision, and next attempts after forgetting that
decision.
