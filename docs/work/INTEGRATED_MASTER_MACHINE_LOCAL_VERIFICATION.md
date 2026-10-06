# Local verification before independent integrated-machine audit

This record reports local checks, not an independent scientific verdict.
The scientific tree is commit `8af5818b67e803fd9f5ae4aa52518a593f3b2952` on
`codex/integrated-master-machine-audit-20261006`, with immediate parent
`9354e757e9dc2fbd429c34ff6cf9990140b6eed9`.

## Preparation and separation

Implementation was performed in an isolated checkout. Other active agents'
checkouts and the received frozen inputs were not modified. The parent is the
published historical checkpoint, not a Git commit of the later frozen inputs.
Accordingly, this commit also publishes received agent, continuation-signature
and variable-master updates; they are not all new integration contributions.

The four initial foundational files, license, toolchain and Lake manifest are
unchanged relative to the original validated target
`4e0febf032821882069e7cfefd7e631fc8461d95`.

## Observed local checks

On Windows, with Lean 4.33.1, Python 3, Git Bash and PowerShell 7:

- `lake clean` succeeded before the rebuild.
- The final complete `lake build` succeeded: 242 jobs, no Lean warnings/errors.
- `scripts/verify.ps1` exited 0.
- `bash scripts/verify.sh` exited 0.
- Both verifiers selected 240 Lean files and checked corresponding build output.
- Every Lean file had exactly one final axiom-audit block.
- Exhaustive sweep: 20,548 constants, 239 modules, 364 compiler-generated
  exceptions, zero handwritten axiom-dependent declarations.
- Stratification: 198 production modules, all classified/reachable, no orphans,
  no production import of tests; machine layers are ordered M0–M19.
- All 23 shipped expected-failure fixtures failed with the stated diagnostics.
- Compiled-code checks passed, including the integrated-machine producer and
  configured-routing boundaries and their underlying analyzer self-tests.
- README and new integrated FR/EN local links were checked.
- Staged whitespace check passed; Git's LF/CRLF advisories were not Lean warnings.

An intermediate newly introduced helper proof failed the all-constant gate.
It was replaced by a constructive induction; the verifier's axiom exceptions
were not relaxed. The observations above describe the final corrected tree,
not the failed intermediate attempt.

## Scope

The new bridge consumes the existing master, a received SAT frontier and fixed
scope, shares the live production, obtains the SAT reduction code from actual
finder outcomes, installs its frontier/circuit and preserves all futures of
the combined rich-reference contract. Separate lowering/action theorems justify
SAT semantics; the reference uses the same SAT algorithm.

Local one/two branch witnesses use the same master and formula. These checks
do not establish arbitrary polynomial SAT solving, physical hardware, total
cost, global byte optimality or minimality of the combined memory. The original
role-profile width and the retained SAT frontier are different readouts.

The independent prompt is
[the complete integrated audit request](ARISTOTLE_INTEGRATED_MASTER_MACHINE_AUDIT.md).
Audit acceptance or completion is not claimed by this pre-submission record.
This record and the audit prompt are temporary work documents and must be
removed before any separately authorized merge into main.
