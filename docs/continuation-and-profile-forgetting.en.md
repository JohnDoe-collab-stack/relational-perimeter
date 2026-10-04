# Continuation and forgetting normalized source profiles

The width result and its scientific target remain unchanged. This extension
specifies what can remain available after an actual normalization without
retaining its historical input in restart memory.

## One execution, two interfaces

`UnifiedMaster.publicInstance` initializes and calls the typed-resource executor
once. Its roles, program, normalization, regime and cursor are projections of
this shared result. `UnifiedMaster.certificate` packages that instance and
proofs about it; it is not retained in restart memory.

The closed certificate pins the actual image regime, restart cursor, produced
readers, head-horizon agreement, historical growth and reference reads.
Inspection admission is equivalent to the produced role bound; its event is
the corresponding read of the produced output, not merely an agreement
between two implementations. The compiled-path gate separately guards against
replaying an equal execution: equality of results alone cannot prove that an
executor was called only once.

These laws specify the deterministic bound check and read defined by the
inspection interface; they do not describe an additional discovery.

`ProducedContinuation.publicStart` uses this same typed-resource execution. That
execution supplies both the roles and relations of the normalization and the
reached cursor from which search resumes. `public_execution_exact` proves its
equality to the audited public execution.

The historical interface retains the source profile, executed result and trace.
The restart interface retains only the live state, normalized output and readers
of the actually produced continuations. It stores neither the source profile,
historical result, resource support nor operational prefix. Correspondence
proofs remain separate from the engine.

The live state retains the assignment, generation, seed and provenance still
consumed by discovery. It is not presented as minimal memory or as erasure of
every reconstructible history.

## Grouping and transports on the same roles

Local rules are constructed from the licenses returned by executed stages.
Actions on arbitrary continuations preserve acceptance, and two normalizing
traces transport the same data to the same output. Obligation equality coincides
exactly with produced-target equality without identifying source profiles.

The binary-class theorem applies directly to the master regime: its carrier is
definitionally the carrier of those same role profiles. Full width is
`2^(input+1)` and executed width is one. Partial grouping policies on the same
roles have width `2^k`, where `k` counts separately retained roles. Those policies
are not presented as additional discovery executions.

Code and image transports have both round-trip laws. The normal-position image
is also connected to actually produced-value obligations, with agreement of
`carry`. This transport is established after reduction and its convergence;
its inverse returns a normal position, not the original source profile or
continuation.

A search extension shares
already-produced heads and uses the actually produced profile of the new suffix.
Its embedding preserves old-profile distinction, respects renormalization and
composes both on profiles and on obligations. This historical extension remains
a scientific interface separate from restart memory.

`Instance.grow` receives the stored instance, executes only new steps from its
terminal cursor and attaches the suffix to the stored history. `Growth.resume`
extends that result in turn. Typed references to old resources are transported
into the extended support; preservation of reads, distinction and composition
are proved. The instance transport is pinned to its producer's result rather
than supplied independently. These historical references are not added to
restart memory: its contract admits only the future operations and reads below.

The generic extension also requires a positively constructed `ProducedPrefix`:
the complete cursor must be the resource executor's returned cursor, not an
unrelated support sharing its boundary. Stored attachment is proved equal to
one uninterrupted execution; this proof does not run that execution again.

## The exact future contract

Two operations are admitted:

- request a number of additional steps of the actual engine;
- read a variable of a produced continuation at an existing role.

Role addresses are an ordinal readout derived from the constituted history.
Read admission checks the role bound. Restart operations receive neither the
old profile nor the scientific archive. Preparation extracts the readers once;
future reads do not traverse the history again.

The runtime entry `ProducedContinuation.executeRequests` computes the successor
and events of each request together. Each step shares its production between
the event and the next state. Separate `next` and `event` functions specify the
contract laws; they are not two runtime passes to launch for these results.

The contract preserves discovery, application and decomposition events, live
state reads and observations of produced continuations. These agreements hold
for every finite sequence of requests. Admission is transported in both
directions. A concrete first-role read is constructed and proved to have a
response: the contract is not empty.

The step count is the input of the existing executor. This construction does
not claim a general interactive input language or a solver for arbitrary SAT
instances.

## What is actually forgotten

The public transformed and retained profiles are distinct. Their actually
executed normalizations produce the same restart memory. Every request sequence
in the contract then produces identical future events. No Lean decoder can
uniformly recover the original profile from that memory.

This does not identify the constituted profiles: their identities and distinction
remain established in the historical interface. It loses their historical input
from restart memory under the advertised contract.

These normalization paths must be distinguished from canonical chronological
search prefixes. Reconstruction under exact preservation of depth and the full
provenance list remains true on the latter domain. It does not prove that
forgetting normalized source profiles is impossible.

## Code references

The grouping interfaces are autonomous local reconstructions informed by the
Apache-2.0 comparison material. They use the local role, trace, finite-image
and continuation interfaces; no external foundation or path dependency is
required. The repository's license remains Apache-2.0.

- [Master instance and certificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean): `publicInstance`, `certificate`, `class_iff_on_executed_regime`, `publicGrowth`, `public_obligations_compose`.
- [Master-facade clients](../Tests/UnifiedMasterInstance.lean): direct application of the class theorem, transports, admission and profile loss.
- [Live engine](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/LiveResourceContinuation.lean): production, restart and event exactness.
- [Contract and separator](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean): `memory_fibres`, `public_profile_irrecoverable`, `public_all_future_events`, `publicContractCertificate`.
- [Clients and concrete computation](../Tests/ProducedContinuation.lean).

These proofs establish neither a total-cost bound, a physical-memory bound nor
forgetting of all provenance. They do not weaken the existing operational-width
result.

## Local reproduction

From the repository root:

Python 3 is required by the verifiers. `RELATIONAL_PERIMETER_PYTHON` can select
its executable when `python3` is not available on the command path.

```sh
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
```

Public clients include concrete checkpoint computations alongside the general
proofs. These local checks are not an independent audit.
