# Exact continuation signatures: roles and the full agent contract

Two historically distinct sources can give the same responses under a fixed
future contract. This addition computes which distinctions that contract must
retain. It also constructs a source whose difference must remain visible and
a continuation that separates it.

The result concerns behavioral distinctions, not minimum bytes or polynomial
cost. The quantum instance and total-cost theorem are not established by these
modules.

## A contract independent of the signature

`FutureContract` specifies transitions, events, reads, admission witnesses and
a constructive admission-or-refusal decision. `Outcome` records reads, events
and admission possibilities for every finite request sequence, including its
final read. The contract also specifies the total transition on refusal.

`FutureEquivalent` means equality of these outcomes on **all** finite sequences.
Its definition does not mention signatures. It compares admission possibilities,
not an automatic identity between admission witnesses. `ExactRealization`
requires positive forward and backward witness transports and both return laws
when witnesses themselves must be transported.

`FiniteFutureBasis` contains executable request sequences and a completeness
proof. The generic interface is conditional; it does not promise a finite basis
for every contract. The read-only instance below constructs its basis and proves
completeness.

The core proves:

- `signature_exact`: equal signatures exactly when all contract futures are
  indistinguishable;
- `separate`: a difference constructs a concrete separating request sequence;
- `minimal_distinctions`: every exact realization retains these distinctions;
- `recoverSignature_exact`: positive coverage allows the signature to be
  recovered from another exact realization;
- `SignatureDynamics.run_exact`: a constructed update with its transition law
  remains exact on all finite sequences.

Positive coverage is proof-side representative construction, not a source
archive in runtime memory. Behavioral congruence alone is not treated as a free
update algorithm.

## Actually constituted sources

`AcceptedRoleSource role` contains an actual constituted role occurrence, its
dependent payload and acceptance proof. The role comes from the existing
execution. `producedOutput` applies `interpretRoleStageAtom` with the occurrence's
formation agreement. Acceptance preservation is separate and is used by the
accepted-target producer.

Three sources are constructed:

1. The execution's accepted left payload.
2. The right payload produced by applying the real action to that left payload.
3. A left payload varied at a variable computed from the current formula and
   decisions, followed by its actually produced output.

The computed variable is proved absent from the formula and decisions, so the
variant is positively accepted. The first two occurrences are distinct and
produce the same output. Reading the computed variable distinguishes the third.

## Exact scope of the new realization

For a role and a read variable received before classification, `roleReadContract`
promises only repeated reads of the produced output at that variable. Its
transitions are identity, its admission witnesses are unit values, and its
domain is closed under every allowed request.

The complete basis is the initial read: every later read repeats it. Reduced
memory is a Boolean. Admission transports and both return laws are constructed.

Typed support producers follow this order:

```text
accepted source + read variable
  -> real action and accepted target
  -> evaluation of the independent basis
  -> finite signature
```

`localCertificate` closes exactness, grouping of two distinct sources, a positive
separator and necessity of the remaining distinction in every other exact
realization of the same contract.

`resources_change_partition` compares the **same source domain** under two read
resources: left and varied sources agree at the selected variable and differ at
the constructed free variable. Resources are variables to read, not a partition
or grouping mask. They remain received contract parameters; this is not an
autonomous search for an optimal contract.

## Composition and execution

`AcceptedRoleHistory` composes sources along the dependent role history.
`produceHistoryReadings` produces a read vector for any number of roles. The
composed contract promises repeated reads of that vector; its basis and exact
realization are closed over this domain.

`executeSigned` produces the head signature before recursing on the tail. Its
erasure is exactly `MasterResources.execute`. The head is independent of the
future horizon, and its readings come from sources attached to roles of **the
same execution**.

The signature is a consumer of real outputs. It does not replace the seed that
drives the next discovery and is not claimed to discover a new agent
decomposition.

`publicSignatureMemory` runs the data-only consumer `executeReadings`. Its output
has type `List Bool`, with no history, support, source-payload or cursor field.
Equality with the rich execution's readings is proved.
`publicSignatureCertificate` separately retains pinned scientific evidence and
head/horizon agreements.

The local signature's compiled code does not depend on a profile image. The
reused master still constructs its **two-occurrence local image**. Named compiled
dependencies show no global profile enumeration on this path. They do not
certify arbitrary client callbacks, garbage collection or transient physical
memory.

## Signatures of all reachable agent states

`ExistingAgent.initialSignature_exact` reuses the previous theorem for initial
profiles of a fixed master and requirement. Their initial signature is unit
because their existing future executions are already equal. The agent's memory,
rights, registers and interpreter are not replaced with `Unit`.

`ReachableAgent` separately closes the full contract on all reachable states,
at a fixed master and received requirement. It reuses the actual `advance`,
`inspect`, `obtain` and `propose` requests, their events, refusals and positive
admissions. Admission witnesses are transported with both return laws; no
agent observation is removed.

The signature is the number of already executed productions. Two sources
have equal signatures exactly when all their continuations have the same
reads, events and admission possibilities. This is not a stipulated equivalence:
the existing contract's read recovers the production count from the register
length and nonempty received scope. That count then determines the effective
memory at this master and requirement. Consequently the initial read alone
forms a complete basis on this closed domain, for every finite request sequence,
without a bounded horizon.

Every production count is positively reachable. Different counts produce a
separator; every exact realization must retain this distinction. `update_exact`
and `dynamics_exact` close updates for one request and arbitrary sequences.
`executeSignedInput` obtains its signature from the actual agent production's
result; erasure returns that production.

`countRealization` also realizes the contract with a dynamic state of type
`ULift Nat`, positive coverage and admission return laws. Its interpreter
**reconstructs** responses from the master, requirement and production count,
using the existing runtime engine. It does not store the personal profile archive
in this state, but reconstruction has a real cost: this establishes neither
constant response time nor a minimum byte footprint for the complete program
and its initial resources. The existing agent's memory and interpreter were not changed.

`no_singleton_realization` proves that a `Unit` state cannot realize the full
contract: its reads already distinguish zero productions from one production.
`recoverCount_exact` constructs factorization through any other exact realization
with positive coverage. `publicCertificate` closes these guarantees on the
public master and an actually received singleton requirement, without an open
scientific hypothesis.

## Cost: remaining limitation

`CostModel` counts reads, decisions, events and transitions at the contract API
boundary. Erasure and nonzero counting rules are proved. Primitive internals,
search, resource construction, allocations and arithmetic are not covered.
No total-cost theorem is inferred from these counts.

## Public entry points and checks

- [Public certificate and memory](../RelationalPerimeter/Agents/ContinuationSignatures/PublicCertificate.lean).
- [Fused execution and data-only consumer](../RelationalPerimeter/Agents/ContinuationSignatures/FusedExecution.lean).
- [Independent contract](../RelationalPerimeter/Constitution/Continuation/Behavior.lean).
- [Minimality and transports](../RelationalPerimeter/Constitution/Continuation/Minimality.lean).
- [Complete lot-level constant sweep](../Tests/ContinuationSignatureAxiomCoverage.lean).
- [Signatures and realization of the full agent contract](../RelationalPerimeter/Agents/ContinuationSignatures/ReachableAgent.lean).
- [Client checks of the complete connection](../Tests/ContinuationSignatureReachableAgent.lean).

```text
lake build +Tests.ContinuationSignatureAxiomCoverage
python scripts/check-continuation-signature-codegen.py
```

Small `#eval` checks are smoke tests, not confirmatory cost experiments. The
repository-wide verification remains separate from this lot-level sweep.

See the [French version](signatures-de-continuation.fr.md).
