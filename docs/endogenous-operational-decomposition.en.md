# Endogenous Operational Decomposition

## 1. Phenomenon

The construction exhibits a search whose operational decomposition is an
output of computation rather than a datum of its branching structure. Opening
produces structural multiplicity. It does not yet decide whether the
alternatives must be carried as independent obligations for the criterion at
hand.

That decision depends on a relation reconstructed by execution. Its witness is
not supplied to the run. The same recursion attempts candidates, retains actual
failures, and returns the relation when an attempt succeeds. The relation then
acts on every continuation of the absorbed branch, while a separate proof
establishes preservation of the criterion.

```text
structural multiplicity ≠ operational independence
```

The resulting reduction neither identifies the alternatives nor proves that
the absorbed branch is impossible. It establishes only that this branch need
not be retained as an independent obligation for this run and this criterion.

## 2. Structural multiplicity

`ExactStructuralOpening` constructively relates the continuations of a parent
to the sum of the continuations of two alternatives. `split` and `merge` carry
both round-trip laws. The opening therefore preserves the available
multiplicity exactly without selecting a branch.

`CriterionExactOpening` is separate data. It states compatibility of the
criterion with the opening without building that compatibility into the
carrier structure. Continuation structure and continuation evaluation remain
distinct.

## 3. Executed reconstruction

`ReconstructionSystem` supplies a candidate list and an attempt function. It
contains no witness of the relation being sought. `exploreCandidates` traverses
the list by structural recursion. For each candidate, the concrete call to
`attempt` returns either `none` or a relation.

`ExecutedReconstruction` retains the prefix of `FailedAttempt` values, the
selected candidate, the successful-attempt equation, and the suffix that was
not executed. `ReconstructionRun` adds the equation proving that the traversed
list is exactly the extracted list. The attempt count is derived from the
tested trace; it is not attached afterwards.

`SuccessfulRun` is a view of the `found` constructor of that same result. The
`EndogenousOperationalDecomposition` package therefore has no parallel
relation field: `producedRelation` is projected from this view, and
`relation_comes_from_executed_run` gives its exact equation with the optional
output of the run.

In the growing instance, stage `n` produces `n + 1` distinct decoys followed by
one useful candidate distinct from every decoy. Every decoy actually returns
`none`, the final candidate
constructs `GrowingRelation.absorb n`, and the run executes exactly `n + 2`
attempts. `growingRun_failedAttempts_exact` derives `n + 1` failures from the
proof-carrying rejected prefix, so every call except the final successful one
is accounted for as a failure. The total count grows strictly with the stage.
From stage `1` onward, those failures also form a strict majority of the
executed attempts (`growingRun_failures_strictMajority`).

## 4. Action on continuations

`RelationalContinuationAction` gives every directional relation a total action:
every continuation of the source receives a continuation of the target. Its
signature requests no proof that the input continuation already satisfies the
criterion. The action is therefore defined before any conclusion about which
particular alternative is accepted.

`OperationalReduction.absorbLeft` composes this action with the opening. A
continuation from the left branch is transported to the right; a continuation
already on the right is retained.

## 5. Preservation without identity or impossibility

`CriterionPreservingAction` separately proves that the action preserves the
criterion. `EndogenousOperationalDecomposition.reduction_preserves` combines
this proof with the opening agreement. The reduction function and its
proof-theoretic license are therefore not conflated.
`EndogenousOperationalDecomposition.viable_iff_after_reduction` then proves,
for this criterion, the equivalence between viability of the parent
multiplicity and viability of the retained right branch alone. This is what
licenses no longer carrying the left branch as an independent obligation.

The concrete criterion is positivity of the continuation: it accepts `1` and
rejects `0`. The relation `absorb n` has an observably increasing action, so its
preservation theorem is not a proof of a constantly true property. The instance
also proves `left ≠ right` and positively constructs a left continuation
satisfying this criterion. Operational absorption yields neither state equality
nor a refutation of the absorbed branch. Likewise, `none` records failure of one
specified attempt; it never becomes a proof that every possible relation is
absent.

## 6. Produced state and feedback

`ProducedOperationalState` retains four outputs: visible result, tested-candidate
provenance, retained relational decisions, and next seed. `ProducedFrom`
supplies the four equations tying those fields to the specified run. Provenance
and decisions have distinct types and distinct contents.

`FeedbackStep` reconstructs from the current state, produces the next state,
and iterates by passing exactly that output to the recursive call. In the
instance, the returned relation itself produces a `GrowingDecision` and the
next seed. `filterCandidatesByDecisions` then consumes the contents of the
retained decisions and removes the obligations whose stage labels match from
the next extraction. `GrowingPhenomenon.feedbackRunIsDecompositionRun`
identifies this feedback run with the run carried by the decomposition witness.
The reconstructed transformation is therefore not merely recorded: its result
constitutes the conditions of the following computation.

## 7. Non-factorization separator

At every stage `n`, a first state is the canonical output of the shared run. A
second retains exactly its visible output, candidate provenance, and seed, but
erases the decision produced by the relation. Provenance contains no duplicate
of that decision. Their `visibleProjection` values are exactly equal. Yet the
retained state filters the designated obligation and the next run executes `n + 2`
attempts, versus `n + 3` after erasure.

`nextReconstruction_notFactors n` constructively concludes that the next
reconstruction outcome cannot be recovered from that projection alone. The
decision is therefore not a descriptive annotation: forgetting it removes data
actually consumed by the following filter.

## 8. Perimetral instance

`PerimetralComputationalState` pairs a `RootedGeneratedHistory` with an
`EndpointOperationalRealization` indexed by that history. The realization
positively carries its exact endpoint and the closure obstruction inherited at
that endpoint. Both its visible output and its reconstruction seed equal
`History.length`: the natural number remains a derived readout of an already
constituted history and defines neither the perimeter nor its occurrences.

The connection preserves two distinct movements:

```text
unary GeneratedStep
→ new constituted history
→ binary operational opening
→ executed reconstruction
→ preserved reduction
→ produced next state
```

`advanceConstitution` adds exactly the step returned by `generate`. At the
canonical boundary it equals `oneStepAfterPerimeter`.
`EndpointIndexedReconstruction` indexes the run by the exact endpoint at which
its operational state is realized and carries the closure obstruction of that
endpoint with an exact equation. `operationalOpening` is read from that
realization. The relation used by `reconstructedReduction` is obtained by
applying `Option.map` to the relational output of the run; it is not an argument
of the executor. `advanceOperational` then produces its state from the same
indexed run before `advance` associates it with the newly generated endpoint.
`advance_seed_is_derived_length` proves that this feedback remains aligned with
the new constituted history, and `perimetralReconstruction_relation_exact`
then identifies the relation reconstructed at every aligned state.

## 9. Exact scope

The result is relative to an architecture, a run, and a criterion. It does not
say that every search discovers a reduction, that every multiplicity is
redundant, or that failure of a procedure proves ontological independence. It
positively shows that an operational decomposition can be constituted during
computation and that the decision produced by its relation changes the
following computation.

The growing instance is not presented as a machine-time model or as a
complexity classification. Its counters measure exactly the candidates
attempted by the published recursion. The central theorem concerns the
constitution of operational organization, not a complexity-class claim.

## 10. Lean declaration map

| Content | Main declarations |
|---|---|
| exact structural multiplicity | `ExactStructuralOpening`, `CriterionExactOpening` |
| failures and success from one run | `ExecutedReconstruction`, `exploreCandidates`, `ReconstructionRun`, `SuccessfulRun` |
| relation projected from executed success | `SuccessfulRun.relation`, `relation_comes_from_executed_run`, `growingRun_relation_exact` |
| action on every continuation | `RelationalContinuationAction`, `OperationalReduction.absorbLeft` |
| separate preservation and absorption license | `CriterionPreservingAction`, `reduction_preserves`, `viable_iff_after_reduction` |
| distinction and viability of the absorbed branch | `alternativesDistinct`, `absorbedAlternative_viable` |
| distinct candidates, majority failures, and growing work | `candidates_nodup`, `growingRun_failedAttempts_exact`, `growingRun_failures_strictMajority`, `growingRun_attempts_exact`, `growingRun_attempts_strict` |
| produced decision and following filter | `feedbackInitial_decision_exact`, `secondExtraction_consumes_producedDecision` |
| same run in decomposition and feedback | `GrowingPhenomenon.feedbackRunIsDecompositionRun` |
| loss through decision forgetting | `nextReconstruction_notFactors` |
| connection to the perimetral endpoint | `EndpointOperationalRealization`, `EndpointIndexedReconstruction`, `perimetralReconstruction_obstruction_exact`, `advance_seed_is_derived_length`, `perimetralReconstruction_relation_exact` |
