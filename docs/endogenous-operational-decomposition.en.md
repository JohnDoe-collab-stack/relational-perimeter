# Endogenous Operational Decomposition

## Result

The construction exhibits a search whose **operational decomposition is an
output of the computation rather than a datum of its branching structure**.

Opening produces structural multiplicity. What determines whether that
multiplicity must be carried as multiple independent obligations is a
transformation that:

1. does not exist as data until the run reconstructs it;
2. is found by executed work that genuinely fails on most candidate relations;
3. acts on arbitrary continuations, before anything is known about which
   alternative is accepted;
4. comes with a separate preservation proof that licenses dropping one
   alternative for the criterion at hand, without identifying the alternatives
   and without proving the dropped one impossible.

The result of the transformation then supplies the retained state, seed,
decision history, and provenance used by the next stage. The following
reconstruction therefore takes place under conditions produced by the previous
one.

In short, **structural multiplicity and operational independence are
separated, and that separation is decided during the computation, by the
computation, from material the computation has produced**.

![Executed architecture of the endogenous operational decomposition](figures/endogenous-operational-decomposition.svg)

## Operational stability and exponential branching

The framework first constitutes the structured objects on which the computation
acts. The computation then constitutes their operational status by determining,
from a transport it has actually discovered and a separately proved
preservation law, whether structurally distinct alternatives must still be
carried as independent obligations.

For an executed history containing `n` openings, the repository constructs
three finite carriers from the same openings:

- the complete, duplicate-free carrier of structural profiles has exact width
  `2^n`;
- before a transport licenses any reduction, the carrier of pending
  operational profiles has the same exact width `2^n`;
- after each executed discovery has supplied its transport and preservation
  proof, the carrier of retained operational positions has exact width `1`.

These numbers are read from enumerated carriers, not stored as independent
annotations. Every structural role has a positively constructed accepted local
payload. The width reduction uses the actual retained frontier of every
executed step. A singleton of the same numerical width, but built from the
wrong sibling, is rejected by the exact retained-target raccord. Thus the
equality of widths does not replace the semantic reduction.

The transient trace is derived from the actual entry, opened, and retained
frontiers of every step. It is exactly `1 → 2 → 1`, uniformly bounded by `2`,
while the unreduced product of the structural choices grows as `2^n`. The
construction therefore exhibits, on this explicit family, how stability under
transformations reconstructed by the run prevents structural multiplicity from
becoming exponential operational width. The `2^n` carrier represents the
independent status of all structural choices; it is not presented as a list of
`2^n` states spontaneously emitted by the sequential engine.

The causal content is typed independently of this arithmetic. The failed
candidate prefix is extracted from the executed search itself, every member of
that prefix is proved to have failed, the selected candidate is proved to have
succeeded, and the measured attempt count is exactly the length of that prefix
plus one. For the canonical initial discovery actually executed at every
depth, at least nine
tenths of the measured attempts belong to this proved failed prefix. The
discovered map acts on arbitrary continuations. Its preservation law is
consumed separately. The absorbed sibling remains viable and distinct, and the
retained output is the datum transmitted to the next constituted situation.

![Endogenous operational stability](figures/endogenous-operational-stability.svg)

### Exact limit of a state-and-quantity projection

The repository also constructs an extensional stability view that retains the
source and retained states, one observed accepted input and output, the width
trace, and its bound. It then gives two total transports with the same such view
and the same observed output, but different actions on another admissible
continuation. Consequently, no function of that state-and-quantity view can
recover the total operational action.

This identifies the exact relative limitation of a Lyapunov-style reading in
the present construction. A description by states, an observed trajectory, and
a bounded quantity is a forgetful projection of the constituted operational
process: it records the stability, but it does not determine the transformation
whose executed reconstruction produced that stability. This is a formal
non-factorization result for the projection defined here, not a claim that every
formulation of classical stability theory has been formalized.

## Executed chain

For each input, one authoritative recursion constructs the following chain:

```text
constituted state
  → generated operational root
  → endogenous candidate extraction
  → filtering by produced provenance
  → structural opening into two distinct children
  → executed search for a relation between them
  → compilation and validation of the discovered transport
  → application to an arbitrary continuation
  → separately proved preservation of acceptance and frontier viability
  → retained target and executed Boolean determination
  → transmitted seed, decision history, and provenance
  → next root, candidate domain, and relation search
```

The public computation is
`ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution`.
Its result is projected from
`executeConstitutiveExecutionHistory`; a second replay does not supply the
public history, terminal state, decision, or accounting.

The entry boundary follows the same causal discipline. The first threaded
state is constructed from the endpoint stored by the actual measured
initialization run. Its generation is then proved equal to the canonical
generation; an independently reconstructed source is not substituted for the
one that was produced.

## What is formally separated

The types keep the following distinctions visible:

- generation of two alternatives is not their operational independence;
- a total continuation map is not its acceptance-preservation theorem;
- preservation for a criterion is not equality of alternatives;
- absorption of one obligation is not a proof that the absorbed alternative is
  impossible;
- equality of a readout is not equality of the constituted search;
- a seed formed from a produced state is not an informationally novel value;
- exact two-sided transport is not the directed transport used for absorption.

The last distinction directly connects the computation to the four foundational
modules. `ExactTypeTransport` records reversible carrier transport. By contrast,
`AcceptingContinuationTransport` contains a directed map and a separate
preservation law. The computational result depends on the latter and does not
silently strengthen it into an equivalence.

## Evidence exposed by the repository

The public statement module is
[`EndogenousOperationalDecomposition.lean`](../RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean).
It exposes axiom-free declarations for:

- structural distinction of the opened alternatives;
- the total transformation of arbitrary continuations;
- the separate acceptance-preservation theorem;
- viability transport and exact preservation of frontier viability;
- the independence of the complete step from acceptance evidence;
- the absence of any constructed stage and of every positive-length
  authoritative descendant history after failed discovery;
- failure of every generated decoy relation candidate and the exact attempt
  count before discovery succeeds;
- the exact provenance-filtered attempt law and strict growth of the total
  relation-search counter emitted by the authoritative recursion, in addition
  to the stage-local reference growth;
- construction of the first threaded state from the endpoint of the measured
  initialization run;
- constructor-level formation of the next seed and extraction bundle from the
  executed state, distinct from their later canonical-equality proofs;
- consumption of the produced seed and provenance by the next discovery;
- equal projected readings with different constituted candidate traces;
- counterfactual comparisons constructed from one executed origin: comparison
  of the retained state with the history-erased state separates constituted
  candidate traces, while comparison with the blocked state separates decision
  histories and discovery outcomes despite agreement on every permitted
  projectable datum; the erased and blocked comparators are not themselves
  emitted by the authoritative run;
- non-factorization of the next outcome through the permitted projection on
  that two-point separator domain: the projection reads assignment, generation,
  and search seed, whose values are deliberately equal for the two comparators;
- canonical, uniquely owned measured accounting and the polynomial bounds on
  the explicitly instrumented work of the constructed family;
- complete and duplicate-free structural carriers of exact width `2^n`,
  pending carriers of exact width `2^n`, and retained operational carriers of
  exact width `1`;
- accepted local payloads for every structural role, together with the exact
  transient trace `1 → 2 → 1` and its uniform bound `2`;
- extraction of the actually failed candidate prefix and the exact equation
  between its length and the measured attempt count;
- rejection of a wrong singleton that has the correct numerical width but not
  the retained semantic target;
- non-factorization of total operational action through the extensional
  state-and-quantity stability view.

The complete implementation remains under
`RelationalPerimeter/Computation/ConstitutiveSearch/`. In particular,
`OperationalFrontierStatus.lean` defines the generic pending/reduced boundary,
while `ExecutedOperationalReduction.lean`,
`ExecutedOperationalReductionHistory.lean`,
`ExtensionalOperationalStability.lean`, and
`EndogenousOperationalStability.lean` establish the executed causal chain, its
carriers, its exact widths, and the projection boundary. The statement layer is
an entry point into that implementation, not a substitute for it. The
regression suites include `EndogenousOperationalStabilityRegression.lean`,
which tests the public widths, the measured failed prefix, the discovered map,
the wrong-singleton rejection, and the non-factorization separator.

## Exact scope

The result is constructive, executable, uniformly indexed by depth, and
axiom-free. It is instantiated on one explicit generated SAT family based on a
polarity-flip symmetry. The discovery performs real decidable work, rejects
decoy candidates, and the attempt counter emitted by the authoritative
provenance-filtered recursion obeys an exact general law and grows strictly
with successive inputs. Failed discovery produces neither a stage nor any
positive-length authoritative descendant history.

The next search depends on the preceding result in two different senses:

- materially, counterfactual comparison of the produced state with
  history-erased and blocked states constructed from the same executed
  origin shows that decision history and provenance can change the candidate
  domain and the next discovery outcome; the comparator states are analytical
  constructions, not additional states emitted by the authoritative run;
- causally, the next root is formed from a seed read from the produced state,
  although the state invariant forces that seed to equal its canonical value.

The repository does not claim `P = NP`, `P ≠ NP`, a polynomial-time solver for
arbitrary SAT instances, or a theorem about every search space. Its polynomial
bounds concern explicitly emitted counters and the unary parameter of the
constructed family. These boundaries do not weaken the exhibited phenomenon;
they delimit exactly where it has been proved.
