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
- the absence of a constructed stage after failed discovery;
- failure of every generated decoy relation candidate and the exact attempt
  count before discovery succeeds;
- strict growth of executed relation-search attempts;
- constructor-level formation of the next seed and extraction bundle from the
  executed state, distinct from their later canonical-equality proofs;
- consumption of the produced seed and provenance by the next discovery;
- equal projected readings with different constituted candidate traces;
- separator states that agree on every permitted projectable datum while
  differing in decision history and discovery outcome;
- non-factorization of the next outcome through the permitted projection;
- canonical, uniquely owned measured accounting and the polynomial bounds on
  the explicitly instrumented work of the constructed family.

The complete implementation remains under
`RelationalPerimeter/Computation/ConstitutiveSearch/`. The statement layer is an
entry point into that implementation, not a substitute for it. Two regression
suites preserve both the independently audited counterprobes and the larger
execution/accounting surface.

## Exact scope

The result is constructive, executable, uniformly indexed by depth, and
axiom-free. It is instantiated on one explicit generated SAT family based on a
polarity-flip symmetry. The discovery performs real decidable work, rejects
decoy candidates, and its recorded number of attempts grows with the input.

The next search depends on the preceding result in two different senses:

- materially, the produced decision history and provenance change the candidate
  domain and can change the next discovery outcome;
- causally, the next root is formed from a seed read from the produced state,
  although the state invariant forces that seed to equal its canonical value.

The repository does not claim `P = NP`, `P ≠ NP`, a polynomial-time solver for
arbitrary SAT instances, or a theorem about every search space. Its polynomial
bounds concern explicitly emitted counters and the unary parameter of the
constructed family. These boundaries do not weaken the exhibited phenomenon;
they delimit exactly where it has been proved.
