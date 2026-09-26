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
- causal formation of a seed is distinguished from variation of its value;
- exact two-sided transport is not the directed transport used for absorption.

The last distinction directly connects the computation to the four foundational
modules. `ExactTypeTransport` records reversible carrier transport. By contrast,
`AcceptingContinuationTransport` contains a directed map and a separate
preservation law. The computational result depends on the latter and does not
silently strengthen it into an equivalence.

## Endogenous operational stability and exponential branching

The framework first constitutes the structured objects on which the
computation acts. The computation then constitutes their operational status by
determining whether structurally distinct alternatives must be carried as
independent obligations.

This statement is now explicit in the types. Every
`ThreadedConstitutiveRoleStage` carries three typed frontiers from the same
executed discovery:

```text
singleton source [parent]
  ↔ binary opening [left, right]
  ↔ retained singleton [right]
```

The first equivalence is the exact structural opening. The second is the
acceptance-preserving absorption supplied by the relation reconstructed at that
stage. It proves neither that the siblings are equal nor that the absorbed
sibling is impossible; on the contrary, the absorbed sibling is constructively
proved viable at every executed stage. The type of the role stage also pins the
absorption to the transport reconstructed from that stage's discovery.

The causal connection is proof-relevant rather than numerical. The retained
continuation contains the assignment produced by the full executed step. A
`RetainedNextConditionRaccord` is indexed by both the head role and its exact
dependent tail, and proves that this assignment is the one consumed by the
tail's source continuation. An unrelated tail cannot inhabit this raccord.

`OperationalStabilityCertificate` is computed from the same
`ThreadedConstitutiveRoleHistory` that indexes the authoritative causal run. For
each step, its causal witness contains an `ExecutedStageOperationalReduction`.
This single typed object binds the generation-produced opening, the
discovery-produced absorption, the continuation materially computed by the
complete operation, its equality with the executed output, criterion
preservation, viability of the absorbed sibling, and the raccord to the exact
tail.

For an execution of `n` stages, the role history indexes an explicit structural
carrier: an obligation is one left or right choice at every stage of that exact
history. Lean proves that this carrier is complete, duplicate-free, and has
width `2^n`.

The operational reduction is source-indexed. For every structural obligation,
`LicensedReductionPlan` recursively records what happens to that source at
each opening. A left source can enter the retained class only through
`absorbLeft`, whose argument is the complete executed reduction; a right source
uses `retainRight` with a non-absorptive retention license. The absorption
reduction contains the generated opening, the absorption reconstructed from
discovery, the materially executed output, criterion preservation, viability
of the absorbed sibling, and the exact-tail raccord. The retention license
keeps the generated opening, executed retained output, retained choice, and
exact-tail raccord, but its type and constructor neither import nor project the
absorption-bearing reduction. Lean proves that the plan's
absorption trace is computed from the source decisions themselves. In
particular, sibling sources have different plan traces even though they reach
the same representative.

`LicensedOperationalCarrier` is therefore not an arbitrary singleton. It
contains the computed retained obligation and, for every member of the full
structural carrier, a source-specific licensed plan. The complementary
`AbsorptionFreeReductionPlan` is obtained by removing exactly the
`absorbLeft` constructor while keeping terminal reduction, right retention,
its executed material, and the dependent-tail raccord. Its reachable-source
invariant is derived from those constructors rather than supplied as a premise.
Lean then proves that this ablated operation grammar cannot reduce a left
source; the retained source remains positively executable and is constructed
without the complete absorption-bearing reduction.
Consequently, no `AbsorptionFreeSingletonCoverage` can cover the complete
structural carrier at a positive opening. Thus absorption is necessary for the
certified singleton coverage, not merely data stored beside an independently
obtained width bound.

`CausalExponentialPreventionCertificate` packages these facts together:

```text
complete duplicate-free structural carrier       = 2^n
source-indexed licensed operational carrier       = 1
singleton coverage without licensed absorption    = impossible
```

The certificate is constructed at every node of
`CausalExponentialPreventionHistory`, and Lean proves that this history has one
local certificate per executed opening. The older constant-image collapse and
its executable decision-path normalizer remain available as extensional
corollaries, but the causal result no longer rests on their singleton image.
It rests on licensed coverage and on the failure of the corresponding
absorption-free coverage. Structural siblings remain unequal throughout.

For every positive history, the retained width is proved strictly smaller than
the unabsorbed structural width. The certificate also provides the numerical
readout:

```text
width trace = [1, 2, 1, 2, ..., 1]
trace length = 2 * n + 1
every recorded width is 1 or 2
every recorded width is at most 2
```

Thus, in the explicit comparison formalized here, discovered and
criterion-preserving absorption is exactly what licenses carrying one
operational representative instead of preserving all `2^n` structural choices
as independent obligations. This is not inferred from the fixed shape of a
list: each source supplies a different reduction plan, each left crossing
contains the complete executed reduction, and removing the right to cross the
opened side makes singleton coverage uninhabitable. The statement concerns
carried operational obligations. It is distinct from total work: relation
search, failed candidates, compilation, validation, execution, transmission,
and readout remain measured separately.

The construction also identifies the exact boundary of a state-only account.
The state produced by execution and a blocked constitution built
counterfactually from the same executed origin have the same permitted
projection: assignment, generation, and seed. The retained constitution
positively constructs a complete one-step stabilization witness and has the
coarse numerical readout `some [1, 2, 1]`; the blocked constitution admits no
such witness and has readout `none`. The three numbers are deliberately only a
width projection; the full retained witness contains the history, dependent
roles, causal absorptions, and raccord. Consequently, neither witness
availability nor even this coarse readout factors through the permitted
projection, and neither can be recovered by any further view computed only
from it. A same-depth reference state is separately distinguished by the
projection, so the projection itself is not constant.

This is the precise relation to classical stability analyses. Such an analysis
may study a dynamics after its state variables and evolution law have been
fixed. Here the formal result concerns a prior constitutive question: which
structurally distinct alternatives count as independent operational obligations
is itself reconstructed during execution. An enriched state description could
of course carry this constitutive evidence; the theorem says exactly that the
specified projection, and every view factoring through it, does not.

## Evidence exposed by the repository

The public statement module is
[`EndogenousOperationalDecomposition.lean`](../RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean).
It exposes axiom-free declarations for:

- structural distinction of the opened alternatives;
- the total transformation of arbitrary continuations;
- the separate acceptance-preservation theorem;
- viability transport and exact preservation of frontier viability;
- type-level equality of every stored absorption with the transport generated
  by its executed discovery, and unconditional viability of the absorbed
  sibling at every executed stage;
- the proof-relevant assignment raccord between the retained continuation and
  the source continuation of its exact dependent tail;
- the structural carrier indexed by the exact history, its completeness,
  duplicate-freedom and width `2^n`;
- source-indexed licensed reduction plans whose trace is computed from each
  source, whose sibling traces are distinct, and whose left constructors carry
  the complete executed reduction produced from discovery;
- the licensed singleton carrier covering every structural source, the
  constructive impossibility of complete singleton coverage in the exact
  grammar obtained by deleting `absorbLeft`, the positive survival of the
  retained source in that grammar, and the recursive prevention history
  carrying one local certificate per executed opening;
- the preservation of structural inequality under operational
  co-classification and the strict width separation on every positive
  authoritative history;
- the exact `1 → 2 → 1` frontier profile at every executed stage, the alternating trace
  of length `2n + 1`, and its uniform bound by `2` on the authoritative history;
- the numerical singleton-width equality as a corollary, distinct from the
  proof-relevant content raccord;
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
  the separator pair: the projection reads assignment, generation, and search
  seed, whose values are deliberately equal for the two comparators, while a
  canonical reference element of the same domain proves that the projection
  itself is nonconstant;
- positive construction of a full stabilization witness for the retained
  constitution, impossibility of such a witness for the blocked constitution,
  their exact coarse width readouts `some [1, 2, 1]` and `none`, and
  non-factorization of both witness availability and that readout through the
  permitted projection or any view of it;
- canonical, uniquely owned measured accounting and the polynomial bounds on
  the explicitly instrumented work of the constructed family.

The complete implementation remains under
`RelationalPerimeter/Computation/ConstitutiveSearch/`. The statement layer is an
entry point into that implementation, not a substitute for it. Two regression
suites protect the target production statements corresponding to the
independently enumerated adversarial probes, together with the larger
execution/accounting surface; they do not claim textual identity with
historical audit files that are not distributed in either repository.

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
  while the state invariant also proves its exact canonical value.

The repository does not claim `P = NP`, `P ≠ NP`, a polynomial-time solver for
arbitrary SAT instances, or a theorem about every search space. Its polynomial
bounds concern explicitly emitted counters and the unary parameter of the
constructed family. These boundaries do not weaken the exhibited phenomenon;
they delimit exactly where it has been proved.
