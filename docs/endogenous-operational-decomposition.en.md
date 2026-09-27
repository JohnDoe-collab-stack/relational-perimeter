# Endogenous Operational Decomposition

## Result

The construction exhibits a search whose **operational decomposition is an
output of the computation rather than a datum of its branching structure**.

Opening produces structural multiplicity. The computation equips that
multiplicity with an operational status using a transformation that:

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
separated, and their operational status is constituted during the computation
from material the computation has produced**.

![Executed architecture of the endogenous operational decomposition](figures/endogenous-operational-decomposition.svg)

## Operational stability and exponential branching

The framework first constitutes the structured objects on which the computation
acts. The executed discovery then supplies the transport witness that indexes
the operational status of an opening; a separately proved preservation law
licenses the corresponding absorption for the criterion under study.

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
payload. For the same executed opening, the position type indexed by `none`
contains its two sibling positions, while the position type indexed by
`some discoveredTransport` contains exactly the retained one. The global
retained carrier recursively combines these status-indexed position types. A
singleton of the same numerical width built from the other sibling is proved
distinct from the exact retained frontier. Thus equality of widths does not
replace the semantic reduction.

The transient trace `1 → 2 → 1` is a numerical readout of the entry, opened,
and retained frontiers of each step and is uniformly bounded by `2`. In this
explicit family those lengths reduce definitionally to the same literal
readout, so the trace is not a load-bearing causal premise. The causal statement
is carried instead by the status-indexed position types and the transport
actions: erasing the operational status transport indexes the same opening by
two pending positions, while incorporating the transport returned by executed
discovery indexes it by the single retained position. Iterating this distinction
separates the pending width `2^n` from the retained width `1`. The `2^n`
carrier represents the independent structural choices; it is not presented as
a list of `2^n` states spontaneously emitted by the sequential engine.

The causal content is typed independently of this arithmetic. The failed
candidate prefix is extracted from the executed search itself, every member of
that prefix is proved to have failed, the selected candidate is proved to have
succeeded, and the measured attempt count is exactly the length of that prefix
plus one. For the canonical initial-origin discovery associated with each input
depth, at least nine tenths of the measured attempts belong to this proved
failed prefix; this statement is scoped to that initial run, not to every stage
of the public history. The discovered map acts on arbitrary continuations. Its
preservation law is consumed separately. The absorbed sibling remains viable
and distinct as standalone positive theorems rather than premises of the
reduction certificate, and the retained output is the datum transmitted to the
next constituted situation.
On this explicit family, the successful relation has a canonical value at each
fixed depth; its operational status is nevertheless constituted by the
executed search that returns it, records the failed prefix, supplies its typed
transport, and feeds its result into the next state.

![Endogenous operational stability](figures/endogenous-operational-stability.svg)

### Constitutive production, exhaustive expansion, and independent addressing

The comparison now follows one typed production chain. The executed role
history constructs `ConstitutiveNormalizerProgram`, whose canonical value has
one instruction per opening. `StructuralObligation roles` is an abbreviation
for that program's `Profile` type, while `structuralFrontier roles` is the
program's recursively generated `profileFrontier`. The extensive carrier is
therefore produced by the program's instructions; it is not a second carrier
derived independently from the role count. At each step, the head alternative
has type `instruction.Alternative`: its two constructors are indexed by the
stored instruction. An alternative, profile, or addressing for another
instruction cannot be substituted directly merely because both openings are
binary.

The program expansion is proved complete and duplicate-free, and satisfies

```text
program.profileWidth = 2 ^ program.instructionCount.
```

`IndependentProgramProfileAddressing roles program` assigns a finite slot and
an injective address to every profile of that particular program. The
repository proves constructively

```text
program.profileWidth ≤ slotCount.
```

For the public program, `instructionCount = n`, hence every independently
addressing interface for its complete expansion needs at least `2^n` slots.
The bound follows from injectivity, completeness, and absence of duplicates in
the program-produced frontier; the interface stores no numerical width.

Each instruction stores the typed code returned by one executed opening. A
separate recursive `IsAuthoritative` proof identifies every instruction with
that returned code. The program-indexed interpreter consumes profiles produced
by the same program and is proved, through constructive structural adapters,
exactly equal to `normalizeStructuralAcceptedPayload` on every accepted
expanded profile. Every generated profile has a positively constructed
accepted payload indexed by that exact program, so this semantic statement is
non-vacuous on the complete expansion. On raw instructions,
`interpretConstitutiveNormalizerInstruction_sensitive` states the semantic
dependence explicitly: if two instruction actions differ on the accepted
source payload, their interpreted left outputs differ. Instruction consumption
is therefore not protected only by a definitional equation. The code erasure
equals the public run's exact `returnedCodes` history. The raw program metric
equals `compiledLocalSize`, and both are exactly `n = input + 1`.

The resulting hierarchy is exact:

```text
executed relational constitution
  -> authoritative typed program            : exactly n instructions
  -> complete extensive profile expansion   : exactly 2^n profiles
  -> independent finite addressing           : at least 2^n slots
```

The program produces the frontier in this precise typed sense: the carrier is
recursively indexed by its stored instructions. Its exact cardinality depends
only on the instruction count because each instruction-indexed alternative has
exactly two constructors. This is a representation-relative result; it does
not say that every representation must materialize the frontier or prove a
universal time or memory lower bound.
The retained operational width and internal instrumented cost remain separate
results. The state-and-quantity projection is further downstream: it is
obtained from the authoritative instruction's total action, but does not
determine that action, as the next section proves.

![Constitutive complexity hierarchy](figures/constitutive-complexity-hierarchy.svg)

### Exact limit of a state-and-quantity projection

The repository also constructs an extensional stability view that retains the
source and retained states, one observed accepted input and output, an
explicitly supplied numerical width readout, and its bound. The generic layer
defines `ActionFactorsThrough`: a total action factors through a projection
when one action on projected values recovers it on every argument. It also
defines `ActionProjectionCollision`: two preimages have equal projections but
their total actions differ at one argument. Its indexed form,
`AnchoredActionProjectionCollision project action first`, fixes the first
preimage in the witness type itself. The generic theorem
`action_not_factors_of_anchored_projection_collision` consumes that anchored
collision and constructively refutes factorization.

On the generated system of an actual executed stage, the total transport
denoted by the authoritative instruction and a comparison transport with the
same executed source and target form such a collision. The authoritative
instruction acts pointwise as the discovered relation on every continuation.
The two transports are separately projected; their projected views are equal
at the observed executed continuation, while their total actions differ on
another admissible continuation. The executed non-factorization theorem is
therefore an instance of the anchored generic theorem. Its public statement,
`authoritative_instruction_projection_collision`, explicitly exhibits a
collision whose first preimage is the authoritative program instruction; that
preimage is not a freely assignable field of the witness.

This identifies the exact relative limitation of the state-and-quantity
projection defined here. That projection retains states, one observed
trajectory segment, and a bounded quantity, but forgets part of the constituted
operational process: it records the stability readout without determining the
transformation whose executed reconstruction produced it. This is a formal
non-factorization result for this specified projection, not a claim that every
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
- causal formation of a seed by a produced state remains distinct from the
  invariant that determines its canonical value;
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
- the local type-indexed comparison on one executed opening: width `2` without
  an operational transport and width `1` with the transport returned by the
  executed discovery;
- accepted local payloads for every structural role, together with the derived
  numerical transient readout `1 → 2 → 1` and its uniform bound `2`;
- extraction of the actually failed candidate prefix and the exact equation
  between its length and the measured attempt count;
- proof that a wrong singleton can have the correct numerical width while
  differing from the exact retained semantic target;
- generic non-factorization of a total action from any projection collision
  with equal projected values and different action at one argument, instantiated
  both by a finite separator and by the generated system of an actually
  executed stage.

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
which tests the public widths, the status-indexed local width change, every
field of the exact executed reduction, the measured failed prefix, the
discovered map, the exact causal histories and normalizer, the wrong-singleton
distinction, the public action-factorization statement, and a generic
projection collision whose projection equality is propositional rather than
definitional.

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
