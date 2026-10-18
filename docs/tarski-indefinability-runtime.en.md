# Tarski indefinability and relational operational closure

## Scope and status

This passage is the canonical text of a distinct scientific claim. Its
registration counts neither as reader review, translation review, nor
independent audit. It separates a constructive semantic Tarski theorem, its
factorization through a relational runtime, and two positive constructions.
It also establishes that the immediate terminal separator derived from the
certification forces every exact realization of the contract to separate the
two terminals.
It claims neither historical novelty, nor an
already constructed Tarskian hierarchy, nor a result about Kripke, revision
theories, or every language equipped with truth.

The [comparative Gödel–Tarski figure](figures/godel-tarski-operational-closure.en.svg)
summarizes this architecture. It is a synoptic representation of the result,
not an additional proof.

## Executed production of the diagonal

An arithmetic truth candidate is received before diagonalization. A single
syntactic production successively constructs the diagonal body, executes
substitution at its own code, produces the diagonal sentence, and records four
ordered occurrences in the same history.

In the Heyting-arithmetic instance, substitution is executed by
`PRFunction.captureAvoidingDiagonalSubstitution`. The terminal code is the one
returned by `PRFunction.runCore`, and the substitution-graph witness is derived
from the `PRFunction.Evaluates` certificate carried by that same execution.
The sentence, its computed code, and the semantic certification therefore do
not come from independent reconstructions.

The executed syntax does not yet contain any truth family. The semantic
readout is added afterwards: for an arithmetic sentence `S`, it is the lifted
type of its satisfaction in the constructive standard semantics.

## Constructive semantic theorem

For the executed diagonal sentence `L` and the received candidate `Cand`, the
certification derived from `diagonal_spec` supplies both directions between
the truth of `L` and the negation of the truth of `Cand` applied to the computed
code of `L`.

Local adequacy would conversely supply both transports between the truth of
`L` and that of `Cand` applied to this same code. Their composition
constructively produces `Empty`. No excluded middle, assumed consistency, or
proof predicate is used.

Global adequacy is defined by two directed transports, for every arithmetic
sentence, between its external truth and satisfaction of the candidate at its
code. Specializing it to the executed diagonal production gives the rejected
local adequacy. Thus, for every candidate arithmetic predicate, such global
bilateral adequacy leads to `Empty`.

The HA instance exposes both presentations without conflating them.
`heytingArithmeticRejectsSemanticTruthCandidate` directly receives both
implications between `sentence.models` propositions.
`heytingArithmeticRejectsTotalTruthCandidate` receives their `PLift`
presentation for the runtime. The former explicitly constructs the latter by
lifting and lowering witnesses; no equality of types is used.

## Positive operational grouping

Two sources are initialized from the same executed production. They share its
occurrences and production history, while retaining two distinct positions:
the value of the diagonal sentence and the candidate read at its code.

The `tarskiRuntimeNext_occurrences` and `tarskiRuntimeRun_occurrences` lemmas,
followed by their two terminal specializations, explicitly establish that
these occurrences remain those of the master production after the transition
and after every run.

The authorized `close` request executes a genuine transition from the active
phase to the terminal phase. Active memory retains the position; terminal
projection forgets it and produces a common operational memory. Both runs,
their authorizations, transitions, and events are constructed without any
readout correspondence.

The canonical contract computes events from phase, history, and request,
without copying the position into them. This pole blindness is an explicit
design hypothesis. It is exactly what constructs the equality of traces
recorded in `TarskiObservedOperationalGrouping`. The sources and active memory
continue to distinguish the two positions.

This hypothesis must not be overstated. If the position were added to the
event, event exactness would remain possible with active memory that retains
it, but the traces of the two sources could no longer be equal. Minimal
grouping by memory collision would remain a distinct object; it is the common
observational grouping that could no longer be constructed.

The positive regression test constructs one alternative realization whose
event exposes the pole during the active phase. In that same realization,
`event_exact` holds, both runs are constructed, and terminal memory collision
is computed. The test then proves that the two traces of the `close` step are
distinct. The complementary negative fixture fails exactly when it attempts
to add their equality. The terminal case of this alternative event is
deliberately independent of the pole, since terminal memory has already
forgotten it.

This test also reuses the generic directed-readout bridge. Under the two
conditional terminal preservations, it recovers local adequacy and then the
Tarski rejection with these pole-exposing events. Dependence on event
blindness is therefore excluded by construction, not merely by inspecting the
body of the canonical theorem.

## Localization of the exact obstruction

Diagonal certification also constructs a finite separator of the two
terminals for the already fixed contract. Its request list is empty because
the outcome associated with the empty list immediately reads the received
terminal. Every `ExactRealization` of this contract must therefore project the
two terminals to distinct memories. This separation comes from the terminal
readout rather than from hidden dynamics. It does not contradict positive
grouping, which concerns an operational realization with no readout-preservation law.

The minimal common interface is directed terminal readout preservation. It
completes a given operational realization with a `memoryRead` family, one
function from the source readout to memory, and one function from memory to the
target readout. It receives neither an equality of readout types, nor
`propext`, nor round-trip laws. A bilateral terminal correspondence combines
two opposed preservations and therefore contains four directed functions.

For one and the same realization, an executed grouping supplies equality of
the projected memories of both terminals. Dependent transport along this
equality, composed with one directed preservation, derives one direction of
local adequacy. The two opposed preservations derive both directions. This
derivation consults neither diagonal certification,
nor an impossibility theorem, nor a Gödel witness.

The same directed interface now serves both branches without conflating them.
In the Gödel branch, one direction transports `Truth(G)` to `Proof(G)`. In the
Tarski branch, both directions are required to obtain bilateral local
adequacy.

The directed factorization also localizes what each partial closure produces.
Writing `C = Truth(Cand(⌜L⌝))`, diagonal certification gives
`Truth(L) ↔ ¬C`. Then:

- the value-to-candidate direction alone gives `¬Truth(L)` and `¬¬C`
- the candidate-to-value direction alone gives `Truth(L)` and `¬C`
- both directions together give `Empty`

These consequences are proved separately in Lean and specialized to the HA
instance. Neither partial theorem depends on the opposite bridge or on the
bilateral rejection.

The final rejection is then a separate composition:

```text
collision of computed memories
+ bilateral readout correspondence for the same realization
→ local adequacy at the executed diagonal
+ constructive diagonal certification
→ Empty
```

The minimal theorem does not depend on equality of event traces. A second
theorem receives the canonical `TarskiObservedOperationalGrouping` so that
pole blindness and trace equality occur explicitly in its statement. The
contradiction remains localized in the combination of memory collision and
readout correspondence, not in the event alone.

## Preserved open possibility

The identity realization positively supplies exact readout correspondence at
both terminals. It nevertheless preserves the positions, so those terminals
remain distinct and do not collide.

The two positive possibilities are therefore separated: the canonical
operational runtime groups without exact readout, while the identity
realization preserves readouts without grouping the terminals. Impossibility
concerns only their combination in one realization at the same computed
terminals.

## Exact limitations

The semantic result concerns arithmetic predicates of the HA instance and the
constructive semantics supplied in the repository. It is not an internal HA
derivation of the syntactic indefinability of a truth predicate.

The Tarskian hierarchical continuation has not yet been constructed. The
current runtime shows an impossible local closure and an open realization
that separates positions; it does not construct a level-indexed family of
languages and readouts. It establishes no result about the real numbers, AC,
or CH, and does not strengthen Gödel's theorems.
