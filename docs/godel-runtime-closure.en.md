# Runtime closure and Gödelian distinction under an exact contract

## Scope and status

A single executed diagonal production supplies one positive master resource,
then an H1 history shared by two distinct constitutive sources. The semantic
pole reads the truth type of the produced sentence, while the syntactic pole
reads its proof type. The future contract and, for the conditional result, its
exact realization are fixed before the closure policy. Both sources execute
the same authorized `close` request: their phase changes from active to
terminal while their pole, history, positive provenance, and pole-indexed
readout are preserved.

An operational realization without a readout-exactness law preserves
authorizations, transitions, and events. Its active memories are distinct.
Execution of `close` then produces one common terminal memory and identical
events. The two constitutive sources remain distinct. The grouping thus
computed is exposed through the generic operational interface without
reconstructing its runs, events, terminals, or collision. A directed terminal
preservation supplies only its two local factorizations. Their composition
along the computed collision then produces `Truth(G) → Proof(G)` without
assuming or deriving an equality between `Truth(G)` and `Proof(G)`, without
reverse transport, and without global `read_exact`. The `Eq.mp` conversions
used are the read equalities `read terminal = Truth(G)` and
`read terminal = Proof(G)` supplied by the runs, together with the conversion
inside `directedReadout` along the `memoryRead` equality induced by the
computed collision. No `Truth(G) = Proof(G)` equality is assumed or derived.
This production consumes neither `trueWitness` nor `unprovable`. The directed
rejection adds them afterward from the same produced witness.

Separately, if a collision of the two computed terminals is required under an
exact realization of the fixed contract, the execution and readout laws impose
`Truth(G) = Proof(G)`, then `Truth(G) → Proof(G)`. This historical equality path
remains available without becoming a premise of the directed path.

Those two witnesses also certify an immediate terminal separator. The two
nonempty runs on `[close]` first compute their terminals. The empty list `[]`
then executes no new closure: it observes the readouts of those already
produced terminals. Every `ExactRealization` of the contract must therefore
preserve their distinction in its projected memories. This use of the witnesses
belongs to the finite-separation path and remains distinct from the directed
rejection.

Collision under exact realization remains a closure hypothesis, not a
consequence of Gödel. The action is authorized and executable independently of
that hypothesis. The result quantifies over every exact realization of the
fixed contract. It asserts neither that every grouping is impossible nor that
every notion of closure is impossible. It gives no quantitative memory or cost
bound and concerns neither the continuum nor AC or CH. The general mechanism is
an obstruction to the exact fusion of two distinct observations. Here the
Gödelian witness fixes the truth/proof pair at issue, the inhabitation of the
first type, and the emptiness of the second. No claim of mathematical novelty
or strict strengthening of an earlier result is made.

The claim `GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION` retains its
identifier. The concrete operational adapter, the generic exposure of the
already computed grouping, and the directed rejection complete its proofs
without replacing the historical paths. These changes reopen its reviews. No
new independent audit is claimed before a completed report on this new revision
has been read. An English translation of this passage is published in this lot
and likewise remains pending review.

## Positive H1 and received contract

The [positive master resource](../RelationalPerimeter/Constitution/Godel/PositiveExecutionCore.lean)
receives the history of the same `ExecutedGodelProduction` and extracts its
ordered occurrences by a positive structural fold over its prefixes. It reruns
neither the diagonal production nor the former dependent extractor. The
[H1 module](../RelationalPerimeter/Constitution/Godel/OperationalH1.lean)
constructs an actual `History` through three effective extensions: production,
certification, and continuation. Its origin observations connect the first two
occurrences to the received executed occurrences of the master resource. The
third is a newly generated occurrence. Their order and distinctions arise from
the construction of the history. A possible equality of observed values does
not identify any occurrence.

This construction depends on neither a circular Gödelian presentation nor its
rejection. It projects neither `trueWitness` nor `unprovable`. The type of the
received production nevertheless contains the constitutive obligations of the
Gödelian certification. This interface dependency is distinguished from use of
the negative projections in the runtime.

A source stores the master resource, H1, its pole, an additional operational
history, and its phase. Its depth is an observation computed from that history.
It does not replace the occurrences. The canonical context constructs the
master resource and H1 once, then initializes both sources with those same
values. Later continuations extend their own `History` through `History.extend`.

One inductive family of authorizations is shared identically by the future
contract and the operational realization. `continue` is authorized in the
active phase. `close` is authorized only at the received active H1. A terminal
source admits no further request. Total transitions on unauthorized requests
remain stable. Events provide the phase and depth before and after the request
without consulting the pole.

The constitutive readout is fixed directly from the produced sentence and the
pole. The downstream [perimetral bridge](../RelationalPerimeter/Constitution/Godel/OperationalPerimetralBridge.lean)
consumes the same master resource. It establishes an exact and exhaustive
transport between the occurrences of both H1 histories, identifies their three
roles, and preserves both immediate-order relations. This connection does not
become a premise of the readout kernel or the runtime rejection.

## Executed action and terminal grouping

The search receives the H1 context and selects `close`. Authorization consumes
that action and supplies a witness for each source. Decomposition consumes those
authorizations to construct two `ExecutedStep` values. Two `ExecutedRun` values
are then constructed from those steps. Their terminals and events are those of
the executed steps. No layer supplies an arbitrary second copy of those
outputs.

The canonical trace is a `NonemptyRequestTrace` constructed with head `close`
and an empty tail. Its computed list is therefore `[close]`. Nonemptiness comes
from this positive datum. It is no longer a negative field stored beside a list
that could be empty.

The active operational memory preserves the master resource, H1, the pole, and
the received history. After `close`, the `grouped` memory preserves the master
resource, H1, and the history while forgetting the pole. This forgetting occurs
only after the terminal transition. It is justified by the operational
contract: no continuation is admitted from a terminal, total transitions are
stable there, and events do not consult the pole. The authorization-transport
laws, `next_exact`, and `event_exact` realize this contract without imposing an
exact readout. This justification does not claim to establish a complete
`FutureEquivalent`, which would include the contested reading.

`GodelOperationalRealizationWithoutRead` exposes precisely this separation.
`godelOperationalGroupingWithoutRead` constructs both runs on the canonical
trace, their terminal collision, and their identical events. Grouping therefore
does not hold before execution: the active memories still distinguish the
poles. `GodelOperationalRealizationWithoutRead.toOperational` exposes the
transitions, events, authorizations, decisions, projection, and laws of this
realization through `OperationalRealization` without transporting its constant
reduced readout. `GodelOperationalGroupingWithoutRead.toExecutedOperationalGrouping`
directly reuses the two runs, their event lists, their terminals, and their
collision. Only the generic wrapper of the nonempty trace is reconstructed. The
identity realization remains exact for the fixed contract. It permits open
continuations and preserves distinct constitutive terminals after `close`.

## Readout exactness and rejection

`DirectedTerminalReadoutPreservation` receives a family of memory readings, a
local factorization from the left readout into that family, and a local
factorization from that family into the right readout. It receives neither
`Truth(G) → Proof(G)`, nor an equality of types, nor an inverse law. On
`godelExecutedOperationalGrouping`, `directedReadout` composes those two
factorizations along the already computed equality of terminal memories.
`godelComputedGroupingToProducedCompleteness` connects the terminal readings to
the poles preserved by both runs and thereby produces `Truth(G) → Proof(G)`.
Its transitive closure contains neither `trueWitness` nor `unprovable`.
`rejectGodelComputedGroupingToEmpty` then applies the one-way constructive
kernel to this transport and to both projections of the same witness.

The HA instance separately exposes the operational realization, the computed
grouping, the conditional positive transport, and its rejection. It adds no
arithmetic hypothesis to the already executed Gödelian production.

Once the execution and exact realization are fixed, the constructor
`godelOperationalClosureOfTerminalCollision` receives as its only additional
closure argument the collision of the two computed reduced outputs of `close`.
Its body constructs the canonical context, searched action, authorization,
decomposition, and execution. This property concerns that constructor, not an
arbitrary inhabitant of `OperationalSameRegimeClosureAt`, whose structure
explicitly packages those five layers together with the collision. The common
memory is the left output. The collision connects the right output to that
memory. The constructor receives neither a third memory, nor an equality of
readouts, nor a truth-to-proof conversion.

The kernel uses `ExecutedRun.terminal_eq_run`, then the direct
`godelExactRunExact`, proved by induction with `next_exact`. Composed with the
collision, those laws produce equality of the projections of the constitutive
terminals. Two applications of `read_exact` then give equality of their
readings. Stability of the pole and readout along the run reduces this equality
to `Truth(G) = Proof(G)`. No truth or unprovability fact, totalization, circular
rejection, `event_exact`, or equivalence of all futures supplies this passage.

`godelTerminalReadExactToEndpointEquality` localizes the same boundary for the
constructed operational realization. In its packaged proof, adding an exact
readout is composed with the two executed runs and their terminal collision.
Those runs certify and preserve the constitutive chain that was actually
constructed. They are not claimed as the logically minimal premises of every
derivation of the equality. In this packaged proof, the critical passage follows
the `close` transition, its preservation by `next_exact`, the terminal
collision, and preservation of the readings by `read_exact`. For the
constructed operational projection, those steps are nevertheless not the
logically minimal premises. The global `readExact` hypothesis already identifies
the readings of terminal sources with the same projected memory, even when
those sources are constructed independently of the runs. The former shortcut
that already identified the initial projections by depth alone was replaced,
without a compatibility alias.

The `Eq.mp` transport then constructs `Truth(G) → Proof(G)`. This conversion is
a typed consequence of the derived equality, not a theorem that physically
produces proof code. Finally, and only then, `trueWitness` supplies the input
and `unprovable` rejects the resulting proof of the same sentence. Equivalence
of all futures of the terminals remains a parallel consequence under exact
realization. It is not a premise of the critical kernel.

The generic theorem `distinct_memory_of_separator` uses only the direction
“same projected memory implies same futures” of
`equal_memory_same_futures`, then its constructive contraposition. It does not
establish the converse “same futures implies same memory” and therefore does
not characterize memory as a canonical quotient. `godelTerminalSeparator`
applies this bound to the two terminals actually produced by the closure runs.
Their difference is certified by `trueWitness` and `unprovable` from the same
witness.

## Exact foundational localization

The Gödelian witness already fixes the incompatibility between inhabitation of
`Truth(G)` and emptiness of `Proof(G)`. Execution of `close` therefore does not
create that incompatibility. Its own role is to construct positively, in the
operational realization without readout exactness, the common terminal memory
that did not exist between the distinct active memories.

Under an arbitrary exact realization, `next_exact` transports the assumed
collision of the reduced `close` outputs to the projections of the computed
constitutive terminals, and `read_exact` then forces equality of their readings.
Execution thus produces and localizes the terminal collision under study. The
obstruction to its exact preservation comes from the incompatible Gödelian
readouts that the contract requires preserving.

The demonstrated boundary is not a general sufficient principle for every
relational constitution. It concerns the constructed Gödelian runtime and its
fixed contract. Each of its two positive possibilities is realized: terminal
grouping under the operational contract without an exact readout, and the exact
realization that preserves distinct constitutive terminals. Adding to an exact
realization the hypothesis that identifies its two computed terminal outputs is
rejected.

The exact conclusion is therefore:

> **For the constructed Gödelian runtime, `close` produces an operational
> terminal collision under a realization that preserves authorizations,
> transitions, and events without preserving the readout. For every exact
> realization of the fixed contract, the empty separator certified by the
> witnesses already imposes distinction of the projected memories of those
> terminals. Complementarily, the computed operational collision and a
> directed preservation produce `Truth(G) → Proof(G)` before any use of the
> witnesses, then their incompatibility produces `Empty`. The historical
> rejection separately composes `next_exact`, the assumed terminal collision,
> and `read_exact` to impose `Truth(G) = Proof(G)`, after which truth and
> unprovability of the same sentence produce `Empty`. Execution constructs and
> localizes the collision. It does not create the Gödelian incompatibility that
> makes this collision impossible under exactness.**

## Dependencies and checks

Formation retains the execution, the master resource, and H1 in the types,
together with the received data stored by the sources. Execution successively
consumes search, authorizations, steps, runs, and computed terminals. The
directed proof consumes the computed grouping and two local factorizations. The
rejection adds the two Gödelian facts. The historical proof consumes collision
and transition/readout exactness. Operational transport forgets the pole only
at the terminal under its contract without exact reading. The historical bridge
separately preserves the identity and provenance of occurrences.

The generic [Execution](../RelationalPerimeter/Constitution/Continuation/Execution.lean)
and [CommonMemoryGrouping](../RelationalPerimeter/Constitution/Continuation/CommonMemoryGrouping.lean)
modules provide runs and grouping under complete realization without knowing
Gödel. The [Gödelian runtime](../RelationalPerimeter/Constitution/Godel/OperationalClosure.lean)
exposes the direct kernel, the produced conversion, and the rejections. The
[HA instance](../RelationalPerimeter/Instances/HeytingArithmetic/OperationalClosure.lean)
closes this chain on the existing arithmetic production without receiving a
new abstract hypothesis for data already constructed in the repository.

The [dependency check](../Tests/GodelOperationalClosureDependencies.lean)
explicitly traverses `ConstantInfo.type` and `ConstantInfo.value?` at every
encountered constant. It examines the transitive types and bodies of the
positive roots, separately reports dependencies of the received Gödelian
interface, forbids the negative projections before rejection, verifies the
required executed passages, and checks the schemas of sources, events, and
traces. Positive regressions and negative fixtures verify precise clients of
these interfaces. Those mechanical checks certify neither the meaning of the
text, nor an independent audit, nor the originality of the result.

The earlier totalization result is preserved. No theorem compares its premises
with those of the runtime collision. This connection exposes another
conditional chain under an explicit future contract.
