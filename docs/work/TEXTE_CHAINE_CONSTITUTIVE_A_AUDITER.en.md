# Constitutive computation decomposition and machine

In this framework, the relational constitution of dependencies is primitive.
The computation itself produces its operational decomposition during its
execution and from what it has already produced. The relations actually
found, together with their preservation proofs, determine which alternatives
can be pursued together. Grouping them does not identify the source alternatives.

The machine gives this production an effective continuation. It turns the
discovered reduction code into a configured program that acts on new inputs.
These inputs use the produced organization without repeating the search that
established it. When a new search is requested, it receives the state and
frontier left by the preceding execution: the branches still pursued after
that stage.

Memory is governed by explicit continuation contracts. Some distinctions can
disappear from its representation because no future of its contract observes
them. Others must remain distinguishable because a future request can still
reveal their difference. For the machine's coherent core, this boundary is
characterized exactly and applies to every exact realization of the same
contract, regardless of its encoding.

## Objects constituted before they are counted

The occurrences on which the computation acts belong to a history of
constitutive relational roles. Their position, formation, source, target and
provenance are not replaced by a collection of values without history.
Profiles are choices of occurrences over this dependent history. Their
frontier and its count are constructed afterward: extensivity is a
quantitative readout of what has already been constituted.

The public master supplies an execution and a restart point. Roles,
normalization, obligations and profile continuation consume that same result.
The machine receives this master, along with a SAT formula, constituted
contexts and reading permissions declared as inputs. These received contexts
are not presented as outputs of the canonical public run.

Initialization is pinned for every master index, formula, received contexts
and scope by `MasterMachine.receive_exact`. The `receive_core_exact` and
`receive_problem_exact` laws expose both components; this guarantee does
not rely only on the index-zero example.

## Decomposition is produced before its continuation

The current stage searches for a transformation on the data it receives.
It applies the discovered result and produces its decomposition before
continuing from the resulting state and context. The head has no future tail
among its parameters; changing the continuation horizon does not change this
production. The produced provenance and seed constrain the next discovery.
Here, temporality means the order of primitives and their typed dependencies.

A transformation acts on the source's continuations, not merely on an accepted
example chosen afterward. Its separate proof guarantees preservation of the
acceptance criterion. It asserts neither equality of the sources nor
impossibility of the source no longer pursued independently. When a searcher
supplies no transport, the alternatives remain separate; this failure does
not prove that every possible transport is impossible.

In the studied master, the images of the local outputs actually produced
compose the global obligation regime. Two profiles are carried together
exactly when their produced targets are equal, or when their traces
co-determine them toward a common target. The canonical outputs converge,
and their global image has width one. The realization of this image has two
return laws between representations of obligations; it does not reconstruct
the source profiles. Preservation on arbitrary continuations remains
distinct from this convergence of canonical outputs.

## The discovered relation becomes a reusable action

A machine restart produces a shared live action. The selector returned by
this production opens the received SAT contexts. The searcher compares these
contexts and constructs reduction code whose absorptions carry the discovered
relations. This code supplies both the retained frontier and the program to
configure; no partition or expected width is passed to the search.

The discovered relation witness is consumed by evaluation of the code on
continuations and by the preservation proof. The compiled circuit reads
the code's constructor tree and selector, not the erased proof witness.
Its agreement with the transport is established separately in Lean.

The configured program then acts on packets containing a position and values
of variables permitted for reading. For every typed continuation of the
opened frontier, its action gives exactly the readout of the continuation
transported by the discovered code. A separate proof guarantees that the
transport preserves SAT when the source continuation satisfies SAT.
Admission of a raw packet checks only its position and size; it is not a
proof of satisfiability.

These routing requests do not restart the SAT searcher or consult historical
assignment functions. The next restart does perform a new search on the
frontier actually retained. The next live state comes from the same shared
production. The connection is directed: the live engine supplies the selector
to SAT; the SAT frontier feeds the next SAT search. SAT does not in turn drive
the live engine. In the current live family, the selector's value is determined
by depth, although the executed path reads the search result.

## One and two branches with the same searcher

An example uses the same public master, the formula
`[[positive 12, positive 1, positive 2]]`, depth, selected variable 12,
permissions and searcher. The previously received decision on variable 1 is
the only datum changed. This formula requires at least one of variables
12, 1 and 2 to be true. All four children have positively constructed SAT
continuations, and the two children of each opening are distinct.

| Received decision on variable 1 | Frontier after the first restart | Effect of packet `(0, [false])` | Variable of the second restart | Frontier after the second restart |
| --- | --- | --- | --- | --- |
| true | one branch | `(0, [true])` | 14 | one branch |
| false | two branches | `(1, [false])` | 14 | two branches |

In the first case, variable 1 already satisfies the clause: changing variable
12 does not destroy this satisfaction. The search finds the relation
authorizing grouping. In the second, the directed searches do not obtain
their agreement and both branches remain. The
subsequent packet uses the circuit installed in each case; the permutation
of its position number in the second case is not an identification of sources.
The second restart consumes the frontier produced by the first, and SAT
viability is preserved at each restart. The two initial decisions are valid
received histories for this interface, not two prefixes claimed reachable
from a single canonical run.

## Exact memory for the permitted futures

The core accepts search restarts, reads and pulses. Its reduced memory keeps
the current constitutive frontier, the permitted finite values, configured
connections and a normalized bank. It does not restore the full functional
assignment or the reference memory's historical readers to answer requests.

Exactness holds for every finite request list, with all interleavings and
refusals, and for every source memory of the contract. Minimality has a
distinct domain: for two coherent source memories, whose connections and
two bank readouts have the permitted sizes, their reduced projections
are equal if and only if all their observable futures are equal. Every other
exact realization of the same contract must preserve this distinguishability,
without having to preserve these particular fields or their encoding. This
is behavioral minimality, not a minimum number of bytes.

A pulse of zeros reveals the connections through their effect, without
adding their configuration to the observations. A restart makes it possible
to recover the live values still used. Necessity is therefore established
from the machine's future responses, not from its chosen representation.

A witness constructs two valid live states whose assignments differ at
variable 1, with the same present observation. Under permission to read
variable 2, all their futures agree. Under permission to read variable 1,
one restart distinguishes them. This witness concerns received core states;
it is not presented as a continuation of the SAT scenario above or as two
reachable public prefixes.

The integrated machine adds SAT routing and problem reads to these requests.
Its realization preserves exactly all finite futures of the combined
contract, including admissions, events, observations and refusals. It keeps
the SAT frontier, which the next search needs. Complete minimality of this
combined memory is not inferred from core minimality.

Continuation of produced profiles and the contract of repeated reads of
variable 10 after action are also exact in their own domains. The source
profile may be unrecoverable from its restart memory without having been
identified with another profile. These contracts are not conflated with the
pulse and routing contracts of the integrated machine.

## Productions are shared at each request

The executable entry produces a pair containing the event and next state.
It uses that event and continues from that state without repeating the
transition to obtain the two results separately. The specification with
separate functions remains a reference for comparison, not the active runner.
Compiled-code checks also follow producers, arguments and helper effects at
the stated local boundaries.

The circuit is still represented and interpreted in software. Eliminating
repeated searches on the configured path is real, but it makes neither the
initial search, routing nor memory free. Physical realization and total
physical cost remain distinct obligations.

## Widths are consequences of these regimes

In the formalized binary class, the extensive readout counts `2^n`
constituted profiles. Every regime considered is surjective onto its
obligations. Its width is exactly `2^n` if and only if `carry` is injective:
each profile then remains a distinct obligation separately addressable
through the regime. In the public master, `n = input + 1`; this same carrier
also receives the executed width-one regime, without identifying profiles.

On the same roles, comparative policies keeping `k` roles separate have
width `2^k`, for `0 <= k <= n`. Their spectrum is proved for the relevant
status class, not for all possible regimes. They use the authorized
transports of already-produced roles; they are not new decisions discovered
by the SAT search. A non-injective policy of width `2^(n-1)` exists for
every positive `n`.

The result therefore characterizes exactly the preservation of full
extensive width as operational width. Through the executed regime, it also
establishes that the multiplicity of profiles does not itself impose this
full width. Profile width, retained SAT-frontier width, the number of memory
cells and computation cost remain distinct quantities.

## Scope and evidence

The chain connects an organization actually produced, its action on
continuation and the distinctions for which memory must account under a
contract. Its passages and proofs are detailed in the
[evidence table](PREUVES_CHAINE_CONSTITUTIVE_MACHINE.fr.md), with the contract
map and example reproduction. The [French version](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.fr.md)
describes the same objects, hypotheses and boundaries.

This explanation does not replace the four protected paragraphs of the
[canonical target](../conclusion-largeur-exponentielle-conservation-identites.fr.md),
or S1–S8 and G1–G10 of the [existing protocol](ARISTOTLE_INTEGRATED_MASTER_MACHINE_AUDIT.md).
The class theorem is a general finite result; the search and machine described
are constructions of the master and its received contexts. The text claims
neither unpredictability, a general polynomial SAT solver, a total-cost bound,
nor originality established by Lean checks alone.

This file and its companion are the working documents submitted for independent
review. Their publication is not an audit verdict. Contracts, figures and
Lean statements are unchanged. The canonical wording is explicitly clarified
to mean full width `2^n`, not every exponential growth. The earlier protocol
and verdict remain tied to their commit; they are not a new audit of this lot.
