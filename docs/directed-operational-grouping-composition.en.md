# Directed composition under operational grouping

## Scope and status

This development isolates two constructive kernels of directed
incompatibility and builds a positive non-diagonal instance of the same
composition mechanism. It distinguishes three data that are not
interchangeable: a memory collision computed by two executions, two local
readout factorizations, and the transverse transport made possible by equality
of the terminal memories.

The result does not characterize a quotient memory and proves no converse from
future equivalence to memory equality. It does not say that every grouping is
impossible. It proves nothing about all real numbers, AC or CH, physical cost,
or bibliographic novelty.

## Two generic constructive incompatibilities

The one-way kernel receives a transport `P → Q`, a witness of `P`, and a
refutation `Q → Empty`. It produces `Empty` by applying those three data in
order. It contains no Gödel, Tarski, or operational datum.

The bilateral kernel receives two transports `P → Q` and `Q → P`, together
with a constructive certificate formed by `P → Q → Empty` and
`(Q → Empty) → P`. It first constructs a refutation of `Q`, then a witness of
`P`, and finally `Empty`. It uses no equality of types, `propext`, or excluded
middle.

The operational wrappers do not receive the transverse transports as
hypotheses. They receive an `ExecutedOperationalGrouping` and one or two
directed terminal preservations. Each transverse transport is produced by
`directedReadout` or `reverseDirectedReadout`, hence by composing the local
factorizations along the equality of terminal memories derived from the two
runs and their computed collision.

## Positive non-diagonal instance

For one constitutive role and the same master run, the instance uses the two
already constructed accepted sources `variedLeftSource role` and
`leftSource role`. Their distinction is proved before the runtime is built.
The `source` and `target` positions only index them and do not replace that
underlying constitutive distinction.

The `close` request is authorized only in the active phase and computes a
terminal phase. Both runs are nonempty. Active events expose the position, so
the two traces remain distinct. The memory projection retains the position in
the active phase and retains at the terminal only the Boolean actually read at
the `run.selected` resource.

Equality of the two terminal Booleans is neither postulated nor obtained by an
independent simplification. It follows through the existing chain
`same_sources_other_resource_agree`, `produceRoleSignature_exact`, and
`FutureEquivalent.read`. Equality of the terminal memories is then obtained
by transporting that equality under the `grouped` constructor.

The terminal readouts are dependent types indexed by the produced Booleans.
The source factorization explicitly encodes a Boolean as a natural number.
The target factorization explicitly decodes that number and uses the decoding
law for the encoding. Transport between the two terminal readouts is produced
only by `positiveDirectedGrouping.directedReadout` applied to these
factorizations. A concrete source witness is transported to a concrete target
witness. This construction builds no inhabitant of `Empty` and no proof of
`False`.

The instance therefore positively establishes that operational collision and
directed preservation can be compatible when the terminal readings are
compatible. The Gödel and Tarski obstructions do not arise from the mere
existence of the transport mechanism. They arise when data specific to those
instances make the produced transport incompatible.

## Gödel connection

The Gödel realization without readout is exposed through the
`OperationalRealization` interface by reusing its transitions, events,
authorizations, decisions, projection, and exactness laws. Its constant
reduced readout is not transported.

The already computed Gödel grouping is exposed through
`ExecutedOperationalGrouping` by reusing exactly its two runs, their events,
their terminals, and their collision. Only the structural wrapper of the
nonempty trace is rebuilt. No search, authorization, decomposition, execution,
or collision is recomputed.

On this same realization and grouping, a directed terminal preservation
produces `Truth(G) → Proof(G)`. This production remains independent of
`trueWitness` and `unprovable`. The final rejection then applies the one-way
kernel to the produced transport and to both fields of the same Gödel witness.
The Heyting Arithmetic instance separately exposes the realization, the
grouping, the conditional positive transport, and the rejection.

## Tarski connection

The Tarski diagonal certification is adapted to the pure bilateral
certificate by reusing only its two directions. Construction of local adequacy
still precedes use of that certification: the two canonical transports are
derived from the runs, the collision, and the two directed preservations. The
bilateral kernel then consumes those transports and the certification.

The two one-way consequences remain separately available. Neither direction
alone is promoted to a bilateral correspondence or to a contradiction.

## Finite separation and limits

Separation by a finite future remains a distinct mechanism. It establishes
that every exact realization must retain a difference revealed by a finite
request. It does not provide the converse that equal futures force equal
memory.

The directed kernels do not automatically replace the repository's abstract
totalization regimes. No adapter to these regimes is constructed. The form it
would need is not established. No additional connection is claimed here.
