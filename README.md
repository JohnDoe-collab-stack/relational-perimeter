## Foreword

*Mathematicians now have, with Lean, a proof tool precise enough to compare not
only the results proved, but the meanings that proofs acquire according to the
formal ontologies in which they are situated.*

*`Relational Perimeter` puts this possibility to the test by treating relations
as primitives of formal constitution. From this choice, it re-examines the
meanings of familiar notions such as role, perimeter, circularity, closure,
whole, residual, transport, and turning. It follows their constitution in the
types: which relations are primitive, which witnesses are given, which
occurrences are generated, which relations are preserved by transports, and
which data are actually consumed by proofs.*

*The carrier, understood as the formal support equipped with its structure, is
not neutral. In the four-node example, separating models show that local data
alone determine neither order nor participation in the whole. For every
presentation, returning to a rooted, composable history then makes it possible
to reconstruct order, adjacency, and factorization from the global constitution
of the object.*

*The scope of this formalization goes beyond a mere terminological refinement.
By stratifying construction, realization, admission, and normative satisfaction,
it shifts the very criteria of identity and completeness. An occurrence receives
its identity from the relational history that constitutes it, not from its
value alone. A whole is complete when its relations positively determine its
interior domain, not when it exhausts every possible continuation. What might
appear as incompleteness then becomes the non-exhaustion of generation. The
affirmative perimetral turning designates the exact point at which an already
constituted and complete whole continues to produce beyond its regime.*

*The perimeter is thus an exact quantitative measure without constitutive
numerical evaluation. Its quantity is carried by the reversible correspondence
between the successive positions of the chain and the occurrences of the
history that realizes them, together with their order and adjacency: no
interior position is omitted, and no perimeter occurrence remains outside this
correspondence. The closing place completes the circular system of requirements
without entering this interior quantity, since it is not generated as an
occurrence. The `History.length` available in the development is therefore only
a secondary numerical projection of this relational measure.*

*The methodological distinction between theorem and chain extends this
stratification without opposing them as two unrelated terms. The theorem
expresses a terminal propositional result; the chain retains the relations,
witnesses, provenances, and typed dependencies within which its proof acquires
its meaning. The same theorem may be situated in different constitutive chains;
conversely, a chain may carry more structure than the theorem's minimal logical
proof actually consumes. Comparison therefore holds together what proofs
establish and the relational constitution within which they establish it.*

*This approach makes comparable what terminal theorems alone leave invisible.
Two systems may establish similar propositional results while giving objects
and proofs different relational constitutions, and therefore different
meanings. The relational constitution of the perimeter, circularity, and the
affirmative perimetral turning provide the formal setting in which this method
is deployed.*

<br>

# Relational Perimeter

**Primitive relations, constituted wholes, and affirmative perimetral turning in Lean**

This repository contains a constructive Lean formalization in which relations
are part of the constitution of formal objects rather than annotations added
afterwards. A single proof-relevant family,
`Compatible : Implicit → Explicit → Type`, occurs in three distinct positions:
inside each node, between successive nodes, and at the distinguished closing
pair.

The formalization separates:

- given relational witnesses from the generated occurrences that realize them;
- the constituted perimeter from the primitive closing junction;
- relational closure from node identity, pole identification, and periodic
  return;
- residual determination from the proof-theoretic source of rejection;
- exact carrier transport from preservation of relational architecture;
- continued constitution from admission by the circular regime.

The resulting **affirmative perimetral turning** is the first generated step
beyond the constituted perimeter. It remains constructed, locally exact,
faithfully labelable in the unique residual role, and exactly interpretable,
while falling outside the preceding regime and specification.

## Documents

- [English presentation](docs/primitive-relations-and-perimeter-constitution.en.md)
- [Présentation française](docs/relations-primitives-constitution-perimetre.fr.md)
- [Conceptual authorship and AI-generation disclosure](AI_AUTHORSHIP.md)

## Lean sources

- `SegmentedResidualRole.lean`: abstract residual-role determination;
- `AbstractSegmentedTurning.lean`: abstract boundary, continuation, and regime
  turning;
- `ExactTypeTransport.lean`: constructive two-sided transport between types;
- `StrongPerimetralTurning.lean`: the constructive circular presentation and
  its perimetral instance.

## Build

The repository pins Lean 4.33.1 and has no Mathlib dependency.

```text
lake build
```

The four Lean files are constructive: they contain no `sorry`, `axiom`, or
`noncomputable` declaration, and their final axiom-audit blocks report no axiom
dependency for the audited declarations.

## Résumé français

Ce dépôt formalise en Lean une architecture constructive où les relations sont
primitives et participent à la constitution des objets, des occurrences et des
chaînes. Le périmètre est l'histoire enracinée et composable qui réalise les
jonctions successives données. La jonction fermante reste primitive et n'est
pas parcourue par la génération. Le premier pas au-delà du périmètre constitue
un tournant périmétral affirmatif : la génération continue, tandis que
l'incorporation de cette continuation dans le même régime devient impossible.
