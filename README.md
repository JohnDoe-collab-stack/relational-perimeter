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

*In this sense, the framework is endogenous relative to the primitive
presentation it receives. It does not generate its own primitives; within a
single typed architecture, it constructs or establishes the identities, roles,
histories, exact quantity of the perimeter, and changes of status that proceed
from them.*

*The carrier, understood as the formal support equipped with its structure, is
not neutral. In the four-node example, separating models show that local data
alone determine neither order nor participation in the whole. For every
presentation, returning to a rooted, composable history then makes it possible
to reconstruct order, adjacency, and factorization from the global constitution
of the object.*

*The scope of this formalization goes beyond a mere terminological refinement.
By stratifying construction, realization, admission, and satisfaction of a
specification, it shifts the very criteria of identity and completeness. An
occurrence receives its identity from the relational history that constitutes
it, not from its value alone. A whole is complete when its relations positively
determine its interior domain, not when it exhausts every possible continuation.
What might appear as incompleteness then becomes the non-exhaustion of
generation. The affirmative perimetral turning designates the exact point at
which, beyond an already constituted and complete whole, generation produces a
continuation outside the regime in which that whole is maximal.*

*The perimeter thus determines an exact quantity whose exactness does not
depend on numerical evaluation. This quantity is carried by the reversible
correspondence between the successive positions and the occurrences of the
deployment; their order and adjacency are established by distinct structural
relations. The closing place completes the circular system of requirements
without entering this interior quantity, since it is not generated as an
occurrence. `History.length` provides only a subsequent, derived numerical
reading of it.*

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

The project also extends the given/generated distinction to the organization
of computation itself. A structural opening supplies two alternatives, but the
relation that makes one obligation operationally absorbable into the other is
returned only by an executed reconstruction: the run records its failed
candidates, constructs the relation, and a separate theorem proves preservation
of a nontrivial criterion. The relation then produces a decision and a seed;
the decision filters the next candidate extraction. A non-factorization theorem
shows, at every stage, that forgetting this decision while preserving output,
candidate provenance, and seed loses information needed to recover the next
executed outcome.

```text
primitive relations
→ constituted whole
→ generated continuation
→ operational opening
→ reconstructed transformation
→ criterion-preserving reduction
→ conditioned next situation
```

## Documents

- [English presentation](docs/primitive-relations-and-perimeter-constitution.en.md)
- [Présentation française](docs/relations-primitives-constitution-perimetre.fr.md)
- [Endogenous operational decomposition](docs/endogenous-operational-decomposition.en.md)
- [Décomposition opérationnelle endogène](docs/decomposition-operationnelle-endogene.fr.md)
- [Conceptual authorship and AI-generation disclosure](AI_AUTHORSHIP.md)

## Lean sources

Foundational core:

- `SegmentedResidualRole.lean`: abstract residual-role determination;
- `AbstractSegmentedTurning.lean`: abstract boundary, continuation, and regime
  turning;
- `ExactTypeTransport.lean`: constructive two-sided transport between types;
- `RelationalPerimeter/Foundations/`: the circular presentation, free
  constitution, rooted histories, exact perimeter realization, residual
  continuation, regime, structural length, and concrete interpretation,
  separated in dependency order;
- `StrongPerimetralTurning.lean`: the compatibility façade that re-exports
  those foundational layers;
- `RelationalPerimeter/Instances/FourNodeExample.lean`: the autonomous
  four-node instance and its separating traces;
- `RelationalPerimeter/Instances/CollapsedConcreteAlgebra.lean`: a local
  one-point interpretation showing that exact occurrence transport does not
  by itself preserve free-level state and target distinctions.

Endogenous operational decomposition:

- `RelationalPerimeter/Computation/`: structural opening, executed
  reconstruction, relational action, reduction, produced state, feedback, and
  non-factorization;
- `RelationalPerimeter/Instances/`: the growing constructive family and its
  alignment with perimetral histories;
- `RelationalPerimeter.lean`: the public façade;
- `Tests/`: closed constructive regressions kept outside the public façade.

## Build

The repository pins Lean 4.33.1 and has no Mathlib dependency.

```text
lake build
```

All Lean sources are constructive: they contain no `sorry`, `axiom`, or
`noncomputable` declaration, and their final axiom-audit blocks report no axiom
dependency for the audited declarations.

Repository checks are available on both supported command surfaces:

```text
./scripts/verify-constructivity.ps1
./scripts/verify-axiom-audits.ps1
./scripts/verify-smoke.ps1
./scripts/verify-links.ps1
./scripts/verify-document-parity.ps1
./scripts/verify-manifest.ps1
```

```text
bash scripts/verify-constructivity.sh
bash scripts/verify-axiom-audits.sh
bash scripts/verify-smoke.sh
bash scripts/verify-links.sh
bash scripts/verify-document-parity.sh
bash scripts/verify-manifest.sh
```

`MANIFEST.sha256` records the normalized published contents. The GitHub Actions
workflow runs the same gates on Linux and Windows.

The executable observation under `Smoke/` is explicitly non-confirmatory. It
exposes one closed run for inspection; the Lean theorems and regression modules
carry the general claims.

## License

This repository is licensed under Apache-2.0. See [`LICENSE`](LICENSE).

## Résumé français

Ce dépôt formalise en Lean une architecture constructive où les relations sont
primitives et participent à la constitution des objets, des occurrences et des
chaînes. Le périmètre est l'histoire enracinée et composable qui réalise les
jonctions successives données. La jonction fermante reste primitive et n'est
pas parcourue par la génération. Le premier pas au-delà du périmètre constitue
un tournant périmétral affirmatif : la génération continue, tandis que
l'incorporation de cette continuation dans le même régime devient impossible.
