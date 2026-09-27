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

The same relational method is extended to computation. The repository exhibits
a search whose **operational decomposition is produced by the computation**:
opening creates two structurally distinct alternatives, an executed search
reconstructs a directed transport between them, and a separate preservation
proof permits one obligation to be absorbed for the criterion under study.
Neither equality of the alternatives nor impossibility of the absorbed one is
asserted. The retained result and its provenance then condition the next
discovery.

![Endogenous operational decomposition](docs/figures/endogenous-operational-decomposition.svg)

The framework first constitutes the role occurrences and the complete profile
carrier on which the computation acts. For `n` binary openings this source has
exact width `2^n`. A downstream regime has that full exponential width exactly
when it keeps the constituted profiles as distinct, separately addressable
obligations. The executed reduction instead consumes, at every role, the
reconstructed total action and its separate preservation proof; it groups the
same source identities into one operational obligation without identifying the
two local occurrences. Its local `2 → 1` readings are recursively derived from
the actual reduction history, not supplied as a causal premise. The public
certificate ties this reduction to the same executed roles, program,
interpreter, failed-candidate work, and output transmitted to the next
situation.

A state-and-quantity projection preserves the observed states, output, width
readout, and bound, but does not determine the total operational action. At the
generic level, `ActionFactorsThrough` expresses recoverability of a total
action from a projection, while `AnchoredActionProjectionCollision` records
equal projected values whose total actions differ at one argument and fixes
its first preimage in the witness type. On the
actual executed generated system, the total transport stored by the
authoritative instruction and a comparison transport instantiate this
collision: their separately constructed views are equal, they agree at the
observed executed continuation, and their total actions differ on another
admissible continuation. The instruction acts pointwise as the discovered
relation on every continuation. The public collision theorem mentions that
authoritative instruction explicitly in its conclusion. In this exact sense,
the specified state-and-quantity view is a forgetful projection of the
constituted operational process.

![Endogenous operational stability](docs/figures/endogenous-operational-stability.svg)

The repository now proves the extensive equivalence at the level of a general
relational class. Primitive source, formation, target, and provenance relations
constitute a dependent history of role occurrences. Complete occurrence
profiles are derived from that history before any program or operational
regime. Their width is the product of the realized local arities; uniform
binary histories therefore have exact width `2^n`. The class is unbounded and
has an inhabitant independent of the public SAT execution; the wider class also
contains variable-arity histories.

An operational regime may preserve those profile identities as distinct
obligations or group them. Lean proves, for every problem in every binary
relational extensive family:

```text
regime width = 2^stageCount
  ↔ constituted identities remain distinct and separately addressable
     through that regime.
```

The same condition is equivalent to exact minimum addressing capacity
factorized through the regime. On the public carrier, the certificate
constructs the full-width identity regime and positively proves its complete
conservation condition; on the same constituted identities, the executed
regime has width one and fails separate preservation. A single certificate
ties the roles, profile carrier, downstream program, exact interpreter, and
executed reduction to the same run. The program consumes the already
constituted profiles; it does not create their alternatives. Its transformed
case uses the reconstructed total action, its preservation proof is separate,
and the action is positively non-identity on the executed source. The resulting
reduction groups distinct viable identities into one operational obligation;
its local `2 → 1` readings are recursively derived from the reduction history.

![Relational extensivity and operational obligations](docs/figures/relational-extensive-iff.svg)

This is a theorem about exact carrier width and factorized finite addressing in
the formalized class, not a universal time or memory lower bound. The audited
state-and-quantity projection and instrumented execution costs remain distinct
downstream results.

## Positioning and scope

![Relational Perimeter formal architecture](docs/figures/relational-perimeter-formal-architecture.svg)

`Relational Perimeter` is a relational architecture formalized in dependent
type theory in Lean, not a competing logical foundation. Its constitutive
primitive relations, generated histories, exact realizations, interpretations,
regimes, and specifications remain separate interfaces. In particular, a
continuation may be positively generated, equipped with an exact concrete
realization, faithfully classified by its unique residual place, and
structurally interpreted without being admitted to the circular regime or
satisfying the circular specification.

The canonical positioning statement, its limits, and the primary references
for the external comparisons are available in the parallel versions listed
below.

## Documents

- [English presentation](docs/primitive-relations-and-perimeter-constitution.en.md)
- [Présentation française](docs/relations-primitives-constitution-perimetre.fr.md)
- [Positioning and scope](docs/positioning-and-scope.en.md)
- [Positionnement et portée](docs/positionnement-et-portee.fr.md)
- [Endogenous operational decomposition](docs/endogenous-operational-decomposition.en.md)
- [Décomposition opérationnelle endogène](docs/decomposition-operationnelle-endogene.fr.md)
- [Conceptual authorship and AI-generation disclosure](AI_AUTHORSHIP.md)

## Foundational Lean sources

- `SegmentedResidualRole.lean`: abstract residual-role determination;
- `AbstractSegmentedTurning.lean`: abstract boundary, continuation, and regime
  turning;
- `ExactTypeTransport.lean`: constructive two-sided transport between types;
- `StrongPerimetralTurning.lean`: the constructive circular presentation and
  its perimetral instance.

## Computational construction

- `RelationalPerimeter/Computation/ConstitutiveGeneration.lean` connects the
  computation directly to the generated histories of the four foundational
  modules;
- `RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean` is
  the public statement layer for the computational phenomenon;
- `RelationalPerimeter/Computation/ConstitutiveSearch/` contains the complete
  executable construction, its relational transports, SAT instance, feedback
  recursion, and production-level measured accounting;
- `Tests/ComputationalPhenomenonRegression.lean` protects the production
  statements corresponding to the independently enumerated adversarial probes,
  including the production seed and the causal connection between measured
  initialization and the first threaded state;
- `Tests/ConstitutiveExecutionRegression.lean` protects the complete executed
  and measured surface;
- `Tests/EndogenousOperationalStabilityRegression.lean` protects the exact
  structural, pending, executed, and transient widths together with the causal
  map, measured-failure, wrong-singleton, and non-factorization boundaries. In
  particular, it checks the public `ActionFactorsThrough` statement and a
  generic projection collision whose equality is propositional rather than
  definitional.
- `Tests/RelationalExtensiveIffRegression.lean` protects the class-level
  exponential `iff`, its exact factorized-capacity form, the independent
  unbounded members of the relational classes, and the one-chain public
  reduction from action and preservation to grouped obligations.

The computational tree imports the foundational modules directly. It has no
dependency on an external alignment layer, a separate foundation layer, or a
readout facade.

## Build

The repository pins Lean 4.33.1 and has no Mathlib dependency.

```text
lake build
```

The complete repository gate is available on both supported command surfaces:

```text
pwsh -NoProfile -File scripts/verify.ps1
bash scripts/verify.sh
```

Both gates traverse the declared import boundaries and compile four
expected-failure fixtures. These fixtures verify that the public certificate
constructor remains private, that profiles from distinct stored instructions
are not directly interchangeable, that the projection collision remains indexed
by the authoritative instruction transport, and that an interpreter which
ignores an arbitrary raw instruction cannot satisfy its semantic output
specification.

All Lean sources are constructive: they contain no `sorry`, `axiom`, or
`noncomputable` declaration, and their final axiom-audit blocks report no axiom
dependency for the audited declarations. The default build includes the public
modules and the regression suites.

## Résumé français

Ce dépôt formalise en Lean une architecture constructive où les relations sont
primitives et participent à la constitution des objets, des occurrences et des
chaînes. Le périmètre est l'histoire enracinée et composable qui réalise les
jonctions successives données. La jonction fermante reste primitive et n'est
pas parcourue par la génération. Le premier pas au-delà du périmètre constitue
un tournant périmétral affirmatif : la génération continue, tandis que
l'incorporation de cette continuation dans le même régime devient impossible.

Cette architecture porte aussi une décomposition opérationnelle endogène de la
recherche. L’ouverture produit une multiplicité structurelle ; une relation
dirigée est ensuite reconstruite par l’exécution, sa préservation est prouvée
séparément, et le résultat retenu conditionne la découverte suivante. Ainsi, le
nombre d’alternatives engendrées et le nombre d’obligations qui doivent rester
indépendantes ne sont pas confondus.

Pour `n` ouvertures binaires exécutées, le carrier source des profils constitués
a une largeur exacte `2^n`. Un régime aval possède cette largeur exponentielle
complète si et seulement s’il conserve ces profils comme identités distinctes
et séparément adressables. La réduction exécutée consomme au contraire, à
chaque rôle, l’action totale reconstruite et sa preuve séparée de préservation ;
elle regroupe les mêmes identités sources en une obligation sans identifier les
deux occurrences locales. Ses lectures `2 → 1` sont dérivées récursivement de
l’histoire de réduction effective. Une projection par état et quantité conserve cette stabilité
observée sans déterminer l’action opérationnelle totale. Le transport total
porté par l’instruction faisant autorité et le transport de comparaison sont
projetés séparément vers deux vues égales, alors que leurs actions totales
diffèrent sur une autre continuation admissible. L’instruction agit point par
point comme la relation découverte sur toute continuation. Le théorème
générique de non-factorisation consomme explicitement cette égalité de
projections.

Le dépôt prouve désormais l’équivalence extensive au niveau d’une classe
relationnelle générale. Des relations primitives de source, de formation, de
cible et de provenance constituent une histoire dépendante d’occurrences de
rôle. Les profils complets d’occurrences sont dérivés de cette histoire avant
tout programme et tout régime opérationnel. Leur largeur est le produit des
arités locales réalisées ; une histoire uniformément binaire de longueur `n`
a donc une largeur exacte `2^n`. La classe est non bornée et possède un membre
indépendant de l’exécution SAT publique ; la classe plus large contient aussi
des histoires à arités variables.

Un régime opérationnel peut conserver ces identités de profil comme obligations
distinctes ou les regrouper. Lean prouve, pour tout problème de toute famille
extensive relationnelle binaire :

```text
largeur du régime = 2^stageCount
  ↔ les identités constituées restent distinctes et séparément adressables
     à travers ce régime.
```

La même condition équivaut à la capacité minimale exacte d’un adressage
factorisé par le régime. Sur le carrier public, le certificat construit le
régime identitaire de pleine largeur et prouve positivement sa condition
complète de conservation ; sur les mêmes identités constituées, le régime
exécuté a une largeur un et ne conserve pas les identités séparément. Un
certificat unique rattache
les rôles, le carrier de profils, le programme aval, l’interprète exact et la
réduction exécutée à une même exécution. Le programme consomme les profils déjà
constitués ; il ne crée pas leurs alternatives. Son cas transformé emploie
l’action totale reconstruite, sa preuve de préservation demeure distincte, et
l’action est positivement non identique sur la source exécutée. La réduction
obtenue regroupe des identités distinctes et viables en une seule obligation
opérationnelle ; ses lectures locales `2 → 1` sont dérivées récursivement de
l’histoire de réduction.

![Extensivité relationnelle et obligations opérationnelles](docs/figures/relational-extensive-iff.svg)

Il s’agit d’un théorème sur la largeur exacte d’un carrier et l’adressage fini
factorisé dans la classe formalisée, non d’une borne universelle en temps ou en
mémoire. La projection auditée par état et quantité et les coûts instrumentés
de l’exécution restent des résultats aval distincts.

## License

Apache-2.0. See [LICENSE](LICENSE).
