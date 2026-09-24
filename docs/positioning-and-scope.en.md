# Positioning and Scope

`Relational Perimeter` is not a logical foundation competing with ZF,
Martin-Löf type theory, the Calculus of Inductive Constructions, or homotopy
type theory. It is a constructive relational architecture formalized in
dependent type theory in Lean. Its natural position lies at the intersection
of typed transition systems, proof-relevant dependent histories, trace
semantics, and specification and admission interfaces.

This position is comparative; it is not an established equivalence with any
of these frameworks. The repository formalizes the architecture in Lean. Its
transport to other foundations and its characterization through external
mathematical constructions remain research questions.

![Relational Perimeter foundations and formal architecture](figures/relational-perimeter-formal-architecture.svg)

## Foundation and architecture

Lean supplies the dependently typed language and proof checker used here. The
architecture organizes, within that language, primitive relations, witnesses,
roles, histories, occurrences, realizations, interpretations, regimes, and
specifications.

Lean must in particular be distinguished from the Calculus of Inductive
Constructions that forms the core language of Coq/Rocq. Lean is based on a
related dependent type theory, described as a version of the Calculus of
Constructions with inductive types and a hierarchy of universes. This proximity
does not justify identifying the two systems.

The project's proof relevance comes in particular from placing its
**constitutive primitive relations**, steps, histories, occurrences, and
relevant witnesses in `Type`. Some derived relations, such as precedence,
instead live in `Prop`. This organization is compatible with several dependent
type theories; it does not by itself give the project a homotopical character.

## Relational classification

The circular requirement system is defined by:

```lean
def CircularRequirement (P : CircularPresentation) : Type _ :=
  NonClosingPosition P.perimeter ⊕ FinalRequirement P
```

Three formally distinct objects, which the construction does not identify,
must remain separate:

- `FinalRequirement P` is the type of the closing classificatory place;
- the residual occurrence is data actually generated in the continuation
  beyond the perimeter;
- `P.finalJunction` is the primitive compatibility witness between the final
  node's implicit component and the initial node's explicit component.

The exact realization of the interior perimeter relates the non-closing
positions to the occurrences of the canonical deployment:

```text
NonClosingPosition P.perimeter
  ≃
History.Occurrence (perimeterDeployment P).history
```

The closing place does not belong to this correspondence. It faithfully
classifies the unique new occurrence of the first continuation; it is neither
that occurrence nor the primitive final junction.

## Generation and the status of the continuation

The dynamic layer uses a proof-relevant transition family:

```lean
Step : State → State → Type
```

Dependent histories and their occurrences are constructed from this family.
`perimeterDeployment P` is the canonical deployment of the constituted
perimeter. Applying generation at its terminal endpoint produces
`oneStepAfterPerimeter P`, followed by a residual occurrence that is faithfully
labelled by `FinalRequirement P`.

The project's central articulation is that a continuation can be **positively
generated, equipped with an exact concrete realization, faithfully classified
by the unique residual place, and structurally interpreted**, without thereby
being admitted to the circular regime or satisfying the circular
specification.

The continuation is therefore not eliminated by its change of status. It
remains an available and exactly interpretable construction. Three negative
results must remain distinct: rejection of a bilateral totalization attempt,
non-admission of the continuation to the circular regime, and its failure to
satisfy the circular specification.

## Separation of interfaces

The conceptual skeleton can be summarized by the following separation:

```text
classification | generation | realization | interpretation | admission | satisfaction
```

The bars express a metatheoretical separation of interfaces, roles, and
statuses in the architecture. They do not represent a chain of typed
inequalities formalized in Lean.

- **Classification** supplies the available positions and roles.
- **Generation** produces states, steps, histories, and occurrences.
- **Realization** constructs an exact correspondence or a concrete realization
  between specified carriers.
- **Interpretation** relates an occurrence and boundary data to an additional
  semantic structure.
- **Admission** incorporates a history into a regime with its own witnesses.
- **Satisfaction** responds to an independent specification with its own
  witnesses.

In the circular instance studied here, admission and satisfaction recognize
the same carrier of histories through distinct interfaces and witnesses. Their
adequacy is proved; it does not identify them as structures.

## External affinities and limits of the claims

The architecture has precise affinities, but the repository claims none of
the following as established equivalences:

- `Step`, `History`, and occurrences relate the construction to typed
  transition systems and operational semantics;
- the separation between generated histories, admitted histories, and
  histories satisfying a specification recalls trace semantics;
- history concatenation recalls free-path constructions, without establishing
  any universal property of a free category;
- placing constitutive witnesses in `Type` recalls the proof relevance of
  several intensional theories, without introducing univalence, higher
  identity types, or homotopical content.

An enriched graph, automaton, or transition system could encode a substantial
part of these data. The contribution formalized here is their explicit
organization into layers whose dependencies and changes of status are
controlled in the types.

## External research question

The Lean code establishes the internal separations described above. The open
question is therefore no longer their formal validity, but their position in
the literature: which parts are equivalent to known constructions, which
reduce to them, which are merely related to them, and whether their precise
combination contains genuinely new elements.

Answering this question requires a declaration-by-declaration and
assumption-by-assumption comparison. The project does not yet claim
mathematical novelty established by such a study.

## Primary references for the positioning

- Per Martin-Löf, [*Intuitionistic Type Theory*](https://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf), 1984.
- Peter Aczel and Nicola Gambino, [*Collection Principles in Dependent Type Theory*](https://doi.org/10.1007/3-540-45842-5_1), 2002.
- Lean, [*Dependent Type Theory*](https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/) and [*Propositions and Proofs*](https://docs.lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/).
- Coq/Rocq, [*Core language: Calculus of Inductive Constructions*](https://docs.rocq-prover.org/V8.12.0/refman/language/core/index.html).
- Gordon D. Plotkin, [*A Structural Approach to Operational Semantics*](https://doi.org/10.1016/j.jlap.2004.05.001), revised version of the 1981 Aarhus notes.
- C. A. R. Hoare, [*Communicating Sequential Processes*](https://www.cs.ox.ac.uk/ucs/hoarebook.pdf), 1985.
- The Univalent Foundations Program, [*Homotopy Type Theory: Univalent Foundations of Mathematics*](https://homotopytypetheory.org/book/), 2013.
- Tom Leinster, [*Basic Category Theory*](https://arxiv.org/abs/1612.09375), open version of the 2014 book.
