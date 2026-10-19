# Constitutive Progression of Theories and Gödelian Obstructions

## Scope and status

This development constructs a finite progression of arithmetic theories from
positive histories. At every stage, it produces a Gödel sentence for the
current proof regime, certifies its truth and unprovability, adds that exact
sentence as a new occurrence, and then executes a fresh Gödel production in
the extended regime.

The result connects two transformations without identifying them. A theory
change modifies the type of available proofs, while a representation change
determines where one stage's distinctions must be preserved across memory,
futures, and readouts.

## Certified histories

A `TheoryHistory` is a finite history rooted in standard arithmetic. An
extension does not receive an extensive totality of axioms. It adds one
sentence occurrence to the already constituted history.

`SoundTheoryHistory` positively certifies every step:

```text
certified source history
  + truth witness for the added sentence
  → certified extended history
```

Soundness of a historical axiom follows its occurrence witness. Soundness of a
derivation recursively follows its construction. A proof certificate checked
for one history decodes to a typed derivation, and a typed derivation encodes
back to a certificate checked for that same history.

## Gödel production at an arbitrary stage

Every certified finite history determines an effective Gödel system. Its proof
checker receives the code of that history. Its unprovability predicate and its
diagonal proof are constructed for that same regime.

The canonical execution at stage `T` produces a sentence `G_T` and two
witnesses:

```text
Truth(G_T)
Proof_T(G_T) → Empty
```

The root reuses the proof checker, unprovability predicate, and diagonal
expression published for the existing HA instance. This compatibility does not
replace its public declarations.

## One executed step

`executeGodelTheoryProgression` constructs one step:

```text
T
  → executed production of G_T
  → T⁺ = T + {G_T}
  → proof of G_T in T⁺
  → executed production of G_T⁺ in T⁺
```

Provenance is retained both in the type and in exact equalities:

- the source execution is the canonical execution of the source history
- the target history adds that execution's sentence, with no substituted sentence
- its certification consumes the truth witness of the same execution
- the target proof comes from the `newest` occurrence of that sentence
- the target execution is the canonical execution of the resulting certified history

The central result of one step is:

```text
(Proof_T(G_T) → Empty) × Proof_T⁺(G_T)
```

There is no contradiction. The two components concern two different proof
families. The development also constructs:

```text
Truth(G_T) → Proof_T⁺(G_T)
Proof_T(φ) → Proof_T⁺(φ)
Truth(G_T⁺)
Proof_T⁺(G_T⁺) → Empty
```

The first conversion does not manufacture the target proof from its truth
argument. The `Truth(G_T)` witness has already been consumed to certify the
soundness of the extension, while `Proof_T⁺(G_T)` is constructed separately
from the exact occurrence added to the history. The function is constant: it
ignores its truth argument and returns the target proof already constructed
from the added occurrence. It performs no truth-to-proof computation.

Old proofs are transported through the complete executed chain:

```text
source certificate
  → decoded source derivation
  → axiom transport into the extension
  → re-encoded target certificate
```

## New sentence and irreversibility

The new production is not a copy of the old one. The repository proves:

```text
G_T ≠ G_T⁺
```

If the two sentences were equal, the already constructed proof of `G_T` in
`T⁺` would become a proof of `G_T⁺` in `T⁺`, contradicting the new
unprovability certificate.

Uniform reverse proof transport is rejected as well:

```text
(∀ φ, Proof_T⁺(φ) → Proof_T(φ)) → Empty
```

Such a transport would send the target proof of `G_T` back to `Proof_T(G_T)`,
which the source certificate excludes. This proof consumes the old
unprovability result, not the unprovability of the new sentence.

## Representation-level localization at both stages

The existing runtime constructions are reapplied without duplication to the
source execution and then to the target execution.

At every stage:

- a positive operational grouping computes a common terminal memory without
  imposing global readout exactness
- directed preservation adapted to that collision would produce the forbidden
  truth-to-proof conversion for that stage
- a finite terminal separator, carried by the empty request list after the
  close runs, already distinguishes the produced readouts
- every exact realization of the contract must therefore retain two distinct
  terminal memories

Theory extension is not a hidden runtime effect. It is the explicit
constitutive action between two stages. Each runtime remains indexed by the
production of its own stage.

## Specific gain of the connection

A theory progression alone establishes the displacement of the proof regime:

```text
Tₙ → Tₙ₊₁ = Tₙ + {Gₙ}
```

The present connection additionally establishes a universal conclusion about
the admissible representations at every effectively produced stage. For every
exact realization `A` of the contract at stage `n`:

```text
project_A(truth_terminal(Gₙ))
  ≠ project_A(proof_terminal(Gₙ))
```

This formula concerns the memory projections of the two terminals actually
computed by the runs. It does not directly compare an abstract truth with a
proof object presumed to exist. The readouts attached to the terminals and the
contract laws provide the observable distinction that every exact realization
must retain.

This separation obligation does not arise from a general impossibility of
grouping. At the same stage, the development positively constructs an
operational grouping that computes a common terminal memory. What is
impossible is to combine that collision with the directed preservation that
would produce `Truth(Gₙ) → Proof_Tₙ(Gₙ)`.

The transition to `Tₙ₊₁` then incorporates exactly `Gₙ`. The former
unprovability remains a fact indexed by `Proof_Tₙ`, while the new occurrence
constructs `Proof_Tₙ₊₁(Gₙ)`. Execution of the resulting regime then
produces `Gₙ₊₁`, with its own unprovability and its own universal
separation obligation relative to the new contract.

The result therefore does not merely follow a sequence of theories. At every
stage, it determines:

- the grouping that remains constructible
- the preservation requirement that makes this grouping impossible
- the distinction that every exact representation must retain
- the new localization of this constraint after extension of the regime

The specific gain of the connection is thus to turn every proof boundary into
a universal rule on admissible representations, and then constructively track
the reappearance of that rule around the new production of the next regime.

### Scope of the certification rule

The rule provides a rejection certificate:

```text
certified finite separator
  → rejection of every exact fusion of the relevant terminals
```

It does not turn the absence of a known separator into a positive certificate:

```text
no separator found
  ⇏ exact fusion is admissible
```

Positive certification of a grouping requires construction of its runs, its
collision, and the preservation laws actually promised by its contract. The
positive grouping exposed here satisfies its operational contract without
claiming global readout exactness. The universal separation obligation instead
concerns every realization that claims this exactness.

## Finite iteration

`SoundGodelTheoryStage.advance` performs compilable recursion on a natural
number:

```text
T₀
  → T₁ = T₀ + {G₀}
  → T₂ = T₁ + {G₁}
  → …
  → Tₙ
```

`SoundGodelTheoryStage.executedTrace` additionally retains every executed step
and the terminal stage that it actually produced. The recursive case directly
consumes that terminal to construct the next progression. A stage retains its
master Gödel execution together with its canonicity proof. The terminal thus
also transports the target execution produced by the step, and the next
progression consumes it instead of recomputing it from the history alone.
`executedTrace` does not call `advance`. The theorem
`executedTrace_target_eq_advance` establishes only after execution that the
shared terminal agrees with the simpler iterator.

Transport of an old proof follows that retained chain as well. The
`ExecutedGodelTheoryTrace.preserveProof` method recursively consumes every
stored step and its directed translation. Public transport to `advance` is
obtained only afterwards, by transport along the equality between the
executed terminal and the simplified terminal.

At each link, the current sentence is unprovable at its own stage and provable
at the next stage. Old proofs are transported to every later finite stage. The
next sentence is fresh, and the current production has both its operational
grouping and its exact-separation obligation.

This iteration constructs neither an infinite limit, an extensive union of all
theories, nor a complete final theory. It follows a finite succession of
effectively constituted productions and extensions.

## Foundational result

The progression connects two displacements:

```text
displacement of the proof boundary
  T ⟶ T + {G_T}

representation-level localization of the obstruction
  G_T relative to Proof_T
  then G_T⁺ relative to Proof_T⁺
```

The previous sentence becomes provable when the proof regime is extended. A
new sentence, produced relative to that stronger regime, carries a new
unprovability result and new representation constraints. Incompleteness is
thereby tracked as a finite constitutive progression of proof regimes and
their preservation boundaries.

The result concerns the unprovability supplied by the formal interface. It
does not automatically assert unrefutability of every sentence, a complete
final theory, a transversal runtime comparing the same `G_T` before and after
extension, or bibliographic priority. It concerns neither the real numbers,
AC or CH, nor any temporal, memory or physical cost bound.
