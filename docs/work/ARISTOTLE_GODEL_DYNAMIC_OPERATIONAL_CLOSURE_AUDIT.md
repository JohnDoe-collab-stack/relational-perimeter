# Fresh independent formal audit — dynamic Gödel operational closure

## Audit identity and immutable target

This request starts a **brand-new independent audit with uploaded sources**.
Do not continue, reuse, summarize, or infer a verdict from any earlier
Aristotle project, report, or conversation. In particular, the earlier project
that received no repository and returned no verdict is only a failed delivery
record. Earlier audits are neither evidence nor authority for this run.

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Published branch: `work/godel-dynamic-operational-closure`
- Exact revision to audit: `31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b`
- Scientific code-and-prose evidence revision:
  `e2b75474c8bef91cfb9f24d6fed8d408e38d0269`
- Base revision before this work:
  `c3a12b5114ca519aae8e8c83eec6b6d723d450d4`
- Lean toolchain: `v4.33.1`
- Registered claim:
  `GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION`

## Uploaded autonomous input

This fresh project was initialized with a source archive containing:

```text
relational-perimeter/                       complete checkout and .git history
SOURCE_INPUT_MANIFEST.txt
```

This audit task is additionally supplied with the following six files:

```text
lean-4.33.1-linux-minimal.tar.zst.part-00
lean-4.33.1-linux-minimal.tar.zst.part-01
lean-4.33.1-linux-minimal.tar.zst.part-02
lean-4.33.1-linux-minimal.tar.zst.part-03
lean-4.33.1-linux-minimal.tar.zst.part-04
lean-4.33.1-linux-minimal.tar.zst.part-05
```

Do not clone or fetch the repository. Network access is not required. Enter the
uploaded checkout and first report:

```text
cd relational-perimeter
git rev-parse HEAD
git status --short
git merge-base --is-ancestor e2b75474c8bef91cfb9f24d6fed8d408e38d0269 31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b
git merge-base --is-ancestor c3a12b5114ca519aae8e8c83eec6b6d723d450d4 31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b
```

The checkout must be clean and already detached at the exact target. Its
`.git` directory is included so ancestry and object contents can be checked
locally.

These six files are the ordered parts of an exact Linux Lean toolchain. Locate
them without using the network, concatenate them in lexical order, verify the
archive, and install it only into scratch space outside the repository:

```text
find .. -type f -name 'lean-4.33.1-linux-minimal.tar.zst.part-*' -print | sort
cat $(find .. -type f -name 'lean-4.33.1-linux-minimal.tar.zst.part-*' -print | sort) \
  > /tmp/lean-4.33.1-linux-minimal.tar.zst
sha256sum /tmp/lean-4.33.1-linux-minimal.tar.zst
mkdir -p /tmp/relational-perimeter-lean-4.33.1
tar --zstd -xf /tmp/lean-4.33.1-linux-minimal.tar.zst \
  -C /tmp/relational-perimeter-lean-4.33.1
TOOLCHAIN=/tmp/relational-perimeter-lean-4.33.1/lean-minimal
$TOOLCHAIN/bin/lean --version
$TOOLCHAIN/bin/lake --version
export PATH="$TOOLCHAIN/bin:$PATH"
$TOOLCHAIN/bin/lake build
```

The required SHA-256 of the reconstructed toolchain archive is:

```text
e17865e02d7df304e195253516c9a7f7afdb3202e5a13d471a89c032c0621f86
```

Expected versions are Lean `4.33.1` at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and Lake
`5.0.0-src+819816b`. The toolchain archive contains no project proof objects;
the project must be rebuilt from the uploaded source checkout.

Audit the mathematical and foundational content of that immutable revision,
not merely whether it compiles. Do not modify the repository. A successful API
submission or a green build is not an audit verdict.

## Exact target

Determine whether the implementation constructively localizes the obstruction
to an exact terminal-memory collision as claimed:

1. one executed Gödel production supplies a single positive execution core and
   operational H1 shared by two rich sources;
2. both sources execute the same authorized, nonempty `close` trace;
3. `close` is a genuine active-to-terminal transition, not an identity step;
4. a positive operational realization can erase the pole only at the terminal
   phase and thereby construct a common terminal memory while preserving
   authorization, transitions, and events, but without claiming readout
   exactness;
5. independently, the rich contract has an exact identity realization whose
   two terminal outputs remain distinct;
6. for an arbitrary exact realization, an assumed equality of the two computed
   reduced terminal outputs yields
   `Truth(G) = Proof(G)` through executed runs, `next_exact`, the collision, and
   `read_exact`;
7. only after that equality/conversion has been derived are the truth and
   non-provability components of the same produced Gödel witness consumed to
   obtain `Empty`.

The target is conditional and deliberately narrow. It does not claim an
impossibility of all grouping, all closure, all totalization, or all runtimes;
it does not claim a new incompleteness theorem; and it makes no claim about the
usual real numbers, the continuum, AC, CH, memory complexity, width, or physical
cost.

## Files that must be read completely

Read the complete imports, declarations, parameter lists, result types, and
proof bodies of at least:

```text
RelationalPerimeter/Constitution/Continuation/Execution.lean
RelationalPerimeter/Constitution/Continuation/CommonMemoryGrouping.lean
RelationalPerimeter/Constitution/Godel/Diagonal.lean
RelationalPerimeter/Constitution/Godel/PositiveExecutionCore.lean
RelationalPerimeter/Constitution/Godel/OperationalH1.lean
RelationalPerimeter/Constitution/Godel/OperationalClosure.lean
RelationalPerimeter/Constitution/Godel/OperationalPerimetralBridge.lean
RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean
RelationalPerimeter/Instances/HeytingArithmetic/Godel.lean
RelationalPerimeter/Instances/HeytingArithmetic/OperationalClosure.lean
Tests/GodelOperationalClosureDependencies.lean
Tests/GodelOperationalClosureRegression.lean
Tests/HeytingArithmeticOperationalClosureRegression.lean
docs/godel-fermeture-runtime.fr.md
docs/scientific-claims.json
scripts/verify.sh
scripts/verify.ps1
```

Also inspect every expected-failure fixture referenced by the registered claim,
the import-boundary manifests, and `Tests/AllConstantsAudit.lean`. Follow
transitive definitions whenever a theorem body delegates the relevant work.

## Seven fixed acceptance criteria

Use exactly these seven criteria. Do not silently replace the target with a
nearby theorem, a cardinality observation, or a weaker static incompatibility.

### 1. Independent operational closure hypothesis

Verify that the closure structure does **not** receive any of the following,
directly or through a wrapper field: endpoint equality, `Truth(G) → Proof(G)`,
an old total-loop/totalization object, a contradiction, or the desired
rejection theorem.

Its distinctive negative-case datum must be equality of the two terminal
memories actually computed by the two `close` runs under one already-fixed
exact realization. Check both types and values of every wrapper transitively.

### 2. Actually executed, positive grouping

Verify the entire constitutive order:

```text
single executed Gödel production
→ positive execution core
→ operational H1 and constituted occurrences
→ received context
→ searched close action
→ authorization
→ decomposition
→ two ExecutedStep values
→ two ExecutedRun values over the same nonempty singleton trace
→ computed terminal memories
→ terminal collision
```

The same core and H1 must be shared. Outputs must be consumed rather than
independently reconstructed. The two rich source occurrences and poles must
remain distinct. Nonemptiness must be positively constructed by the trace,
not stored as a negative proposition.

### 3. Fixed exact future contract and dynamic readout bridge

Verify that `next`, `event`, and `read` are fixed before the closure policy and
that the exact realization is fixed before the collision hypothesis. Rebuild
the endpoint equality from:

```text
leftRun/rightRun
+ terminal_eq_run
+ run exactness derived from next_exact
+ equality of the computed reduced terminals
+ read_exact
+ pole/read preservation along the rich runs
```

Confirm that `FutureEquivalent`, `event_exact`, or a static initial-memory
equality is not substituted for this chain.

### 4. No circular use of Gödel-negative facts

Inspect transitive dependencies in both theorem types and values. The positive
core, operational H1, context, search, authorization, decomposition, grouping,
and endpoint-equality bridge must not depend on:

- `ExecutedGodelWitness.trueWitness`;
- `ExecutedGodelWitness.unprovable`;
- `ExecutedGodelWitness.rejectProducedCompleteness`;
- an old circular presentation, total loop, totalization, contraction kernel,
  or pre-existing closure rejection;
- `Empty.elim` or `False.elim` introduced by the new positive chain;
- event separation as a hidden contradiction.

Distinguish dependencies already inherent in the received
`ExecutedGodelProduction` interface from projections of its negative witness.
The final rejection must consume `trueWitness` and `unprovable`; the earlier
positive construction and equality theorem must not.

### 5. Positive open runtime and positive operational quotient

Verify both affirmative models:

- the identity exact realization exists, supports `continue`, executes `close`,
  and keeps the two rich terminal outputs distinct;
- the operational realization without readout exactness preserves
  authorization, transition, and event behavior, starts with distinct active
  projected memories, executes `close`, and constructs one common terminal
  `grouped` memory.

The latter must not be presented as an `ExactRealization` and must not smuggle
in `read_exact`.

### 6. Reproducibility, constructivity, and concrete HA specialization

Independently run, where the audit environment supports the command:

```text
lake build
bash scripts/verify.sh
pwsh -File scripts/verify.ps1
```

The submitted revision recorded the following results; verify rather than
trust them:

- build: 349 jobs;
- Lean source files checked: 347;
- constants audited: 29,545 across 346 modules;
- written exceptions: 0;
- compiler-generated exceptions: 474, unchanged from the pinned base;
- expected-failure fixtures: 48, with exact diagnostics;
- scientific registry: 20 claims and 124 distinct declarations
  (96 public and 28 test declarations).

Check `#print axioms` for at least:

```text
StrongPerimetralTurning.godelOperationalGroupingWithoutRead
StrongPerimetralTurning.godelExecutedGroupingToEndpointEquality
StrongPerimetralTurning.godelTerminalReadExactToEndpointEquality
StrongPerimetralTurning.godelOperationalClosureToEndpointEquality
StrongPerimetralTurning.rejectGodelTerminalReadExactToEmpty
StrongPerimetralTurning.rejectGodelOperationalClosureToEmpty
StrongPerimetralTurning.godelExactRuntimeRejectsCommonTerminalMemory
RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalGroupingWithoutRead
RelationalPerimeter.HeytingArithmetic.heytingArithmeticTerminalReadExactToEmpty
RelationalPerimeter.HeytingArithmetic.heytingArithmeticExactRuntimeSeparates
RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureToEmpty
RelationalPerimeter.HeytingArithmetic.heytingArithmeticOperationalClosureRejected
```

Confirm there is no `axiom`, `sorry`, proof hole, `noncomputable`, `Classical`,
`propext`, `Quot.sound`, `native_decide`, `unsafe`, or equivalent bypass in
the relevant transitive dependency cone. Verify that the HA result uses the
one concrete arithmetic execution and adds no new arithmetic soundness or
incompleteness assumption.

### 7. Exact foundational scope and French statement

Determine exactly what the proof establishes and what it does not. In
particular, decide whether the runtime is genuinely part of the derivation or
merely decorative, whether the terminal collision is genuinely post-execution,
and whether Gödel contributes a final obstruction not already forced by events
or pole-labelled operational data.

As part of this same seventh criterion, validate the French theorem statement
below sentence by sentence against the exact Lean revision. This is not an
additional criterion. For every substantive sentence or bullet, return one of:

- `TRUE` — exactly supported;
- `TOO STRONG` — a weaker statement is supported;
- `FALSE` — contradicted by the implementation;
- `NOT VERIFIED` — the available formal evidence does not establish it.

For every verdict, cite exact declarations and source locations. For each
`TOO STRONG`, `FALSE`, or `NOT VERIFIED` item, supply corrected French wording
that would be exactly justified.

## Required adversarial reconstructions

Do not merely invoke the final packaged theorems. In a scratch Lean file,
without changing the repository, perform these reconstructions:

1. Construct the positive operational realization, both `close` runs, and
   their common projected terminal memory without using the packaged positive
   grouping theorem.
2. Derive `Truth(G) = Proof(G)` from an arbitrary exact realization and an
   equality of the two computed reduced `close` terminals, without invoking
   `godelExecutedGroupingToEndpointEquality` or
   `godelOperationalClosureToEndpointEquality`.
3. Derive `Empty` from that equality using the truth and non-provability of the
   same produced sentence, without invoking either packaged final rejection.
4. Construct the identity exact realization and show that its two computed
   rich `close` terminals are distinct.
5. Attempt to derive the contradiction using only events, authorization,
   transition exactness, or the positive operational grouping, while excluding
   `read_exact`, `trueWitness`, and `unprovable`. Report the exact result.

## Specific anti-shortcut questions

Answer each with a formal reference or a scratch theorem:

1. Does `godelRuntimeNext ... .close` genuinely change `.active` to
   `.terminal`? Confirm `godelClose_changes_phase` and
   `godelClose_not_identity` rather than trusting their names.
2. Are the initial projected operational memories provably distinct and the
   common memory obtained only after `close`?
3. Do runtime events omit the pole? Can `event_exact` alone still separate the
   two terminal memories by another route?
4. Is pole information preserved in the rich terminal state even though the
   positive operational projection forgets it at the terminal phase?
5. Is the readout-independent projection demonstrably weaker than an exact
   realization, and is this weakness stated honestly?
6. Can a shorter static proof from equality of initial projected memories
   replace the executed-run proof for the constructed operational model? If
   not, exhibit the obstruction. If yes, identify the exact bypass and mark the
   target failed.
7. Do the dependency tests inspect both theorem types and values, including
   projections and wrappers, and do they reject the obsolete static shortcuts
   `godelRoleBlindReadExactToEndpointEquality` and
   `rejectGodelRoleBlindReadExactToEmpty`?

## French statement to validate verbatim

# Théorème de localisation constructive de l’obstruction à la fermeture exacte

## Résultat fondationnel

À partir d’une unique production gödelienne exécutée, une même phrase diagonale \(G\), ses occurrences et leur provenance alimentent deux constructions distinctes.

Le contrat riche associe aux deux pôles les readouts :

\[
T=\mathrm{Truth}(G),
\qquad
P=\mathrm{Proof}(G).
\]

Ce contrat est fixé avant toute hypothèse de fermeture.

Trois résultats sont établis constructivement.

### 1. Possibilité affirmative du regroupement opérationnel

Un même H1 positif est construit depuis l’exécution gödelienne, puis partagé par deux sources riches distinctes :

- la source sémantique, associée à \(\mathrm{Truth}(G)\) ;
- la source syntaxique, associée à \(\mathrm{Proof}(G)\).

Leurs mémoires opérationnelles actives restent distinctes, car elles conservent encore leur pôle.

Les deux sources exécutent ensuite la même requête autorisée `close`. Cette exécution :

- consomme les autorisations produites ;
- construit deux `ExecutedStep` ;
- construit deux `ExecutedRun` sur la même trace positivement non vide ;
- fait réellement passer les sources de la phase active à la phase terminale ;
- conserve leur histoire, leur provenance et leur pôle dans l’état riche ;
- produit les mêmes événements, lesquels ne contiennent pas le pôle.

Dans la réalisation opérationnelle sans exactitude du readout, la projection oublie le pôle seulement après `close`. Les deux runs produisent alors une même mémoire terminale `grouped`.

Le regroupement terminal est donc effectivement construit. Il n’est ni supposé avant l’exécution, ni obtenu en identifiant les sources riches.

### 2. Possibilité affirmative de la réalisation exacte

Le contrat riche possède indépendamment une réalisation exacte, notamment sa réalisation identité.

Cette réalisation :

- préserve les autorisations ;
- préserve les transitions ;
- préserve les événements ;
- préserve les readouts ;
- conserve la distinction entre les deux sources ;
- permet la continuation ouverte ;
- exécute également `close`, mais produit alors deux terminaux riches distincts.

L’existence de cette réalisation exacte n’implique donc aucune collision des mémoires. Elle montre positivement que l’exécution et la continuation restent possibles lorsque les distinctions exigées par le contrat sont conservées.

### 3. Nécessité démontrée de la séparation sous exactitude

Considérons maintenant une réalisation exacte arbitraire du contrat riche, fixée avant la politique de fermeture.

Si l’on exige que les deux sorties réduites calculées par les runs de `close` soient égales, alors :

1. `terminal_eq_run` relie chaque terminal riche à son run effectivement exécuté ;
2. `next_exact` transporte ces runs vers la réalisation réduite ;
3. la collision supposée identifie leurs mémoires terminales projetées ;
4. `read_exact` transporte cette égalité vers les readouts riches ;
5. la conservation du pôle pendant les runs ramène ces lectures aux deux endpoints gödeliens.

On obtient ainsi :

\[
\text{collision des terminaux calculés}
+
\text{exactitude du readout}
\Longrightarrow
\mathrm{Truth}(G)=\mathrm{Proof}(G).
\]

Cette égalité de types produit ensuite, par transport :

\[
\mathrm{Truth}(G)\to\mathrm{Proof}(G).
\]

Enfin seulement, la vérité certifiée et la non-prouvabilité du même énoncé produit sont consommées :

\[
t:\mathrm{Truth}(G),
\qquad
u:\mathrm{Proof}(G)\to\mathrm{Empty},
\]

d’où :

\[
u(\operatorname{transport}(t)):\mathrm{Empty}.
\]

La dépendance complète est donc :

\[
\begin{aligned}
&\text{runs exécutés}\\
+{}&\text{collision des mémoires terminales projetées}\\
+{}&\text{exactitude des transitions et du readout}\\
\Longrightarrow{}&
\mathrm{Truth}(G)=\mathrm{Proof}(G)\\
\Longrightarrow{}&
\mathrm{Truth}(G)\to\mathrm{Proof}(G)\\
+{}&\text{vérité et non-prouvabilité du même }G\\
\Longrightarrow{}&
\mathrm{Empty}.
\end{aligned}
\]

L’égalité entre vérité et preuve est ainsi dérivée de l’exécution, de la collision terminale et de l’exactitude du contrat. Elle n’est pas reçue comme hypothèse de fermeture.

## Contribution fondationnelle

L’obstruction n’est intrinsèque ni à l’exécution, ni à `close`, ni au regroupement opérationnel.

Une collision terminale est positivement réalisable sous un contrat qui préserve les autorisations, les transitions et les événements, mais qui ne prétend pas préserver le readout dépendant du pôle.

L’obstruction apparaît exactement lorsqu’une même projection prétend simultanément :

- fusionner les deux mémoires terminales calculées ;
- préserver exactement les readouts distincts imposés par le contrat riche.

La frontière formellement établie est donc :

> Une constitution relationnelle peut regrouper les mémoires terminales de sources distinctes lorsque le contrat projeté n’exige plus la distinction oubliée. Elle ne peut pas effectuer cette même fusion dans une réalisation qui doit préserver exactement des observations gödeliennes incompatibles.

Le rôle du témoin gödelien est précisément localisé. Il ne crée pas la collision et n’interdit pas tout regroupement. Il fournit :

- les deux readouts \(\mathrm{Truth}(G)\) et \(\mathrm{Proof}(G)\) ;
- un témoin de vérité du premier ;
- une réfutation de l’habitation du second.

L’exécution et l’exactitude produisent d’abord la conversion interdite. Les données négatives du témoin interviennent seulement pour rejeter cette conversion.

## Portée exacte

Le résultat établit une obstruction conditionnelle pour le contrat et la fermeture spécifiés. Il ne démontre pas :

- l’impossibilité de tout regroupement ;
- l’impossibilité de toute fermeture ou de toute totalisation ;
- un nouveau théorème d’incomplétude ;
- un résultat sur tous les runtimes ;
- un résultat sur le continuum, les réels, AC ou CH ;
- une borne de mémoire, de largeur ou de coût physique.

La conclusion exacte est :

> **Le regroupement opérationnel est constructible. La réalisation exacte est constructible. Leur combinaison avec une collision terminale devient impossible lorsque l’exactitude exige de conserver la distinction entre les readouts vérité et preuve du même énoncé gödelien. Cette frontière est produite par l’exécution, formellement dérivée et constructivement localisée.**

## Required final report

Return one self-contained report containing:

1. the exact audited commit and clean/dirty state;
2. a binary overall verdict: `VALIDATED` or `NOT VALIDATED`;
3. a seven-row table, one row per fixed acceptance criterion, with
   `PASS` or `FAIL`, exact evidence, and any counterexample;
4. the complete results of the independent reconstructions;
5. the build, verification, dependency, and `#print axioms` results;
6. a separate table validating every substantive sentence and bullet of the
   French statement with `TRUE`, `TOO STRONG`, `FALSE`, or `NOT VERIFIED`;
7. an explicit answer to each anti-shortcut question;
8. the exact boundary between the generic conditional theorem and the concrete
   Heyting-arithmetic realization;
9. a list of every remaining limitation, without adding a new acceptance
   criterion or moving the target.

Use `VALIDATED` only when all seven fixed criteria pass and the French final
conclusion is exactly supported. Otherwise use `NOT VALIDATED` and identify the
first precise declaration or dependency that fails. Do not promise a later
verdict: finish the audit on the pinned revision.
