# Independent scientific audit: exact target and root corrections to unification

## 1. Assignment and independence

Audit the exact candidate described below. Retrieve the repository yourself from
GitHub. Do not launch another audit, contact another agent, repair production,
rewrite the target, weaken a mandatory dependency, or seek a positive verdict.

The corrected scientific target is committed and published on GitHub. Retrieve
it yourself using the exact branch and commit below. No ZIP, patch application
or author-supplied checkout is required. This protocol is not an independent
audit report and its author checks do not determine your verdict.

Report failures plainly. Build the candidate unchanged. Run mutations only in
separate disposable copies. Keep the pinned candidate and its evidence intact.

## 2. Exact retrieval and pinning

Repository: https://github.com/JohnDoe-collab-stack/relational-perimeter.git

Audit branch: `codex/unification-root-corrections-audit`

Exact scientific target commit: `924bc6c38153e6e5e7e0b2290d03b5eca28881dd`

Target parent / correction baseline: `9354e757e9dc2fbd429c34ff6cf9990140b6eed9`

Scientific target Git tree:
`5ab3e1c42cfd2d7b34f62855a48b33e24adbfbf9`

The branch also carries a subsequent protocol-only commit. Its only added
files are this prompt and `AUDIT_UNIFICATION_ROOT_CORRECTIONS_SOURCE_MANIFEST.json`.
Audit the scientific commit above, NOT the branch tip. Check that any descendant
changes are confined to these two protocol artifacts; unexpected scientific
changes must be reported, never silently audited instead of the pinned target.

SHA-256 of `AUDIT_UNIFICATION_ROOT_CORRECTIONS_SOURCE_MANIFEST.json`:
`39789e5fa038a3f082d347842880dced062b50158618a046eba3bff5b8337578`

The scientific target contains 298 source-tree files. Only the 12 paths listed
in section 4 differ from its parent. The manifest belongs to the protocol-only
descendant and describes the scientific target, excluding the two added protocol
artifacts. Audit generated outputs separately from this source-tree inventory.

Historical comparisons:

- preceding independent unification audit:
  `8468f88448c51a0cd0ae178865fd014968131c47`;
- preceding unified implementation:
  `44512e832565b4a2979e44beeab238e5719cf1df`;
- independently validated original target:
  `4e0febf032821882069e7cfefd7e631fc8461d95`;
- pinned main / merge-base:
  `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`;
- subsequently published constitutive-agent addition:
  `f6c6d2c051ae0886056d47cf5357253c137a1319`.

Retrieve the manifest from the audit branch before detaching the scientific
target. Save it outside the target checkout. Verify its pinned SHA-256 and all
scientific source hashes independently. A Bash retrieval sequence is:

```bash
git clone --config core.autocrlf=false --config core.eol=lf --branch codex/unification-root-corrections-audit https://github.com/JohnDoe-collab-stack/relational-perimeter.git target-checkout
cd target-checkout
git show origin/codex/unification-root-corrections-audit:AUDIT_UNIFICATION_ROOT_CORRECTIONS_SOURCE_MANIFEST.json > ../SOURCE_MANIFEST.json
git checkout --detach 924bc6c38153e6e5e7e0b2290d03b5eca28881dd
git rev-parse 'HEAD^{tree}'
git rev-parse 'HEAD^'
git merge-base HEAD origin/main
git status --short
git diff --check 9354e757e9dc2fbd429c34ff6cf9990140b6eed9 924bc6c38153e6e5e7e0b2290d03b5eca28881dd
```

Verify HEAD equals the exact scientific target, its parent equals the correction
baseline, its tree matches, its checkout is clean, all 298 source entries match
the manifest, and the parent-to-target changes contain only the 12 scoped paths.
If a pin, hash or tree differs, stop with AUDIT BLOCKED; do not choose a newer
commit or regenerate the manifest to match what you have. Record current remote
references separately. A later branch movement never changes the audit target.

## 3. Immutable scientific target

Quote these four paragraphs unchanged in the final report. Audit each clause,
including its quantifiers, operational dependencies and declared scope.

> Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.
>
> Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.
>
> Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application carry est injective.
>
> L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.

Formal scope already declared in production must be checked, not expanded:
full operational width equals `2^stageCount` iff `carry` is injective, for
finite surjective obligation regimes in the binary class. In the public
instance `stageCount = input + 1`. Partial regimes with width `2^k` remain
valid; the theorem does not characterize every asymptotically exponential
function. It is not a total-time, physical-memory, universal SAT, universal
foundational-superiority or information-novelty theorem.

The general finite-surjection lemma is a counting fact. It legitimately
accepts trivial relation fields. Do not demand an artificial relational
dependency in that lemma, and do not substitute that lemma alone for the
constitutive, executed grouping mechanism.

Extensivity is a quantitative readout of constituted profiles, not a producer
of relational roles and not a prerequisite through which execution must pass.

## 4. What this correction lot includes and excludes

The 12 changed paths are:

- `README.md` (only the compiled-check description);
- `RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean`;
- `RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean`;
- `RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean`;
- `Tests/UnifiedMasterInstance.lean`;
- `Tests/ProducedContinuation.lean`;
- `docs/continuation-et-oubli-des-profils.fr.md`;
- `docs/continuation-and-profile-forgetting.en.md`;
- `scripts/check-unified-codegen.py`;
- `scripts/unified_codegen_analysis.py`;
- `scripts/unified_codegen_selftest.py`;
- `docs/work/PLAN_CORRECTIONS_UNIFICATION_APRES_AUDIT.fr.md`.

The last file is a temporary work plan, not a scientific proof or permanent
provenance record. Its cleanup remains required before an authorized merge.

The four original foundation files, toolchain, dependency manifest, license,
existing figures, published agent modules/tests/docs and
`scripts/check-agent-codegen.py` are protected. Verify preservation against
the correction baseline and their entries in the pinned source manifest.

The agent modules already published in the base are regression consumers here.
Their separate ongoing independent audit is NOT this audit. Do not submit,
alter or communicate with it. Unpublished continuation-signature work and
concurrent README/root/verifier changes have deliberately not been included.

## 5. Prior findings and the correction hypotheses to test

The previous independent audit gave two distinct verdicts:
EXACT TARGET ESTABLISHED; UNIFICATION REQUIRES CORRECTIONS.

These are historical findings, not instructions for your verdict. The previous
report need not be available: all relevant defects are specified here.

| Item | Previously exposed defect | Claimed correction to inspect |
| --- | --- | --- |
| R01 | Certificate lacked positive advance admission and explicit injectivity/composition guarantees. Agreement alone allowed an empty admission. | Concrete positive producers and finite-list admission equivalence with both witness return laws; reference and historical composition fields closed by `Facts`. |
| R04 | A free origin with the right boundary could carry a different full support. | `ProducedPrefix origin history cursor` fixes the complete origin as an index; the same origin persists through growth and resume. |
| R06 | One static closure route could execute the producer twice. | Separate symbolic application analysis, preserving the older shared route API. |
| R07 | Old execution hidden in a consumer such as `Instance.stagewise` was not checked. | Full exported stagewise, normalization and checkpoint consumers checked transitively for replay and new production. |
| R08 | Nested readers could retain an archive without adding a top-level memory field. | Bounded retained-value/capture analysis from the actual factory into projected memory and public source/checkpoint paths. |
| R08b | Lookalike helper names could receive the privileges of trusted target/live boundaries. | Exact qualified generated symbols, unique defining-artifact ownership, and identical direct/closure-call policies. |
| R11 | Permanent transplantation provenance was insufficiently explicit. | NOT CLOSED. Explicitly deferred by the user, as explained below. |

R11 is openly unresolved: the user did not authorize a named permanent external
provenance reference. Do not invent one, waive the issue, call it fixed, or
replace it with a temporary work-plan note. Audit licensing/autonomy and
documentary provenance honestly as separate matters. A technical correction
verdict does not itself establish complete unification with every prior
documentary requirement closed.

The author's local checks report two native Windows verifiers, clean builds,
and targeted coherent controls. They are leads only, not your independent
evidence. Do not copy their pass status into your report.

## 6. Build, integrity and constructivity

Use the repository's Lean 4.33.1 toolchain unchanged. In the exact candidate:

```bash
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
git diff --cached --check
lake update
```

Run the applicable shell natively when possible. Record OS and actual shell
versions. If PowerShell is unavailable, mark its execution NOT RUN, not passed.
Do not install or change a dependency to make the target pass.

Record before/after hashes for the full source manifest, toolchain, license and
all production sources. Compare the candidate tree and clean status before/after.
`lake update` must leave the manifest byte-identical. Builds may generate
ignored artifacts; they may not change candidate source files.

Independently verify exactly one final AXIOM_AUDIT block in every Lean file,
every printed name exists, no written declaration depends on an axiom, and no
forbidden construct occurs. Sweep every environment constant, not just printed
ones. Identify compiler-generated exceptions individually and establish that
no hand-written declaration consumes them. Check executable Type-valued
witness producers; positive data must not be concealed by a Prop projection.

Inventory all Lean files, olean/C artifacts, production-root reachability and
strata. Check missing outputs fail the verifiers. Inspect import-gate parsing,
forbidden-token parsing and intended-diagnostic matching independently.

## 7. Method, stratification and complete execution chain

For each layer, record producer, actual inputs/ports, constituted indices,
consumer, transport and the laws really consumed. Follow the whole chain:

primitive relations and witnesses -> constituted roles/history -> executed
operational production -> normalization -> exact obligation image ->
historical extension/reference transport -> restricted future continuation.

The extensive readout is downstream of constituted roles; it is not inserted
as an execution prerequisite in this chain.

Separate construction/realization/admission, proposition/incorporation,
operational/representational output and diagnosis/prevention. Do not treat a
carrier equivalence as relational preservation or a directed semantic action
as an invertible transport.

Check one shared master result supplies all public projections. Whole head
production, not just an irrelevant label, must be produced prefix-locally
inside the execution recursion. Verify all-head exactness and horizon
independence remain certificate guarantees. Construct two valid histories with
the same head and different tails and compare their head production/decision.

A future-derived or delayed replacement must not merely survive because
completed data are irrelevant after reduction. Distinguish a genuine causal
change from unused cosmetic future data; substantiate the judgment by both
types/proofs and the actual compiled consumers.

## 8. Normalization, exact image and widths

Check arbitrary licensed actions, arbitrary continuations and preservation
separately from the canonical convergence equation. Both siblings remain
viable and distinct. Normalization constructs its target and indexed trace
through elimination of executed decisions, rather than prescribing a target
and restoring a trace by cast afterward.

The exact image regime must be constructible before convergence; width one
must be derived from convergence, not from choosing Unit or a singleton marker.
For every source pair, check both equivalences:
`carry p = carry q iff producedTarget p = producedTarget q`, and equality
iff executed codetermination. The image must neither merge different outputs
nor split equal outputs. Check exact image transport and both return laws.

Class and executed carriers must be definitionally identical, and the class
iff must apply directly to the public executed regime without adapters or
casts. Check both directions and all quantifiers. Two explicit distinct
profiles must be grouped on that carrier without identifying the profiles.

A constant function is extensionally legitimate after genuine convergence.
Its mere existence is not a counterexample. The question is whether an
independent constant regime can replace the master's pinned produced image
and evade the production guarantees.

Preserve partial `2^k` regimes and the generic counting theorem. Do not infer
total computational efficiency from final width one.

## 9. Complete-origin prefix and stored growth

Inspect `MasterResources.ProducedPrefix`, its constructors/accessors,
`UnifiedMaster.Growth`, `resource_history_extension`,
`Instance.producedPrefix`, `Growth.producedPrefix` and `Growth.resume`.

The complete designated origin includes support, kinds, values and references,
not merely depth or boundary. It is an index fixed by the caller's constituted
context, not an independently chosen field certified by boundary equality.
That same origin must persist throughout resumed growth.

Construct a legitimate origin with an extra resource and the same boundary.
It must have its OWN valid prefixes and extensions, preserving genericity;
it must not certify the original origin's terminal cursor or growth. Test
count zero and arbitrary positive counts. Reuse the actual produced prefix,
not an invented inconsistent witness that fails before the intended point.

Stored growth must execute only the requested suffix from the returned cursor,
not replay the original prefix. Check zero/nonzero suffixes and at least two
resumptions, exact history/endpoint/count laws, injective profile extension,
reference reads, composition and preservation of prior obligation laws.

Disclose the intentionally strengthened generic API. It is not byte-identical
source-level compatibility; it must preserve the old scientific results.

## 10. Future contract and certificate closure

Read the actual `ProducedContinuation` and `LiveContinuation` inputs,
memory, event/read semantics and admission predicates.

Construct positive advance witnesses on source and projected memory, including
zero and nonzero advance. Admission may not become Empty while agreement
between two empty implementations still passes. Check inspection at zero,
last valid slot, slot=count and larger slots against actual reader count.

Verify source-to-memory and memory-to-source admission for arbitrary finite
request lists. Both concrete witness return laws must be closed and accessible
through `UnifiedMaster.Facts`. They rely on this concrete admission witness
structure; do not generalize proof-irrelevant behavior to arbitrary Exact
interfaces with richer witnesses.

Check `executeInput` produces event and successor from one actual live
execution, and `executeRequests` shares it. Exact finite future observations
and events must refer to actual produced readers/output, not only mutually
agreeing invented implementations.

Verify `Facts` closes original regime/head/horizon/restart/inspection guarantees
AND the new positive admission, reference injectivity, composed reads,
profile embedding and obligation composition laws. Construct positive client
probes that consume the certificate fields, not only standalone theorem names.

## 11. Forgetting and compiled retention

The future contract is intentionally restricted. Keep two scientific objects
distinct: the full historical certificate/archive and the runtime memory.
Runtime continuation may not demand the normalized source profile or archive.

Construct the source-profile separator from reachable normalized profiles of
the same public execution, prove identical allowed memory/future observations,
and prove no uniform source-profile decoder. Do not use synthetic unreachable
states or an empty future contract.

This does NOT claim irreversible erasure of every chronological coordinate.
Inspect the chronological decoder obstruction and disclose exactly what depth
or provenance permits reconstruction.

Absence of a Source field or proof erasure does not prove absence of retained
archives: inspect nested fields, reader closures, aliases and initializers.
Report the actual bounded static analysis, not a physical-heap theorem.

## 12. Independent review of compiled-code checking

Read all three unified-codegen scripts in full. Independently inspect generated
C rather than treating CODEGEN_OK as a proof.

The shared `bodies/reachable/select/absent/calls/producer_routes` interface is
consumed by the unchanged agent checker. Its static route counts must retain
their old meaning. Dynamic application multiplicity is a separate Analysis.

For producer entry applications, test:

| Entry | Expected applications up to the recursive producer boundary |
| --- | --- |
| `UnifiedMaster.publicInstance` | 1 |
| `UnifiedMaster.resource_history_extension` | 1 |
| `UnifiedMaster.Instance.grow` | 1 |
| `UnifiedMaster.Growth.resume` | 1 |
| `UnifiedMaster.publicContinuation` | 2 |
| `UnifiedMaster.publicGrowthTwice` | 3 |

The last two include legitimate origin plus suffix productions. These numbers
are not counts of elementary operations inside recursion or a total-cost bound.

Check sharing, branch-exclusive calls, a closure applied twice, helper-hidden
applications, closure aliases, static closure objects, constructor-contained
closures, unresolved callbacks, cycles and missing C artifacts. A route
count of one must not imply that a closure was applied only once.

Check exported `Instance.stagewise`, `normalization` and `checkpoint`
consumers for zero new production and no transitive old-executor replay.
Mutations may remove a redArg optimization: inspect the surviving full wrapper
instead of counting a missing optimized symbol as substantive rejection.

Trace archived inputs through factory -> projected memory and the actual
public source/checkpoint flows. Check each retained field: live, output,
readers. Reproduce a reader retaining an archive in a nested environment/list,
including a noinline named helper whose behavior is otherwise equal.

Audit the explicit boundary registry independently. It currently relies on
these exact generated declarations and authoritative C artifacts:

| Declaration | Policy / defining artifact |
| --- | --- |
| `ExecutedCausalNormalization.result___redArg` | archive / ExecutedCausalNormalization.c |
| `ExecutedChainNormalization.target___redArg` | produced / ExecutedRoleIndexedReduction.c |
| `LiveContinuation.project` | live / LiveResourceContinuation.c |

All are fully qualified under
`ConstitutiveSearch.EndogenousDecomposition`. Rich historical getters are
conservatively tagged archive. Resolve the exact symbols and namespaces from
actual compilation. Missing, foreign or duplicate definitions must fail;
an imported prototype is not defining-artifact ownership.

Lookalike helper names must not inherit these policies. Test direct calls,
closures, aliases and static objects. Check invalid policies and arity. Also
inspect the semantic bodies of authorized boundaries: exact naming/ownership
alone does not establish that a changed body is still a sound declassification.

State what unknown client callbacks, generated-C forms, unsupported control
flow and runtime allocation behavior remain outside the guarantee. Do not turn
bounded graph/flow checks into an unrestricted soundness or memory claim.

## 13. Mandatory coherent mutations

Freeze each patch before its confirmatory run. Preserve its hash, exact diff,
command, complete outcome and first relevant diagnostic. Mutations must run
only in disposable copies. Preserve names/statements when feasible.

A syntax/import/setup failure, deleted-name failure, lint or timeout is not a
substantive scientific rejection. If a test merely names a deleted theorem,
adapt that fixture enough to reach the intended failure. Keep setup failures
separate and mark inconclusive cases honestly.

At minimum test the following families; historical patches must be adapted
coherently to the strengthened API, not called rejected because they no longer
apply:

M01 independent Unit regime replacing the produced image;
M02 prescribed target with trace recovered afterward;
M03 source-ignoring normalization/action;
M04 completed-future-derived head and delayed decomposition, including coherent
    value-preserving old-executor replay in a consumer;
M05 removal of action-output exactness with a genuine reconstruction attempt;
M06 removal of arbitrary-continuation acceptance preservation;
M07 deletion of the distinctness witness and identification of siblings,
    as separate variants;
M08 merging different targets or splitting equal targets;
M09 equivalent carrier adapter replacing the same-carrier interface;
M10 independently reconstructed execution/reference transport;
M11 origin replay instead of suffix-only growth;
M12 old-prefix reconstruction when resuming the returned growth;
M13 corrupted typed-reference reads, injectivity or composition;
M14 same-boundary foreign full origin/support and unrelated suffix/cursor;
M15 historical archive in nested memory or reader closures, including helper
    names impersonating the authorized target/live boundary;
M16 runtime restart by replaying the scientific archive;
M17 separate event/successor production instead of one shared executeInput;
M18 fake inspection values, permissive inspection admission and empty advance;
M19 synthetic/unreachable separator replacing actual profile forgetting;
M20 gate bypasses: multiline/commented imports, private forbidden declarations,
    wrong-diagnostic fixture failures, hidden helper/initializer production;
M21 two applications of the same producer closure with one static route;
M22 missing/foreign/ambiguous boundary ownership and indirect-call policies.

Independent rebuilding of distinction or preservation from the SAME constituted
witnesses can be legitimate. Judge the surviving guarantee, not mere field
necessity. Likewise distinguish harmless redundant data, an interface/tooling
gap and loss of a target dependency. Do not force every mutation to fail.

Run both the shipped positive/negative fixtures and your own public-client
probes. Ensure intended failure diagnostics, not just nonzero exits.

## 14. Non-regression, autonomy and documents

Compare scientific declarations against main, the original validated target,
the prior audited unification, and the published base. Inventory additions,
intentional generic-interface strengthening, theorem modifications/deletions
and changed regression coverage. Check the protected agent still builds and
its unchanged compiled checker still runs. Do not claim this audits all its
scientific behavior or unpublished signatures.

Read the canonical French/English documents, README, module headers and work
plan. Map claims to production proof, probe-only result, bounded C evidence,
conditional interface or unsupported statement. Check all local links and
bilingual scope. Existing diagrams are protected; do not redraw them.

R11 remains open. Verify autonomy and license without turning permanent
provenance into an external technical dependency or hiding the documentary
omission. Temporary work documents remain excluded from an eventual main
integration. An audit is not permission to merge.

## 15. Required final questions

Answer each VERIFIED / QUALIFIED / FALSE / NOT RUN, with exact file,
declaration, client probe and mutation/log evidence as applicable.

Q01 Are target, parent, candidate tree, manifest and historical pins exact?
Q02 Were clean builds and both platform verifiers actually run?
Q03 Are all written declarations constructive, executable where required and axiom-free?
Q04 Are all source modules, compiled outputs, reachability and strata accounted for?
Q05 Are the foundations, manifest, license and prior scientific results preserved?
Q06 Does the master share one real produced execution?
Q07 Do actual typed-resource ports supply the data consumed in order?
Q08 Are whole head production and decision prefix-local and certificate-pinned?
Q09 Does erasure recover the existing public executor for all required prefixes?
Q10 Does generic normalization construct target and trace executably?
Q11 Are its rules licensed by actual executed roles?
Q12 Are action, acceptance preservation, viability and distinction kept separate?
Q13 Are arbitrary normalizing traces semantically coherent?
Q14 Is canonical convergence confined to its correct data domain?
Q15 Are normal-position and produced-value images precisely related?
Q16 Do claimed exact transports have both return laws?
Q17 Is the image regime constructed before convergence?
Q18 Do both carry fiber equivalences hold?
Q19 Are class and executed carriers definitionally identical?
Q20 Does the genuinely two-way class iff apply directly with correct quantifiers?
Q21 Are explicit distinct profiles grouped without identification?
Q22 Are full, partial and executed widths stated with the correct scope?
Q23 Does stored growth consume history and execute only a suffix?
Q24 Does repeated growth consume the actual returned cursor and full origin?
Q25 Are profile and obligation extension/composition laws preserved and closed?
Q26 Are reference maps constructed, read-preserving, injective and composable?
Q27 Are resource transports pinned to their actual full producer/support?
Q28 Is restart based on the same execution/normalization rather than a new instance?
Q29 Does the retained runtime memory exclude archived sources within the analysis's scope?
Q30 Are event and successor produced together once?
Q31 Is the future contract explicitly nonempty with admission preserved both ways?
Q32 Are every finite allowed event/read and concrete witness return law exact?
Q33 Are forgetting witnesses actual reachable normalized profiles?
Q34 Is source-profile non-recoverability constructively proved?
Q35 Is chronological reconstruction explicitly distinguished?
Q36 Are static route counts and application counts kept distinct and correctly checked?
Q37 Is certificate closure robust to independent runs/regimes/transports?
Q38 Do coherent corruptions fail substantively rather than just by missing names?
Q39 Are gate bypasses, missing artifacts and unresolved effects honestly handled?
Q40 Are documents accurate, bilingual-consistent and locally linked?
Q41 Are autonomy and licensing preserved, with deferred provenance disclosed?
Q42 Is integration/work-document cleanup still explicitly open?
Q43 Is each unchanged target paragraph VERIFIED?
Q44 Which unification requirements remain unresolved?

Additionally answer R01-R12 individually:

R01 Are original certificate guarantees plus positive admission, witness
    returns, reference injectivity and all composition guarantees closed?
R02 Is inspection admission exact at all boundary cases?
R03 Do inspection values match the actual executed target/readers?
R04 Does the prefix index pin the full designated origin for all counts,
    while a different legitimate origin remains usable only for its own chain?
R05 Are stored and repeated growth concrete and suffix-only?
R06 Does the compiled checker distinguish applications from static routes,
    rejecting helper/closure/alias/initializer duplication?
R07 Do every relevant public consumer exclude old-executor replay?
R08 Does bounded retention analysis reject nested/archive captures and fake
    boundary names, and are exact registry policies semantically justified?
R09 Does repeated public growth avoid duplicate origin production through
    dependent implicit arguments?
R10 Are scientific results and published-agent consumers preserved, and any
    source-level API strengthening disclosed?
R11 Is documentary provenance still open, and are all other documentary
    claims/licensing checks accurate?
R12 Are retrieval, source pinning and independent reproduction complete,
    with actual platform and every unexecuted check clearly reported?

## 16. Required evidence and deliverables

Create a separate audit project under `audit/`, never inside the target:

- `UNIFICATION_ROOT_CORRECTIONS_SCIENTIFIC_AUDIT.md`: all 18 protocol sections,
  unchanged target, clause/dependency table, R01-R12 and Q01-Q44 answers;
- README: exact pins, GitHub retrieval, commands, OS/tool versions, limitations;
- positive and intended-failure client probes importing only RelationalPerimeter;
- frozen mutation patches, hashes, outcomes and intended diagnostics;
- independent axiom/reachability/declaration/compiled-flow/document checks;
- raw build/probe/mutation logs and before/after source hashes;
- `reproduce.sh` and `reproduce.ps1`: clone the GitHub repository themselves,
  checkout the exact scientific commit, verify its tree/manifest, rerun checks,
  probes and mutations, and recheck target source integrity.

Preserve the exact pinned source manifest in your reproduction materials. Run
each wrapper end to end if available; syntax checks or separately run commands
are not end-to-end reproduction. Report unavailable platforms as NOT RUN.

Do not list audit probes as Lake targets of this repository. Elaborate them
against the candidate using its own toolchain. Keep written probe declarations
constructive and axiom-free, with one final audit block per Lean probe.
A genuinely negative mathematical statement may be proved constructively;
an expected-failure fixture must fail for the intended type/semantic reason.

## 17. Verdict rules

Give separate judgments, never one blanket positive label:

1. Immutable target:
   EXACT TARGET ESTABLISHED / EXACT TARGET REQUIRES CORRECTIONS /
   EXACT TARGET NOT ESTABLISHED / AUDIT BLOCKED.
2. Technical correction lot:
   ROOT CORRECTIONS VERIFIED / ROOT CORRECTIONS REQUIRE CORRECTIONS /
   ROOT CORRECTIONS NOT ESTABLISHED / AUDIT BLOCKED.
3. Full unification:
   UNIFICATION ESTABLISHED / UNIFICATION REQUIRES CORRECTIONS /
   UNIFICATION NOT ESTABLISHED / AUDIT BLOCKED.

The third verdict must not silently close known-open R11. If it remains a
mandatory documentary condition of full unification, full unification still
requires that correction even when every technical repair is VERIFIED.

A positive scientific verdict requires all mandatory scientific clauses and
dependencies VERIFIED. A FALSE central scientific clause means NOT ESTABLISHED;
a material QUALIFIED clause means REQUIRES CORRECTIONS. An unavailable optional
platform must be disclosed; it does not automatically falsify a theorem.

Keep mathematical truth, public-interface completeness, actual runtime
sharing, bounded tooling coverage, documentary provenance and integration
readiness separate. Do not declare no regression without performing the
relevant comparisons. No author assurance or desired outcome overrides evidence.

## 18. Final integrity statement

State explicitly:

- which exact tree and sources you audited;
- whether any candidate source changed;
- which mutations ran in disposable copies and which did not run;
- which results are production facts versus probe-only facts;
- whether both reproduction wrappers ran end to end and on which OS;
- every remaining correction, including the deferred documentary item;
- that no audit submission, merge or modification of other agents was performed
  beyond this assigned independent audit.

Do not repair the repository. Report the smallest genuine remaining defects.
