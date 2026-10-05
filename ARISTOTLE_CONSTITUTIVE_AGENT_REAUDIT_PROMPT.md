# Independent scientific re-audit of the complete constitutive agent

## 1. Assignment, retrieval and immutable revisions

Perform an independent, exhaustive scientific audit. Report failures plainly.
Do not repair the target repository, weaken the specification, substitute a
different instance or seek a positive verdict. Audit the complete composed
agent, not only the latest diff. A successful build is not a scientific verdict.

Retrieve the repository yourself from GitHub:

- Repository: https://github.com/JohnDoe-collab-stack/relational-perimeter.git
- Branch: `codex/constitutive-agent-corrections-audit`
- Exact scientific target: `f039bdf3d822441e9e8b976ea54cf0177f58cffe`
- Scientific target tree: `b42c25cbc03233e17e3577d0d45a9bb741bd1b15`
- Immediate parent: `27546b9db4aa72769772d9253050e92fcfb0974d`
- Previous scientific re-audit target: `d52f3c0311d9572f84863481d508d38db2e5613c`
- Its scientific parent: `924bc6c38153e6e5e7e0b2290d03b5eca28881dd`
- First agent audit target: `f6c6d2c051ae0886056d47cf5357253c137a1319`
- Pre-agent baseline: `75057f09cc9a535e8be3390999fa688c9ee3a96d`
- Earlier master repair: `8468f88448c51a0cd0ae178865fd014968131c47`
- Original validated computational target: `4e0febf032821882069e7cfefd7e631fc8461d95`
- Expected `origin/main` and merge-base: `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Toolchain: unchanged `lean-toolchain`, Lean 4.33.1.

Clone, fetch, and detach at the exact target. Verify tree, parent, ancestry and
merge-base; record the actual remote branch tip. Later prompt/preparation-only
commits are permitted, but must not replace the scientific target. Inspect
their diffs. Stop and report `AUDIT BLOCKED` if a pinned revision is unavailable
or inconsistent; never silently audit another tree. The target is autonomous:
do not add Mathlib, port to another Lean version or depend on another repository.

The following Bash retrieval commands need no scientific placeholder:

```bash
git clone --branch codex/constitutive-agent-corrections-audit https://github.com/JohnDoe-collab-stack/relational-perimeter.git target
git -C target fetch origin
git -C target checkout --detach f039bdf3d822441e9e8b976ea54cf0177f58cffe
git -C target rev-parse HEAD 'HEAD^' 'HEAD^{tree}' origin/main
git -C target merge-base HEAD origin/main
git -C target merge-base --is-ancestor HEAD origin/codex/constitutive-agent-corrections-audit
```

## 2. Received requirement and completion criterion: quote unchanged

Read the complete `docs/work/PLAN_AGENT_CONSTITUTIF_PERSISTANCE.fr.md`, especially
sections 2-16. Its implementation ledger is author evidence, not your verdict.
Read the canonical French/English documents and the full scientific note:

- `docs/agent-constitutif-et-persistance.fr.md`
- `docs/constitutive-agent-and-persistence.en.md`
- `docs/constitution-calcul-et-persistance-pour-ia.fr.md`
- `docs/work/PLAN_CORRECTIONS_AGENT_REAUDIT.fr.md`

Quote this received requirement unchanged:

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

Quote this completion criterion unchanged:

> La première instance est achevée lorsque l’exigence concrète gouverne ses
> autorisations, que sa production opérationnelle est celle du moteur réel,
> que ses réponses et refus satisfont la spécification indépendante, et que
> le suivi de ces garanties se compose sur toutes ses interactions finies.
>
> La mémoire complète doit permettre cette continuation tout en ne permettant
> pas de reconstruire uniformément le profil initial oublié. Cette propriété
> doit être réalisée sur des sources distinctes effectivement construites.
>
> L’ensemble doit être livré comme une instance construite et exécutable, non
> comme une liste d’interfaces abstraites supposées satisfaites. Le résultat
> scientifique sera ce paquet fermé ; la transposition à d’autres exigences ou
> à d’autres agents restera une nouvelle tâche de preuve.

Every concrete obligation must be closed by production on the actual public
master. A plan, a conditional interface, a test-only lemma, a named field or a
previous audit is not a replacement for the construction and its consumers.

## 3. Scope and constitutive stratification

This is a constructed symbolic interactive agent, not a language model,
general SAT solver, cost theorem or general human-alignment theorem. The
nonempty received variable scope governs restitution, not engine discovery.
Acceptance is contextual; it does not prove satisfaction of one global
arbitrary SAT instance. Register length is not independent-obligation width.

Forgetting concerns the initial source profile in the entire specified runtime
memory under a nonempty future contract. It does not mean erasure of every
chronological history, constant heap size, polynomial total cost, information
novelty or security against arbitrary inspection of compiled closures.

Preserve construction / realization / admission / specification satisfaction;
exact reference transports / criterion-preserving actions / lossy projection;
operational output / representation readout. A carrier equivalence alone
does not transport constitutive determinations. Extensivity is a downstream
readout, not a second constitutive foundation.

Trace the order: primitive relations and positive witnesses -> constituted
roles/history -> actual master actions and targets -> received requirement and
initial register -> current resources/request -> production, read, permission
and response -> transported next memory -> every finite future. No independent
target, carrier, answer or permission may be attached afterward as a substitute.

## 4. Integrity and clean reproduction

Hash all tracked files before/after. Never change the protected target's
tracked files. Place probes, mutations and reports in a separate audit project.
Build artifacts and logs are allowed. Compare target with immediate parent,
previous scientific target, pre-agent baseline and original main.

Run in the pinned checkout, with versions, platforms, exits and logs:

```text
git status --porcelain
git rev-parse HEAD HEAD^
git merge-base HEAD origin/main
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
git diff 27546b9db4aa72769772d9253050e92fcfb0974d HEAD --check
git diff 75057f09cc9a535e8be3390999fa688c9ee3a96d HEAD --check
lake update
```

Check manifest bytes across `lake update`. Independently recount tracked files,
Lean files, production modules, fixtures and diagnostic sites. Author-local
counts are 308 tracked files, 181 Lean files, 159 inventoried production modules,
26 fixtures at 28 diagnostic sites. They are observations to verify, not axioms.
The original 23 fixtures/25 sites must remain byte-identical to the parent;
three new privacy fixtures add three sites. Compare the four foundations,
license, toolchain, manifest, existing figures and earlier scientific sources.

Use an existing Python 3 interpreter; `RELATIONAL_PERIMETER_PYTHON` can select
it without editing scripts. If a platform/tool is unavailable, mark `NOT RUN`.
PowerShell on Linux is not a Windows run. The author's Bash and PowerShell 7
checks were on Windows; independently report only platforms you actually use.

## 5. Constructivity, executability and import coverage

Inspect every tracked Lean source, including private declarations and tests.
Reject handwritten `axiom`, `sorry`, `admit`, `unsafe`, `noncomputable`,
`Classical`, `native_decide` and `implemented_by`, and transitive handwritten
axiom dependencies, including `propext` and `Quot.sound`. Require exactly one
final AXIOM_AUDIT block per Lean file, real fully qualified names, no axioms.

Independently sweep every environment constant. Generated exceptions must be
established from actual source/metadata origin, not name heuristics. Check no
handwritten consumer depends on them. In the author's external sweep two
derived Repr declarations and one generated congr_simp declaration were
initially misclassified; inspect their origins, preserve raw output and explain
any reclassification. Do not blindly copy the author's 18,255/360 counts.

Compile necessary Type-valued producers, provenance, initialization, worker,
authorizations and request evidence. Prop erasure must not conceal absent
constitutive data. Check all production modules are reachable from the public
root, all sources have fresh build outputs and the stratification inventory
enforces every boundary. Agent strata A10-A16 are terminal and root A17;
earlier science must not depend on this layer or an unconstrained substitute.

## 6. Complete reading and producer-consumer table

Read all seven `RelationalPerimeter/Agents/Constitutive/` modules, their three
agent test files, all changed tooling and necessary upstream foundations,
grouping, master-resource, live-continuation and contract modules in full.
Do not review headers/exports only. Distinguish inherited and new guarantees.

Create a clause table: producer, actual input, positive witness, consumer,
transport/agreement law, closed certificate field, public probe, mutation and
verdict. Verify this starting map; names are under `ConstitutiveSearch.Agent`:

| Obligation | Sources to follow |
| --- | --- |
| Received scope/permissions | Requirement: receive, scopeSupport, scope_exact, resolvePermission |
| Actual target/provenance | ProducedEvidence: TargetOrigin, AnswerTarget, initialTargets, resumedTarget |
| Master initialization/full memory | State: normalizedRegister, start, sourceStart, project, initialize_from_master_exact, agent_memory_factors_through_output |
| Historical producers/references | State: HistoricalProduction, RegisterRealization, History.realization, handle_transport, references |
| One actual request/worker | Execution: step, runSteps, performCertified, interactionProducer, executeProducedInput, executeRequests |
| Independent specification | Execution: Authorization, Decision, ResponseEvidence, needed; Agreement: response/obtain laws |
| Independent rich continuation | Agreement: sourcePerform, RichAuthorization, RichAdmission, sourcePerform_exact, bridge, both admission return laws |
| All internal stages/futures | Persistence: FollowedStages, followStages, RequestStages, Followed, all_executed_determinations_followed, all_future laws |
| Loss in whole runtime memory | Persistence: initial_memories_equal, initial_profile_not_recoverable, forgotten_sources_same_future |
| Closed public instance | PublicInstance: prepare, Prepared.memory, Prepared.certificate, publicAgent, Session; Persistence: certify |

## 7. Received scope, initialization and nonvacuity

Show empty scope is refused, nonempty scope is positively realized, and real
permissions agree with it. Different scopes must change admission of the same
read without changing its value; duplicates must not create new rights.
Selection codes must select already constituted occurrences, not replace their
carrier by a free Boolean product. Test valid codes, wrong length, empty scope
and actual initialization at multiple inputs. Refusing everything is not safety.

Inspect Prepared.prepare_exact, InitializationCertificate and Prepared.certificate
for exact scope, code, profile, memory and continuation. One public initialization
must share one actual master. Invalid input may require initial production; do
not invent a no-work claim. Different valid profiles can legitimately yield
equal memory after proved convergence; that alone is not failed selection.

## 8. Targets, contextual criterion and positive origins

Initial register targets must be the actual normalized master output components
in role order, not merely accepted alternatives. initialTargets requires the
retainedExecutedOperationalTargetProfile equality. TargetOrigin must depend on
that continuation, contain positive formation data and omit the source choice.

Resumed target, event and successor must project the SAME live production;
the target is its built stage application output. Eliminate actual origin to
derive acceptance through TargetOrigin.accepted and AnswerTarget.accepted;
trace consumers through ReplyCriterion, RequestEvidence and satisfaction.
Test accepted-only substitution, free origin tag, foreign context and captured
initial profile. A legitimately reconstructed redundant witness is not a defect.

## 9. Historical formation, support reads and exact transports

Follow HistoricalFormation, not_given, MaterialReading, values and actual
HistoricalProduction ports. Initial normalization reads master/profile data;
components read the produced bundle. A rich resumed head must share one producer
for target and next cursor. materialRegister, RichOperation, sourceProduced,
sourcePerform and RichAuthorization must consume those actual support reads.

Engine resource support and historical target support are different layers.
Follow both real extensions, not one conflated transport. Verify the register
realization's read square, old handle preservation, injectivity, positional
shift and repeated extension. Reference injectivity is not read-value
injectivity; extension into a larger support is not a bijection onto new ports.
Test foreign references, wrong ports/context/cursor and replaced support reads.
An equal alternate value reader can preserve mathematics while violating a
protected support path: distinguish the proof from the compiled-path gate.

## 10. Actual request production and prefix locality

Read publicAgent, Session.execute/produce, executeProducedInput,
interactionProducer, performCertified, runSteps and LiveContinuation.produce.
One worker step shares one live production for event, registered target and
next state. Current memory/request form the head without future requests;
the produced next memory feeds structural recursion.

Probe two valid futures sharing a head with different tails. Verify whole head
production/decision and consumed head-exactness/horizon-independence fields,
not merely a singleton projection. Distinguish structural locality from physical
scheduling. Future-derived operative data and delayed execution are substantive;
inert metadata or pure rewriting that preserves the actual chain is not
automatically falsity. Report interface limits without inventing necessity.
Separate callable entry points do not imply two runs within one invocation.
Rich specification replay must stay outside runtime resumption.

## 11. Independent replies/refusals and effective obtain

ResponseEvidence must independently require actual occurrence, permission and
read equality for an answer; precise out-of-scope, absent handle or wrong-value
facts for refusal. A responder-defined correctness predicate is insufficient.
Construct good/opposite candidates on real targets; test inspect/propose/obtain,
missing handles, scopes and refusal priority. Prove both authorization directions
and positive response, not universal refusal. Refusal preserves ENTIRE memory.

For permitted obtain of handle h at register length r, prove actual produced
stage count h + 1 - r. Cached h < r performs zero stages; missing h ends at
length h + 1 and returns a positive target. Out-of-scope obtain produces no stage.
Test first/farther missing and cached handles, actual event productions and
multi-stage consumers, not a separately declared work number alone.

## 12. Independent rich contract and every finite future

The rich Source must read actual master/history resources, not project into
the runtime responder. Shared independent decision logic is not circularity;
trace the reader. Separate next, event, read and admission agreements in bridge.
Construct both admission maps and both return laws on witnesses, not only Prop
implications. Verify they are consumed.

Follow every internal stage as well as request boundaries, with actual engine
resources, old handles, register realization, response and next agreement in
producer order. Quantify every finite request sequence, including refusal events;
respect the stated admitted-trace scope for admission reflection/preservation.
Check old reads, received scope and contextual acceptance persist after restart.

## 13. Complete memory, irreversible profile loss and real sources

Inspect nested Memory and Session fields and runtime values. Session retains
only declared Memory; Prepared/Source archives stay outside session/resumption.
Check entire Memory including TargetOrigin factors through actual output.
Use distinct actual constituted profiles with valid initialization codes to
produce equal full memories and prove no uniform decoder back to the source
profile. Empty contracts, unreachable separators or equal observations do not
satisfy the requirement. Equal full memory must produce equal actual finite
events/replies/successors and the promised admission correspondences.

Source identities remain distinct even when memory cannot recover them.
Explain retained provenance and omissions. Do not infer chronological erasure,
heap minimality or closure-security from equality, fields or proof erasure.

## 14. Certificate closure and public clients

Inspect EVERY Certificate field and certify/Prepared.certificate. The new
targetsAccepted, targetReads, resumedOrigin, followedStages, followedReferences
and internalStages fields must be closed from actual producers/laws, including
Followed.cons referencesExact and request_stages_exact. Followed.cons has been
strengthened: disclose its changed arity, do not claim all signatures unchanged.
References must pin the actual sourcePerform next history, not an independent
equal-looking map. These are engine references, not rich target-support transport.

Construct probes importing only RelationalPerimeter for every section 6 row and
all new consumers. Include multi-stage obtain, origin acceptance, target read,
resumed origin, two admission witness returns, internal stages/references,
whole-memory refusal and source loss. No copied/redefined production model,
forbidden construct or axiom; one final audit block per Lean probe.
Attempt foreign target/memory/producer/reference, accepted-only replacement,
independent next/reply and private constructor forgeries. Opening constructors
must not remove mathematical pins. Name-level privacy is interface protection,
not proof of semantic impossibility. Mark probe-only facts explicitly.

## 15. Frozen coherent scientific mutations

Freeze/hash each patch before execution in a disposable copy. Record full diff,
commands, exits and first relevant diagnostic. Adapt downstream uses coherently.
Missing names, lint, timeout or obsolete patch application is not a substantive
scientific rejection. Distinguish root, tests and gates. Attempt these families:

- M01 fixed/foreign scope, out-of-scope authorization, universal refusal.
- M02 ignored length/decoding, free Boolean carrier, detached initialization.
- M03 accepted-only initial target without executed-output agreement.
- M04 unused/foreign origin and source-choice retention in runtime provenance.
- M05 resumed target detached from genuine event/next production.
- M06 distinct event/target/next runs; direct/helper/closure hidden duplicate work.
- M07 future-derived operative head/delayed production; inert metadata separately.
- M08 altered read/comparison, universal permission or refusal.
- M09 out-of-scope obtain, skipped/extra stages, missing positive occurrence.
- M10 changed refusal memory or stages for cached obtain.
- M11 free/given historical support, fake material reads, runtime-projected rich reader.
- M12 wrong reference map/read/position/injectivity.
- M13 swapped transports, foreign cursor, detached extension.
- M14 request-boundary-only following; erase internal stages or exact references.
- M15 erase acceptance/preservation or replace closure by an external premise.
- M16 responder-defined bridge, missing return law, weakened finite/refusal scope.
- M17 hidden initial profile/archive in nested runtime memory or named closures.
- M18 projected/unreachable loss, runtime rich/master replay directly/helper/closure.
- M19 conditional certificate, opened constructors and semantic foreign forgery.
- M20 import/axiom/codegen/fixture bypasses, including the scenarios in section 18.

Survival is not automatically refutation: determine whether the guarantee was
lost, independently supplied, still positively reconstructed or only tool-protected.
Do not demand syntactic indispensability of every redundant proof. Conversely,
never advertise an unconsumed witness as the causal source of a guarantee.
The old external mutation archive is not required: independently reconstruct
the described scenarios. An author's run is not your run; record NOT RUN honestly.

## 16. Compiled implementation and bounded sharing checks

Read check-agent-codegen.py, unified_codegen_analysis.py and its selftests.
Regenerate actual C for each mutation before invoking the gate. Inspect helpers,
aliases, static closures, constructor captures and entry-point dependencies.
Validate one initialization master, one request producer per head, and live
production bounds [1,1] at step. Bound outside-step live calls at [0,0] on the
listed worker/request/head/executor/session routes; model explicit recursion
separately. Unknown helpers/cycles/unsupported closure routes must fail closed.

Test two real productions hidden by noinline helpers, wrappers and closures;
test one extra production outside step; test lawful single-helper refactoring.
The latter must pass: direct-call spelling is no longer a syntax requirement.
Optimizer-eliminated duplicate expressions may legitimately pass. Inspect switch
branches and rejection of unsupported fallthrough/unbraced forms.
Check rich archive/master replay and global extensive enumeration stay outside
runtime restart; local two-source readout is not global enumeration.

Report bounded unfolding, callback, optimizer and heap-visibility limits.
Static route counts are not general cost/heap/security theorems. Analyze F3
support-read paths separately from their possibly redundant value-level equality.

## 17. Structured failures and import/artifact transaction

Read expected_failure_diagnostics.py, expected-failures.tsv, both wrappers,
check-fixture-import-closure.py and test-expected-failure-gates.py completely.
Require actual Lean JSON, exit 1, exact category/site/needle and no unrelated
errors/warnings. Reject success, extra/missing diagnostics, malformed output,
timeout and other exits. Privacy failures are privacy, not dependent-type proofs.

Check fixture lexical policy before Lean: attributes/elaborators, diagnostic
APIs, m!/f! and executable commands must not spoof prescribed errors; handle
comments, characters, strings and malformed/foreign imports. Do not claim the
finite policy is a complete secure parser for arbitrary Lean.

Verify physical production files exactly match stratification; use actual
Lean-resolved direct dependency paths for every module to close transitive
imports. Admit only exact inventoried local paths and pinned toolchain Init and
Init.Omega artifacts, not arbitrary Init/Lean/Std/Lake modules or homonyms.
Reject direct, multiline/comment-prefixed and indirect forbidden imports,
uninventoried modules, unresolved/missing paths and boundary substitutions.

Lake freshness must cover ALL production artifacts with rehash/no-build/no-cache,
not silently build/fetch stale dependencies. Source/config/fixture/artifact/
toolchain fingerprints must remain fixed before each fixture and after the
transaction. Test changed source/artifact, stale/missing output, wrong resolver
path and unauthorized import with freshly built mutant artifacts. Closure
failure must prevent later fixture calls. Standalone Bash/PowerShell routes
must both enforce this, with no bypass flag or trusted stale cache.

## 18. Re-audit findings F1-F7 and gate counterexamples

Previous independent verdict at d52f3c0 was AGENT TARGET REQUIRES CORRECTIONS
and NO REGRESSION VERIFIED. Original external reports are not bundled here.
The descriptions below and production sources suffice for independent review.
For EACH finding give original gap, actual producer/consumer, positive client,
coherent negative attempt, exact rejection/survival reason and remaining limit.

F1: decoded-profile/initial-memory closure; F2: origin-derived acceptance;
F3: positively formed rich support and actual reads; F4: every internal stage
and both real supports/transports; F5: independent contextual criterion over
every finite response. Re-audit these fully, including the six new certificate
fields, rather than assuming earlier repairs passed forever.

F6 residuals: duplicated calls hidden by helper/closure, or extra calls outside
step. Compile live variants that expose [2,2] within step and [0,1] outside.
Confirm substantive compiled-gate rejection and acceptance of a lawful [1,1]
single-helper implementation. Do not count syntax/name/lint failure instead.

F7 residuals: an attribute-installed command elaborator can emit a diagnostic
at the prescribed source site while replacing the real #check error. Reproduce
that attack with actual Lean using Lean.logAt and interpolated messages,
including spoofing the accepted-output dependent-type site's 13:2 record.
First show the unguarded compiler produces the deceptive expected JSON while
the actual type error is absent; then require BOTH wrappers to reject source
policy/closure. Fabricated JSON alone is not an executed spoof demonstration.
Also test comment/character/quoted-spelling diagnostic tricks, unrelated failures,
foreign/transitive imports, stale artifacts and controlled policy-test failure.

Run the policy-only suite and full cross-shell suite in an audit-owned directory
outside target. From the target directory, the default Bash commands are:

```bash
python3 scripts/test-expected-failure-gates.py --policy-only
python3 scripts/test-expected-failure-gates.py --output ../audit/fixture-gate-tests
```

Create that separate audit directory first and preserve its outputs. Windows
may invoke the same scripts with its actual Python/Bash/PowerShell executables.
The author reports 288 positive/576 negative diagnostic matrix cases and
34 scenarios per wrapper (68 outcomes), using independent physical copies.
Recount and inspect logs; distinguish policy mocks from actual compiler runs.
Reference checkout artifacts must not be altered by disposable tests. Missing
PowerShell is NOT RUN, never implied success. A passing gate cannot override
an independent counterexample. No finite suite proves general harness security.

## 19. Required answers and documentary/no-regression review

Answer all 58 questions as VERIFIED / QUALIFIED / FALSE / NOT RUN, with exact
file/declaration/probe/mutation/log references. Never replace evidence by prose.

Q01 Are all revisions, tree, ancestry, integrity and toolchain pins exact?
Q02 Were clean builds, both verifiers and manifest checks actually run as reported?
Q03 Is every handwritten guarantee constructive, axiom-free and executable as needed?
Q04 Are all sources/modules/fresh artifacts and terminal strata exhaustively covered?
Q05 Are prior science, protected bytes and interfaces preserved, with strengthened arity disclosed?
Q06 Does one actual public master support decoded-profile initialization?
Q07 Is scope positively realized and consumed in actual permissions?
Q08 Are valid initialization and permitted requests constructively nonempty?
Q09 Do codes select constituted profiles without global enumeration?
Q10 Are initial targets exact produced normalized components?
Q11 Is target origin dependent positive data without the forgotten source choice?
Q12 Do resumed target, event and next project the same live production?
Q13 Is rich target support formed by actual historical producers?
Q14 Are engine and target supports distinct and both really transported?
Q15 Does the register/support square preserve reads and old handles?
Q16 Are reference injectivity and positional shift separate from value equality?
Q17 Do rich interpreter and authorization consume the support reads and agreements?
Q18 Is response evidence independent of the responder?
Q19 Are wrong candidates, missing handles and scope refusals exact?
Q20 Do valid inspect/obtain positively answer rather than refuse universally?
Q21 Does missing permitted obtain produce exactly h + 1 - r real stages?
Q22 Do cached obtain/refusals avoid stages, with refusal preserving entire memory?
Q23 Is one whole request production shared and pinned in the certificate?
Q24 Is the operative head prefix-local and independent of future requests?
Q25 Are independent rich/runtime next, event, read and admission agreements closed?
Q26 Are both constructive admission maps and witness return laws consumed?
Q27 Are all internal stages and boundaries followed in producer order?
Q28 Do all finite futures preserve old reads, scope and contextual criterion?
Q29 Does runtime Session contain only declared Memory without a hidden archive?
Q30 Does entire Memory, including provenance, factor through produced output?
Q31 Are distinct actual profiles shown to yield equal complete memories?
Q32 Is impossibility of a uniform source decoder proved on valid initializations?
Q33 Do equal memories give the promised exact finite events/replies/admissions?
Q34 Is source-profile loss distinguished from chronological/heap/cost claims?
Q35 Is every announced certificate obligation closed without foreign data/premises?
Q36 Do compiled gates establish their claimed limited sharing/dependency properties?
Q37 Do scientific corruptions fail substantively rather than by names/lints/timeouts?
Q38 Are harmless rewrites and legitimate witness reconstruction classified honestly?
Q39 Do root-only public clients cover the full composed requirement?
Q40 Are bilingual documents, scope and local links faithful?
Q41 Are implementation closure, independent validation and main integration distinct?
Q42 Is the complete immutable agent target established, and what correction remains?
Q43 Does initialization close received scope/code/profile/memory without source leakage?
Q44 Does origin elimination supply the consumed contextual criterion?
Q45 Do historical formation ports determine the actual protected support reader?
Q46 Are both support transports and every internal step consumed by the certificate?
Q47 Is acceptance independently specified and derived over every finite future?
Q48 Do regenerated-C checks detect helper/closure duplicate production and runtime replay?
Q49 Do BOTH fixture routes reject reproduced diagnostic spoofing for the right reason?
Q50 Do the six new certificate fields close their actual producers and consumers?
Q51 Is referencesExact tied to sourcePerform's real next history without conflating supports?
Q52 Do [1,1] step and [0,0] outside-step checks reject extra live work and accept a lawful helper?
Q53 Is the attribute/elaborator spoof demonstrated on real Lean before guarded rejection?
Q54 Does resolved-path closure reject direct/indirect foreign imports and homonyms?
Q55 Are freshness and immutable fingerprint checks transaction-wide and fail-closed?
Q56 Are 26/28 inventory, protected original fixtures and both harness runs independently checked?
Q57 Are generated-axiom classification and unexecuted cases reported without masking failures?
Q58 Are every F1-F7 gap and new assurance boundary actually closed within declared scope?

Inspect documentation claims against production, not tests alone. Check all
local Markdown links and French/English agreement, unchanged earlier diagrams
and the foundation order. This target changes Persistence/test and tooling;
it strengthens Followed.cons and six certificate agreements, not every earlier
science definition. Compare declaration inventories/statements with all named
baselines. Protect the validated computation, master, grouping, transports and
the full-width iff; never substitute agent correctness for their revalidation.
Temporary work plans/protocols may exist on this branch but must not be claimed
as main-integrated canonical science. No merge is requested by this audit.

## 20. Deliverables and verdict rules

Deliver a separate `audit/` project containing:

- `CONSTITUTIVE_AGENT_REAUDIT.md`: all 20 sections, unchanged target quotations,
  clause/producer/consumer tables, F1-F7 results and all 58 answers.
- `README.md`: exact revisions, real platforms, verdicts and reproduction steps.
- Constructive public-client probes, intended-failure clients and exact diagnostics.
- Frozen mutation patches, SHA-256, classifications, full diffs and actual outcomes.
- Independent axiom/coverage/import/declaration/documentation tools and raw logs.
- Before/after tracked hashes, compiled-C evidence and diagnostic spoof evidence.
- `reproduce.sh` and `reproduce.ps1` which freshly clone/pin target, check ancestry,
  run available checks/probes/mutations and verify final integrity.

Run wrappers end to end on available platforms. If only steps or syntax were
checked, say so. Mark missing platforms/probes/mutations NOT RUN. Setup failure
is not scientific rejection; audit probes are not target Lake roots.

Give TWO distinct verdicts:

1. `AGENT TARGET ESTABLISHED` / `AGENT TARGET REQUIRES CORRECTIONS` /
   `AGENT TARGET NOT ESTABLISHED` / `AUDIT BLOCKED`.
2. `NO REGRESSION VERIFIED` / `REGRESSION FOUND` / `REGRESSION REVIEW INCOMPLETE`.

ESTABLISHED requires all mandatory scientific clauses of sections 2 and 6-14
VERIFIED and the announced mandatory correction/protection assurances justified.
A false central clause means NOT ESTABLISHED; a material qualified dependency
or protection defect means REQUIRES CORRECTIONS. Unavailable optional platform
execution must be disclosed, not silently passed or treated as a false theorem.
NO REGRESSION VERIFIED requires actual baseline comparisons.

Separate mathematical truth, concrete closure, interface protection, compiled
implementation, tool assurance, documentary fidelity and untested platforms.
State the smallest real remaining corrections without implementing them.
Audit neither an inflated universal AI claim nor an easier neighboring result.
There is no expected positive outcome or deadline overriding truth.
