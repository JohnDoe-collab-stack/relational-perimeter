# Independent scientific audit: constitutive agent and persistence under contract

## 1. Assignment and exact revisions

Perform a fresh, independent, exhaustive scientific audit. Report failures
plainly. Do not repair the target repository, weaken its specification, or
substitute a different result. A passing build is not a scientific verdict.
Previous audits of the computation or master instance do not validate this new
agent. There is no requested positive outcome.

Retrieve the repository yourself from GitHub; no local checkout is supplied:

- Repository: https://github.com/JohnDoe-collab-stack/relational-perimeter.git
- Branch: `codex/unified-foundation-master-instance`
- Exact scientific target: `f6c6d2c051ae0886056d47cf5357253c137a1319`
- Immediate parent and pre-agent baseline: `75057f09cc9a535e8be3390999fa688c9ee3a96d`
- Earlier master repair submitted for a separate audit: `8468f88448c51a0cd0ae178865fd014968131c47`
- Original independently validated computational target: `4e0febf032821882069e7cfefd7e631fc8461d95`
- Expected `origin/main` and merge-base: `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Toolchain: the unchanged repository `lean-toolchain`, Lean 4.33.1.

Clone and fetch the branch, then check out the exact scientific target detached.
Verify its parent, ancestry and merge-base. Record the actual branch tip. Later
audit-prompt/receipt-only commits are allowed, but must not replace the scientific
target. Do not require the branch tip to equal the target after those commits.
Stop on a missing or inconsistent pinned revision; report AUDIT BLOCKED rather
than inventing a scientific failure or silently auditing another tree.

The target is autonomous. It does not require a path dependency on another
research repository. Use Lean 4.33.1 directly; do not port the target to Lean
4.28 or add Mathlib to make probes work.

## 2. Immutable agent requirement and completion criterion

Read the complete implementation specification in
`docs/work/PLAN_AGENT_CONSTITUTIF_PERSISTANCE.fr.md`, particularly sections 2-16.
Section 17 reports local implementation evidence, not an independent verdict.
Read both canonical agent documents and the entire scientific reference note:

- `docs/agent-constitutif-et-persistance.fr.md`
- `docs/constitutive-agent-and-persistence.en.md`
- `docs/constitution-calcul-et-persistance-pour-ia.fr.md`

Quote this received requirement unchanged in your report:

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

Also quote this completion criterion unchanged:

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

The audit target is the WHOLE composed agent chain, not just certified grouping,
the cardinal iff, a projection-level observer, or an abstract conditional bridge.
Every concrete obligation must be closed by production code on the actual
public master. Do not count a plan, an author claim, a test-only lemma or a
conditional interface as a constructed production guarantee.

## 3. Scientific scope and distinctions

This is a constructed symbolic interactive agent on the existing public family,
not a language model, a general SAT solver, a benchmark claim or a general
human-alignment theorem. The received nonempty variable scope governs
restitution, not which discovery variable the engine selects. An accepted
Boolean read is contextual: initial and resumed entries can have different
continuation contexts. It is not a proof that one global arbitrary SAT instance
is satisfied. Register length is not independent-obligation width.

Forgetting is of the INITIAL SOURCE PROFILE in the ENTIRE specified runtime
memory, under an explicit nonempty future contract. It is not forgetting every
chronological history, constant physical memory, polynomial total cost,
information novelty, or security against external inspection of compiled
closures. The register can grow because the contract promises old reads.

Keep construction, realization, admission and specification satisfaction
distinct. Keep exact reference transports, criterion-preserving directed
actions and lossy memory projection distinct. Identity persistence through a
transport must not be inferred from a carrier equivalence alone. Extensivity
is a downstream readout, not an extra constitutive foundation.

The supported order to audit is: primitive relations/witnesses -> constituted
roles/history -> actual master actions and targets -> requirement realization
and initial register -> current request and resources -> production, read,
authorization and response -> transported next memory -> all finite futures.
No independent carrier, target, answer or responder may be attached afterward
as a substitute for the relevant formation and agreement.

## 4. Integrity and clean reproduction

Hash every tracked file before and after. Do not change any tracked target file.
Build artifacts, logs and installed tooling are allowed. Run probes and mutations
outside the protected target checkout. Compare target to parent and original
main; inventory additions, changed statements and removed interfaces.

In the pinned checkout run and log:

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
git diff 75057f09cc9a535e8be3390999fa688c9ee3a96d HEAD --check
lake update
```

Record versions, OS, exit codes, warnings, build jobs and selected files.
If Python is not resolved automatically, point `RELATIONAL_PERIMETER_PYTHON`
to an existing Python 3 interpreter; do not change the verifier. If PowerShell
is unavailable, explicitly say NOT RUN. PowerShell on Linux is not a Windows
test. Do not infer execution from reading a script.

Compare manifest bytes before/after `lake update`. The four original modules
`SegmentedResidualRole.lean`, `AbstractSegmentedTurning.lean`,
`ExactTypeTransport.lean`, `StrongPerimetralTurning.lean`, the license,
toolchain, prior computation/constitution sources and existing figures should
remain unchanged against the parent. Existing results and the declared scope
of the original computational target must not be weakened.

Local reported counts are 293 tracked files, 181 Lean files, 23 expected-failure
fixtures, 159 production modules and 180 modules in the exhaustive constant
audit. Clean builds reportedly ran 160 and 183 jobs. Recompute these counts
independently; none is evidence until checked by you.

## 5. Constructivity, code generation and coverage

Inspect all tracked Lean files, private declarations, tests and imported
production dependencies. No handwritten `axiom`, `sorry`, `admit`, `unsafe`,
`noncomputable`, `Classical`, `native_decide` or `implemented_by` is allowed.
No handwritten declaration may depend transitively on any axiom, including
`propext` or `Quot.sound`. Every Lean file must contain exactly one final
AXIOM_AUDIT block; every printed name must exist and be axiom-free.

Independently sweep all environment constants. Do not classify a forbidden
dependency as compiler-generated by name alone. Verify source/metadata origin
and that no handwritten consumer depends on those exceptions. The author
reports 17,945 constants and 360 compiler-generated exceptions, zero written
exceptions. Your own sweep is authoritative.

Every Type-valued construction actually needed by the agent must compile to
executable code, including positive provenance, initialization, authorizations,
advance, obtain and shared request evidence. Proof erasure is not a license to
hide missing noncomputable data behind Prop.

Check all production modules are reachable from `import RelationalPerimeter`,
all tracked Lean sources have build outputs, import boundaries are enforced,
and the stratification inventory is exhaustive. Agent ranks A10-A16 are terminal
and the root is A17; no earlier scientific module may depend on this new layer.
Do not accept a free/unconstrained stratum that hides a reversed dependency.

## 6. Complete source reading and clause/dependency table

Read all seven new modules in full, all three new test files, the new fixture,
the changed verification tooling and the production dependencies needed to
trace each claimed datum back to the four original foundations. Do not review
only exports or module headers. Read the earlier grouping, master-resource,
live-continuation, produced-profile and continuation-contract modules where
they are consumed. Distinguish unchanged inherited proof from new agent proof.

All names below are in namespace `ConstitutiveSearch.Agent` unless qualified.
Produce a table with clause, producer, input resources, positively constituted
witness, consumer, transport/agreement law, certificate field, probe/mutation
and verdict. Start with this source map; verify it rather than trusting it:

| Obligation | Production sources/declarations to inspect |
| --- | --- |
| Received scope and actual permissions | `Requirement.lean`: `receive`, `scopeSupport`, `Requirement.scope_exact`, `resolvePermission` |
| Exact target origin, not independent accepted data | `ProducedEvidence.lean`: `TargetOrigin`, `AnswerTarget`, `initialTargets`, `resumedTarget` |
| Actual master initialization and complete memory | `State.lean`: `normalizedRegister`, `start`, `sourceStart`, `project`, `initialize_from_master_exact`, `agent_memory_factors_through_output` |
| Historical resource production and reference square | `State.lean`: `HistoricalProduction`, historical producers, `RegisterRealization`, `History.realization`, `History.handle_transport`, `History.references` |
| One actual step and request production | `Execution.lean`: `step`, `runSteps`, `performCertified`, `interactionProducer`, `executeProducedInput`, `executeRequests` |
| Independent read/reply specification and exact worker | `Execution.lean`: `Authorization`, `Decision`, `ResponseEvidence`, `needed`; `Agreement.lean`: response and obtain laws |
| Independent rich interpreter and exact continuation | `Agreement.lean`: `sourcePerform`, `RichAuthorization`, `RichAdmission`, `sourcePerform_exact`, `bridge`, both admission return laws |
| Every internal stage and every finite future | `Persistence.lean`: `FollowedStages`, `followStages`, `RequestStages`, `Followed`, `all_executed_determinations_followed`, `all_future_*_exact` |
| Actual profile loss in whole runtime memory | `Persistence.lean`: `initial_memories_equal`, `initial_profile_not_recoverable`, `forgotten_sources_same_future` |
| One concrete closed public instance | `PublicInstance.lean`: `prepare`, `Prepared.memory`, `Prepared.certificate`, `publicAgent`, `Session`, `certify` in `Persistence.lean` |

## 7. Scope formation and nonvacuous authorization

Verify `receive` refuses an empty scope and positively realizes a nonempty
received scope through actual typed resources. Permissions must read its
realization and agree with the received variables. Two different scopes must
be able to change admission of the SAME read without changing its value.
Duplicate variables must not create a new permission right.

Inspect selection decoding only after actual roles are constructed. Bool codes
are a readout selecting already constituted occurrences, not a free Boolean
product replacing their carrier. Test wrong length, empty scope, valid codes
and actual initialization at multiple inputs. Construct positive valid
initializations and permissions; refusal of everything is not correctness.

The public initializer must produce/share one master. Invalid selection may
require that initial production; do not infer a no-work guarantee that is not
claimed. An ignored valid profile code can be observationally indistinguishable
after proved convergence; that alone is not a counterexample. Check actual
decode/formation and invalid-input semantics separately.

## 8. Produced targets, context and provenance

Trace the initial register from `master.source profile`, actual normalization
output and its exact executed-output equation. It contains one actual target
component per role, in role order; initial length is input + 1. A handle is a
session-local creation address, not itself a constituted occurrence.

Verify `initialTargets` requires equality with
`retainedExecutedOperationalTargetProfile reduction`. Acceptance alone must
not permit replacing the executed output with another accepted continuation.
`TargetOrigin` must be positive data dependent on that continuation, not an
unused tag. Its initial witness must not retain the source-profile choice.

For resumed stages, the registered target must be literally the actual
`production.built.stage.application.output`, with its actual acceptance context
and origin. Its event and next state must use that SAME production.
Trace how authorization consumes the occurrence, scope, read equality and
contextual criterion. Storing a provenance witness beside an independent target
does not establish the stated chain. Conversely, positively reconstructing a
redundant proof from the same constituted witnesses is legitimate; field
deletion alone need not constitute a scientific defect.

## 9. Typed rich support and transported handles

Inspect `History.realization` and all historical producers, not only its read
equalities. Initial normalization must read the actual master/profile resource;
components must read the produced bundle. A resumed rich head must produce its
target and next cursor from one shared `HistoricalProduction`, not unrelated
functions with equal tags.

The rich target support is distinct from the internal engine resource support.
Do not equate their extension sizes or positions. Both must be followed by
their actual transports (`RegisterRealization` versus `History.references`).

Verify `materialRegister` actually gathers support values; the rich interpreter
and `RichAuthorization.valueExact` must read them. Check the agreement is
consumed in `sourcePerform_exact`, `bridge` and authorization return laws, not
only projected in a test.

Construct register-to-support read and handle transport probes. Verify the
commuting square for every old typed reference, read preservation, injectivity,
positional shift and repeated extension. Stable handles and shifted support
positions are different quantities. Injectivity of references is distinct from
injectivity of read values. A transport into a larger support is not a bijection
onto every new occurrence. Check wrong context, foreign reference, swapped
producer ports and unrelated next cursor failures for intended type reasons.

## 10. Executed request chain and structural locality

Trace actual compiled and Lean paths through `publicAgent`, `Session.execute`,
`Session.produce`, `executeProducedInput`, `interactionProducer`,
`performCertified`, `runSteps` and `LiveContinuation.produce`.

Each worker step constructs one live production shared between event, target
registration and successor state. The head reads only current memory and current
request; future requests do not enter its producer. The resulting memory feeds
the structural recursion. Verify whole-head exactness and horizon independence
are in the closed certificate, not standalone unconsumed observations.

Construct two valid futures sharing a head and differing tails. Check the head
production and decision, not only a singleton projection. Distinguish structural
prefix locality from physical wall-clock scheduling. Cosmetic tail inspection
that yields the same executed decision is not automatically causal falsity;
future-derived operative data, delayed production and duplicate execution are
the substantive issues. Report interface gaps involving inert metadata honestly.

Do not treat `Session.produce` and `Session.execute` being separately callable
as two runs inside one invocation. Check sharing within each actual invocation.
The scientific rich interpreter can replay specifications for proofs; it must
not become a runtime dependency of the reduced session.

## 11. Reply/refusal semantics and effective obtain

Inspect `ResponseEvidence` independently of the responder. For an answer it
must require a permitted variable, a positive target occurrence and equality
with the actual continuation read. For a refusal it must give the precise
out-of-scope, missing-handle or incorrect-value facts. A responder-defined
predicate such as “the emitted answer is correct” is not an independent spec.

Construct correct and opposite Boolean candidates from a real target. Test
inspect, propose, absent handles, out-of-scope requests and their priority.
Authorization iff actual successful candidate reply must hold both ways.
Valid inspection must return its answer; safety by universal refusal fails.
Every refusal must preserve the ENTIRE memory, not just its live state.

For register length r and permitted request `obtain h var`, verify actual worker
stage count is `h + 1 - r`. If h < r, no stage is produced. If r <= h, final
register length is exactly h + 1 and a positively formed target is returned.
Out-of-scope obtain must not run the worker. Check zero, cached, last, first
missing and farther missing handles. Count actual event productions, not a
separately declared work number. Establish this through production theorems,
not only finite evaluations.

## 12. Independent rich contract and all finite interactions

Verify the rich Source carries actual master profile/history and reads actual
resource targets, not `project` followed by the runtime responder. It may reuse
the independent decision specification on its rich material values; shared
logic is not itself circularity. Inspect the full reader dependency.

Separate next, event, read and admission agreement in `bridge`. Construct both
permission/admission maps and both return laws on witnesses. Two implications
of Prop validity are not a substitute for those positive return laws.

Inspect `FollowedStages` inside each multi-stage advance/obtain, as well as
`Followed` at request boundaries. The actual engine resources, old handles,
register realization, response evidence and next agreement must be followed
in order. Request-boundary agreement alone is insufficient for the announced
internal-stage guarantee.

Check the quantification is every finite request sequence, not just admitted
traces or canned tests. Exact events/reads must include refused requests;
admission preservation/reflection must have their stated admitted-trace scope.
Check old reads, received scope and contextual target acceptance persist.

## 13. Whole memory, loss and concrete nontriviality

Inspect the complete schemas and nested fields of `Memory`, `Session`, target
entries and retained runtime values. Memory is requirement/live/register, and
Session only Memory. Prepared and Source may carry the scientific archive but
must remain outside the runtime session and resumption dependency path.

Audit `agent_memory_factors_through_output` on ENTIRE Memory, including positive
TargetOrigin data, not only equal readers or a projected subfield. Use the actual
master's distinct constituted profiles and produced convergence to construct
equal full initialized memories. Prove the no-uniform-decoder statement for
`Memory -> RoleOccurrenceProfile master.roles` on all actual initializations.
Synthetic unreachable states, an empty contract or a smaller observer do not
satisfy this target.

Check the public selection codes positively initialize those actual sources.
Verify equal full memories yield identical actual finite future states, events,
replies and the stated admission correspondences. Source identities must remain
distinct; losing their recoverability in memory is not a proof they are equal.

Keep chronological reconstruction and profile loss separate. Do not infer a
physical heap bound or minimality from proof erasure, logical equality, field
layout or absence of a Source field. Named closure capture checks have bounded
coverage. Explain precisely what retained origin values store and what they
omit rather than calling all provenance erased.

## 14. Closed certificate and public-client probes

Inspect EVERY field of `Certificate` and its construction by `certify`, plus
`Prepared.certificate` and actual public session creation. Each announced
concrete guarantee must be closed by its real producer, not an extra assumed
acceptance, foreign execution, free target, free reference map or responder.
Opening private constructors must not make scientific pins disappear; distinguish
privacy checks from semantic impossibility of a forged scientific guarantee.

Write constructive probes importing ONLY `RelationalPerimeter` for every table
row in section 6. Include actual good/bad candidates, an effective obtain,
whole-memory refusal, head sharing/locality, register-to-support read/square/
position/injectivity, all internal stages, all finite futures, two admission
return laws, valid initialization and whole-memory profile loss. Each probe
must have exactly one final axiom-audit block and no forbidden dependency.
Do not copy or redefine production objects into a parallel toy model.

Provide intended-failure clients for accepted-only initial target replacement,
foreign production/reference/context, independent reply/next, wrong permission
and private session/target mutation where applicable. Report the actual reason;
failure by setup, deleted name, syntax, lint or timeout is not semantic rejection.
Facts available only in your probes must be explicitly distinguished from
production facts consumed by the certificate.

## 15. Mandatory coherent mutation families

Freeze every patch before the run, hash it, apply it only in a disposable copy,
and record exact diff, build/verify commands, exit and first relevant diagnostic.
Adapt dependent interfaces coherently; an obsolete patch is NOT RUN, not rejected.
Do not repair the protected target. Separate production root survival, regression
test failure and verifier rejection. No missing-name or unused-variable failure
counts as a substantive scientific dependency.

At minimum attempt:

M01 replace the received scope with an independent fixed scope; authorize a
variable absent from it, and separately refuse every otherwise valid request;
M02 ignore selection length/decoding, or substitute a free Boolean carrier;
M03 replace an initial target by another merely accepted continuation without
the required executed-output agreement;
M04 detach TargetOrigin from its continuation or replace real provenance by
an unused tag; separately try retaining the initial profile choice there;
M05 register an independent resumed target while retaining genuine event/next;
M06 make event, registered target and successor come from distinct runs,
including a helper-hidden duplicate producer;
M07 make an operative head depend on a completed future or reconstruct it after
the future; also test inert future metadata and classify that variant separately;
M08 change an actual read/candidate comparison while keeping the same nominal
authorization; test universal authorization and universal refusal separately;
M09 perform obtain out of scope, skip required stages, overproduce stages,
or return a missing handle without a positive produced occurrence;
M10 alter memory on a refusal or run stages for a cached obtain;
M11 replace actual rich support production with targets merely declared given,
fake materialRegister reads, or make sourcePerform observe the runtime projection;
M12 alter the handle-to-support map, old read, position shift or injectivity;
M13 swap the engine and target-support transports, attach an unrelated cursor,
or use a transport reconstructed independently of the producing extension;
M14 retain only request-boundary Followed evidence and erase internal-stage
following; determine which certificate guarantees actually survive;
M15 erase contextual acceptance/preservation; distinguish legitimate positive
reconstruction from dropping the guarantee or replacing it by an external premise;
M16 substitute a bridge whose admission is responder-defined, remove one return
law, weaken all-future scope or omit refused-request event agreement;
M17 put the initial source/profile/archive back into Memory or Session through
nested values or named closures, then attempt the full no-decoder theorem;
M18 replace whole-memory loss by equal observations or an unreachable separator,
or replay the rich archive on runtime resumption;
M19 replace the public closed certificate by conditional obligations or open
constructors; test semantic foreign-memory/target/producer forgery, not just mk names;
M20 bypass import/axiom/codegen/expected-failure gates with multiline imports,
comments, a helper/closure, private forbidden constructs or unrelated failure.

Some changes are redundant: an erased field can be legitimately reconstructed
from the same constituted data; a fixed value can equal the actual output after
a proved convergence. Mutation survival alone is not a refutation. Determine
whether the original scientific guarantee was lost, independently supplied,
still positively reconstructed, or only protected by tooling. Do not invent
necessity of every syntactic field. Conversely, a stored witness never consumed
by the claimed guarantee must not be advertised as its causal source.

## 16. Runtime/tooling evidence and no regression

Audit `scripts/check-agent-codegen.py` and its reused parser independently on
actual generated C. Follow named callees, closure targets, constructor objects
and initializer dependencies. Check one public master route in initialization,
one request producer per head and one live production per worker step. Check
runtime paths exclude the rich archive, preparation replay and GLOBAL extensive
profile enumeration. The unchanged engine can construct a two-source local
readout after its action; this is not a global profile enumeration. Discovery's
own path must be checked separately against readout/image dependencies.

State static-analysis limitations, including dynamic callbacks, optimization
and physical heap visibility. Neither route counts nor small evaluations prove
asymptotic total cost. Do not infer those claims.

Independently inspect both verifier implementations, exhaustive constant audit,
stratification boundaries and expected-failure harness. A source lacking its
olean or a handwritten forbidden dependency must fail. A fixture failing for
an unrelated error must not count. Compare selected lists across platforms.

Compare old handwritten declarations/statements and regression coverage with
the pre-agent parent and original validated target. Check the four foundations,
original computational target, exact image/carry laws, general full-width iff,
partial 2^k regimes, stored growth, typed resources and prior future contract
are not weakened or silently redefined. Do not reattribute the finite counting
lemma as a new discovery or require it to consume unused relational witnesses.
The new agent must remain a consumer, not a replacement foundation.

## 17. Documents and final questions

Read README, both agent docs, the scientific reference note, the plan and new
module headers. Map each statement to production code, probe-only evidence,
finite execution, an interpretation or a future ambition. Check French/English
consistency and local links. Inherited submitted-audit receipts are not a
verdict about the new agent. Work plans/protocols must be removed before an
explicitly authorized merge; their presence on a work branch is not a defect.
No merge is authorized by this audit.

Answer every question VERIFIED / QUALIFIED / FALSE / NOT RUN, with exact file,
declaration and probe/mutation/log evidence, not bare yes/no:

Q01 Are target, parent, main and merge-base pinned and integrity preserved?
Q02 Do both clean builds and both verifiers run and pass on their actual platforms?
Q03 Are every handwritten constant and Type-valued construction constructive,
axiom-free and executable where required?
Q04 Are all tracked sources, modules and terminal strata covered and enforced?
Q05 Are prior scientific statements, foundations and protected bytes preserved?
Q06 Is the public initialization one actual shared master with actual-role decoding?
Q07 Is the received scope realized positively and consumed in permission decisions?
Q08 Are valid initialization and nonempty accepted requests positively inhabited?
Q09 Do source codes select actual constituted profiles without global enumeration?
Q10 Are initial targets exactly actual normalized components, not accepted-only substitutes?
Q11 Is TargetOrigin dependent positive provenance without the forgotten source choice?
Q12 Are resumed target, event and successor projections of the same live production?
Q13 Is the rich target support formed by actual producer reads rather than free given targets?
Q14 Are rich and engine supports distinct and both tracked through their real extensions?
Q15 Does the register-to-support square preserve actual reads and old handles?
Q16 Are reference injectivity and shifted positions proved separately from value equality?
Q17 Do rich interpreter and authorization actually consume those support reads/agreements?
Q18 Is ResponseEvidence independent of the chosen responder?
Q19 Are correct/wrong candidates, missing handle and out-of-scope semantics exact?
Q20 Do admitted inspect and obtain actually return answers rather than vacuous safety?
Q21 Does absent permitted obtain perform exactly h + 1 - r actual stages and end at h + 1?
Q22 Do cached obtain and refusals avoid stages, with refusals preserving whole memory?
Q23 Is one shared request production used, with its entire head closed in the certificate?
Q24 Are head decisions structurally prefix-local and independent of future requests?
Q25 Are next/event/read/admission rich-versus-runtime agreements independently closed?
Q26 Are both constructive admission maps and witness return laws present and consumed?
Q27 Are every internal stage and request boundary followed in their producer order?
Q28 Are every finite future, old read, received requirement and contextual criterion covered?
Q29 Does Session retain only the complete declared runtime Memory, not a hidden archive?
Q30 Does whole Memory, including positive provenance, factor through actual produced output?
Q31 Are distinct actual source profiles constructively shown to give equal full memories?
Q32 Is no uniform source-profile decoder proved on actual valid initializations?
Q33 Do the same future requests give identical actual events/replies/memories with two-way admission?
Q34 Is profile loss kept distinct from chronological erasure and physical/cost claims?
Q35 Is every certificate field closed, with no foreign datum or external premise substituted?
Q36 Do compiled-code gates justify their actual limited sharing/dependency claims?
Q37 Do scientific corruptions fail for substantive reasons, not deleted names or lints?
Q38 Are harmless/reconstructed mutation variants distinguished from genuine missing guarantees?
Q39 Do independent public probes cover the entire composed requirement?
Q40 Are documentation, bilingual scope and local links faithful and reproducible?
Q41 Are all five implementation lots A-E genuinely closed, with audit/integration still distinct?
Q42 Is the complete new agent requirement established, and what exact corrections remain?

## 18. Deliverables and verdict rules

Deliver a separate audit project under `audit/`, without modifying the target:

- `CONSTITUTIVE_AGENT_PERSISTENCE_AUDIT.md`: all 18 protocol sections, unchanged
  requirement/completion quotations, clause/dependency and producer-consumer
  tables, all 42 question answers, every finding with precise evidence;
- `README.md`: pinned revisions, toolchain, actual platforms, verdicts and commands;
- constructive public-client probes and intended-failure probes;
- frozen mutation patches, hashes, expected classifications and observed outcomes;
- independent axiom, coverage, declaration, dependency and documentation tools;
- raw logs, before/after tracked-file hashes and compiled dependency evidence;
- `reproduce.sh` and `reproduce.ps1` that freshly clone the exact target, pin its
  ancestry, run checks/probes/mutations and recheck integrity.

Run reproduction wrappers end to end where available. If only individual steps
or syntax checks were run, say so explicitly. Mark every missing platform,
probe and mutation NOT RUN; do not manufacture completion from intended commands.
Do not claim audit probes are target Lake roots. Keep setup failures separate
from semantic failures.

Give two distinct verdicts:

1. New composed agent: AGENT TARGET ESTABLISHED / AGENT TARGET REQUIRES
   CORRECTIONS / AGENT TARGET NOT ESTABLISHED / AUDIT BLOCKED.
2. Prior scientific results: NO REGRESSION VERIFIED / REGRESSION FOUND /
   REGRESSION REVIEW INCOMPLETE.

AGENT TARGET ESTABLISHED requires every mandatory scientific clause in sections
2 and 6-14 to be VERIFIED through actual production constructions and proofs.
A FALSE central clause means NOT ESTABLISHED; a material QUALIFIED dependency
means REQUIRES CORRECTIONS. Optional unavailable platform execution must be
disclosed, not silently passed, but does not itself refute a mathematical law.
Do not give NO REGRESSION VERIFIED without the actual base comparison.

Separate mathematical truth, concrete closure, interface protection, executable
implementation, tooling assurance, documentary fidelity and untested platforms.
State the smallest genuine remaining correction without making it. Evaluate
the actual agent target, neither an inflated universal AI claim nor an easier
cardinality theorem. There is no deadline or expected verdict overriding truth.
