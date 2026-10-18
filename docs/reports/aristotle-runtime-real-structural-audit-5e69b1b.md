# Independent audit report: relational runtime and effective-real correspondence

Révision auditée : `5e69b1bae964bd2aa2de0a6c53a2cebea959f6fc`.

> Note de traçabilité ajoutée lors de l’archivage local : la ligne de révision ci-dessus est le seul ajout au rapport Aristotle téléchargé.

Audit brief: `ARISTOTLE_RUNTIME_REAL_STRUCTURAL_AUDIT.md`, as supplied in the upload.
The message referred to `…_AUDIT_WITH_GIT.md`. No file with that name was uploaded.
The uploaded brief was used, together with the Git bundle `audit-material/runtime-reals-finalization.bundle`, which supplies the Git metadata.

**Overall verdict: `VALIDATED`**, for the narrow terminal statement permitted by the brief.

Section 1.3 and section 5 record one reproducibility caveat. The repository's own `scripts/verify.sh`, run on the exact target commit, stops at its second step. The cause is that the target's registry records an out-of-date source fingerprint (`STALE_SOURCE`). This is the expected self-reference problem: a commit cannot record its own hash, and the brief says to treat this as post-target closure metadata. The same verifier passes with exit code 0 on the closure commit `7a66ea6`. That commit differs from the target only in `docs/scientific-claims.json` and one renamed report, so its Lean sources and scripts are byte-identical to the target's.

---

## 1. Exact revision, tree and clean/dirty evidence

### 1.1 Git metadata

The upload is a snapshot repository with one commit (`8584252…`, "Initial commit"). That commit is not the target. The target's Git history came from the bundle:

```
$ git bundle verify audit-material/runtime-reals-finalization.bundle   -> "is okay", complete history
  ref: 7a66ea6c163c8f08f94377e98f637d25b9aff306 refs/heads/work/runtime-reals-finalization
$ git clone <bundle> repo && git checkout --detach 5e69b1bae964bd2aa2de0a6c53a2cebea959f6fc
$ git rev-parse HEAD            -> 5e69b1bae964bd2aa2de0a6c53a2cebea959f6fc   (matches)
$ git rev-parse HEAD^{tree}     -> b7e15bfaa08800bcf55899c9c3589bacb72ced49   (matches)
$ git rev-parse HEAD^           -> dddce26ef11940302e5f46f2ccc661f3494aabe9   (matches)
$ git status --short            -> (empty: clean)
$ git ls-tree -r --name-only HEAD | wc -l   -> 680
```

The target commit message is "Track safe product archive factory in codegen gate". The bundle contains two later commits after the target: `5503401` and `7a66ea6`, both titled "Refresh runtime real review evidence". The combined diff from the target to `7a66ea6` touches only these files:

```
docs/reports/runtime-real-native-correction-reader-translation-{129e38d -> 5e69b1b}.fr.md
docs/scientific-claims.json
```

### 1.2 Archive hash

- `git archive 5e69b1b | sha256sum` with LF line endings gives `9d2811a6…b906`. This does **not** match the brief.
- `git -c core.autocrlf=true archive 5e69b1b | sha256sum` gives **`d16b9e7c9f22a25fc56b6b1406f336e6ff3e19d4f9b9dfd9cc01df5ead5088af`**. This matches the brief exactly. The submitter's hash was therefore computed on Windows with CRLF line-ending conversion (`.gitattributes` uses `* text=auto`).

### 1.3 Supplied snapshot compared with the target

I extracted the CRLF archive and compared it with the uploaded snapshot.

- All 680 target files are present.
- After normalising line endings, every file matches except `.gitignore`. The upload platform appended extra ignore patterns to that file.
- The upload adds only two files: the audit brief and the bundle. That gives 682 files.

The whole audit used a clean LF checkout of the target commit (`/tmp/…/repo`). Mutations ran only in disposable copies.

---

## 2. Verdict

**`VALIDATED`**, limited to the statement permitted by the brief:

> For the explicitly defined class of effective dyadic presentations, carriers and executable Cauchy families, the relational runtimes and their numerical presentations are connected by a constructed structural numerical/behavioral correspondence that preserves the declared operations, positive relations, families and limits. Rich occurrences and histories are not reconstructed by the readout.

Nothing beyond this statement is validated (see section 8). The verdict rests on three things:

- the ten criteria in section 3, each read against the full Lean definitions and proof bodies;
- the reconstructions and mutations in section 4, checked in Lean;
- the builds, verifier runs, code-generation checks, expected-failure fixtures and axiom checks in section 5.

---

## 3. Acceptance table

| # | Criterion | Verdict | Files, declarations and proof-body dependencies inspected |
|---|---|---|---|
| 1 | Primitive direction | **PASS** | `RelationalRealAddition.Real` has five constructors: `leaf`, `add`, `neg`, `mul`, `certified`. `environment` builds the executable service by recursion on that tree. `toPresentation real := ⟨readout real, readoutsNear real⟩`, and `readout` is `(executeReal real p).code`, i.e. it reads a Step that was executed first. `toCarrier` is built on `toPresentation`. The opposite direction, `ofPresentation := .leaf (presentationToRuntime …)`, is declared and documented as a *realization* of received numerical data. It is never used to form `add`, `neg`, `mul`, inverse, density, bounds or the native limit. `R7_roundtrip_not_identity` (section 4) shows the round trip produces a different constructor tree. |
| 2 | Executed resource identity | **PASS** (with the documented same-index replay limitation) | **Addition.** `AdditionProduction` (private `mk`) holds `left`/`right` Steps. `additionProgram`'s received context is that pair, and `AdditionProduction.readoutExact` proves `code = left.code.add right.code`. **Native limit.** `NativeLimitProduction.groupedSourceExact` and `codeExact` connect the source execution to the grouping. **Uniqueness.** `NativeMediation` and `mediateNative` bind one `termStep` and pass it to both `converges` laws. **Order and density.** `ComparisonPair`, `StrictOrder.pair` and `Density.left/right` are built from executed comparisons. A bare code in place of a Step is rejected by the types (mutation M4a). A replay at the same indices is definitionally equal and is accepted (M4b), exactly as the FR/EN documents state. A replay at a different archive is rejected (M4c). Duplicate executions are rejected by the code-generation gate (`duplicate-valid-native-mediation`, `duplicate-valid-native-production`). |
| 3 | Memory and continuation | **PASS** | `Service` keeps the rich side (`Archive`, `Resource`, `execute`, `next`) separate from the live side (`Memory`, `liveStep`, `readLive`). It ties them with `nextExact`/`eventExact` and the exact-memory condition `separates`. **Addition, negation, multiplication.** Archives keep the child archives, the current journal, a chronological `retained` list and `last`. `additionNext` continues `left.next`, `right.next` and `completedJournal`. **Native.** `nativeNext` replaces only the visited bank entry (`updateBank`, `nativeNext_bank`) and continues the grouping journal. The live memory is `Option SignedDyadicCode`. `nativeLiveStep` ignores that memory and runs each term's kernel from its projected *initial* memory. This forgetting rests on the received uniformity contract `kernelExact` and is described in the module docstring. Resetting the bank or journal is rejected by the types (M6b, M6c). |
| 4 | Closed arithmetic and positive relations | **PASS** | **Operations.** `addEnvironment`, `negEnvironment` and `mulEnvironment` are defined for any child services. `RelationalRealInverse.inverse source (w : Apartness source zero)` is `.certified` with a certificate derived from `ReciprocalRuntime`, not assumed. Its direction, bound and successor come from the owned `StrictOrder` (`ReciprocalDomain.direction`/`away`/`sourceSuccessor`/`nonzero`). **Order.** `StrictOrder` (private `mk`) holds archives, accuracy, response, an executed `ComparisonPair` and a `StrictSeparation`. `Apartness` means forward or backward order. `classifyFinite` has an `inconclusive` branch, and `apartness?` returns `none` for it. There is no `Decidable` instance on `Real` or `StrictOrder` (grep). **Density and bounds.** `produceDensity` and `produceNaturalBound` execute programs, comparisons and margins. **Laws.** `orderedFieldLaws` and `orderedFieldFutureLaws` are concrete. |
| 5 | Native completeness | **PASS** | **Production.** `produceNativeLimit` runs `nativeSourceProgram` from the current bank (`searchNativeSource` → `executeAt … context.archive p`). Its result is passed as the received context of `nativeGroupingProgram source`, and the request type is `Unit`, so it carries no target. `act` builds `nativeNormalized searched`. **Install and reuse.** `nativeNext` installs the produced target, and `nativeNext_read` reads it back exactly. **Convergence.** `nativeAuthoritative.converges` is `observeLimit … .near`: it takes `lim.resource.diagonal` (the owned Step) and applies `family.cauchy`. It is not a copied field. **Caveat.** The grouping is a one-source normalization (`nativeSpecification`: `Source := Unit`, `targetCode := source.diagonal.code`). The installed target code therefore equals the diagonal term's code at the requested precision. That is the standard Cauchy limit, and it is described honestly. |
| 6 | Uniqueness without identity | **PASS** | `nativeUnique` → `nativeNumericalFutures` → `produceNativeUniquenessTrace` (from `initialBank`) → `mediateNative` + `NativeUniquenessTrace.toNumerical`, then `toEquivalent`. I traced the transitive constant dependencies in Lean (section 4, R6). The dependencies of `nativeUnique` and `nativeAuthoritativeUnique` do **not** include `toEffectiveFamily`, `realizedFamily`, `asExecutedCandidate`, `realizeFamily`, `observeCandidate`, `RelationalRealLimitUniqueness.unique` or `currentReadout`, and no axiom appears in them. The positive test `Tests/RelationalRealNativeCauchy.addZeroCandidate` uses `.add (nativeLimit …) (zero …)`, which is a different constructor from `.certified`. I checked the constructor difference separately, through a discriminator function (R3). The conclusion is only `Equivalent × NumericalFutureEquivalent`. |
| 7 | Structural correspondence | **PASS** | The type of `effectiveCorrespondence` is `(P) → (baseDepth) → EffectiveCorrespondence P baseDepth`, with no hypothesis (M9). Each of the six blocks is a `def` whose fields name earlier producers or proofs. For example: `toPresentation_add`, `realization_mul`, `RelationalRealInverse.toPresentation_inverse`, `reflectPresentationOrder`, `produceDensity`, `produceNaturalBound`, `RelationalRealNativeCauchy.nativeCompleteness`, `nativeUnique`, `preserveLimit`, `reflectLimit`, `realizeLimit`, `produceTrace`. Reflection is defined only on images (`toPresentation a`, `ofPresentation …`) and needs received archives. No field gives a rich inverse. Downstream fields (`nativeProducedProjection`, `families.nativeReadout`) do go through `realizedFamily`/`asExecutedCandidate`, and they are labelled as downstream. |
| 8 | Gödel boundary | **PASS** | `GodelRealCorrespondence.realizePresentation (execution) (presentation : EffectiveDyadicPresentation)`: the presentation is a separate argument. Its numerical content comes from `presentation_roundtrip_equivalent`. The equalities `godelInitialIsRuntimeInitial`, `godelProducedRealIsRuntimeProduced` and `godelFirstStepIsRuntimeStep` tie it to the shared runtime. A heuristic scan of the whole environment found no declaration that mentions `ExecutedGodelProduction` and returns a presentation, carrier, family or code without receiving one (M10). The Gödel layer uses the `RuntimeReal`/`CommonRealRuntime` level. The repository never instantiates the generic `effectiveCorrespondence` at the Gödel perimeter. I checked that it does instantiate (`haTerminal`), with no axioms. |
| 9 | Constructivity and executable data | **PASS** | The forbidden-token grep in `verify.sh` is clean. My extra grep for `partial def`, `@[extern`, `implemented_by`, `opaque`, `Decidable` instances and `Classical` in the reals and Gödel-real sources also found nothing. The build log has 7661 "does not depend on any axioms" lines, no "depends on axioms" line and no `sorryAx`. `ALL_CONSTANTS_OK constants=37092 modules=395 generatedExceptions=737 writtenExceptions=0`. The 737 exceptions are compiler-generated equation lemmas (e.g. `mk.injEq`) that use `propext`. None appears in the dependencies of `nativeUnique`, `nativeCompleteness` or `effectiveCorrespondence`. Minor: `Tests/RelationalRealEffectiveCorrespondence.lean` has an empty `AXIOM_AUDIT` block, though its constants are covered by `AllConstantsAudit`. |
| 10 | Documentary exactness | **PASS** | Section 6 audits the FR and EN canonical texts clause by clause. They have the same sections, quantifiers, direction, losses and exclusions. Both state the same-index replay limitation, that `NativeCandidate.converges` is a received law, and that `certified` admits any external service meeting its contract. Neither extends the result to all classical reals. |

---

## 4. Reconstructions and mutations

All of these were run with `lake env lean <file>` against the built target, in a disposable copy. The Lean files are in `audit-reproduction/*.lean.txt`; the `.txt` suffix keeps them from being picked up as project sources.

### Reconstructions (`AuditReconstruct.lean.txt`)

All of these check, and the main declarations have no axioms.

- **R1. Addition step at an arbitrary current archive.**
  - `step.resource.left = executeAt a archive.left (p+1)`, and the same for the right child.
  - `step.code = left.code.add right.code`.
  - `step.next.left/right = child.next`, and `step.next.last = some step.code`.
- **R2. Native transition from an arbitrary bank, without the packaged completeness theorem.**
  - `source.diagonal = executeAt (terms (modulus p)) (bank (modulus p)) p`.
  - The grouping's stored source equals `source`.
  - `step.code = diagonal.code`.
  - `next.bank (modulus p) = diagonal.next`, and `readNativeInstalled next = some step.code`.
  - `next.journal = grouping.completedJournal`.
  - The second transition reads the successor bank entry.
- **R3. Uniqueness for two constructor-different candidates.**
  - The candidates are `nativeCandidate`, which is `.certified`, and `addZeroCandidate`, which is `.add`.
  - A separate function `constructorTag` gives 4 and 1, which proves `real ≠ real` without `cases`.
  - `nativeUnique` gives `Equivalent × NumericalFutureEquivalent`, and its threshold is `nativeUniquenessThreshold`.
- **R6. Transitive-dependency check (Lean metaprogram).** The results are those reported in row 6 of the table.
- **R7.** `ofPresentation P d (toPresentation (.add a b)) ≠ .add a b`. Numerical round-trip equality is not identity.
- **R13. Data flow (definitional).**
  - `execute archive p = produceNativeLimit family archive.bank archive.journal p`.
  - `liveStep m₁ p = liveStep m₂ p` for every pair of memories.
  - `readLive (project a) = a.installed.map code`.

### Mutations (`AuditMutations.lean.txt`, `AuditOpenPrivate.lean.txt`, `AuditGodel.lean.txt`, and source patches)

| # | Patch / attempt | Expected | Actual | First obstruction |
|---|---|---|---|---|
| 4a | Pass `term.code` to `first.converges` in place of a Step | reject | rejected | `Application type mismatch: term.code : SignedDyadicCode, expected Step (environment (family.terms …)) ?a p` |
| 4b | Replace the mediator Step with an independent `executeAt` at the same indices, and compare with `(mediateNative …).secondNear` | survives at type level (documented limitation) | **survives** (`rfl`) | none: `Step` packets are deterministic. This is the limitation FR/EN state. At the compiled level, the code-generation gate rejects duplicate executions. |
| 4c | Replay from a different bank (`other` instead of `bank`) | reject | rejected | `Type mismatch`: the archive index is fixed by the type of `Step` |
| 5a | `⟨charge, _⟩ : NativeTarget source` (prescribed target) | reject | rejected | `Constructor for … NativeTarget is marked as private`. With the meta-level bypass described in mutation 11, `normalizedExact : normalized = nativeNormalized source` still fixes the value. |
| 5b | Rebuild the target from `readout (nativeLimit family) p` | reject | rejected | `Type mismatch: SignedDyadicCode, expected LocalGrouping.GroupedCharge p source.diagonal.code` |
| 5c | `NativeLimitProduction` literal with a separately executed grouping | reject | rejected | `Constructor … NativeLimitProduction is marked as private`. The request type of `nativeGroupingProgram` is `Unit`, so a request cannot carry a target. |
| 6a | `NativeCauchyFamily` without live kernels | reject | rejected | `Fields missing: kernels, kernelExact` |
| 6b | `nativeNext archive (produceNativeLimit family (initialBank family) archive.journal p)` (reset bank) | reject | rejected | `Application type mismatch … expected NativeLimitProduction family archive.bank …` |
| 6c | Same as 6b, but with `Journal.root` (reset journal) | reject | rejected | the type requires `archive.journal` |
| 7 | Turn the numerical round trip into rich equality | refuted | refuted | R7 proves inequality |
| 8a | `StrictOrder` literal from a comparison pair without a separation | reject | rejected | `Constructor for … StrictOrder is marked as private` |
| 8b | `(apartness? (compareCurrent …)).get!` | reject | rejected | `failed to synthesize Inhabited (Apartness a (zero P d))`. The inconclusive branch gives `none`, and inverse needs an `Apartness`. |
| 9 | Terminal package built from assumed fields | not possible in the published declaration | confirmed | `#check effectiveCorrespondence : (P) → (baseDepth) → EffectiveCorrespondence P baseDepth`, with no hypothesis |
| 10 | Derive a dyadic approximation or classical coverage from Gödel alone | no such producer | none found | `realizePresentation` needs `(presentation : EffectiveDyadicPresentation)`. The environment scan returned `#[]`. |
| 11 | Outside-module forgery: `⟨…⟩`, `{ … }`, and `{ seed with last/installed := … }` on `AdditionArchive`, `NativeArchive`, `MultiplicationArchive` | reject | rejected | `invalid {...} notation, constructor for … is marked as private` (×5). The safe seeds `seedAdditionArchive` and `seedNativeArchive` succeed. |
| 11′ | Meta-level bypass: a custom `elab` that refers to the mangled `_private.…AdditionArchive.mk` / `NativeArchive.mk` constant | — | **succeeds** | `private` is a naming boundary at elaboration time, not a kernel boundary. The forged archives are accepted by `executeAt`. `verify.sh`'s forbidden-token list does not catch this. No theorem depends on archives being reachable; they all quantify over every archive. The claim that the "public seed functions cannot prescribe…" remains literally true. |
| 12a | `nativeUnique := unique (asExecutedCandidate first) (asExecutedCandidate second)` | Lean accepts; gate should reject | Lean build OK; **gate rejects** | `REAL_NATIVE_CAUCHY_CODEGEN_FAILED nativeUnique does not derive its result from native futures` |
| 12b | Keep `nativeNumericalFutures` for the futures, but build `Equivalent` through `authoritativeUnique ∘ asExecutedCandidate` | Lean accepts; gate should reject | Lean OK; **gate rejects** | `Native uniqueness reintroduced its old downstream mediation` |
| 12c | Same as 12b, with the `LimitCandidate` adapters written inline (no `asExecutedCandidate` name; uses `observeCandidate`) | Lean accepts; gate should reject | Lean OK; **gate rejects** | same message. Afterwards I restored the source, rebuilt, and the gate printed `REAL_NATIVE_CAUCHY_CODEGEN_OK` again. |
| 13 | (i) Change the installed observation with bank and journal fixed, using a meta-forged `NativeArchive`. (ii) Change the bank with the observation fixed. | (i) rich step unchanged, read changes; (ii) rich step changes | confirmed | (i) `execute (forged) p = execute (seed initialBank) p` by `rfl`, and `readNativeInstalled forged = some r.code`. (ii) `diagonal = executeAt … (bank (modulus p)) p`. Field readers: `bank` and `journal` are read by `produceNativeLimit` (rich `execute`). `installed` is read only by `readNativeInstalled` = `readArchive` = `project`, followed by `readLive = id`. `nativeLiveStep` reads neither. `retained` is read by no later operation; it is kept for the rich contract. |

The 12a–12c mutations are not caught by the Lean type checker. They are caught by the code-generation analysis, which partly works by name matching (`nativeNumericalFutures` must appear, and a list of forbidden names). It caught all three variants I tried. It is still a test, not a proof.

---

## 5. Build, verifier, code generation, fixtures and axioms

| Step | Where | Result |
|---|---|---|
| `lake build` from a clean checkout (no `.lake`, so equivalent to `lake clean`) | target `5e69b1b` | **OK**: 398 jobs, 8 min 58 s wall-clock, 0 warnings. `ALL_CONSTANTS_OK constants=37092 modules=395 generatedExceptions=737 writtenExceptions=0`. |
| `bash scripts/verify.sh` | target `5e69b1b` | **exit 1** at step 2: `SCIENTIFIC_DOCS_ERROR: STALE_SOURCE: RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE`. The registered `source_sha256` is `b66ec9b5…`; recomputing it over 182 files gives `3abe2b41…`. After patching only that hash, the next error is `STALE_SNAPSHOT`, because `evidence_revision` still names `129e38d`. Both fields are rewritten by the closure commit. This is the self-reference problem the brief describes. |
| `bash scripts/verify.sh` | closure commit `7a66ea6` (Lean sources and scripts byte-identical to the target) | **exit 0** (4 min 9 s, with build cached). Output: `SCIENTIFIC_DOCS_STATIC_OK claims=21 declarations=168`; four import-boundary checks OK; `Verified stratification inventory: 329 production modules`; build 398 jobs; `SCIENTIFIC_DOCS_LEAN_OK` (132 public and 36 test declarations); every code-generation check OK; `Verified expected failures: 189 fixtures, exact Lean diagnostics and sites`; `Verified 396 Lean files`. It also reports `SCIENTIFIC_DOCS_OPEN_REVIEWS … independent=not_recorded` as information. |
| Real-runtime code-generation scripts (11) | as above | all OK: addition, negation, multiplication, order, inverse, ordered-field, density, cauchy, limit-uniqueness, family-transport, native-cauchy (245 internal `MUTATION_REJECTED` lines across the scripts) |
| Other code-generation checks | as above | `CODEGEN_OK` (unified), `AGENT_CODEGEN_OK`, `SIGNATURE_CODEGEN_OK` and `REACHABLE_SIGNATURE_CODEGEN_OK`, `VARIABLE_MASTER_CODEGEN_OK`, `INTEGRATED_MACHINE_CODEGEN_OK` |
| Expected failures | as above | 192 active TSV rows and 189 fixture files, each matched to its exact diagnostic, including all 18 `Private*` fixtures (e.g. `PrivateAdditionArchiveUpdate`, `PrivateNativeArchiveUpdate`, `PrivateReciprocalArchive`) |
| `git diff --check` | target | clean |
| `pwsh -File scripts/verify.ps1` | — | **not run**: PowerShell is not installed in the audit environment. This is an environment limitation, not a mathematical result. |

Every count reported by the submitter was reproduced exactly: 398 jobs, 37 092 constants, 395 modules, 737 generated exceptions, 0 written exceptions, 396 Lean files, 189 diagnostics, 192 TSV rows, 329 stratified modules.

---

## 6. Clause-by-clause audit of the FR/EN canonical conclusions

The documents are `docs/runtime-real-cauchy-effective-correspondence.fr.md` and `docs/runtime-effective-cauchy-real-correspondence.en.md`. Both have the same eight sections in the same order.

| Clause (EN / FR) | Lean evidence | Status |
|---|---|---|
| Status: not an independent audit, not an identification of histories, not all classical reals | — | accurate, same in both |
| `presentationToRuntime` builds an identity-modulus family; `runtimeToPresentation` executes the canonical step; `ReadoutOrigin` keeps the step | `RuntimeCorrespondence` (verified by the build and the registry's proof list) | accurate |
| The presentation round trip is exact; the runtime round trip is `RuntimeReadoutEquivalent`; no rich equality | `presentation_roundtrip_readout_exact`, `runtimeReadoutCorrespondence`; R7 | accurate |
| `effectiveCorrespondence` six blocks; "conclusion not assumed by the constructor" | section 3, row 7; M9 | accurate |
| Limit futures and common-runtime numerical futures are numerical only, never exact `FutureEquivalent` | `NumericalFutureEquivalent` docstring and definition | accurate |
| External carrier: no quotients, no choice; history is not reconstructed | `EffectiveCauchyReal`; axiom checks | accurate |
| `Real` is closed syntactically, but `certified` is open relative to its received contract | `inductive Real`, `CertifiedService` | accurate (explicit caveat in both languages) |
| Operations run from current archives first, readout afterwards; inverse is partial under `Apartness` | R1, `inverse`, `ReciprocalDomain` | accurate |
| Order is not made globally decidable; reflection runs fresh comparisons | `reflectPresentationOrder`; no `Decidable` instance | accurate |
| Density and bounds are executed finite witnesses, not order completeness | `produceDensity`, `produceNaturalBound` | accurate |
| Native limit: current bank → diagonal → grouping consumes the same Step → installs → continues the journal; only the visited entry is replaced; the live side retains the installed code and does not re-run the rich production | R2, R13, `nativeLiveStep` | accurate. The canonical text does not say that live kernels run from their projected *initial* memory on every request; the Lean module docstring does (see section 9). |
| Rich archive constructors are private; seeds cannot prescribe last code, installed target or history | M11 (rejected); M11′ (meta-level bypass) | accurate at the level of source syntax (see section 9) |
| The installed field is observation memory, not an input to the next rich computation | M13 | accurate |
| `nativeUnique`: one term Step per query from the current bank, passed to both laws, continues bank and archives; `toEffectiveFamily`/`realizedFamily`/`asExecutedCandidate` do not constitute it | R3, R6, M12 | accurate |
| Same-index pure replay is propositionally equal; "sharing" means binding one datum | M4b | accurate and stated in both languages |
| `LimitCorrespondence` contents; a prefabricated target or bare code cannot replace Steps | M4a, M5a–c | accurate |
| Gödel: same perimeter at H1; presentation received; Gödel computes no approximation | section 3, row 8; M10 | accurate. "These constructions" refers to the presentation/runtime layer. The generic package also instantiates there (`haTerminal`), but the repository does not state or test that instantiation. |
| Non-conclusions: not all classical reals, not least-upper-bound completeness, no identification of same-readout objects, `NativeCandidate` law received, `certified` open, memory minimality relative to the contract, no physical cost bound, no AC/CH/originality | — | accurate, same quantifiers in both languages |

---

## 7. What is proved, what is only tested, what is only documented

- **Proved in Lean** (kernel-checked, no axioms):
  - every declaration in the `AXIOM_AUDIT` blocks, including `effectiveCorrespondence`, `nativeCompleteness`, `nativeUnique`, `mediateNative`, `produceNativeLimit`, the operation, relation, density and bound producers, and the Gödel `realizePresentation`/`realizeCarrier`;
  - the reconstructions R1–R3, R7 and R13, and the inequality and data-flow facts in section 4.
- **Tested only:**
  - "exactly one execution and sharing" at the compiled level: the multiplicity, provenance and route checks in the 16 code-generation scripts;
  - privacy and type obstructions: the 189 expected-failure fixtures and my mutations;
  - the absence of the old route from `nativeUnique`'s compiled body: a partly name-based gate.

  None of these is a theorem about all possible implementations.
- **Documented only:**
  - the interpretation of the "primitive/constitutive" ordering;
  - the SAT-runtime memory discipline beyond what `Service.separates` and the specific `next`/`liveStep` definitions show;
  - the claim that kernel callbacks carry no hidden captures. This is stated as *not* certified.

---

## 8. Limitations, especially effective scope versus all classical reals

- **Scope.** The result covers only effective dyadic presentations, effective Cauchy carriers and families with *received* executable approximations, moduli and Cauchy laws. It does not cover every classical real. It gives no least-upper-bound or Dedekind completeness, no global decidability of order or equality, and no AC, CH, cardinality result, physical memory or cost bound, or originality claim.
- **Received contracts.**
  - `NativeCandidate.converges` is a generic received law; it is derived only for the authoritative candidate and the test candidates.
  - `certified` admits any service meeting its coherence and uniformity contract.
  - `NativeCauchyFamily.kernelExact` and `cauchy` are received inputs; `ofTerms` derives `kernelExact`.
- **Determinism.** Re-evaluating at the same indices cannot be told apart at the type level (M4b). Historical identity comes from position in the trace and continued archives.
- **Privacy.** `private` constructors block ordinary literals and record updates, but not meta-level elaboration of the mangled constant (M11′).
- **Native grouping.** The grouping in the native limit is a one-source normalization: the target code is the diagonal term's code.
- **Gödel layer.** The Gödel coupling is made at the `RuntimeReal` layer. The structural package is generic in `P` and instantiates on the HA perimeter, but the repository neither states nor tests that instantiation.

---

## 9. Corrections suggested (not applied)

1. **Verifier at the evidence commit.** `scripts/verify.sh` cannot pass on the exact scientific commit, because `source_sha256` and `evidence_revision` are necessarily stale there. Either document that the static registry check must be run on the closure commit, or add a mode that checks only fingerprint consistency at the evidence commit. The user should validate `7a66ea6` (or its successor) separately, as the brief requires.
2. **Meta-level privacy bypass.** State in the FR/EN "Rich archive constructors are private" paragraph that privacy is an elaboration-level boundary which meta-programs can bypass. Optionally, add `elab`/`_private` to the forbidden-token scan for production modules.
3. **Live kernel memory.** Say explicitly in the canonical native-limit paragraph that the live kernel runs from its projected initial memory on each request, which the `kernelExact` uniformity contract justifies. Today only the module docstring says so.
4. **Empty audit block.** Fill the empty `AXIOM_AUDIT` block in `Tests/RelationalRealEffectiveCorrespondence.lean`, or document that test modules may leave it empty.
5. **Gödel instantiation (optional).** Add an explicit instantiation of `effectiveCorrespondence` at `godelPerimetralPresentation execution` / H1 if the registry wording "partage le même runtime" is meant to cover the structural package and not only the `RuntimeReal` layer.
