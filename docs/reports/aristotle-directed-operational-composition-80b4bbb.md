# Rapport indépendant Aristotle — composition opérationnelle dirigée

Ce fichier conserve le rapport intégral retourné par Aristotle pour l’audit v5.
La présente introduction est une métadonnée d’intégration du dépôt et ne fait
pas partie du rapport original reproduit ci-dessous.

- Projet Aristotle : `266faf4b-1e98-4f58-aab1-d6f21dd4f5db`
- Tâche d’audit : `13a251cd-6549-4df6-a2be-e532bec79fe9`
- Tâche de récupération verbatim : `e7bbfec1-f4c6-42e7-a652-fefe206b135d`
- Révision finale auditée : `80b4bbb9220c0a002df5d8f9d6dcbe7e990a7fce`
- Arbre audité : `7e55f3f2620524d07f7dc274f1465a3b32483072`
- Audited claim evidence revision (Gödel): `360fa13ef5035c51c9ff2b00f0e3ec5fa38161a6`
- Audited claim evidence revision (Tarski): `31748dcf7b6879a345c2b0b8c28b4a382a816984`
- Audited claim evidence revision (directed composition): `31748dcf7b6879a345c2b0b8c28b4a382a816984`
- SHA-256 du rapport Aristotle original : `b92482c3bac0dc81fb679d60a4147b12c4fdc5367ce136fe2493a62b263fa2ee`
- Taille du rapport original : `28850` octets

Le service a marqué la tâche `COMPLETE_WITH_ERRORS` uniquement après le rejet
HTTP 413 d’un push optionnel du projet d’audit volumineux. Le rapport classe
explicitement cette erreur comme une limite de livraison sans effet sur son
verdict scientifique `VALIDATED`.

## Rapport original reproduit intégralement
# Independent audit report — directed operational composition

Audit label: `directed-operational-composition-80b4bbb-full-audit-20261019-v5`

Verdict: VALIDATED

All seven criteria below are PASS. This audit was rebuilt from the uploaded inputs only. No earlier verdict was inherited. The checkout was never modified. Every scratch file, tool and log was kept outside it.

## 1. Immutable target, ancestry, archives, clean state, runtimes

| Item | Expected | Observed |
|---|---|---|
| HEAD | `80b4bbb9220c0a002df5d8f9d6dcbe7e990a7fce` | same |
| HEAD^{tree} | `7e55f3f2620524d07f7dc274f1465a3b32483072` | same |
| HEAD^ | `360fa13ef5035c51c9ff2b00f0e3ec5fa38161a6` | same |
| bundle ref | `codex/tarski-exact-separation` | `refs/heads/codex/tarski-exact-separation` at 80b4bbb, "complete history", sha1 |
| `git bundle verify` | okay | okay (exit 0) |
| ancestors | dd8d45a, 360fa13, abf6e2e | all three are ancestors (`merge-base --is-ancestor` 0) |
| shallow | no | `false`, 159 commits |
| `git status --porcelain --untracked-files=all` | empty | 0 lines (before and after all work) |
| `git diff --check` | 0 | 0 |
| `git fsck --full` | 0 | 0 |
| source archive vs checkout | byte-identical | 522 tracked files, all identical, no extra or missing file |
| manifest `sourceInputs`, `criticalSources` (59), `localPreflight` (8 logs) | sizes and SHA-256 | all OK |
| `runtimeInputs` | 7 Lean parts + 1 PowerShell | 7 parts OK, aggregate `890afd18…` with 570405234 bytes OK, `powershell-7.6.7-linux-x64.tar.gz` 75913191 bytes `6896f9e3…` OK |
| Lean | 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)` |
| PowerShell | 7.6.7 | `7.6.7` (uploaded binary) |

The build used only the reassembled uploaded toolchain, with `ELAN_HOME`, `LEAN_PATH` and `LEAN_SYSROOT` unset. It rebuilt from source (367 jobs) without any uploaded `.olean`. Logs: `logs/00-manifest-inputs.log`, `logs/01-git-identity.log`, `logs/02-archive-compare.log`.

## 2. Verdict

Verdict: VALIDATED

## 3. The seven acceptance criteria

| # | Criterion | Result | Evidence |
|---|---|---|---|
| 1 | Constitutive provenance and fixed contracts | PASS | The upper layers are unchanged: the target diff touches no file of `SegmentedResidualRole`, `AbstractSegmentedTurning` or `StrongPerimetralTurning` outside the four modified modules listed in section 11. The finite-separation API (`ExactSeparation.lean`) is unchanged. Gödel: one `ExecutedGodelProduction` indexes the master resource and H1, and both sources store the same values. `close` is searched, authorized and decomposed into two `ExecutedStep`, which give two `ExecutedRun`. The contract `godelClosureContract` is fixed before the closure. Tarski: one `ExecutedTarskiProduction`, and both sources come from `tarskiInitialize`. Positive instance: `positiveDirectedSourceAccepted := variedLeftSource role` and `positiveDirectedTargetAccepted := leftSource role` are `AcceptedRoleSource role` values for one `role : RelationalConstitutiveRoleStage run`. `positiveDirectedAcceptedSources_ne` (line 23) comes before the runtime types (line 27 onward) and depends on `three_sources_distinct`. The produced bit is `roleRead role run.selected (positiveDirectedAcceptedSource role side)`, so `run.selected` is a resource of the master run and not a newly prescribed output (S15). |
| 2 | Generic B1 and B2 kernels and wrappers | PASS | `DirectedIncompatibility.lean` imports only `Init`. `rejectDirectedTransport transport sourceWitness rejectTarget := rejectTarget (transport sourceWitness)`, closure 2 constants. `rejectBilateralTransport leftToRight rightToLeft certificate` (a tactic block containing only `let` and `exact`): `rejectRight := fun right => certificate.forward (rightToLeft right) right`, then `left := certificate.backward rejectRight`, then `rejectRight (leftToRight left)`. Closure 6 constants. `BilateralNegationCertificate` has exactly the two fields `forward : P → Q → Empty` and `backward : (Q → Empty) → P`. The wrappers in `DirectedObstruction.lean` take `ExecutedOperationalGrouping` and get their transports only from `grouping.directedReadout` and `grouping.reverseDirectedReadout` (walker: closures contain `directedReadout`, `projectedTerminalsEqual`, `DirectedTerminalReadoutPreservation.transport`, `terminal_eq_run`). S01-S04 rebuild them. S05 shows that raw memory equality is rejected. S06 shows that one preservation cannot become a correspondence. Universes were checked in S01-S04 with an event in `Type (w+1)` and observations in `Type w`. |
| 3 | Concrete Gödel adapter and order of the obstruction | PASS | `toOperational` copies `next`, `event`, `Allow`, `decision`, `project` and the laws, including `event_exact`, and does not include `read`. S07 rebuilds it field by field. S07b fails on `read_exact` with "Invalid field". `toExecutedOperationalGrouping` reuses `leftRun`, `rightRun`, both event lists, the terminals and `terminalCollision`. Only `trace := ⟨.close, []⟩` is new. S08 proves by `rfl` that both runs, both event lists, the collision and the trace list are reused. Order: grouping, then adapter, then a preservation parameter, then `godelComputedGroupingToProducedCompleteness : Truth(G) → Proof(G)`, then `rejectGodelComputedGroupingToEmpty`, which calls `rejectDirectedTransport` with `trueWitness` and `unprovable` of the same `execution.witness`. The walker finds neither witness projection in the positive closure and finds both in the rejection (S09-S10). HA: the four declarations are separate and add no arithmetic hypothesis (S11). The old equality path (`godelExecutedGroupingToEndpointEquality`) and the separator path (`godelTerminalSeparator`) are present and distinct (S23). |
| 4 | Tarski B2 specialization and partial directions | PASS | `toBilateralNegationCertificate := ⟨diagonalForward, diagonalBackward⟩` is fieldwise (S12, rfl). `Diagonal.lean` imports only `Readout` and `DirectedIncompatibility`, not the wrapper. The body of `tarskiExactClosureRejected` is `let adequacy := tarskiExecutedGroupingToLocalAdequacy …` and then `rejectBilateralTransport adequacy.valueToCandidate adequacy.candidateToValue certification.toBilateralNegationCertificate`. The walker shows that `tarskiExecutedGroupingToLocalAdequacy` contains no `TarskiDiagonalCertification` (S13). Each one-way consequence uses only one of `directedReadout` and `reverseDirectedReadout` and no rejection kernel. Models A and B (S14) show that each direction alone is non-contradictory. The direct semantic rejection and `tarskiTerminalSeparator` stay distinct. |
| 5 | Complete positive non-diagonal composition | PASS | All fifteen obligations hold (section 4, S15-S21). `close` changes the phase (`positiveDirectedCloseChangesPhase`). Terminal `Allow` is `Empty`. `next` and the memory transition are total. `event_exact` holds while events expose the side. The module imports neither diagonal branch nor either incompatibility module. W2 finds no constant that concludes `Empty` or `False`. `False.elim` appears only inside `≠` proofs and in the `decision` cases on empty authorizations. |
| 6 | Constructivity, dependencies, gates, non-regression | PASS | All 8 mandatory commands exit 0. 57 negative fixtures give their registered first and only diagnostics. The import boundaries and stratification pass. All five generated-code checks pass. `ALL_CONSTANTS_OK constants=30649 modules=364 writtenExceptions=0`. In 365 Lean files there is no written `axiom`, `sorry`, `noncomputable`, `Classical`, `propext`, `Quot.sound`, `native_decide` or `unsafe`, and each file has one terminal `AXIOM_AUDIT`. Fresh `#print axioms` on 694 declarations and on 96 scratch declarations: all report no axioms. No public declaration was deleted or weakened (section 11). |
| 7 | Registry, bilingual prose, scope, delivery | PASS | `check-scientific-docs.py --static` accepts every fingerprint at the current tree and at each evidence snapshot. Section 8 checks the 3 touched claims field by field. 419 prose sentences and registry sentences, plus 66 figure labels, are all TRUE (AUDIT_SENTENCE_TABLES.md). Every disputed formulation listed in the request was rechecked against the bodies (section 8.2). Both SVGs are well-formed, contain no semicolon and show no overflow (section 9). |

## 4. The 24 reconstructions (scratch Lean files outside the checkout, compiled with `lake env lean`)

| # | Reconstruction | File / declarations | Result | Axioms |
|---|---|---|---|---|
| 1 | B1 directly | S01_S04_generic: `s01_B1`, `s01_B1_matches` | success, definitional match with the source | none |
| 2 | B2 in order, refutation then witness then Empty | `s02_B2`, `s02_B2_matches` | success | none |
| 3 | executed B1 wrapper from `directedReadout` | `s03_transport`, `s03_transport_is_directedReadout`, `s03_wrapperB1`, `s03_matches` | success | none |
| 4 | executed B2 wrapper from both transports | `s04_wrapperB2`, `s04_matches` | success | none |
| 5 | wrapper with raw terminal-memory equality | S05_fail_raw_memory | intended failure, exactly 1 error: `Application type mismatch` expecting `ExecutedOperationalGrouping` | n/a |
| 6 | one preservation becomes a correspondence | S06_fail_one_direction, plus S06b model | intended failure, exactly 1 error: `Fields missing: leftBackward, rightForward`. S06b: a model with a preservation and a refutable correspondence (`modelNoCorrespondence`) | none (S06b) |
| 7 | Gödel operational adapter without readout law | S07_S11_godel `s07_toOperational`, `s07_matches`, plus S07b | success. S07b intended failure, 1 error: `Invalid field read_exact` | none |
| 8 | Gödel grouping adapter, reuse by rfl | `s08_toExecuted`, `s08_matches`, `s08_leftRun_reused`, `s08_rightRun_reused`, `s08_leftEvents_reused`, `s08_rightEvents_reused`, `s08_collision_reused`, `s08_trace_list_reused` | success | none |
| 9 | concrete Gödel positive bridge without witnesses | `s09_bridge`, `s09_matches` | success, and no witness in the closure | none |
| 10 | witnesses added afterwards, rejection | `s10_reject`, `s10_matches` | success | none |
| 11 | four HA Gödel declarations | `HA.s11_realization`, `s11_grouping`, `s11_bridge`, `s11_reject`, plus 4 `_matches` | success | none |
| 12 | Tarski certificate adapter | S12_S14_tarski `s12_adapter`, `s12_matches` | success | none |
| 13 | local adequacy before certification, then B2 | `s13_adequacy`, `s13_reject`, `s13_adequacy_matches`, `s13_reject_matches` | success | none |
| 14 | each Tarski direction alone is non-contradictory | `TarskiModels.modelA_*`, `modelB_*` (P empty with Q inhabited, and P inhabited with Q empty, each with a valid certificate and one direction) | success | none |
| 15 | two accepted sources and inequality before the runtime | S15_S19_positive `s15_source`, `s15_target`, `s15_ne`, `s15_matches_*`, plus the concrete closed instance from `publicRelationalConstitutiveRoles` (`PositiveConcrete.*`) | success | none |
| 16 | two nonempty close runs, distinct traces | `s16_sourceRun`, `s16_targetRun`, `s16_traces_ne`, `s16_close_not_identity`, `s16_terminal_unauthorized` | success | none |
| 17 | produced-bit equality through the three links | `s17_bits`, `s17_matches` (`same_sources_other_resource_agree` → `produceRoleSignature_exact.mp` → `.read`, without simplifying source assignments) | success | none |
| 18 | terminal collision and grouping | `s18_collision`, `s18_grouping` | success | none |
| 19 | encode/decode factorizations, transport, target witness | `s19_preservation`, `s19_transport`, `s19_witness`, `s19_exact`, `s19_matches_transport` | success | none |
| 20 | source equality inferred from memory collision | S20_fail_identify_sources | intended failure, exactly 1 error: `Type mismatch` | n/a |
| 21 | positive dependency on diagonal or incompatibility modules | S21_imports.py plus W2 | 62 reachable local modules, 0 forbidden. No constant concludes Empty or False | n/a |
| 22 | finite separator on a non-diagonal pair | S06b `s22_separator`, `s22_every_exact_separates`, `s22_same_at_selected` | success, and uses neither B1 nor B2 | none |
| 23 | old Gödel equality path and old Tarski one-way paths | `s23_oldEquality`, `s23_oldReject`, `s23_exactSeparates`, `s23_oneWayVC`, `s23_oneWayCV`, `s23_global`, `s23_separator` | success, same types as in the baseline | none |
| 24 | unsupported converse or quotient | S06b `blind_future_equivalent`, `converse_fails` (refutes "same futures → same memory" for every exact realization), plus S24_fail_converse | countermodel proved. S24 intended failure, exactly 1 error: `Application type mismatch` | none |

Totals: 96 successful scratch declarations, each audited by `#print axioms`, and all report "does not depend on any axioms". 5 intended failures, each with exactly the intended first error and no other error.

## 5. Mandatory commands

| # | Command | Exit | Log | Key output |
|---|---|---|---|---|
| 1 | `python3 scripts/check-scientific-docs.py --self-test` | 0 | `logs/cmd1-docs-self-test.log` | `SCIENTIFIC_DOCS_SELF_TEST_OK` |
| 2 | `python3 scripts/check-scientific-docs.py --static` | 0 | `logs/cmd2-docs-static.log` | `SCIENTIFIC_DOCS_STATIC_OK claims=22 declarations=224` (matches the preflight values) |
| 3 | `lake build` | 0 | `logs/cmd3-lake-build.log` | `Build completed successfully (367 jobs)`, `ALL_CONSTANTS_OK constants=30649 modules=364 generatedExceptions=474 writtenExceptions=0`, no warning |
| 4 | `python3 scripts/check-scientific-docs.py --lean` | 0 | `logs/cmd4-docs-lean.log` | `surface=public declarations=166`, `surface=test declarations=58` |
| 5 | `bash scripts/verify.sh` | 0 | `logs/cmd5-verify-sh.log` | 57 expected failures exact, 365 Lean files clean |
| 6 | `pwsh -NoProfile -File scripts/verify.ps1` | 0 | `logs/cmd6-verify-ps1.log` | same results, from a separate run with the uploaded pwsh 7.6.7 |
| 7 | `git diff --check` | 0 | `logs/cmd7-git-diff-check.log` | empty |
| 8 | `git status --short --untracked-files=all` | 0 | `logs/cmd8-git-status.log` | empty |

The 474 `generatedExceptions` are compiler-generated auxiliary constants (`match`/`eq`/`sizeOf` lemmas) that the gate classifies and accepts. The build reports `writtenExceptions=0`. Each audited declaration prints "does not depend on any axioms".

## 6. Transitive type-and-value dependency tables (walker `scratch/W_dependencies.lean`)

The walker traverses `ConstantInfo.type` and `value?` (opaque included), inductive constructors, recursor `all` and `Expr.proj` projection functions. Full table: `scratch/W_dependencies.table.txt`. In the table below, a sentinel marked "present" is in the closure and one marked "absent" is not.

| Root | Closure | Present | Absent |
|---|---|---|---|
| `rejectDirectedTransport` | 2 | itself | everything else |
| `rejectBilateralTransport` | 6 | `BilateralNegationCertificate` | any operational or diagonal constant |
| `ExecutedOperationalGrouping.rejectDirectedEndpointIncompatibility` | 83 | `rejectDirectedTransport`, `directedReadout`, `projectedTerminalsEqual`, `transport`, `next_exact`, `terminal_eq_run` | `reverseDirectedReadout`, any diagonal constant |
| `…rejectBilateralEndpointIncompatibility` | 89 | `rejectBilateralTransport`, both readouts | any diagonal constant |
| `GodelOperationalRealizationWithoutRead.toOperational` | 233 | `GodelOperationalRealizationWithoutRead.event_exact` (copied field), `certifyExecutedGodelWitness` and `fixedPoint_unprovable` (received production type) | `trueWitness`, `unprovable`, `read_exact` |
| `godelComputedGroupingToProducedCompleteness` | 450 | adapter, grouping, search/authorize/decompose, `directedReadout`, `read_run` | `ExecutedGodelWitness.trueWitness`, `.unprovable`, `OperationalRealization.event_exact`, `ExactRealization.read_exact`, `FutureEquivalent` |
| `rejectGodelComputedGroupingToEmpty` | 454 | the above, plus `rejectDirectedTransport`, `trueWitness`, `unprovable` | `read_exact` |
| HA `heytingArithmeticComputedGroupingToProducedCompleteness` | 5200 | as for the generic Gödel root | `trueWitness`, `unprovable` |
| HA `heytingArithmeticRejectsDirectedTerminalPreservation` | 5204 | the above, plus both witness projections and B1 | — |
| `TarskiDiagonalCertification.toBilateralNegationCertificate` | 83 | both certification fields, `BilateralNegationCertificate` | any operational constant |
| `tarskiExecutedGroupingToLocalAdequacy` | 377 | both readouts | `TarskiDiagonalCertification` |
| `tarskiExactClosureRejected` | 391 | `rejectBilateralTransport`, the adapter, local adequacy | `rejectTarskiLocalAdequacy` |
| `tarskiValueToCandidateClosureConsequences` | 369 | `directedReadout`, certification | `reverseDirectedReadout`, B2, `rejectTarskiLocalAdequacy` |
| `tarskiCandidateToValueClosureConsequences` | 370 | `reverseDirectedReadout`, certification | `directedReadout`, B2 |
| `positiveDirectedProducedBitsEqual` | 844 | `same_sources_other_resource_agree`, `produceRoleSignature_exact`, `FutureEquivalent.read`, `localProduction` | `three_sources_distinct`, `positiveDirectedAcceptedSources_ne` |
| `positiveDirectedTerminalTransport` | 971 | grouping, preservation, encode, decode, `decode_encode`, `directedReadout`, `transport` | B1, B2, every Gödel/Tarski/HA constant, `three_sources_distinct`, `positiveDirectedAcceptedSources_ne` |

## 7. `#print axioms`

`scratch/A_axioms.lean` contains 694 declarations: the 29 mandatory names, every name in the `AXIOM_AUDIT` blocks of the required files, and every proof name in the 3 touched registry claims (64 Gödel, 34 Tarski, 37 directed composition). It also covers the earlier Gödel, Tarski, exact-separation and HA roots. Output `scratch/A_axioms.out`: 694 of 694 lines report "does not depend on any axioms". All 96 scratch declarations also report no axioms.

## 8. Registry and prose

### 8.1 Touched claims

| Claim | evidence_revision | Fingerprint | Anchors | Reviews |
|---|---|---|---|---|
| `GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION` | `360fa13e…`. Only registry fields changed after it | accepted at the current tree and at the snapshot | FR `Portée et statut`, EN `Scope and status` | reader pending, translation pending, independent `not_recorded` |
| `TARSKI_RELATIONAL_OPERATIONAL_CLOSURE_OBSTRUCTION` | `31748dcf…`. Its sources are unchanged from 31748dc to HEAD | accepted | FR and EN anchors | pending / pending / not_recorded |
| `DIRECTED_OPERATIONAL_READOUT_COMPOSITION` | `31748dcf…` | accepted | FR and EN anchors | pending / pending / not_recorded. Consumers are the Gödel and Tarski claims |

No verdict from dd8d45a is carried over: independent review is `not_recorded`. The Gödel registry describes the concrete adapter. Its scope separates the use of the witnesses in the directed rejection from their use in the separator path.

### 8.2 Previously disputed formulations, rechecked against the bodies

| Point | Classification | Evidence |
|---|---|---|
| Directed composition FR/EN on `source`/`target` tags | TRUE | `positiveDirectedAcceptedSource` maps the tags to the accepted sources. `PositiveDirectedSource := side × phase`. The walker shows that the inequality is not consumed by the grouping or the transport. |
| Directed registry transport: "only the type equality `positiveDirectedMemoryRead (grouped b_s) = … (grouped b_t)` induced by collision … no equality between the two terminal readout types" | TRUE | `DirectedTerminalReadoutPreservation.transport` uses `Eq.mp (congrArg memoryRead sameMemory)`. Terminal `read` reduces definitionally, so no other type conversion occurs. |
| Gödel FR/EN constructor paragraph | TRUE | The `godelOperationalClosureOfTerminalCollision` signature takes only the collision after execution and realization. The text contrasts this with arbitrary inhabitants of `OperationalSameRegimeClosureAt`. |
| Gödel FR/EN three conversions | TRUE | `read terminal = Truth(G)`, `read terminal = Proof(G)` and the `memoryRead` equality are all disclosed. No `Truth(G) = Proof(G)` equality. |
| Gödel registry scope and transport three-way distinction | TRUE | Both fields name the local read laws, the internal `memoryRead` equality and the absent `Truth(G) = Proof(G)` equality. |
| Gödel registry `event_exact` | TRUE | The text says the kernel does not depend on it, that it is not projected, and that it appears only as a copied field of the adapted realization. The walker matches: `GodelOperationalRealizationWithoutRead.event_exact` is present and `OperationalRealization.event_exact` is absent. |
| Tarski registry proof field | TRUE | It states `TarskiLocalAdequacy`, then `rejectBilateralTransport` with `toBilateralNegationCertificate`, which matches the body. |
| Tarski transport, three-way distinction | TRUE | The text separates the absent left/right readout-type equality, the read laws `tarskiTerminalRead_value` and `tarskiTerminalRead_candidate`, and the `memoryRead` conversion. |
| Tarski EN pole blindness "makes it possible to construct" | TRUE | It agrees with the FR "permet de construire". The test realization with pole-exposing events keeps `event_exact` and the collision, and its traces are distinct. |
| Gödel FR and EN anchors | TRUE | Both are registered. The passages agree sentence by sentence (tables). |
| Directed limit on totalization regimes | TRUE | The text says "No adapter … is constructed. The form it would need is not established." Grep finds no adapter. |
| Figure footer | TRUE | "operational memory is introduced after constitution, as a projection under contract" |
| Figure Gödel label | TRUE | "without Truth(G) = Proof(G) or reverse transport" |

### 8.3 Wording notes (not defects, all classified TRUE)

1. Gödel FR/EN "fournit seulement ses deux factorisations locales" / "supplies only its two local factorizations" leaves the `memoryRead` family implicit. The family is the type through which both factorizations pass, and the next sentences disclose the `memoryRead` conversion.
2. The Tarski registry phrase "la même collision calculée" is correct per instance. The generic theorem receives any `ExecutedOperationalGrouping` on the same realization.
3. `tarskiObservedExactClosureRejected` still ends with `rejectTarskiLocalAdequacy`, not B2. No text claims that it goes through B2. B2 is used by `tarskiExactClosureRejected` and by everything derived from it (`tarskiExactRealizationClosureRejected`, `tarskiCanonicalOperationalCorrespondenceRejected`, HA wrappers).
4. The `AXIOM_AUDIT` block of `Tests/PositiveDirectedCompositionDependencies.lean` audits only `Nat`. That file declares no constant (one `run_cmd`).

Complete FR/EN sentence tables: `AUDIT_SENTENCE_TABLES.md`. They contain 419 prose and registry sentences and 66 paired figure labels. Classes: TRUE 419 + 66, with 0 TOO STRONG, 0 FALSE and 0 NOT VERIFIED.

## 9. SVG validation

The tasks referenced `docs/figures/godel-tarski-operational-closure.fr.svg` (sha256 `75700e29…`) and `.en.svg` (sha256 `a02b43ba…`). Both are well-formed XML (parsed by ElementTree), 1800×1660. Each contains 66 `<text>`, 32 `<rect>`, 23 `<path>` and 5 arrow markers. FR and EN have identical geometry. No character `;` appears anywhere in either file. Rendering used a PIL rasterizer written for this audit (`scratch/svg_render.py`, PNGs `scratch/svg_fr.png` and `scratch/svg_en.png`). I visually inspected both PNGs. Text overflow was measured against the smallest enclosing box with DejaVu Serif metrics, which are wider than Georgia: 0 problems. Arrows run downward from the core, through the positive constructions and the conditional bridge, to the two branches. The Tarski formulas `Truth(L) ↔ ¬Truth(Cand(⌜L⌝))` use U+231C/U+231D, which DejaVu Serif renders as missing glyphs. This is a renderer font limitation, not a source defect. The target diff changes only two lines per figure: the Gödel label and the footer.

## 10. The thirty anti-shortcut answers

| # | Answer | Evidence |
|---|---|---|
| 1 | YES | `DirectedIncompatibility.lean` imports only Init. Closures 2 and 6. |
| 2 | YES | `rejectDirectedTransport : (P → Q) → P → (Q → Empty) → Empty` |
| 3 | YES | B2 calls `rightToLeft` inside `rejectRight` and `leftToRight` on `left`. S02. |
| 4 | YES | `directedReadout := preservation.transport grouping.projectedTerminalsEqual` |
| 5 | YES | S05 and fixture `DirectedWrapperRequiresExecutedGrouping` |
| 6 | YES | S06, S06b and fixture `DirectedPreservationCannotBecomeCorrespondence` |
| 7 | YES | `toOperational` has no read field. S07b. |
| 8 | YES | S08 `rfl` on `leftRun` and `rightRun` |
| 9 | YES | S08 `s08_collision_reused` by `rfl` |
| 10 | YES | `godelComputedGroupingToProducedCompleteness` has no witness in its closure. The rejection applies B1 to it afterwards. |
| 11 | YES | `execution.witness.trueWitness` and `execution.witness.unprovable` |
| 12 | YES | The HA declarations take only `execution`-derived data and the preservation (S11). |
| 13 | YES | `tarskiExecutedGroupingToLocalAdequacy` has no `TarskiDiagonalCertification`. |
| 14 | YES | Models A and B. `rejectBilateralTransport` needs both. |
| 15 | YES | `tarskiValueToCandidateClosureConsequences` and `tarskiCandidateToValueClosureConsequences`, plus the HA versions |
| 16 | YES | `positiveDirectedAcceptedSources_ne` at line 23, before `PositiveDirectedSide` |
| 17 | YES | the same `role`, and `run.selected` |
| 18 | YES | `⟨side,.active⟩ ↦ ⟨side,.terminal⟩`, `positiveDirectedCloseChangesPhase` |
| 19 | YES | `positiveDirectedSourceRun` and `positiveDirectedTargetRun` on `[close]` with an `Allow` witness |
| 20 | YES | events `.active side`, `positiveDirectedEventTracesDistinct`, `terminalCollision` |
| 21 | YES | body of `positiveDirectedProducedBitsEqual`, walker, S17 |
| 22 | YES | `sourceForward` uses encode. `targetBackward` uses decode and `decode_encode`. |
| 23 | YES | `positiveDirectedTerminalTransport := (positiveDirectedGrouping role).directedReadout …` |
| 24 | YES | W2 and S21 |
| 25 | YES | `distinct_memory_of_separator` is unchanged and contains neither B1 nor B2 (S22). |
| 26 | YES | S24 countermodel. No declaration states the converse. |
| 27 | YES | no quotient or minimality declaration, and the prose disclaims them |
| 28 | YES | no adapter to `AbstractSegmentedTurning` regimes |
| 29 | YES | section 11 |
| 30 | YES | section 8 and the sentence tables |

## 11. Non-regression against `dd8d45a73e12140503e665e35dde371d9cf1dad1`

36 files changed (inventory: `logs/diff-inventory-baseline-target.txt`). The Lean diff removes 5 lines in total:

- Two lines in the body of `rejectGodelExecutedOperationalGroupingToEmpty`. The type is unchanged, and the body now calls B1.
- Two lines in the body of `tarskiExactClosureRejected`. The type is unchanged, and the body now goes through local adequacy and then B2.
- One required-name line in `Tests/TarskiOperationalClosureDependencies.lean`, which listed `rejectTarskiLocalAdequacy`. The new list requires the B2 route.

No declaration was deleted or had its signature changed. `SegmentedResidualRole`, `AbstractSegmentedTurning` and the `StrongPerimetralTurning` abstract layers are unchanged. The changes 360fa13 → HEAD are confined to two registry fields. The changes abf6e2e → HEAD cover the Gödel FR/EN constructor and conversion paragraphs and the registry. All earlier Gödel, Tarski, exact-separation and HA theorems still build, are axiom-free (A_axioms), and were rebuilt in S22-S23.

## 12. Limitations relevant to the verdict

- PowerShell 7.6.7 needed `DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1` because the sandbox has no libicu. The gate then ran fully and gave the same results as bash.
- No standard SVG renderer (rsvg, Inkscape, browser, cairosvg) was available, and there was no network access. Rendering used a minimal PIL rasterizer written for this audit, with DejaVu fonts substituted for Georgia. Geometry, text, arrows and overflow were checked. Exact typographic fidelity, gradients and corner radii are approximate.
- Sentence tables pair FR and EN sentences per paragraph automatically. The classifications are mine, based on reading every passage. Three rows are offset where one language splits a sentence differently.
- These verdicts concern the stated scope only: one fixed contract per branch, existence of the positive instance, and conditional rejections.

## Evidence archive

`AUDIT_SCRATCH_EVIDENCE.tar.gz` has sha256 `605e05d8081bc63c315c907619df227e765a6c6ad5ea678a42b638483a353f6a`, 835817 bytes, 61 members (58 files). Absolute sandbox paths in logs were replaced by relative paths. It holds every scratch source and output, the walker sources and outputs, the SVG renderer and PNGs, the sentence-table generator, all command logs, and the diff inventories and patches.

