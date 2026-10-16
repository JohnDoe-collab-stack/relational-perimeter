# Independent adversarial audit — `GODEL_INTERNAL_CLOSURE_OBSTRUCTION`

Auditor: Aristotle (Harmonic). Audit date: 2026-10-15.
Scope: the exact target commit `a020dc3267c0670b1316b2b2f8d5b3259ab40d91` only.
This report changes no production source, test, canonical document or registry
entry. All disposable clients and logs are in `audit-probes/` (outside the Lake
globs). The registry status `independent: not_recorded` is not modified.

**Primary verdict: `EXACT FORMAL TARGET ESTABLISHED`** (conditional scope stated in §14; qualifications in §13).

---

## 1. Target identity, remote status, bundle history, package integrity

| Item | Expected | Observed | Status |
|---|---|---|---|
| Bundle SHA-256 | `e7752ecb…dfc7d7` | `e7752ecb9d865609f90d224da4b766869c2d770a573b76139e76ffc145dfc7d7` | ✔ |
| `git bundle verify` | complete history | "The bundle records a complete history", sha1 | ✔ |
| Bundle head | `refs/heads/work/godel-false-temoin-interne` | `a020dc3267c0670b1316b2b2f8d5b3259ab40d91` | ✔ |
| Commit | `a020dc32…` | `a020dc3267c0670b1316b2b2f8d5b3259ab40d91` | ✔ |
| Tree | `6319175b…` | `6319175b6973a592af8d5c21b618e8400a0256cd` | ✔ |
| Parent | `31c9f655…` | `31c9f6559ef9b56eb91407ff6cd741a9aaabbc1f` | ✔ |
| History length | — | 128 commits; `git fsck --full` clean | ✔ |
| `origin/main` comparison `f13930ce…` | ancestor | present, is an ancestor of the target | ✔ |
| Four foundation files Git-blob identical to `f13930ce…` | identical | `StrongPerimetralTurning.lean` `ff688a80…`, `AbstractSegmentedTurning.lean` `498740b5…`, `SegmentedResidualRole.lean` `e7777100…`, `ExactTypeTransport.lean` `98c6df03…` — same blob on both sides | ✔ |
| Evidence revision `31c9f655…` → target diff | docs only | only `docs/scientific-claims.json` (evidence revision + one anchor hash) | ✔ |
| `ENONCE_FORMEL_STABLE_GODEL.md` SHA-256 | `1f3aad0a…6e41ed` | identical (working file and Git blob) | ✔ |
| `Conclusion formelle` anchor | `4187627b…0d49f` | reproduced independently (UTF-8, LF, body of the section, stripped) | ✔ |
| Registry source fingerprint `47d3f338…` | — | accepted by `check-scientific-docs.py --static` (STALE_SOURCE / STALE_SNAPSHOT checks pass) | ✔ |
| Toolchain | `leanprover/lean4:v4.33.1` | Lean 4.33.1, commit `819816b2e0a3`, x86_64 Linux | ✔ |
| Remote tip | `a020dc32…` | **not checked**: `git ls-remote` → "Connection reset by peer" (no network) | environment limitation |

Package manifest (436 entries): 435 files match size and SHA-256. One mismatch:
`.gitignore` (manifest 46 bytes; delivered file 140 bytes, with extra archive
patterns appended by the upload environment). The tracked blob of `.gitignore`
in the bundle is the 41-byte LF original (46 bytes after CRLF conversion); the
file is not scientific content. The delivered snapshot is a CRLF (Windows)
checkout; after CR removal every tracked file except `.gitignore` is byte-identical
to its Git blob. **All Lean work in this audit was done on two fresh clones of
the bundle at the exact commit** (LF, unmodified), not on the delivered snapshot.

Every mathematical conclusion below is bound to commit `a020dc32…`.

## 2. Plain-language reconstruction of the exact claim

Fix any system `S` satisfying the generic interface
`EffectivelyPresentedSoundGodelSystem` (unary formulas and sentences with
injective numeric codes, a substitution, a diagonalization operator with a
*checked* diagonal equivalence certificate, a Boolean proof checker, a Boolean
equivalence checker, a truth predicate valued in `Type`, soundness of checked
proofs, truth-transport along checked equivalences, and an unprovability formula
representing "no checked proof" in both directions).

1. **Production.** Running diagonalization, then self-application, then
   certification produces one sentence `G` (propositionally equal to
   `godelSentence S.toGodelSyntax S.unprovabilityFormula`), the exact checked
   fixed point `ProvableIff G (substitute U (quote G))`, a truth witness of `G`
   and a function `Proof G → Empty`, all stored in one witness record.
2. **Affirmative constitution.** That witness record becomes the difference and
   provenance of a circular presentation `P` whose endpoints are literally the
   types `Truth G` and `Proof G`; the framework then constructs, with no
   admission hypothesis, an exact realization of the whole and a strict one-step
   continuation `H` whose boundary source resource is `.continued E.witness`.
3. **Rejected hypothesis.** `Admission(E)` = a circular refinement of `P` by
   `H` together with a positive-continuation witness for its extension. From one
   such admission, the refinement's `realizesFinal` applied to that witness
   yields the bilateral attempt; either totalization of `P` is projected,
   turned into a contraction kernel, which yields `Truth G = Proof G` and by
   transport `Truth G → Proof G`. Applied to the already produced truth of `G`,
   then to the produced unprovability, this yields `Empty`, and only then `False`.
4. **Retention.** One dependent record keeps the produced data, the whole, the
   continuation, occurrences, provenance and both rejections simultaneously.
5. **Instance.** Intuitionistic HA closes the interface; the generic result is
   instantiated for it.

## 3. Declaration-by-declaration table

F = formation (indices/type), X = execution (data produced/projected/read),
Pr = proof consumption, T = transport. "✔" = verified by reading the full body
and by probe.

| Declaration (file:line) | F | X | Pr | T | Verdict |
|---|---|---|---|---|---|
| `EffectivelyPresentedSoundGodelSystem` (Diagonal.lean:427) | interface: types, codes, Boolean checkers, `Truth : Sentence → Type`, contracts | — | — | — | ✔ conditional contracts; admits degenerate inhabitants (P06) |
| `toGodelSyntax` / `toGodelInterpretation` | `Proof := CheckedSentenceProof encode proofCheck` (Σ code, `PLift (check = true)`) | field renaming | — | exact | ✔ |
| `executeGodelDiagonalProduction` / `executeGodelSentenceProduction` | records indexed by `sourceFormula` with `diagonalExact`, `sentenceExact` | compute `diagonalize U`, then `substitute d (quote d)` | `rfl` | identity of formula and sentence | ✔ |
| `certifyExecutedGodelWitness` (Diagonal.lean:219) | `ExecutedGodelWitness` indexed by production | fixed point from `godelSentence_fixedPoint` after rewriting by `sentenceExact`, `diagonalExact`; `unprovable := fixedPoint_unprovable`; `trueWitness := fixedPointUnprovability_implies_truth … unprovable` | `diagonalizeExact`, `representsUnprovability{Forward,Backward}`, `proofSound`, `provableIffTruth{Forward,Backward}` | same `production.sentence` in all four fields | ✔ |
| `executeGodelProduction` (Diagonal.lean:319) | history `received → diagonalized → sentenceProduced → witnessProduced` | three `extend` steps `.diagonalize`, `.selfApply d`, `.certify p` | — | step indices force witness = certify(selfApply(diagonalize)) | ✔ |
| `ExecutedGodelProduction.occurrences` (Diagonal.lean:365) | occurrences in `execution.history` | case analysis on the actual history | `OccurrenceNext` facts | `witnessIsCertification` by `rfl` after unification | ✔ (three distinct ordered occurrences) |
| `effectiveGodelExecution` (Diagonal.lean:535) | `abbrev` of `executeGodelProduction` | — | — | — | ✔ |
| `godelCircularPresentation` (PerimetralCorrespondence.lean:168) | `Difference := ExecutedGodelWitness`, `Provenance c := PLift (c = witness)`, `Endpoint := Type uP`, `leftEndpoint := Truth G`, `rightEndpoint := Proof G`, `TotalLoop := ExecutedGodelTotalLoop` | builds perimeter produced → certified → continued | `rejectInitialContraction := Empty.elim (witness.unprovable (Eq.mp c witness.trueWitness))` (line 201) — built from produced data, not received | `initialLeftPole`, `initialRightPole` are `rfl` | ✔ |
| `godelInitialProvenance`, `godelProvenance_retains_witness` | provenance only for the exact witness | `PLift.up rfl` / `.down` | — | candidate = witness | ✔ (P04 F3) |
| `executedGodelPerimetralOccurrenceCorrespondence` | links executed occurrences and perimetral positions | reads `execution.occurrences` | `toPrecedes.ne` | `executed.production = witness.production`, initial resource = `.produced executed.production` | ✔; no map between the two occurrence types, none claimed |
| `godelAffirmativeConstitution` (PerimetralCorrespondence.lean:508) | closed term, no admission argument | `perimeterRealization P`, `oneStepFaithfullyLabelledExtension P`, `oneStepAfterPerimeter_positiveContinuation P`, `oneStepAfterPerimeterStrict P` | `old_new_occurrences_disjoint`, `oldOccurrence_injective` | source resource `.continued E.witness`, source difference = witness, provenance at witness, target `.beyond .first` | ✔ |
| `GodelPositiveSameRegimeAdmission` (line 568) | `Σ R : CircularRefinement P H, PositiveContinuation R.extension` | — | — | indexed by `P` and `H` | ✔ exact |
| `godelFinalInterpretationOf` | `finalClosureInterpretation (finalBoundaryOccurrence a.1.toLabelled a.2)` | uses both components | — | — | ✔ (`rfl`, P01) |
| `godelBilateralClosureAttemptOf` (line 594) | `BilateralClosureAttemptAt (godelFinalInterpretationOf a)` | `a.1.realizesFinal a.2` | — | — | ✔ (`rfl`, P01; omission probes P04 F5–F8) |
| `godel{Explicit,Implicit}TotalizationOf`, `…KernelOf` | — | project `.explicitTotalization` / `.implicitTotalization`, then `toContractionKernel` | — | — | ✔ (IR: `proj[1]` / `proj[2]` of the attempt, P03) |
| `godelExplicitKernelToProducedCompleteness` (line 649) | input `ExplicitContractionKernel (godelCircularPresentation w)` | runtime: identity on the truth witness (types/proofs erased, P03) | `explicitKernelContractsClosureDifference k` → `.endpointContraction` (reads `reconstructsLeft`, `reconstructsRight`, `initialLeftPole`, `initialRightPole`) | `change` then `Eq.mp` | ✔ no negative field read |
| `godelImplicitKernelToProducedCompleteness` (line 665) | implicit kernel | same | `leftRoundTrip`, `absorbsCoincide`, `rightRoundTrip`, endpoint poles | `Eq.mp` | ✔ |
| `godel{Explicit,Implicit}AdmissionToProducedCompleteness` | — | kernel-of-admission → conversion | — | — | ✔ |
| `rejectGodel{Explicit,Implicit}AdmissionToEmpty` (lines 727, 739) | `Admission(E) → Empty` | `witness.unprovable (conversion admission witness.trueWitness)` | uses produced truth and produced unprovability of the same witness | — | ✔ |
| `rejectGodel{Explicit,Implicit}SameRegimeAdmission` (lines 751, 761) | `Admission(E) → False` | `Empty.elim (…ToEmpty a)` | — | — | ✔ Empty before False |
| `executedGodelPerimetralCorrespondence` (line 828) | dependent record | all fields filled by the declarations above | — | `producedTruth = witness.trueWitness`, etc. (`rfl`, P01) | ✔ |
| `heytingArithmeticEffectiveGodelSystem` (HA Godel.lean:355) | closes interface with `Predicate`, `Sentence`, `haProofCheck`, `haEquivalenceCheck`, `haTruth := PLift models` | — | `internalFixedPoint_derivable`, `haDerivation_sound`, `provHA_spec`, decoder/encoder | — | ✔ no perimetral constant in its closure (P07) |
| `heytingArithmeticGodelPerimetralCorrespondence` (line 387) | instance | `executedGodelPerimetralCorrespondence (effectiveGodelExecution HA)` | — | — | ✔ (`rfl`, P05) |

## 4. Constitutive order and both causal traces

Dependency order established by the terms (not a temporal order):

1. `effectiveGodelExecution S` — closed; produces `E.witness` (sentence, fixed
   point, `trueWitness`, `unprovable`) through the three-step history.
2. `godelCircularPresentation E.witness` — formed from that witness; its
   negative field is *constructed* from `unprovable` and `trueWitness`.
3. `godelAffirmativeConstitution E` — closed term with no admission argument;
   produces `Whole(P)`, the labelled continuation, its positive witness,
   `StrictContinuation(P,H)`, exactness equalities and three distinct occurrences.
4. `Admission(E)` — a later λ-bound hypothesis whose type is indexed by `P`
   and `H`.

Explicit trace (verified as definitional equality to a hand-written
factorization, P01 `explicitEmpty`, `rfl`):

```text
a : Admission(E)
  → a.1.realizesFinal a.2                 : BilateralClosureAttemptAt (godelFinalInterpretationOf a)
  → .explicitTotalization                 : ExplicitTotalization P
  → .toContractionKernel                  : ExplicitContractionKernel P
  → explicitKernelContractsClosureDifference → .endpointContraction : Truth G = Proof G
  → fun t => Eq.mp _ t                    : Truth G → Proof G
  → applied to E.witness.trueWitness       : Proof G
  → E.witness.unprovable                   : Empty
  → Empty.elim                             : False
```

Implicit trace: identical with `.implicitTotalization`,
`ImplicitTotalization.toContractionKernel` (whose `absorbsCoincide` is
`absorbsLeftAsCurrent.trans absorbsRightAsCurrent.symm`) and
`implicitKernelContractsClosureDifference`. Verified by `rfl` (P01 `implicitEmpty`).

`rejectGodel…AdmissionToEmpty` exist before `rejectGodel…SameRegimeAdmission`,
and the latter is literally `Empty.elim` of the former (P01, `rfl`).

## 5. Affirmative data precede and survive the rejection

- Precede: `godelAffirmativeConstitution E : GodelAffirmativeConstitution E`
  type-checks as a closed term (P01). Nothing in it mentions `Admission(E)`.
- Survive: `executedGodelPerimetralCorrespondence E` holds simultaneously
  `producedTruth`, `producedUnprovability`, `positiveWhole`, `strictContinuation`,
  `affirmative` (occurrences, provenance, source resource), `finalInterpretationOf`,
  `sameRegimeAdmissionToBilateralAttempt`, both conversions, both `…ToEmpty`,
  both rejections. P01 `package` repackages all of them; P01 checks by `rfl`
  that the retained truth/unprovability/fixed point are exactly the certified
  witness fields and that the retained whole/continuation are those of the
  affirmative constitution.
- The rejections have type `Admission(E) → False`; no term of `False` is built
  without an admission hypothesis (the whole build reports no axiom).

Precision: `Whole(P)` and `StrictContinuation(P,H)` are *co-retained*; their
inhabitants are not inputs of the rejection path. The admission depends on `P`
and on the history object `H` through its type, not on the certificates
`perimeterRealization P` or `oneStepAfterPerimeterStrict P` (see finding G-7).

## 6. Path verdicts

- **Explicit path: established.** Every step is a projection or a definitional
  composition; the conversion uses only the positive kernel fields and the
  endpoint identities.
- **Implicit path: established.** Symmetric; the implicit kernel's coincidence
  is derived from the totalization's two "absorbed as current" equalities.

## 7. Continuation-dependency verdict

- *Full constitutive path:* `Admission(E)` is indexed by `P` and `H`; the
  attempt is `a.1.realizesFinal a.2`, which consumes the refinement and its
  positive witness. The transitive closure of `rejectGodel…AdmissionToEmpty`
  contains `oneStepAfterPerimeter`, `godelPerimetralContinuation`,
  `generate_after_perimeter`, `PositiveContinuation`, `CircularRefinement`,
  `CircularRefinement.realizesFinal` (P02, "H-CHECK").
- *Terminal subterm:* the closure of `godel{Explicit,Implicit}KernelToProducedCompleteness`
  contains **none** of these (P02). The conversion can be built from bare
  totalizations or bare kernels without any admission (P01
  `fromBareExplicitTotalization`, `fromBareImplicitTotalization`).
- Both facts hold together as the target states. **Verdict: established.**

## 8. Projection / genericity verdict

- Terminal form is generic: P01 builds `kernelToEq`/`eqToKernel`,
  `eqToTotalization`, `implicitKernelToEq`, `eqToImplicitTotalization`
  constructively (no `Empty`/`False` elimination): the explicit kernel (and
  each totalization) of this `P` is interconvertible with `Truth G = Proof G`.
  This is interconvertibility, not an isomorphism (`reconstruct` is not
  determined). P01 also proves `(Truth G → Proof G) → Empty` and
  `(Truth G = Proof G) → Empty`, so all of these types are provably empty.
- Consequence for methodology: any implication between these uninhabited types
  is derivable by ex falso, and P01 shows two such bypass routes from an
  admission (`bypassViaAttachment` through `rejectExplicit`,
  `bypassViaPresentation` through `explicitContractionKernelRejected`). The
  audit therefore judges the *specific terms*. The declared route uses neither (§11).
- Gödel-specific genealogy: the perimetral layer takes from the Gödel side the
  witness record (difference, resource payloads, provenance index), its
  sentence (both endpoints), its `trueWitness` and `unprovable` (collision and
  negative field). The fixed point, diagonal history and occurrences are
  consumed upstream by certification and retained in the correspondence. A
  foreign witness, sentence, provenance or resource cannot be substituted
  without an explicit equality (P04 F1–F4).
- **Verdict:** the target supplies the claimed executed genealogy; the terminal
  contraction is generic, as the target itself states.

## 9. Generic-interface scope and HA instance

- **Generic scope:** P06 constructs `degenerateSystem` (one formula, one
  sentence `()`, checker always `false`, equivalence checker always `true`,
  `Truth := Bool`). It satisfies every contract, and the full correspondence
  instantiates verbatim (axiom-free). The generic theorem is therefore
  conditional on contracts that do not by themselves force arithmetic,
  self-reference or nontrivial provability. The target explicitly disclaims
  more (§3.8, ENONCE §8). Scope result, not a defect.
- **HA instance: established.** The fields are literally `haProofCheck`,
  `haTruth`, `haUnprovabilityPredicate`, `haDiagonalize`, `haProofSound` (`rfl`,
  P05). The checker is the root-history primitive-recursive `proofCheckBit`;
  `decodeAcceptedHistoryProof` rebuilds a typed intuitionistic HA `Derivation`
  from an accepted code line by line (no choice); `haCheckedProofOfDerivation`
  encodes and certifies acceptance. P05 runs encode → decode → standard-model
  soundness on a genuine derivation of `0 = 0` (axiom-free). Soundness is
  `haDerivation_sound` (induction over the derivation, with full induction axiom
  schema in `StandardArithmeticAxiom`). Representation is `provHA_spec`
  (`provHA` = ∃ of the arithmetized graph of `proofCheckBit`). The diagonal
  certificate is an HA derivation, `internalFixedPoint_derivable`, encoded and
  accepted by the same checker. The transitive closure of
  `heytingArithmeticEffectiveGodelSystem` (4782 constants) contains no constant
  from `StrongPerimetralTurning`, `PerimetralCorrespondence`,
  `AbstractSegmentedTurning` or `SegmentedResidualRole`, and from the generic
  Gödel module only the interface type and the two checked-certificate
  abbreviations (P07). The conclusion is not imported as a premise.
  `heytingArithmeticGodelPerimetralCorrespondence` is definitionally the generic
  theorem at HA (P05). See G-5 for the checker's practical executability.

## 10. Adversarial probes

All commands: `lake env lean audit-probes/<file>` from a clean clone of the
exact commit, after `lake build`. Logs are in `audit-probes/logs/`.

| # | Source | Expected | Actual | Interpretation |
|---|---|---|---|---|
| 1 | P01 `package`, `rfl` checks | packaging succeeds | exit 0; axiom-free | all retained data available together |
| 2 | P01 `explicitPathOnly` | conversion via explicit path only | ✔ | explicit path independent of the implicit one |
| 3 | P01 `implicitPathOnly` | via implicit path only | ✔ | symmetric |
| 4 | P01 `explicitEmpty`/`implicitEmpty` + `rfl` vs production | `Empty` before `Empty.elim` | ✔ definitionally equal to the production declarations | order confirmed |
| 5 | P02 (closure analysis), P01 `conversionUnderArbitraryReject` | no negative field read | body constants of kernel→completeness: kernel type, `godelCircularPresentation` (index), endpoint projections, `Eq.mp`, `_proof_1` (= `endpointContraction (explicitKernelContractsClosureDifference k)`). Value closure **not unfolding the index**: only `explicitKernelContractsClosureDifference`, `endpointContraction`. Unfolding the index adds `ExecutedGodelWitness.unprovable`, `trueWitness`, `Empty.elim`, `Empty.rec`. No `rejectInitialContraction` projection, no `PositiveClosureObstruction.rejectsContraction`, no `BilateralClosureAttemptAt.attachment`/`rejectExplicit`, no `ContractedClosureDifference.reject` in any closure. The same body type-checks for a presentation whose `rejectInitialContraction` is an arbitrary hypothesis `r` | negative constants occur only in the index `P`, as the target states. For the whole admission path the closure also contains `rejectInitialContraction`/`positiveClosureObstruction`/`False.elim`, reached through the *type* `FinalClosureInterpretation` (its `targetObstruction` field indexes the attempt's type) and foundation constructions; no projection of them is executed (P02/P03) |
| 5b | P03 compiled IR of verbatim copies | — | attempt = `proj[3]` (`realizesFinal`) of `a.1` applied to `a.2`; kernels = `proj[1]`/`proj[2]` of the attempt; kernel→completeness compiles to the identity on the truth witness; `…ToEmpty` compiles to `witness.unprovable witness.trueWitness` and **does not read the admission** | see G-1: terminal dependence on the admission is propositional (erased equality) |
| 6 | P01 `fromBare…Totalization` | possible from bare totalizations | ✔ | narrower terminal dependency, consistent with §3.5 |
| 6b | P01 `bypassVia…` | additional routes exist | ✔ | foundation obstruction routes exist; not used by the target (G-2) |
| 7 | P01 `kernelToEq`/`eqToKernel`/`eqToTotalization`/`implicitKernelToEq`/`eqToImplicitTotalization` | interconvertible with `Truth G = Proof G` | ✔ constructive both ways | expected structural fact |
| 8 | P04 F9; P01 `completenessIsEmpty` | must fail | F9: "Type mismatch `t : I.Truth …` expected `coding.Proof …`". Also `(Truth G → Proof G) → Empty` is proved, so **no** derivation from affirmative constitution alone can exist | impossibility proved, not just a failed attempt |
| 9 | P04 F1–F4; P06 | foreign substitution blocked | F1: kernel of `godelCircularPresentation w'` rejected (expected `… E.witness`). F2: `I.Truth s` rejected (expected `I.Truth E.witness.production.sentence`). F3: provenance needs `w' = w`. F4: reduces to `.continued E.witness = .continued w'`, unsolved. P06: two distinct `ExecutedGodelWitness` records exist (`witnessRecordsNotUnique`); their sentences are propositionally canonical; foreign provenance is refutable. P01 `executedWitnessCanonical`: every `ExecutedGodelProduction` has exactly the canonical witness | substitution is blocked definitionally and permitted only through an explicit propositional transport. Sentence canonical, records not unique, as claimed |
| 10 | P04 F5–F8 | omissions fail | F5 omit positive: "don't know how to synthesize placeholder for `snd`" and a function type in place of an attempt. F6 omit refinement: `PositiveContinuation r.extension` ≠ admission. F7 omit `realizesFinal`: unsolved goals `ExplicitTotalization P`, `ImplicitTotalization P`. F8 different positive `p'`: attempt at another interpretation, type mismatch | the attempt is pinned to the admission's own refinement and witness |
| 11 | P04 F10; P01 | no cross-history identification | equality of `E.occurrences.certifyOccurrence` with `affirmative.certificationOccurrence`: type mismatch, `History.Occurrence E.history` vs `History.Occurrence (godelPerimetralContinuation E).history`. Within each history, distinctness proved | consistent with the claim |
| 12 | P05 | real checker and decoder | `rfl` identities; encode/decode/soundness on `0 = 0` axiom-free; `#eval haProofCheck 0 0 = false` | ✔; but running the checker on real codes overflows the stack (G-5) |
| 13 | P05, P01, P06 `#print axioms` | axiom-free | all "does not depend on any axioms" | ✔ |
| 14 | P06 | degenerate inhabitant | ✔ builds; generic correspondence applies | scope result (G-3) |
| — | P07 | HA closes interface without perimetral premises | no perimetral constant in closure | ✔ |

No probe succeeded in a way that refutes the exact claim. Probes 5b and 6b
narrow or qualify dependencies (G-1, G-2). Probe 9 shows a stronger
canonicity fact for `ExecutedGodelProduction` than the target states.

## 11. Axiom audit and forbidden mechanisms

- 91 Lean files changed against `f13930ce…` (89 added, 2 modified:
  `RelationalPerimeter.lean`, `Tests/AllConstantsAudit.lean`). Each has exactly
  one `AXIOM_AUDIT_BEGIN/END` block, ending the file.
- 848 `#print axioms` lines in these files. Each is matched one-for-one by a
  "does not depend on any axioms" message in the build log. The whole build log
  contains 0 "depends on axioms" messages and 5378 axiom-free messages.
- The three core files audit every declared constant (32 + 47 + 38).
- `grep -w` over the 91 files finds no `axiom` (outside `#print axioms`),
  `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot.sound`,
  `native_decide`, `unsafe`, `implemented_by`, `partial`, `extern`, `csimp`,
  `bv_decide`, `ofReduceBool`. Kernel `decide` occurs (InternalPRDeterminacy)
  and is not a bypass.
- `scripts/verify.sh` independently runs the same constructivity gate (exit 0).

## 12. Reproduction

Environment: Linux x86_64, Lean 4.33.1 (`819816b2e0a3`) via elan, Python
3.11.14 (`/usr/local/bin/python3`), git 2.47.3. No network.

| Command (clone 1 of the bundle at `a020dc32`) | Exit | Key output | Log SHA-256 |
|---|---|---|---|
| `python3 scripts/check-scientific-docs.py --self-test` | 0 | `SCIENTIFIC_DOCS_SELF_TEST_OK` (7 tests) | `c1f9f238…` |
| `python3 scripts/check-scientific-docs.py --static` | 0 | `SCIENTIFIC_DOCS_STATIC_OK claims=19 declarations=92`; open reviews printed | `65855285…` |
| `lake build` | 0 | `Build completed successfully (338 jobs)` | `3aeca659…` |
| `python3 scripts/check-scientific-docs.py --lean` | 0 | `LEAN_OK surface=public declarations=77`, `surface=test declarations=15` | `9ac47a8c…` |
| `bash scripts/verify.sh` (**separate fresh clone 2**, independent full build) | 0 | 338-job build, 23 expected-failure fixtures exact, "Verified 336 Lean files: build, constructivity, audit blocks, import boundaries, and migration boundaries are clean." | `b95038b5…` |
| `pwsh -NoProfile -File scripts/verify.ps1` | not run | `pwsh` not installed and not installable (no network) | — |

Full logs: `audit-probes/logs/`. The supplied `ARISTOTLE_VERIFY_*.log` files
were checked only against the manifest hashes. They were not used as evidence.
The PowerShell gate is **not independently reproduced**. This is an environment
limitation, not a target failure.

## 13. Findings

| ID | Severity | File / declaration | Finding | Consequence |
|---|---|---|---|---|
| G-1 | Medium (qualification) | `PerimetralCorrespondence.lean:649,665,727,739` | At the compiled (erased) level, the kernel→completeness conversion is the identity on the truth witness, and `rejectGodel…AdmissionToEmpty` compiles to `witness.unprovable witness.trueWitness` without reading the admission (P03). The admission's contribution to the terminal step is the propositional equality `Truth G = Proof G`, which the compiler erases. | The registry's "execution" reading (admission → `realizesFinal` → totalizations) holds for the attempt and kernel extraction, which are executed projections. For the terminal conversion it holds at the level of the kernel proof term. It does not hold as runtime data flow. The claim is unaffected: the target's "proof" judgment is about consumption in the term. |
| G-2 | Low (additional route) | `StrongPerimetralTurning.lean:5956` (`rejectExplicit`), `explicitContractionKernelRejected` | The unchanged foundation already refutes any admission through the attachment obstruction or the presentation's negative field (P01 `bypassVia…`). | The Gödelian route is one of several refutations of the same empty type. It is not the only one, and none is claimed unique. In this `P` the negative field is itself built from `witness.unprovable` and `trueWitness`, so those routes also pass through the Gödel certificates. |
| G-3 | Scope | `Diagonal.lean:427` | The generic interface has a degenerate, non-arithmetic, non-self-referential inhabitant (P06). | The generic theorem's Gödelian content comes from the realization; HA supplies it. This matches the target's own scope statement. |
| G-4 | Info (positive) | `Diagonal.lean:365` | Every `ExecutedGodelProduction` has exactly the canonical witness (P01). `ExecutedGodelWitness` records are not unique (P06). | Consistent with §3.7, and slightly stronger than stated. |
| G-5 | Low | HA `Godel.lean:50`, `Coding.lean:17` (`natDouble`) | `haProofCheck` is total, constructive and compilable, but evaluation on the code of an actual derivation (even `⊢ 0 = 0`), or on `(5, 78)`, aborts with deep recursion / stack overflow in the interpreter, even with `ulimit -s unlimited --tstack=4000000`. Unary recursion over large codes causes this. `haProofCheck 0 0` evaluates to `false`. | "Boolean proof verification" holds as a defined, proved-correct and proved-complete function. Its behaviour enters the proof through lemmas, not through demonstrated runs. No target obligation requires feasible runs. |
| G-6 | Low (test coverage) | `Tests/GodelPerimetralCorrespondenceRegression.lean` | Implicit-path regression coverage stops at kernel extraction. The implicit `…ToEmpty`/`…False` terminals are covered only by the production axiom audit and the correspondence record. | P01 independently covers the implicit terminal. No effect on the claim. |
| G-7 | Low (wording) | `ENONCE_FORMEL_STABLE_GODEL.md` §2 ("L'ordre constitutif démontré") | The demonstrated order is a dependency order: the constitution is admission-free, and the admission type is indexed by `P` and the history `H`. The inhabitants `Whole(P)` and `StrictContinuation(P,H)` are retained alongside the rejection. They are not antecedents consumed by it. | Accurate under the dependency reading that the document itself uses (§4, §7). It should not be read as "the whole certificate is consumed by the rejection". |
| G-8 | Info | `PerimetralCorrespondence.lean:35` | `ExecutedGodelPerimeterResource` constructors accept arbitrary payloads; the index alone does not exclude foreign ones. Exactness comes from the constructed perimeter and the proved equalities (`sourceResourceExact`, `productionResourceExact`). | Probe F4 shows these equalities force the exact witness. |
| G-9 | Env | package | `.gitignore` altered in the delivered snapshot; remote not reachable; PowerShell gate not run. | Not a target defect; all work was rebound to the bundle commit. |

No finding identifies an unmet obligation of the exact target.

## 14. Sub-verdicts and primary verdict

| Sub-claim | Verdict |
|---|---|
| Executed generic Gödel production | Established |
| Identity of produced and consumed sentence and witness | Established (same `E.witness`; sentence propositionally canonical; records not unique, as stated) |
| Affirmative constitution and provenance | Established |
| Occurrence claims within and across the two histories | Established (distinct ordered occurrences in each; correspondence through production/resource/witness; no cross-type identity, none claimed) |
| Same-regime admission to actual bilateral attempt | Established (`a.1.realizesFinal a.2`, `rfl`) |
| Explicit totalization and contraction path | Established |
| Implicit totalization and contraction path | Established |
| Independence from projected negative fields | Established (negative constants only in the index `P` and in type indices of the attempt; never projected; parametricity probe) |
| `Empty` before `False` | Established |
| Retention of positive whole and continuation | Established |
| Generic interface scope | Conditional, admits degenerate realizations (as disclaimed) |
| Concrete HA realization | Established (checker practically non-runnable, G-5) |
| Accuracy of `ENONCE_FORMEL_STABLE_GODEL.md` | Accurate; one wording precision (G-7) and the execution/erasure qualification (G-1) |
| Full constitutive explanatory conclusion | Established as a formal constitutive explanation within the stated conditional scope |

### Primary verdict: **EXACT FORMAL TARGET ESTABLISHED**

**Scope.** For every `S : EffectivelyPresentedSoundGodelSystem`, under exactly
its contracts, Lean (4.33.1, axiom-free, constructive) constructs:

- the executed and certified witness of one canonical `G`;
- the affirmative whole and the strict continuation, admission-free;
- two rejections `Admission(E) → False`, each factoring definitionally through
  the admission's own refinement and witness → `realizesFinal` → bilateral
  attempt → totalization → positive kernel → `Truth G = Proof G` →
  `Truth G → Proof G` → produced truth → produced unprovability → `Empty` →
  `False`;
- one record retaining all of these together.

HA is a concrete, premise-independent realization. The result does not
strengthen incompleteness, does not prove `False` in HA, and gives no uniqueness
of the explanation or of witness records.

**Why this is more than `Truth(G) ∧ ¬Proof(G)`.** The conjunction alone is the
`ExecutedGodelWitness` record. The target additionally constructs and checks
the following:

1. The endpoints of a perimetral presentation are *literally* those two types,
   for the same executed witness, and the provenance admits only that witness.
2. An admission-free whole and continuation exist over that presentation, with
   the continuation's boundary resource `.continued E.witness`.
3. The admission hypothesis cannot be refuted along the declared route without
   passing through `realizesFinal`, a totalization and its contraction kernel.
   Probes F5–F8 show each omission fails. The kernel-to-completeness body reads
   no negative field: its value closure without the index has only the two
   positive contraction constants.
4. The collision uses the previously produced certificates of that same `G`.

The terminal pattern `A, A→B, B→Empty` is generic, and the kernel is
interconvertible with the type equality. The executed genealogy (internal
diagonal production, the same witness, its provenance, the constituted `P` and
`H`, the admission indexed by them, and the realized attempt) is supplied by
the terms. A bare projection does not construct it.

The registry's independent-review status should remain `not_recorded` until
this report is read and integrated in a separately authorized revision.
