# Independent audit of gates 7.1–7.3 (presented dyadic completion) at `ba549cd`

**Final verdict: `AUDIT INCOMPLETE`**

The audit could not obtain the evidence that only the compiler can provide:

- that the kernel accepts the ten new Lean files;
- the output of `#print axioms`;
- the positive tests;
- the diagnostics of the 20 expected-failure fixtures;
- the compiled-code (generated C) check.

The pinned compiler, Lean v4.33.1, was not available offline. The target does not compile
under the Lean v4.28.0 that was available (§5.2). The static, constitutive, documentary and
registry analyses were all carried out. None of them found an essential submitted claim that
is false, circular, bypassed, or obtained by changing scope. The undecided items are listed
in §9.

Throughout this report, the following labels are used:

- **[proved]**: a fact established by a Lean run that was actually executed.
- **[measured]**: the result of a command that was actually executed.
- **[static]**: a reading of the source or a script analysis, without compilation.
- **[interpretation]**: the auditor's judgement.

---

## 0. Transport, identity of the revision, environment

| Item | Result |
|---|---|
| Archive SHA-256 `7aec9a16…e398` | **NOT VERIFIABLE.** The archive file itself was not in the environment; only its extracted contents were present. |
| `PACKAGE_MANIFEST.json` (sha256 `3a9b951a…f09f6b`) | [measured] `relational-perimeter-ba549cd.bundle` is 5,444,199 bytes, sha256 `396bb7c6…14ebd`, which matches the manifest. `ARISTOTLE_RUNTIME_REAL_GATE7_AUDIT.md` is 12,999 bytes, sha256 `cf26a818…c68d6`, which matches the manifest. |
| Clone | [measured] `git clone relational-perimeter-ba549cd.bundle target`, then `git checkout ba549cd03552dd5d0c7f5737305c684bf7d49897`. |
| `git rev-parse HEAD` | [measured] `ba549cd03552dd5d0c7f5737305c684bf7d49897` |
| `git status --porcelain` | [measured] empty, both before and after the audit. The target was never modified, and all experiments ran in separate disposable clones. |
| Bundle heads | [measured] `refs/tags/codex-audit-gate7-ba549cd`. `git fsck --full` exit 0. 153 commits, single root `e42bbe8`. |
| Commits | `8321280` "Prove presented dyadic completion characterization", whose parent is `b3a213e`. `ba549cd` "Clarify ordered completion contract layers" changes two documentation lines, "enrichit une complétion présentée" → "enrichit une structure présentée" (and the English equivalent). |
| Toolchain | [measured] `lean-toolchain = leanprover/lean4:v4.33.1`. `lake-manifest.json` lists `packages: []`. `elan toolchain install leanprover/lean4:v4.33.1` failed with `SSL connect error (Connection reset by peer)`. The only Lean available was v4.28.0. Python 3.11.14 was available. `pwsh` was absent. |

---

## 1. Formation / execution / proof / transport table

[static] Each row is based on a complete reading of the bodies.

| Construction (file:line) | Indexing (types) | Executed operation that constructs the data | What the proof consumes | What the projection or transport preserves and forgets |
|---|---|---|---|---|
| `carrierNativeFamily` (RelationalRealCarrierCompleteness.lean:21) | `CarrierFamily` → `NativeCauchyFamily P baseDepth` | `NativeCauchyFamily.ofTerms` over `ofCarrier P baseDepth (family.terms n)`, with outer modulus `family.modulus` | The current `Step`s `first`/`second` (via `currentReadout`), `ofPresentation_readout`, `family.cauchy` at the inner moduli `(family.terms n).modulus r`, and the monotonicity of each inner modulus (no cofinality) | It preserves the codes of the owned steps. It does not recompute any code independently of the received step. |
| `carrierCompletion` (:113) | `CarrierCompletionResult P baseDepth family` | `let native := nativeCompleteness (carrierNativeFamily …)`, then `toCarrier native.limit` | Convergence: `preserveCarrierLimit (asExecutedCandidate native.candidate)`, rewritten by `native.candidateExact`/`limitExact`, then `returnedCarrierLimitToOriginal`. Uniqueness: `carrierLimitNativeCandidate` (which uses `originalCarrierLimitToReturned`), then `native.uniqueness`, then `equivalentCarrier`, then `carrier_roundtrip`. | The whole native packet is retained in the field `native`. The carrier forgets archives, journals and occurrences. The returned family and the two bridges are **consumed, not stored**. |
| `carrierCompletion_perimeterIndependent` (:121) | Two runs `(P, d)` and `(Q, e)` of the same family | Two productions | The uniqueness of P applied to the convergence of Q | Only an `EffectiveCauchyReal.Equivalent`; no identification of the runtimes. |
| `PresentedDyadicData/Structure` (PresentedDyadicCompletion.lean:18–44) | `Carrier : Type` | None. This is a contract. | — | No field of type `Carrier → EffectiveCauchyReal.Carrier`. `numericalCarrier` is **derived** from the four numerical fields. |
| `PresentedDyadicCompletion.complete` (:69) | `(family : PresentedFamily C) → LimitResult C family` | Supplied by the instance | — | The value, its convergence and its uniqueness. No candidate is received. |
| `carrierCompletionStructure` (:175) | `PresentedDyadicCompletion carrierPresentedCore` | `carrierCompletion P baseDepth (asCarrierFamily family)` | `produced.convergence`, `produced.uniqueness` | **Forgets the native packet** in the `LimitResult` (value, convergence, uniqueness). |
| `canonical{Additive,Negative,Multiplicative}Family` (:186–195) | `PresentedFamily C` | `presentCarrierFamily` applied to `addCarrier`/`negCarrier`/`mulCarrier`, which are numerical presentation-level operations (RelationalRealAddition.lean:753, :810; RelationalRealMultiplicativeLaws.lean:250) | — | Numerical specification only. |
| `carrier{Add,Neg,Mul}Convergence` (CarrierOrderedCompletion.lean:173–198) | `Converges carrierPresentedCore (canonical…) (addCarrier x y)` | `nativeOperationConvergence` over the runtime real `.add (ofCarrier x) (ofCarrier y)` | `add_readout_exact`, `ofPresentation_readout`, `readoutsNear real` | Proof-time realization: a fresh runtime real is built inside the proof (§4.4 Q20). |
| `carrier{Additive,Multiplicative}Laws`, `carrierOrderLaws` (CarrierOrderedFieldLaws.lean:60, 82, 159) | Packets of laws over `carrierPresentedCore` | Runtime laws `add_comm (f a) (f b)` and so on, and `RelationalRealOrderedField.orderedFieldLaws P baseDepth` | `carrierReadoutLaw` = runtime law + `carrier_roundtrip` + `toCarrier_add`/`neg`/`mul` + numerical congruences | Equivalences only. |
| `carrierInverse` (:34) | `CanonicalCarrierDomain x` = `CarrierApartness x canonicalZeroCarrier` | `inverseCarrier x (runtimeCarrierDomain …)`. The domain is transported to the runtime zero by `transportCarrierApartness`. | — | `carrierInverse_perimeterIndependent` is proved by algebraic uniqueness from the two unit laws. It does not compare the domain witnesses. |
| `produceCarrierDensity` (CarrierOrderedCompletion.lean:63) | `CarrierDensityResult P baseDepth x y origin` | `realizeCarrierOrder` (initial archives), then `produceDensity realizedOrigin (Journal.root P baseDepth)` | `packet.targetExact`, `packet.orders`, `carrierReadoutConstant`, `transportCarrierOrder` | It retains `realizedOrigin`, `packet`, `code`, `target` and the orders. `carrierOrderedData.density` projects **only** `⟨code, left, right⟩`. |
| `produceCarrierNaturalBounds` (:98) | `CarrierNaturalBoundResult` | `produceNaturalBound realized initialArchive (Journal.root …)` | `packet.lowerExact`/`upperExact`, `packet.orders` | Projects `⟨lower, upper, lowerOrder, upperOrder⟩`. |
| `carrierDensityReadoutExact` / `carrierNaturalBoundsReadout_perimeterIndependent` (:141, :117) | Exact equality of the **selected codes** for the same `origin` or the same `x` | — | `readout_is_storedAction`, `action.codeExact`, `selectionExact`, `currentReadout` of the retained `pair.left`/`pair.right` and `probe` steps, `responseExact` | Numerical equality of the codes only, never equality of the packets. |
| `comparisonMorphism` (DyadicCompletionCharacterization.lean:48) | `CompletionMorphism Source Target` | `Target.completion.complete (presentCarrierFamily Target.core (numericalCarrier Source.core x))` | Convergence and uniqueness of the target | The map is determined up to `Target.Equivalent`. |
| `preservePresentedLimit` / `mapProducedLimit` (:67, :82) | Convergence toward `diagonalTransportFamily` | — | `convergence.near (p+1)`, `normalizedEquivalentNear` at `p+1` of `morphismNumerical f value`, `Near.compose` | It does not claim that the families are equal. The diagonal forgets the source producers. |
| `orderedMorphismTransports` (DyadicCompletionOrderedCharacterization.lean:176) | `OrderedMorphismTransports Source Target f` for **every** `f` | — | `presentedCarrierEquivalent`, `{add,neg,mul}CarrierCongr`, `equivalentByLimitUniqueness`, `transportCarrierOrder`, `presentedInverseUnique` | Equivalences, and orders transported. The density and bound codes are those of the source. |
| `relativeOrderedCharacterization` (:197) | Carrier completion ↔ **every** `Target : PresentedDyadicOrderedFieldCompletion` | Forward = `comparisonMorphism`; backward = `reverseMorphism` (= `numericalCarrier`) | `fromToTarget`, `toFromTarget`, `mapProducedLimit`, `comparisonUnique` | Round trips are behavioural equivalences only. |

---

## 2. Answers, §4.1 Carrier completion

1. **VERIFIED [static].** `carrierCompletion` (RelationalRealCarrierCompleteness.lean:113–117) takes only `P`, `baseDepth` and `family`. It executes `nativeCompleteness (carrierNativeFamily P baseDepth family)`. `nativeCompleteness` (RelationalRealNativeCauchy.lean:391) produces `limit := nativeLimit family` and `candidate := nativeAuthoritative family`. No limit or candidate is received. Compiled confirmation (multiplicity of the call to `nativeCompleteness` = 1, checked by `check-real-carrier-completion-codegen.py`) is **NOT RUN**.

2. **QUALIFIED [static].** The packet is retained in the field `native : NativeCompleteness (carrierNativeFamily P baseDepth family)`, and `limitExact : limit = toCarrier native.limit` holds by `rfl`. The same `let native` feeds convergence (`nativeCarrierConvergence family native`) and uniqueness (`nativeCarrierUniqueness family native`). Both bridges are connected to that production:
   - convergence goes through `returnedCarrierLimitToOriginal` applied to `preserveCarrierLimit (asExecutedCandidate native.candidate)`;
   - uniqueness goes through `originalCarrierLimitToReturned`, used inside `carrierLimitNativeCandidate`, and then `native.uniqueness`.

   Qualification: the bridges and `carrierReturnedFamily` are consumed but not stored in the result. Also, the type `CarrierCompletionResult` does not pin `convergence`/`uniqueness` to `native`: any proof of the same statement inhabits these fields. Only `limit` is pinned. This is not a defect of the claim, which says the packet is retained, not the bridges.

3. **VERIFIED [static].** Convergence and uniqueness are constructed from the native packet. `carrierCompletion_perimeterIndependent` (:121) composes the uniqueness of the run `P, baseDepth` with the convergence of the run `Q, otherDepth`. That is a positive consequence of two distinct executions.

4. **QUALIFIED [static]; fixtures NOT RUN.**
   - Dropping the packet: the field is required, and its type is indexed by `carrierNativeFamily P d family`.
   - Changing the family: the result is dependently indexed by `family`.
   - Resetting the archive: `Step` is indexed by the archive.
   - Ignoring a module: the inner and outer moduli appear in `CarrierFamily.cauchy` and `CarrierLimit`.
   - Receiving the terminal carrier: the signature has no such parameter.

   Several fixtures are weak typing tests (see §6). For example, `CarrierCompletionCannotDropNativePacket` only checks that `produced.native.limit` is not a `NativeCompleteness`. The actual rejection rests on the structure of the type, which was confirmed by reading it.

5. **VERIFIED [static].** Two projections forget rich evidence, and both do so after execution:
   - `carrierCompletionStructure` forgets the native packet;
   - `carrierOrderedData.density` and `naturalBounds` forget the `Density`/`NaturalBound` packets.

   The texts state that the carrier is a downstream projection, that the native packet "remains available in the result" (true of `CarrierCompletionResult`), and that the ordered contract "projects their codes and bounds only after this production". These statements are accurate. No text claims that the generic interface preserves the packet.

## 3. Answers, §4.2 Presented dyadic completion

6. **VERIFIED [static].** The fields of `PresentedDyadicData` are `Carrier`, `approximation`, `modulus`, `modulusMonotone`, `coherent`, `dyadic` and `dyadicExact`. `PresentedDyadicStructure` adds `Equivalent`, `refl`/`symm`/`trans`, `toApprox` and `fromApprox`. There is no terminal map, no canonical comparison, no selected limit, and no round trip. `complete` belongs to the separate layer `PresentedDyadicCompletion`. It is the completion operator, receives only the family, and must produce value, convergence and uniqueness: this is the content of a completion, not the conclusion of the characterization. [interpretation] The core does carry, by design, the components of a numerical carrier (approximation, modulus, coherence), which `numericalCarrier` assembles. This is the "presented" character, and it is stated as such.

7. **VERIFIED [static].** The fields correspond exactly to the enumerations in the FR and EN texts ("Contrat non circulaire" / "Non-circular completion contract"). `PresentedDyadicOrderedFieldData` contains exactly the operations, laws, convergences toward the canonical families, separation↔order and apartness↔order conversions, density and bounds listed in the texts.

8. **QUALIFIED [static].**
   - The carrier-side dyadic constants are numerical: `dyadicCarrier code := ofPresentation (constant code)`. They are linked to the runtime by `carrierReadoutConstant` (CarrierOrderedFieldLaws.lean:19), which consumes `constant_readout`.
   - The canonical families are numerical specifications (`addCarrier`, …). Their convergences consume native runtime operations (`.add/.neg/.mul` and the `*_readout_exact` lemmas). [interpretation] The same statement would follow numerically, because the target is the presentation of the carrier itself. The runtime use is therefore genuine but not logically necessary. The texts say "numerical readouts already connected to constituted runtime operations", which is accurate.
   - Field laws, order laws, inverse, density and bounds really consume runtime productions (`carrierReadoutLaw`, `realizeCarrierOrderOn`, `runtimeCarrierDomain`, `produceDensity`, `produceNaturalBound`).

9. **VERIFIED [static].** `carrierCompletionStructure` covers every `family : PresentedFamily carrierPresentedCore`, with no fixed example. The test also completes `decayFamily` (variable terms, outer modulus `p+1`, inner moduli `p+2`) and `boundedFamily`.

10. **VERIFIED [static]; kernel acceptance NOT RUN.**
    - `presentedCarrierEquivalent` (:120): one bit `p+1`, two distinct thresholds `C.modulus y (p+1)` and `x.modulus (p+1)`, and a response `(p+1) + convergence.threshold (p+1)`.
    - `normalizedEquivalentNear` (CarrierQuantitativeTransport.lean:12): three comparisons at `p+2` and two composition losses (`Near.compose` twice, with `target.weaken (next (p+1))`).
    - `preservePresentedLimit`: threshold `p+3`, `normalizedEquivalentNear` at `p+1`, then a single composition.
    - `diagonalTransportFamily`: modulus `succ p + family.modulus (succ p)` and `weaken (next p)`.

    The moduli are not conflated, and no margin is silently reduced. The fixture `NormalizedComparisonNeedsTwoLosses` (expected diagnostic `PrecisionExtension (p + 2) r`) is NOT RUN.

11. **QUALIFIED [static].**
    - On the carrier side, density and bounds are first rich productions (`CarrierDensityResult` and `CarrierNaturalBoundResult` retain `realizedOrigin`, `packet`, `code`, `target` and the orders). Their orders are **reused** through `transportCarrierOrder orders.1.toCarrier …`, not reconstructed.
    - The exact readout theorems pass through the retained steps and actions.
    - In the generic contract, the witness is `Σ code, Order x (dyadic code) × Order (dyadic code) y`. It is positive and lives in `Type`, but it is not a runtime packet. The generic contract cannot require one, and the texts do not claim that it does.

12. **VERIFIED [static].** `PresentedDyadicOrderedFieldData (C : PresentedDyadicStructure)` is indexed by the **structure**. It constructs no limit and receives no completion. It is joined with a completion in `PresentedDyadicOrderedFieldCompletion` (`core`, `completion`, `ordered`). The target text, after `ba549cd`, says "enriches a presented structure … joins this packet with the completion", which is exact. Note: the request's wording ("enriches a completion") is accurate only in the sense of a sibling field. The earlier wording at `8321280` ("enriches a presented completion") was less exact, and `ba549cd` corrects it.

## 4. Answers, §4.3 Characterization and relative uniqueness

13. **VERIFIED [static].** `comparisonMorphism.map x := (Target.completion.complete (presentCarrierFamily Target.core (numericalCarrier Source.core x))).value`. The other fields (`mapEquivalent`, `mapDyadic`, `presents`) are derived from the target's convergence and uniqueness. No terminal map is received.

14. **QUALIFIED [static].** `CompletionMorphism` has the fields `map`, `mapEquivalent`, `mapDyadic` and `presents`. Limit preservation (`preservePresentedLimit`, `mapProducedLimit`) is derived. Name-based check: `CompletionMorphism.mapProducedLimit` is not a field. Qualification: `presents` is a convergence datum, one canonical family per point. It is what makes uniqueness immediate (`mapAsProducedLimit`), and the plan and texts state this explicitly. `mapEquivalent` and `mapDyadic` are derivable from `presents`, as `comparisonMorphism` shows; they are redundant but harmless.

15. **VERIFIED [static].**
    - `PointwiseEquivalent f g := (x : Source.core.Carrier) → Target.core.Equivalent (f.map x) (g.map x)`, which lives in `Type`.
    - There is no `funext`, `Eq` between functions, or `propext`.
    - `fromToTarget` holds at `EffectiveCauchyReal.Equivalent`, and `toFromTarget` at `Target.core.Equivalent`.
    - The test `noTagIdentity` proves that `toTarget (fromTarget ⟨false, firstZero⟩) ≠ ⟨false, firstZero⟩` (as `Empty`). This shows the round trip is not an identity.

16. **VERIFIED [static]; kernel NOT RUN.**
    - Zero and one: `mapEquivalent` + `mapDyadic` + `zeroExact`/`oneExact`.
    - Addition, negation and multiplication: `morphismNumerical`, `{add,neg,mul}Numerical` through the **canonical** families, the congruences, and `equivalentByLimitUniqueness` (whose `comparisonFamily` has modulus `p+2`).
    - Order: `orderToSeparation` → `transportCarrierOrder` → `separationToOrder`, in both directions.
    - Apartness: through the conversions.
    - Inverse domain: `transportApartness` + `preserveZero`.
    - Inverse: `presentedInverseUnique`, using the two unit laws.
    - Density and bounds, and the produced limits in both directions: as listed in §1.

    Qualifications:
    - (a) `RelativeOrderedCharacterization` is only packaged between the carrier completion and an arbitrary `Target`. The texts claim exactly that. Between two arbitrary ordered completions, `comparisonMorphism`, `comparisonUnique`, `orderedMorphismTransports` and `orderedComparisonRoundtrip` are generic, but they are not packaged together.
    - (b) The only ordered positive test uses as `Target` the carrier completion at another perimeter. It has the same core and the same `Order`, so it does not exercise a structurally distinct ordered target. The genericity follows from the types alone.

17. **VERIFIED [static].**
    - `preserveDensity` and `preserveBounds` keep `w.1` (respectively `w.1, w.2.1`) and transport the orders through `mapDyadic`. They never invoke `Target.ordered.density`.
    - `densityTransportCode` (`rfl`) only asserts that the code is preserved by transport.
    - The exact equalities `*ReadoutExact` appear only in `OrderedCompletionPointwiseEquivalent`, over a single shared core. They are proved from execution by `carrierDensityReadoutExact` and `carrierNaturalBoundsReadout_perimeterIndependent`, not from the mere validity of a witness.

18. **VERIFIED [static]; axiom output NOT RUN.**
    - A scan of the 10 new files found no `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot`, `native_decide`, `unsafe`, `implemented_by`, `decide`, `funext`, `Quotient`, `partial`, `opaque` or `extern`.
    - The only potentially axiom-generating constructs are the `simp only […]` inside `conv` in `composeSignedBoundMixed`, `sixFineOneMiddleBudget` and `composeThreeOneThree`. [measured, indicative] A verbatim copy of `composeSignedBoundMixed` and `sixFineOneMiddleBudget`, with their prerequisites copied from `Precision.lean`, was run under **Lean v4.28.0** (`audit-probes/StandaloneSimpAxiomProbe.lean`). Output: `'composeSignedBoundMixed' does not depend on any axioms` and `'sixFineOneMiddleBudget' does not depend on any axioms`. This is not evidence for v4.33.1.
    - No cofinality is assumed: `carrierNativeFamily` uses only monotonicity. No quotient or extensive real is used.

## 5. Answers, §4.4 Constitutive dependence and runtime alignment

19. **Complete path [static]** (carrier family → limit → ordered structure → readout):
    1. Primitive relation and context: `P : CircularPresentation`, `baseDepth`, and the received context `family : CarrierFamily` (terms, outer modulus, Cauchy law at the inner moduli).
    2. Realization of each term: `ofCarrier P baseDepth (family.terms n)` (= `ofPresentation … (toPresentation …)`). This is produced in `carrierNativeFamily` and stored as the terms of the `NativeCauchyFamily`.
    3. Executed production: `nativeCompleteness` runs the native diagonal and grouping (`nativeLimit`, `nativeEnvironment`). The packet stores `realized`, `limit`, `richService`, `candidate`, `convergence` and `uniqueness`. The convergence observations (`observeLimit`) consume the `lim.resource.diagonal` owned by the limit step and the bank `la.bank (family.modulus s)`. The test `currentArchiveOwned` asserts `diagonalArchive = (previousLimit P d).next.bank 3`.
    4. Action and continuation: each `Step` installs `next.installed = some ⟨bank, journal, 2, resource⟩` (test `nextInstalled`). The archive is the index of the following step; `CarrierNativeCannotResetArchive` checks that `old.next` cannot be replaced by the initial archive (NOT RUN).
    5. Grouping and completion: `toCarrier native.limit` (projection); `carrierCompletionStructure` (the packet is forgotten); `carrierOrderedCompletion` (operations, laws, density and bounds as projections of `CarrierDensityResult`/`CarrierNaturalBoundResult`).
    6. Readout: codes `inspectedDensityCode origin.accuracy (approx x response) (approx y response)` and the bounds `lower`/`upper`. The rich packets are forgotten, and no lemma restores them.

20. **QUALIFIED [static].**
    - Sharing is correct in `carrierCompletion` (a single `let native`) and in `produceCarrierDensity` (a single `realizedOrigin` and a single `packet`, reused by `left`/`right`).
    - Some proofs, however, carry out fresh realizations that are not continuations of a stored production: `nativeOperationConvergence` (`.add (ofCarrier x) (ofCarrier y)` built inside the proof), `realizeCarrierOrderOn` and `carrierInverseUnitRight` (from `initialArchive`), and `produceCarrierDensity`/`produceCarrierNaturalBounds` (from `initialArchive` and `Journal.root`).
    - These are independent executions used to establish laws. They are not presented as shared productions, and they establish nothing that is claimed to be shared. [interpretation] This is not a hidden replay: no theorem claims that these runs continue a previous memory. Nor is it an alignment with an earlier archive.

21. **VERIFIED [static].**
    - The family is a dependent index of `CarrierCompletionResult`, and the moduli are fields of `CarrierFamily` consumed by `cauchy`.
    - The archive is the index of `Step`; journals are fixed at `Journal.root` in the packets.
    - The candidate cannot be received.
    - The target of a morphism is arbitrary, but it must satisfy `presents` for the produced family.

    The fixtures that probe these points are NOT RUN.

22. **VERIFIED [static].** No theorem uses an equality of readouts to reconstruct a history, an occurrence or a Cauchy packet. The readout equalities (`carrierDensityReadoutExact`, `carrierNaturalBoundsReadout_perimeterIndependent`, `returnedNormalizedTermAt`) conclude only equalities of codes or approximations. Native Cauchy witnesses and occurrences are forgotten by `toCarrier`, `carrierCompletionStructure` and the density/bounds projections. The texts never say they can be recovered ("They do not recover moduli, Cauchy witnesses, banks, archives, or journals forgotten by readout").

23. **VERIFIED [static]; legitimate sharing is distinguished from vacuity.**
    - In `carrierOrderedCompletionIndependent`, the fields proved by identity (`preserveOrder o := o`, `addEquivalent := refl`, …) come from the core, `Order` and `Apartness`, which are shared and independent of `P`. The plan states this explicitly ("L'équivalence positive est celle de l'unique noyau `C` partagé").
    - The non-trivial fields compare two distinct runs: `completeEquivalent`, `inverse` and `*ReadoutExact`.
    - `candidateAgreement` compares two candidates that are proved structurally distinct (`candidatesDistinct : firstZero = secondZero → Empty`).
    - `comparisonUnique` compares an arbitrary `f` with `comparisonMorphism` through the target's uniqueness, so it is not vacuous.
    - `relativeForwardExact` and `relativeBackwardExact` (`rfl`) are legitimate definitional unfoldings.

---

## 6. Constructivity, build and negative gates (commands)

### 6.1 Commands requested in §5

All executions took place in a disposable clone at `ba549cd` (`/tmp/audit/py`). Its `git status` stayed empty.

| Command | Exit | Relevant output |
|---|---|---|
| `lake clean` / `lake build` with **v4.33.1** | **NOT RUN** | Compiler not available (`SSL connect error`). |
| `lake build` with v4.28.0 (toolchain swapped in a separate clone) | 1 | `Unknown option 'linter.checkUnivs'`, `Unknown option 'linter.defProp'`, `Unknown option 'warn.classDefReducibility'`, `Precision.lean:368:8: Tactic 'rewrite' failed`, `RelationalProfileConstitution.lean:544:74: … does not contain 'List.prod'`. |
| `lake build Tests.PresentedDyadicCompletion` with v4.28.0, after only deleting the three unknown `set_option` lines (65 files) | 1 | `Instances/HeytingArithmetic/Coding.lean:210:10: No goals to be solved`, `Precision.lean:368:8: Tactic 'rewrite' failed`. Proof-level incompatibility. Abandoned: patching proofs would mean auditing a modified target. |
| `python3 scripts/check-scientific-docs.py --self-test` | 0 | 7 tests OK; `SCIENTIFIC_DOCS_SELF_TEST_OK` |
| `python3 scripts/check-scientific-docs.py --static` | **1** | `SCIENTIFIC_DOCS_ERROR: STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` |
| `python3 scripts/check-scientific-docs.py --lean` | **NOT RUN** | Requires `lake env lean`. |
| `bash scripts/verify.sh` | **1** | Stops at the `--static` step on the same `STALE_SOURCE`, before `lake build`. **Not green.** |
| `pwsh -NoProfile -File scripts/verify.ps1` | **NOT RUN** | `pwsh` absent. |
| `git diff --check` | 0 | Empty. |
| Sub-steps of `verify.sh` that do not use Lean | 0 | `check-import-boundaries.sh --self-test` and the 4 boundary files (`IMPORT_BOUNDARY_OK …`); `check-stratification.sh --self-test`; `check-stratification.sh` (`337 production modules, all enforced, no orphan`); `unified_codegen_selftest.py`. |
| Structural AXIOM_AUDIT check (the `verify.sh` loop, run on its own) | 0 | 406 files, exactly one block each, closing as the last line. |
| `verify.sh` forbidden-term scan (run on its own) | 0 | No occurrence outside `#print axioms`. |
| `scripts/check-real-carrier-completion-codegen.py` | **NOT RUN** | Requires `.lake/build/ir/*.c`. |
| `scripts/check-expected-failures.sh` (20 new fixtures) | **NOT RUN** | Requires the compiler. |

### 6.2 Analysis of `STALE_SOURCE` [measured]

- The fingerprint (`source_fingerprint`) of every claim includes `CONFIG` + `claim["checks"]` + the import closure of the proofs. For `GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`, `checks = [scripts/expected-failures.tsv, scripts/stratification.tsv]`.
- The recorded fingerprint equals the fingerprint at its `evidence_revision` `5e69b1b` (True), but not the current one.
- The **only** files that changed are `scripts/expected-failures.tsv` (+20 lines, 0 removed) and `scripts/stratification.tsv` (+8 lines, 0 removed), both modified by `8321280`.
- **Second stale claim, masked:** `RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` (evidence `1a2bd65`) is stale for the same reason. The validator stops at the first failure.
- At the parent `b3a213e`, `--static` passes: `SCIENTIFIC_DOCS_STATIC_OK claims=21 declarations=168`.
- Conclusion: this is exactly the conservative freshness rule on shared manifests, triggered by purely additive lines. It is separate from the mathematical verdict on gates 7.1–7.3. Even so, the global verifier is **red** at the target.

### 6.3 Constructivity and audit blocks of the new files [static]

| File | Declarations | `#print axioms` | Missing | Printed but not declared here |
|---|---|---|---|---|
| RelationalRealCarrierCompleteness | 11 | 11 | 0 | 0 |
| PresentedDyadicCompletion | 25 | 25 | 0 | 0 |
| CarrierQuantitativeTransport | 12 | 12 | 0 | 0 |
| PresentedDyadicOrderedField | 12 | 12 | 0 | 0 |
| CarrierOrderedFieldLaws | 23 | 23 | 0 | 0 |
| CarrierOrderedCompletion | 17 | 17 | 0 | 0 |
| DyadicCompletionCharacterization | 23 | 23 | 0 | 0 |
| DyadicCompletionOrderedCharacterization | 33 | 33 | 0 | 0 |
| Tests/RelationalRealCarrierCompleteness | 34 | 34 | 0 | 0 |
| Tests/PresentedDyadicCompletion | 44 | 44 | 0 | 0 |

- All data live in `Type`. The only recursion is structural; no `partial` is used.
- The printed axiom **results** were NOT RUN at v4.33.1.
- The documentation: every backticked identifier in the FR and EN texts that names a declaration exists in the target. The remaining tokens are `AC`, `CH`, `baseDepth` and the claim identifier. FR and EN have the same set of code tokens and the same number of headings. The **types** of those declarations could not be confirmed by the compiler; they were confirmed by reading.

### 6.4 The 20 expected-failure fixtures [static; diagnostics NOT RUN]

Fixtures that are meaningful as types:

- `CarrierFamilyCannotIgnoreInnerModule` (`PrecisionExtension ((family.terms n).modulus p) r`)
- `CarrierLimitCannotIgnoreOuterModule`
- `CarrierNativeCannotResetArchive`
- `CarrierReturnedLimitNeedsBridge`
- `NormalizedComparisonNeedsTwoLosses`
- `PresentedCarrierEquivalentNeedsConvergence`
- `CarrierOrderTransportNeedsEquivalence`
- `SevenMarginsCannotUseBinaryBudget`. Here `DirectedUpper.compose` requires two `(q+1)` bounds to give `q`, so the expected diagnostic `DirectedUpper (p + 1) a` is consistent.

Weak fixtures [interpretation]:

- Name-based ones (`Unknown constant`): `PresentedCoreCannotReceiveTerminalMap`, `PresentedConvergenceCannotBeOpaque`, `CompletionMorphismCannotReceiveLimitPreservation`.
- `rfl` failures over an arbitrary family or modulus: `CanonicalOperationCannotChooseFamily`, `OwnFamilyCannotChooseModule`.
- An obviously wrong term: `CarrierCompletionCannotDropNativePacket`, `CarrierDensityValidityCannotGiveExactReadout`, `CarrierEquivalenceCannotIdentifyCarriers`, `PointwiseComparisonCannotIdentifyFunctions`.

These fixtures do not demonstrate the stated property on their own. It rests on reading the types (§2–§4), which confirms it.

### 6.5 Compiled-code checker [static]

`check-real-carrier-completion-codegen.py` covers four routes: `carrierCompletion`, the term adapter, the Cauchy law, and the factory. It includes 26 argument mutations plus 2 duplicated-call mutations, 28 in total, which matches its final message. The mutations are meaningful:

- removing the packet in `lean_ctor_set` or in the uniqueness closure;
- each argument of `nativeCompleteness`/`toCarrier`;
- each module, monotonicity argument and owned step of the law;
- duplicating `nativeCompleteness`/`toCarrier`, which tests multiplicity 1.

It is bounded: its docstring excludes logical laws and callback internals, so it does not present itself as a semantic theorem.

**Partial fail-open** (`unified_codegen_analysis.py:200–203`): a helper absent from the parsed C, called **without** a closure-relevant argument, returns the **union of the tags** of its arguments instead of failing. Unsupported control flow does fail closed (lines 96–108, 240–300).

---

## 7. Independent probes and counterchecks

The files are in `audit-probes/`, outside the target. **Status: NOT RUN**, because they need the target compiled at v4.33.1. Only `StandaloneSimpAxiomProbe.lean` was executed (v4.28.0, indicative; §4 Q18).

| Probe | Countercheck | Expected outcome [static] |
|---|---|---|
| N01 | Supply the carrier limit to `carrierCompletion` | Function expected / too many arguments |
| N02 | Build `CarrierCompletionResult` without `native` | Missing field (anonymous constructor arity) |
| N03 | Reuse the packet of another family `g` for `f` | Type mismatch `carrierNativeFamily P d g` vs `… f` |
| N04 | Substitute the family in `native` | Same |
| N05 | Reset the archive (`old` in place of a step at `old.next`) | Index mismatch `old.next` vs `initialArchive` |
| N06 | Terminal map `C.toCarrier` | Unknown constant |
| N07 | Limit preservation as a field `f.preservesLimits` | Unknown field |
| N08 | `f.map = g.map` via `funext` from `PointwiseEquivalent` | Mismatch `Target.core.Equivalent …` vs `Eq` |
| N09 | `x = y` from `EffectiveCauchyReal.Equivalent` | Failure of `cases`/`rfl` |
| N10 | A single loss (`p+1`) where `p+2` is required | `PrecisionExtension (p + 2) r` expected |
| N11 | Exact density readout from a valid witness | `rfl` fails (the codes are not definitionally equal) |
| N12 | Ordered transport with `refl d` on an unrelated `b` | Mismatch `Equivalent b d` |
| N13 | Seven segments composed by binary association | `DirectedUpper (q+1)` expected at the composition of `middle` (`p+2`) with `right3`; includes a positive control through `composeThreeOneThree` |
| P01 | Positive: roundtrip and uniqueness between two **arbitrary** ordered completions, plus `#print axioms` for `relativeOrderedCharacterization` and `carrierCompletion` | Must compile with "does not depend on any axioms" |

---

## 8. Non-loss and fidelity of scope

**Diff `b3a213e..ba549cd` [measured]:**

- 33 files added (8 modules, 2 tests, 20 fixtures, 2 canonical texts, and the codegen checker).
- Modified files: `RelationalPerimeter.lean` (+8 imports, +5 `#print axioms`), `Tests/AllConstantsAudit.lean` (+2 imports), `scripts/expected-failures.tsv` (+20), `scripts/stratification.tsv` (+8), `verify.sh` (+1), `verify.ps1` (+2), and the plan (+1605/−178).
- **No deletion** in any `.lean` file or script.
- The gate-6 texts (`runtime-real-cauchy-effective-correspondence.fr.md` and `runtime-effective-cauchy-real-correspondence.en.md`) are unchanged.

**The 178 lines deleted from the plan [static]:**

- They rewrite the terminal target. The old "Cible terminale : correspondance avec les réels usuels" required an executable `fromExtensive` and an "archimédien complet" characterization.
- It becomes "Cible terminale : caractériser les réels depuis le runtime". This version:
  - explicitly drops an executable `fromExtensive` from a bare quotient, with a stated reason;
  - moves the classical obligations to 7.4 (`carrierCoverage`, `constructive`/`relationalCoverage`, correction, faithfulness, transports, completion principle of `E`).

[interpretation] This is a documented re-specification of the **classical target 7.4**, which remains open. It does not weaken gates 7.1–7.3, and no earlier Lean theorem, contract, quantifier or audit is touched. It is not purely additive, however, and it should be noted as a scope change of the terminal target.

**FR/EN texts [static]:**

- Read independently, they correspond paragraph by paragraph: same structure, same code tokens.
- Their statements agree with the Lean:
  - `PresentedDyadicOrderedFieldData` enriches the structure;
  - round trips are behavioural;
  - witnesses are forgotten and never recovered;
  - no implication toward 7.4, all classical reals, least upper bounds, AC or CH.
- One imprecision, minor and not blocking: "Readout-independence theorems consume the retained `Step`s and actions." This is true of the code and bound theorems. But the identity-proved fields of `carrierOrderedCompletionIndependent` rest on the shared core, which the canonical text does not repeat. The plan does say it.

---

## 9. Exactly what remains undecided

1. Whether Lean v4.33.1 accepts the 10 new files and their whole closure (167 modules, 89,341 lines), including the arithmetic margins (`composeThreeOneThree`, `normalizedEquivalentNear`, `preservePresentedLimit`, `transportCarrierOrder`) and the `rw` steps that depend on `*Exact` equalities.
2. The printed axiom outputs for the 234 declarations of the audit blocks.
3. The execution of the two positive tests.
4. The exact diagnostics and sites of the 20 fixtures.
5. `check-real-carrier-completion-codegen.py` (28 mutations) on the generated IR.
6. `check-scientific-docs.py --lean`, `verify.sh` beyond the docs step, and `verify.ps1`.
7. The probes N01–N13 and P01.

## 10. Corrections to report (independent of the incomplete status)

1. **Global verifier red at the target (registry, not mathematics).** `--static` and `verify.sh` fail with `STALE_SOURCE` on `GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`, and also on `RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE`, which is masked. The cause is purely additive lines in `expected-failures.tsv` and `stratification.tsv`. The repository must re-fingerprint the claims or make the freshness rule finer. This must not be counted as green.
2. *(Not blocking.)* Strengthen the weak fixtures listed in §6.4 so that they test the property and not a name or a trivial mismatch.
3. *(Not blocking.)* Make `unified_codegen_analysis.py:200–203` fail closed for unknown helpers.
4. *(Not blocking.)* Add an ordered positive test with a structurally distinct target, and optionally package `RelativeOrderedCharacterization` between two arbitrary completions if that scope is wanted. It is not claimed today.
5. *(Not blocking.)* Note in the history that the plan restructured the classical terminal target (7.4).

No result about gate 7.4 is promised or inferred.
