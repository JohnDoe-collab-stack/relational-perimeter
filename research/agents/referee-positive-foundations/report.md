# Independent referee verdict: positive circular foundations

Referee `/root/positive_foundation_referee`, 2026-10-09, branch `codex/positive-circular-foundations`. **ESTABLISHED in the selected scope; independent AI review, human check pending.** The proved programme results remain T2. No canonical source or documentation changed by this referee; no commit, external publication, full build, or child agent launched.

## Method and evidence

Applied the supplied Labyrinth independent referee method. Read the primitive declarations and historical circular structure in `StrongPerimetralTurning.lean`, `ExactTypeTransport.lean`, foundation plan §§9, 11, 17, and the previous foundation referee report before inspecting the implementation. Read all five implemented modules, the `RelationalPerimeter.Constitution` facade, and the historical source diff.

The extracted block from `structure LocalNode` through `NonClosingNext.toPrecedes` is text-identical to HEAD after normalization of line endings and trailing whitespace. Names, constructors, defining equations, and existing order/adjacency lemmas were preserved. The historical diff removes this block, imports the new positive module, and replaces the original first nine fields by the positive parent; endpoint and obstruction fields remain present.

Authored `IndependentProbes.lean.in` from the definitions, without reusing the coordinator's example code. One small process ran after the coordinator's readiness signal:

```text
lake env lean research/agents/referee-positive-foundations/IndependentProbes.lean.in
```

Exit code 0; **22 audited declarations, all independent of axioms**, recorded in `independent-probes.log`. No failed run or repair was needed. The `.lean.in` extension deliberately keeps the probe outside the repository's `.lean` build-output requirements. The coordinator was immediately told the process had ended so the full build could start. The full repository build and global validation are the coordinator's responsibility and are not represented as independently rerun here.

## Claim-by-claim verdicts

| Claim | Verdict and exact scope |
|---|---|
| Positive presentation independent of contraction rejection | ESTABLISHED. `PositivePresentation.lean:18` contains the same nine positive fields, without endpoints, loop type, or rejection. Its import depends only on extracted primitives. This is a nonempty finite witnessed perimeter, since `perimeterPositive` is an input. It does not yet implement an arbitrary positive generation algebra from §9. |
| Endpoint readings and rejection are distinct enrichments | ESTABLISHED. `EndpointBoundary` at :30 imposes initial pole agreements but no separation. `CircularClosureObstruction` at :40 receives loop/closure and rejection data separately. `endpointsSeparated` uses the rejection enrichment. Independent common-Unit-pole model at probe :29 and direct contradiction from the rejection field at :42 confirm the distinction. |
| Exact historical preservation and reconstruction | ESTABLISHED. Bridge :48, :55, :63 and :72 give positive, endpoint-boundary, obstruction, and full historical round trips. Their defining equations reconstruct the original data; structure case analysis suffices. Independent generic proof at probe :139 reconstructs the historical structure without using the author's round-trip theorem. The original example is recovered in `Examples.lean:114`. |
| Positive and obstructed models exist | ESTABLISHED. `Examples.lean` equips the same positive chain with identified Unit poles or separated Bool poles and an obstruction; :68 preserves the same parent. Both author and independent examples permit raw node recurrence. That recurrence does not identify generated cursors or occurrences. |
| Boundary extraction is authoritative | ESTABLISHED. `closingBoundary` at boundary module :31 reads the final implicit source, initial explicit target, selected closing junction, and initial difference/provenance. Probe :145 confirms exact junction and provenance views. No alternative chosen witness is introduced by extraction. |
| Rich transport retains selected indices and both chosen witnesses | ESTABLISHED. `BoundaryCarrierTransport` :46 provides exact maps on explicit, implicit, difference, the selected closing fibre, and the selected provenance fibre. `BoundaryTransport` :55 adds three index and two witness equations. The relation and provenance families themselves are not transported over arbitrary indices. |
| Inverse and composition preserve the selected data | ESTABLISHED. :79 derives inverse agreement by applying each backward map to the forward agreement and its return law; :102 composes each agreement explicitly. Probe :71 uses nonidentity `Bool.not` on all five carriers, moving all three selected indices and both chosen witnesses from false to true; :84, :92, :97 and :103 independently test inverse values, composition, equipped role return, and provenance mapping. |
| Unit, associative and inverse laws are sufficient pointwise laws | ESTABLISHED. :133–173 supply forward laws for every selected carrier. :185 derives backward pointwise agreement from forward agreement and exactness. :194–210 establish reflexivity, symmetry and transitivity of existence separately from the data in `Type`. Global equality of function-containing structures is not claimed. |
| Equipped final role preserves the selected constitution under rich morphisms | ESTABLISHED. :215 stores a closing witness with exact agreement to the indexed boundary; source, target and provenance are authoritative boundary views. :237 transports the witness using its separate preservation equation. :242–276 prove endpoint views, provenance and identity/composition/two inverse returns. This is the selected equipped role layer, not the full §11 circular role grammar. |
| Bare equivalence does not preserve a chosen closing witness | ESTABLISHED as a precise countermodel. Author `closingSwap_cannot_lift` at examples :100 fixes the weak fibre map and refutes enrichment by its missing witness agreement. Independent closing-only swap at probe :108 and impossibility at :122 confirm it. This does not refute every rich transport between the same boundaries: identity remains valid. |
| Provenance preservation is independent of closing preservation | ESTABLISHED by an additional independent countermodel. Probe :115 preserves the closing witness and all three selected indices but flips only the provenance fibre; :130 shows that specified weak map cannot enrich to rich transport. Thus a closing-witness law alone is insufficient. |
| A bare singleton role fibre cannot force rich boundary preservation | ESTABLISHED by independent diagnostic. Probe :150 provides a uniform exact role-fibre transport between false- and true-marked boundaries, while :162 shows the identity map on their closing fibres fails the chosen-witness agreement. Contractibility is compatible with an informative equipped index; the fibre alone does not reconstruct the transport data. |

## Scope corrections already applied or retained

No blocking flaw or false formal assertion was found in the implemented scope. The source module comments are appropriately qualified: selected boundary data, no preservation of a whole generated history, no occurrence created by the junction, and raw node recurrence distinct from historical free execution.

The exact wording for integration should be:

> The positive circular data layer and its exact historical obstruction bridge are implemented. Exact transports preserve the selected closing boundary signature, including the distinguished closing witness and initial provenance, with pointwise laws. The equipped final role retains these data under those morphisms.

Do not replace that wording by completion of all of §§9, 11 or 17. The following remain outside this result:

- A positive generation/formation algebra and its general deployment theorem independent of obstruction.
- An unpointed boundary with potentially empty closing fibre, before adding its witness.
- Full circular role grammar, interior/final branch preservation, and equipped total role classification.
- Transports of arbitrary compatibility or provenance fibres, order/adjacency, realization/formation, history composition, endpoint pole operations, or contraction obstruction.
- A generic dependent-signature equivalence or full constitutive quantity transport.

The indexed `EquippedFinalRole B` is still contractible as a fibre. Its indexed structure and restricted rich morphisms carry the selected data; they do not make singleton simplification impossible. The independent cross-boundary fibre transport documents this limit. These are scope boundaries, not deficiencies in the requested selected implementation.

## Integration recommendation

Accept the implemented claims as T2 with this independent AI referee named and human check pending, subject to the coordinator's full build/global checks. The two swap countermodels should remain distinct: one closes the inference from exact closing-fibre equivalence to chosen junction preservation; the other closes the inference from junction preservation to chosen provenance preservation. The raw node recurrence model closes any accidental inference from positive circularity to raw state nonrecurrence.

Files owned by this referee: `design-check.md`, `IndependentProbes.lean.in`, `independent-probes.log`, and this report, all under `research/agents/referee-positive-foundations/`.

## Addendum: final role uniqueness and exact transport

2026-10-09, subsequent source reread requested by the coordinator. No new independent build was needed or run. The coordinator reports that the final full build passes without axioms; the 22-declaration independent probe evidence above is unchanged.

**ESTABLISHED — `EquippedFinalRole.unique`, boundary module :228.** The chain `first.witnessExact.trans second.witnessExact.symm` proves equality of the witnesses of two roles over the same boundary. The already reviewed extensionality lemma then proves equality of the roles, including their proof fields. Together with `canonical`, this gives an inhabited subsingleton, hence the precise contractibility of each indexed fibre. It does not compare boundaries, recover forgotten boundary data, or imply that the total family of equipped roles is singleton-valued.

**ESTABLISHED — `EquippedFinalRole.exactTransport`, boundary module :280.** The forward map is the already reviewed role transport along `map`; the backward map uses `map.reverse`. `transport_reverse` has exactly the orientation required by `forwardBackward`, and `transport_reverse_right` has exactly the orientation required by `backwardForward`. The definition adds packaging, not stronger assumptions or a new conservation inference. Because its supplied map is a `BoundaryTransport`, it accompanies the selected source/target/provenance agreements and maps the chosen closing witness. A bare `ExactTypeTransport` between role fibres still cannot recover that rich map.

The terminal audit block explicitly includes both declarations. Verdict and scope limits remain unchanged: T2, independent AI referee named, human check pending. The table's earlier source lines after :228 refer to the pre-addendum version; the declarations themselves are unchanged apart from the two reviewed additions.

## Addendum: new map and state-of-the-art review

Read the eight new T2 nodes in `labyrinth/knowledge.json` and their matching rows in `labyrinth/sota.json`, the three new dead ends, and the four affected positive-circle/generation/role/transport questions. **ESTABLISHED WITH METADATA CORRECTIONS** for integration: mathematical statements are accepted in the selected scope; the correction below concerns dependency provenance, not a failed theorem.

Independent `CheckNewMap.ps1` verifies eight unique T2 nodes with refereed review, 32 exact file/line/anchor references, existing evidence files, valid link targets, and exact agreement between each new statement and its SOTA result. Output is saved in `new-map-check.log`. The script does not verify proof dependencies; those were checked manually.

The working-tree status is explicitly given in `scope.working_tree`, with the base commit and branch, and in the SOTA `about` text. No new theorem is mislabeled as a published/literature result or as human-checked. The questions retain the correct distinctions: positive data and bridge answered; general positive generation still open; equipped roles and rich transports partial. The empty unpointed fibre, complete role grammar, full dependent families, poles and obstruction are expressly outside the result. The three new dead ends correctly refute automatic chosen-junction preservation, automatic provenance preservation from the junction law, and raw node nonrecurrence from positivity.

One exact dependency correction was sent to the coordinator: **remove `th.boundary-calculus → th.boundary-extraction` with relation `uses`, or replace `uses` by `supports`.** The generic boundary calculus takes arbitrary `ConstitutiveBoundary` values and does not consume `closingBoundary`. All other new links are acceptable at their declared conceptual or aggregate scope.

One review-provenance precision was also sent: `th.separator-provenance-witness` uses the original countermodel authored in this referee's independent probes. Its independent checking should therefore be attributed to the coordinator's reread/spot check of that proof, rather than its author's own review alone. Suggested review text once that reread is performed: “Modèle du referee, relu indépendamment par le coordinateur ; vérification humaine en attente.” This is a distinction of authorship and checking, not an objection to the compiled proof.

No generated documents were reviewed as part of this addendum because the coordinator was regenerating them. Additional referee-owned files: `CheckNewMap.ps1` and `new-map-check.log`.

## Review closure after corrections

2026-10-09. Reread the two corrected map nodes, the provenance SOTA row, and `research/agents/coordinator-positive-foundations/report.md`. The dependency edge now uses `supports`, as requested. The provenance countermodel now names the coordinator as its independent checker, cites that separate report, and its SOTA row explicitly distinguishes model authorship from independent rereading. The report correctly projects `provenanceExact` and reduces the specified flip to `true = false` while preserving the other four carriers. Both metadata corrections are **applied and accepted**.

**Final verdict: ESTABLISHED in the selected scope, T2 with independent AI checking and human verification pending.** No unresolved blocking correction remains from this referee. No further build was run here. The coordinator reports final global verification on 107 Lean files and a successful 104-job build; those repository-wide checks remain coordinator evidence, distinct from this referee's 22-declaration independent Lean run and 32-reference map check. The generated dashboard and reader documents are not asserted to have received independent visual review from this referee.
