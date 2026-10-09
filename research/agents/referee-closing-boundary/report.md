# Independent referee report: closing boundary before junction choice

Referee `/root/positive_foundation_referee`, lot 1 of `docs/plan-suite-fondations-positives.fr.md` §4, 2026-10-09. **ESTABLISHED in the requested scope; T2, independent AI review, human verification pending.** No blocking source correction found. Prior reports remain preserved in their original archive.

## Evidence and conduct

Read the continuation plan, existing selected boundary/role interfaces, and both new modules `ClosingBoundary.lean` and `ClosingBoundaryExamples.lean`. Used the previously read Labyrinth method and maintained the distinction between proof tier and review provenance. Wrote only this new referee archive. No canonical edit, commit, publication, child agent, or full build by this referee.

Independent probes were authored from the interfaces, without reusing the coordinator's constant-fibre examples. They use Bool source/target sorts, an Option Bool difference, a selected Bool provenance, and a compatibility family whose selected off-diagonal fibre varies while another fibre is Unit. Thus the empty example tests an actual selected fibre, not globally empty compatibility, and its shape exists directly before a junction is added.

After the coordinator's readiness signal, ran one small Lean process at a time:

```text
lake env lean research/agents/referee-closing-boundary/IndependentProbes.lean.in
```

The first run exited 0 but **did not pass the axiom requirement**: the overlapping-pattern definition of this referee's auxiliary `selectedFamily` had a generated dependency on `propext`. This was not a dependency in the reviewed implementation. Saved that output in `first-probes-with-axiom.log`, replaced only the auxiliary definition by explicit `Bool.rec` eliminators, and reran. The final run exited 0 with **20 audited declarations, all independent of axioms**, recorded in `independent-probes.log`. The coordinator was told immediately that the final process had ended and the global build could start. That global build remains coordinator evidence.

## Claim-by-claim verdicts

| Claim | Verdict and reasoning |
|---|---|
| Closing shape is definable before a junction is chosen | ESTABLISHED. `ClosingBoundaryShape` retains every old boundary field except `junction`; `ClosingWitness` is its selected compatibility fibre. Source, target, difference and provenance remain chosen. This is not an assertion that all primitive data are unselected. |
| A concrete witness constructively yields an indexed pointing | ESTABLISHED. `PointedClosingBoundary B` is a one-field structure over B, and `point` takes a concrete `ClosingWitness B`. `pointingTransport` supplies explicit witness-to-point and point-to-witness maps with both exact returns. |
| Propositional habitation of pointing is equivalent to habitation of the selected fibre | ESTABLISHED. `nonempty_pointed_iff` eliminates `Nonempty` into another proposition and constructs another `Nonempty`; no witness is extracted into arbitrary `Type`. Independent `witnessPointingHabitation` reproves the two directions directly. This equivalence is not a general choice function from mere existence. |
| An empty selected fibre prohibits pointing and final-role existence | ESTABLISHED. `noPointingOfEmpty` receives a function from the fibre to False and eliminates proposition-valued existence into False. `noFinalRoleOfEmpty` uses the exact existential-role/inhabitation equivalence. Independent `emptySelectedFibre` and `emptySelectedHasNoPropositionalPoint` directly inspect the junction of an alleged point. Another compatibility fibre of the same shape is independently inhabited, showing the obstruction is at the selected indices. |
| Empty selected fibre cannot be obtained by forgetting an already pointed constitutive boundary | ESTABLISHED. `shape_fibre_nonempty` returns the original junction as a proposition-valued inhabitant of the forgotten fibre. `empty_not_from_constitutive` transports that proposition along shape equality and contradicts Empty. The independent `emptyShapeCannotBeForgotten` reconstructs this argument directly with `boundary.junction`, without using that theorem. |
| Forgetting and reconstruction are exact | ESTABLISHED. `shape_roundTrip` returns the entire shape; `pointing_roundTrip` returns the entire indexed pointing; `boundary_roundTrip` returns the original `ConstitutiveBoundary`. The stored functions, selected indices and selected provenance are carried unchanged. Independent `directShapeReturn`, `directPointingReturn`, and `directOldBoundaryReturn` reprove all three by reduction/structure analysis. The independent Unit model also checks all four selected non-junction data. |
| Final role is adapted without another choice of junction | ESTABLISHED. `pointed.FinalRole` is an abbreviation for the previously validated `EquippedFinalRole pointed.toConstitutiveBoundary`. `finalRole` reads its canonical witness from that boundary. `finalRole_junction` reads the exact agreement to `pointed.junction`. No choice is regenerated or imposed by the role. |
| Role is inhabited and unique for each fixed pointing | ESTABLISHED. `finalRole_unique` delegates to exact witness agreement in the existing role. Independently, `roleIsUniqueForFixedChoice` applies the role extensionality lemma to the equality obtained from the two exact witness equations. Its quantifier fixes the pointing; it does not quantify over arbitrary closing witnesses and assert they coincide. |
| A Unit fibre supplies a pointing and unique role | ESTABLISHED. Author `unitPointing`, `unitRole`, and their uniqueness claims use the one Unit value. Independent `unitPoint` constructs a point on different selected-data sorts and preserves source, target, difference and provenance on reconstruction. |
| Two Bool witnesses yield distinct pointings on the same shape, each with a unique role | ESTABLISHED. Author `falsePointing`/`truePointing` project any alleged equality to the contradictory Bool equality. `bool_same_shape` confirms forgetting both yields the same shape. Their role witness views remain distinct. Independent `chosenFalse`/`chosenTrue` and `choicesRemainDistinct` confirm this on a nonconstant compatibility family. |
| Per-choice role uniqueness does not imply uniqueness of all fibre witnesses or of total equipped choices | ESTABLISHED in the precise countermodel. The author proves nonuniqueness of pointings and closing witnesses. Independently, `totalFalse` and `totalTrue` inhabit the sigma total of pointing and final role; `equippedTotalRemainsDistinct` projects an alleged equality to equality of the pointings. Each role fibre is still unique. This rules out the inference from fibrewise role uniqueness to uniqueness of that total. |

## Scope and integration

The module comments correctly say that only the closing witness is omitted and that propositional existence remains in Prop. The three direct models match the plan's Empty/Unit/Bool requirements. Their empty model is independently constructed, and the formal impossibility of deriving it by forgetting an old boundary is explicit. The Bool model states uniqueness per choice, not uniqueness of the whole fibre. The old `ConstitutiveBoundary` signature is unchanged; the new module imports it and provides exact adapters.

Lot 1 is completed in this selected scope. This review does not close the positive generation algebra, transport of full relation families or operations, complete interior/final role classification, rigidity, or universal minimality of the boundary signature. It does not show that proposition-valued inhabitance generally yields a computationally chosen junction, nor that a contractible role makes every underlying fibre contractible. The induced pointer/witness exact transport is stronger data than their merely proposition-valued habitation equivalence, and remains constructively supplied.

The extra independent sigma-total diagnostic may be integrated as a new result only with its own authorship/checking provenance: its source is this referee's probe, so an independent coordinator reread/spot check should be named before calling that new original diagnostic independently refereed. The existing author's Bool countermodel already suffices for the lot's required distinction.

Verdict: accept the new source claims as T2 with independent AI review and human verification pending, subject to the coordinator's repository-wide validation. No formal flaw or unfulfilled obligation within lot 1 was found. No generated map/document/dashboard review is implied by this report.

Owned files: `design-check.md`, `IndependentProbes.lean.in`, `first-probes-with-axiom.log`, `independent-probes.log`, and this report, all under `research/agents/referee-closing-boundary/`.

## Addendum: map, documents and review closure

2026-10-09. Read the five new T2 nodes (`th.closing-shape-bridge`, `th.closing-pointing-exact`, `th.closing-empty`, `th.closing-role-choice`, `th.closing-choice-multiplicity`) in `labyrinth/knowledge.json` and their matching SOTA rows. Read the new dead end `x.role-unique-choice`, source node `src.closing-worktree`, and updated `q.equipped-final-role`. Also read `docs/frontiere-sans-jonction-choisie.fr.md` and the amended continuation plan, including its completed lot-1 checklist.

Independent `CheckLotMap.ps1` passed: **5 unique new T2 nodes, 20 exact source anchors**, matching SOTA statements, existing evidence files, and valid graph-link targets. Output is archived in `lot-map-check.log`. Manual reading accepts the statements, declared assumptions and consumed data. Dependency links are acceptable at the aggregate declaration scope: the witness/pointing calculus consumes the underlying shape/pointing declarations, while role adaptation consumes reconstruction and the existing role's canonical/unique results; these links do not claim necessity of every return theorem in those aggregates.

The working-tree/base revision is explicit in the map scope and SOTA text. Each new formal result remains T2, with named independent AI checking and human verification pending. The original sigma-total diagnostic from this referee is not promoted to a separate map result, so no additional authorship/review attribution is required for it. The author-source Bool countermodel already supports the new dead end.

The reader-facing document accurately distinguishes the shape's retained selected indices/provenance, a concrete junction in Type, merely propositional habitation, three exact returns, empty shapes constructed directly, and role uniqueness for a fixed choice. Its statement that the selected empty shape cannot come from forgetting an equipped boundary is formally justified. The plan properly closes only lot 1; positive generation, full fibre transports, complete role grammar and general minimality remain open. `q.equipped-final-role` consequently remains partial, with no claim of global choice uniqueness or rigidity.

Read the tail of `closing-workspace-verification.log`: the coordinator's full build finished with 106 jobs, and the repository script verified 109 Lean files. These are coordinator checks, distinct from the referee's final 20-declaration independent probe and 20-anchor map check. No further Lean process or full build was run by this referee. No dashboard rendering or generated reader-artifact visual inspection is claimed here.

**Review closed: ESTABLISHED in lot 1's selected scope. No unresolved correction.** Human verification remains pending. Additional referee-owned files are `CheckLotMap.ps1` and `lot-map-check.log`.

The active `closing-source-snapshot.json` was also read and independently checked against the working files with SHA256: 26 files, zero mismatches. This checks snapshot identity, not new semantic claims or compilation.
