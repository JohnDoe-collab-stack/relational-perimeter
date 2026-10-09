# Independent referee report: positive formation and deployment

Referee `/root/positive_foundation_referee`, lot 2 of `docs/plan-suite-fondations-positives.fr.md` §5, 2026-10-09. **ESTABLISHED in the requested path/deployment scope; T2, independent AI review, human verification pending.** No blocking source correction found. New archive only; previous reports preserved.

## Method and evidence

Read the lot-2 plan, current primitives/closing shape/positive presentation, and the three new modules `PositiveGeneration.lean`, `PositiveGenerationBridge.lean`, and `PositiveGenerationExamples.lean`. Applied the previously read Labyrinth method. No canonical source/document edit, full build, commit, publication, or child agent launched by this referee.

Authored independent probes from the definitions. A Bool-state model has Step `Bool × Bool`: the first component is the compatibility witness and the second is additional payload. A separate directed model has heterogeneous interfaces (`Option Bool` explicit, Bool implicit), Bool differences, and a forward step with its own Bool payload; its closing fibre is empty. These data are separate from the author's examples.

After readiness, ran one small Lean process:

```text
lake env lean research/agents/referee-positive-generation/IndependentProbes.lean.in
```

**Exit 0; 38 audited declarations, all independent of axioms**, in `independent-probes.log`. No failed run or repair. The coordinator was immediately informed that the process had ended, allowing the full repository build to start. That full build is separate coordinator evidence, not independently rerun here.

## Claim-by-claim verdicts

| Claim | Verdict and precise scope |
|---|---|
| Positive formation interface receives primitives, state nodes and admissible steps without obstruction | ESTABLISHED. `PositiveFormation` declares independent primitive/state/step universes, complete `node` readouts, typed `Step`, and its compatibility projection. It receives this interpretation and admissible-step family; it does not produce the primitive sorts or establish freshness of differences/provenances. No transition from every state is required. |
| Finite histories are composable and retain their full step data | ESTABLISHED. `PositiveHistory.nil/cons` index finite paths by source and target states; `append` recurses on the first path and preserves its Step fields. Nil, right unit and associativity laws are constructive inductions. This is the ordinary inductive finite-path interface; no stronger universal algebraic property is separately asserted. |
| Deployment is built from the supplied steps and has exact endpoints | ESTABLISHED. `deploy` creates a boundary at nil and an advance carrying `F.compatibility step` at cons. `deploy_start` is definitional; `deploy_final` follows the tail induction. Nodes are complete `LocalNode` values, so the endpoint agreements include their local selected data. |
| Composition respects terminal reindexing | ESTABLISHED. Spine `append` takes a suffix indexed at the first spine's actual `finalNode`. `appendAlong` explicitly uses `terminalExact.symm` to reindex a suffix indexed at the named endpoint. `deploy_append` uses `deploy_final` for that connection and proves the equation by induction. Independent `concreteIndexedAppend` checks a three-step composition; `appendedTerminal` and `appendedPreservesAllThreeWitnesses` check its terminal Bool readout and all three exact compatibility witnesses. |
| History occurrences and deployed nonclosing positions have exact maps both ways | ESTABLISHED. `Occurrence.here/later`, `toPosition`, and `fromPosition` follow corresponding constructors. Both round trips are proven, then packaged as `positionTransport`. Independent probes compute both second-position returns on a two-step path. This transport is over a fixed supplied history; it is not an inverse of deployment on the space of all histories. |
| Empty history has no occurrence/position; cons gives concrete positivity | ESTABLISHED. Nil impossibility is constructor elimination; `.here` supplies an occurrence on every cons path. Independent `nilHasNoPosition` directly eliminates a position on the empty deployment. The positive circular constructor receives an actual occurrence in Type, not merely an unspecified proposition-valued existence. |
| Every deployed link preserves its node pair and selected compatibility | ESTABLISHED. `SuccessiveLink` stores full source node, target node, and the compatibility witness at those indices. History and spine `linkAt` follow the selected occurrence/position; `deploy_link_exact` proves equality of these complete records by occurrence induction. Independent `actualHeadLink` checks source, target and compatibility; `actualTwoLinkWitnesses` checks distinct true/false compatibilities in successive links. |
| An unpointed closing shape is extracted before closure | ESTABLISHED. `boundaryShape` reads the deployed terminal implicit source, initial explicit target, and initial difference/provenance without receiving a junction. `boundary_source_exact` derives the source readout from the terminal theorem. The independent heterogeneous directed path has an occurrence and valid forward compatibility but `openCannotClose` and `openCannotPoint` directly refute its closing witness/pointing. |
| Positivity plus a concrete closing witness builds a positive circular presentation | ESTABLISHED. `toCircular` retains the same node, deployed perimeter, chosen positive position, and supplied junction. Initial/deployment/junction/boundary agreements are exact. Independent `closedPresentation`, `circularCarriesChosenWitness`, and `circularKeepsSelectedProvenance` inspect the chosen data directly. A positive history alone does not supply the closing witness. |
| Endpoint readings and obstruction can be added afterwards through the historical bridge | ESTABLISHED. `PositiveGenerationBridge` separately imports the old bridge; generation itself has no historical obstruction import. `toHistorical` applies `ofPositive`; positive parent, endpoint boundary and obstruction returns are inherited exactly, and perimeter deployment is unchanged. Independent `historicalKeepsExactLayers` checks all three layers on a two-step example by reduction. |
| A chosen continuation is additional data, not general determinism | ESTABLISHED. `ChosenPositiveContinuation` supplies one successor and one witnessed step at each state. Its `walk` recursively builds a finite history at the supplied count and supplies positivity at successor count. The directed model has no such global choice because its terminal state has no admissible step. Independent `openHasNoGlobalChosenContinuation` checks this. Distinct admitted/chosen successors remain possible; independent `distinctSuccessors` checks distinct target node readings from the same Bool source. |
| Repeated raw nodes do not identify occurrence positions | ESTABLISHED. Author examples distinguish `.here` and `.later .here` on a two-step path even when raw node values repeat. Independent `rawNodesReturn`, `twoOccurrencesRemainDistinct`, and `twoPositionsRemainDistinct` verify a false→true→false path. The structural occurrence distinction does not imply raw state values are always distinct. |

## Required scope corrections and independent separators

No false implementation claim was found. The source comments correctly restrict the preserved data to nodes and selected compatibility readouts and deny an inverse of arbitrary Step payloads. Two limits were explicitly sent to the coordinator for the documents/map:

1. **Deployment need not be injective on histories.** Independent `differentFullHistories` distinguishes the extra second components of two one-step histories via `extraHeadPayload`. `equalDeploymentDespiteDifferentPayload` proves their deployed spines equal by reduction because the same first component supplies compatibility. Thus preservation of `compatibility(step)` and exact occurrence/position transport do not imply reconstruction of all Step data. These are two simultaneously established facts, not a failed proof of a stronger injectivity claim.
2. **General positive paths may return to the same State.** The independent two-step path is indexed false→false and passes through true. Its complete raw source/terminal nodes agree, while positions remain distinct. Canonical historical cursor non-return theorems cannot be asserted for all newly defined generic positive histories. A finite witnessed cycle in this State relation is allowed; it does not identify its positions or establish infinite periodic execution.

The original payload-loss countermodel in the referee probe may be integrated as a new result only with its authorship/checking provenance distinguished: a coordinator's independent reread/spot check should be named before assigning that original referee-authored result independent review. It is not needed to accept the implementation's already explicit limited preservation claim.

## Plan completion and remaining work

Lot 2's five obligations are met at this interface: deployment nodes/compatibilities retained; nil separated from positive paths; deployment composition with explicit endpoint reindexing; closure from a concrete chosen witness; later historical enrichment. The author's four required models are implemented and compiled in their targeted build; independent probes corroborate their relevant distinctions with different data.

“Generation” here means construction of finite histories/spines from admitted step witnesses, optionally from a separately supplied global continuation. It does not manufacture an admissible Step, a target state or a closing witness from the primitive sorts alone. “Formation” is the specified state-node/step compatibility interface, without additional freshness or provenance-production axioms. That is the announced relative scope, not universal generation of arbitrary primitives.

Full signature transports, history-operation transport laws, complete interior/final role grammar, rigidity, and the general coupled turning problem with several successors remain outside this review. No statement of universal minimality, global nonperiodicity, or generic Step reconstruction is justified. No new T1/T3 promotion is appropriate. The independent code establishes precise models and constructive proofs, not exhaustive enumeration.

Accept the new formal claims as T2, independent AI referee named, human check pending, subject to coordinator repository-wide validation. No generated map/document/dashboard review or global build is implied by this source report.

Owned files: `design-check.md`, `IndependentProbes.lean.in`, `independent-probes.log`, and this report in `research/agents/referee-positive-generation/`.

## Final documentary and map review

2026-10-09. Read the current `labyrinth/knowledge.json` and `labyrinth/sota.json` for lot 2, including its eight new T2 nodes, three separating dead ends, source node and updated `q.positive-generation`/`q.multiple-generation`. Read `docs/formation-et-generation-positives.fr.md` and the amended continuation plan, including the completed second tranche.

Independent `CheckGenerationMap.ps1` passed: **8 T2 nodes and 32 exact source references**, with matching SOTA statements, named review state, existing evidence files and valid link targets. The question's statement also agrees exactly with its SOTA row. Output is saved in `generation-map-check.log`. Manual review accepts the stated hypotheses, consumed data and links at their aggregate declaration scope: composition uses the terminal deployment agreement; closing uses the position map and closing-shape reconstruction; historical enrichment uses the positive constructor and existing historical bridge. The separating claims are correctly restricted to their concrete models.

`q.positive-generation` is answered **only relative to the received State/node/Step signature**. Its note explicitly retains received primitives/steps and excludes generic Step reconstruction and universal nonperiodicity. The full families/operations transport and role grammar remain open. `q.multiple-generation` remains open for the general coupled turning mechanism, while acknowledging that the present signature permits distinct successors. No new theorem is presented as T1, literature-verified or human-checked. The original referee-authored payload-loss model is not separately promoted to a map result; its scope diagnostic supports the already qualified deployment claim.

Two wording clarifications were requested, applied by the coordinator, and reread:

- Plan §5 obligation 1 now says **“les témoins de compatibilité de chaque pas”**, rather than suggesting all Step data are retained in the spine.
- The reader document now says **“linkAt lit les nœuds et le témoin de compatibilité du pas situé à une occurrence”**, matching its actual `SuccessiveLink` return type.

The remaining prose correctly distinguishes Step data retained in the history from compatibility readouts retained in the spine, concrete Type data from proposition-valued existence, optional globally chosen continuation from general admissibility, and generic state returns from strict historical cursor non-return. The document's node/provenance retention statement concerns complete node readouts; it expressly does not impose a law of provenance propagation between arbitrary steps. Its iteration counter is qualified as a constructor input, not a new structural quantity definition. The plan closes only lots 1 and 2.

The first attempt to read the active snapshot fell in the coordinator's archival/recreation interval and found no file; it was not counted as a successful validation. After the exact file was recreated, a fail-fast independent read/hash check confirmed **30 files and zero SHA256 mismatches** in `generation-source-snapshot.json`. This certifies file identity at that snapshot, not new semantic claims. The prior documents/snapshot are preserved in the coordinator's iteration archive.

Read the global verification log tail: coordinator build succeeds with 109 jobs and the repository script verifies 112 Lean files. The coordinator also reports that `rebuild -VerifyLean` recompiles these 38 independent probes successfully. These are coordinator checks; no new Lean execution or complete build was run by this referee for the documentary review. No dashboard rendering or visual QA is asserted here.

**Final verdict: ESTABLISHED in lot 2's relative path/deployment scope. Both documentary clarifications are applied and accepted; no unresolved correction remains.** T2 with independent AI review; human verification pending. Additional referee-owned files: `CheckGenerationMap.ps1` and `generation-map-check.log`.
