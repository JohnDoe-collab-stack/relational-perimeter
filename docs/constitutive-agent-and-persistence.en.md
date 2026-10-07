# Constitutive search and restitution agent

This instance extends the existing public calculation with an interactive
session. A request can inspect a production, advance the engine, obtain a
production not yet available, or submit a value for authorization. The received
scope governs replies; their values come from actually produced continuations.
Restart memory supports this work without uniformly recovering the initial
source profile.

This is a symbolic agent constructed in Lean, not a language model, a general
SAT solver or a general human-alignment result. The previous scientific target
and the four foundational modules remain unchanged.

## Input and requirement

`publicAgent input scope selectionCode` receives a nonempty scope of variables
and a selection code. It constructs one public master result and then interprets
that code over its actually constituted roles. A wrong-length code and an empty
scope yield distinct refusals. Decoding traverses one role history without
enumerating profiles.

`InitializationCertificate` connects the exact `prepare` result to the received
scope, decoding of the actual supplied code, and initialized memory.
`Prepared.certificate` combines this agreement with the continuation certificate
on the same master. Code and decoded profile remain in this scientific package,
not in restart memory. Invalid-selection and wrong-length refusals have public
laws.

The scope supplies no expected answer. It determines which variables may be
read, not which variables discovery selects. Different scopes may therefore
change authorization for the same read without changing its truth. Duplicate
variables add no permission.

The requests are:

| Request | Effect |
| --- | --- |
| `advance steps` | Executes the requested real stages. |
| `inspect handle var` | Reads an existing target if the variable is permitted. |
| `obtain handle var` | Produces missing stages, then returns the permitted read. |
| `propose handle var value` | Authorizes only a value equal to the actual read. |

Outside scope, missing target and incorrect value are distinct refusal reasons.
For `obtain`, a permitted variable leads to an available target and its answer:
correctness is not obtained by refusing every request.

## Productions and response guarantees

The initial register contains one component of the normalized target per role,
with its own context and acceptance guarantee. Each resumed stage appends
`production.built.stage.application.output`, the actual stage output. Initial
and resumed targets need not have the same acceptance context. A Boolean read
is not presented as a global SAT proof.

`TargetOrigin` is a witness dependent on the continuation: it identifies the
local production whose output it is, rather than merely attaching a label.
The initial factory requires exact agreement with the executed roles' outputs;
acceptance alone does not permit inserting another continuation. This witness
does not retain the normalized source-profile choice.

Each target's acceptance is obtained by eliminating its `TargetOrigin`: it comes
from the normalization license or the resumed stage output. `AnswerTarget` no
longer stores an independent acceptance proof. This guarantee is then consumed
by the reply criterion.

A numeric handle is a session-local address, not a constituted occurrence by
itself. Resolution constructs a typed reference to an actual target. Appending
preserves old handles; historical-support references are transported by the real
extensions. The readable register size is not independent-obligation width.

`History.realization` forms the rich target support through typed-port
producers, from the actual normalization and stages. Its agreement links every
register reference to the historical reference reading that target.
`History.handle_transport` closes the square between register extension and
support extension; reads, reference injectivity and position shifts are proved
separately. This rich support is not retained in runtime memory.

`HistoricalFormation` follows the support itself, with its ports and formation
tree. Only the initial master/profile pair is given. Normalization, cursor,
components and resumed targets are added by their producers. A support containing
a target reference cannot be declared given with the same values. `MaterialReading`
carries this formation and the actual reads; `RichOperation` carries this reading
and its resulting decision. Its result is eliminated from these objects and then
connected to the runtime result.

With `r` entries and handle `h`, when the variable is permitted and the handle
is missing, `obtain` produces exactly `h + 1 - r` stages and the register reaches
exactly `h + 1` entries. If the handle is already present, no stage is produced.
These laws concern the actual worker's events. A refusal leaves the entire
memory unchanged.

`performCertified` constructs the next memory, event and response witness
together. One local decision is shared between its message and authorization.
`interactionProducer` reads current memory and request through its ports;
`executeProducedInput` returns that whole production. Simple APIs project its
data without running a second decision procedure.

`ResponseEvidence` is a specification independent of the responder: it requires
permission, an occurrence and agreement with its value, or the precise facts
justifying a refusal. It is not defined as “the selected reply is correct”.

## Agreement with the rich history

The scientific source retains the initial profile and resource history. Its
interpreter reads that history's targets, not projected runtime replies.
Transition, event, read and admission laws are proved separately and composed
over every finite request sequence.

Rich reads and authorizations consume the realized support values and then
their agreement with the reduced entries. `FollowedStages` also follows every
internal stage of a request: the certificate does not stop at request boundaries.

Each `InternalStepAgreement` closes agreement with the live production, appended
target and its acceptance. It contains two distinct extensions: the current
engine support extension and the historical target support extension.
`FollowedStages.engineTransport` and `historicalTransport` compose these extensions
through the last state; their reads, injectivity and positions are those of the
realized extensions. The followed events and final memory are proved equal to
those of the actually executed stages.

Rich permissions refer to the received scope; runtime permissions refer to its
resource-carried realization. Their passage has both return laws on witnesses,
not merely two validity implications.

The head uses only current memory and request. No future-request parameter
enters its producer. The certificate closes head exactness, horizon independence
and continuation agreements.

For a positive reply, `ReplyCriterion` requires authorization and acceptance of
its target in its own context. `FiniteResponseCriterion` applies this requirement
to every reply of the real executor. Finite following implies this contract;
`Certificate.satisfaction` consumes that proof. No external acceptance premise
is required from the client.

## Forgetting and scope

`Memory` contains exactly the requirement, live engine and target register.
`Session` contains only that memory. Neither initial code nor an explicit source
profile field is retained there. The scientific `Prepared` package and rich
history are separate from the runtime session and are not consulted to act.

Factorization through the normalized target yields equality of the complete
memories of two provably distinct source profiles. Hence no Lean function from
this memory to the source profile uniformly reconstructs all initializations.
Identical future requests produce identical memories, replies and events;
admissions are preserved and reflected.

Forgetting concerns the initial-profile distinction in this memory under this
contract. It removes neither provenance still needed by discovery nor every
chronological history. It is not a proof of constant physical memory, polynomial
cost or security against external inspection of compiled closures. The register
grows to retain the promised reads.

The compiled-code check excludes rich archives and global profile enumeration
from resumption. The reused engine still builds a local readout of its two
occurrences after the action; this readout does not select discovery. Discovery
has a separate dependency check.

This check covers `Session.execute`, `produce` and `executeAll`, together with
initialization. It follows helpers, aliases and resolved closure applications.
Call bounds concern one entry or one explicit structural unfolding, not a whole
execution of arbitrary length. An unresolved required indirect call fails the
check rather than being assigned zero cost. Expected failures are checked using
Lean JSON diagnostics with frozen file, line, column and characteristic message;
an extra error or printed text does not validate the fixture.

## Declarations and reproduction

All modules are reachable from `import RelationalPerimeter`.

| Obligation | Declaration in `ConstitutiveSearch.Agent` |
| --- | --- |
| Scope formation | `receive`, `Requirement.scope_exact` |
| Actually interpreted codes | `decode_encode`, `initialized_codes_admitted` |
| Initialization certified with its input | `InitializationCertificate`, `Prepared.prepare_exact`, `initialize_invalid_selection`, `initialize_wrong_length` |
| Actual targets | `initialTargets`, `resumedTarget`, `executed_step_register_exact` |
| Shared reply and witness | `performCertified`, `executeProducedInput`, `executedEvidence` |
| Admitted and incorrect replies | `candidate_authorization_exact`, `admitted_inspection_returns`, `correct_candidate_returns`, `incorrect_candidate_refused` |
| Effective obtaining | `obtain_produces_and_returns`, `obtain_register_exact`, `obtain_work_exact` |
| Refusal without a memory change | `refusal_preserves_memory` |
| Handles and references | `History.realization`, `History.handle_transport`, `RegisterRealization.advance_position`, `RegisterRealization.injective`, `runSteps_old_read` |
| Independent local laws | `sourcePerform_exact`, `bridge` |
| Rich formation and reading | `HistoricalFormation`, `HistoricalFormation.not_given`, `MaterialReading`, `RichOperation`, `sourceProduced` |
| Two composed internal transports | `InternalStepAgreement`, `FollowedStages.engineTransport`, `FollowedStages.historicalTransport`, `FollowedStages.execution_exact` |
| Acceptance criterion for all replies | `ReplyCriterion`, `FiniteResponseCriterion`, `Followed.satisfies`, `Certificate.satisfaction` |
| All finite interactions and their internal stages | `FollowedStages`, `all_executed_determinations_followed`, `all_future_requests_exact`, `all_future_events_exact`, `all_future_reads_exact` |
| Two-way admissions | `admissions_forward`, `admissions_reflected`, `admission_received_return`, `admission_realized_return` |
| Whole memory and forgetting | `agent_memory_factors_through_output`, `initial_profile_not_recoverable`, `forgotten_sources_same_future` |
| Closed package | `certify`, `Prepared.certificate` |

The [Agents/Constitutive](../RelationalPerimeter/Agents/Constitutive/PublicInstance.lean)
layer is terminal: earlier modules do not import it. Both stratification checkers
enforce ranks A10 through A16 and public-root rank M19, as recorded in the
[inventory](../scripts/stratification.tsv).

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -File scripts/verify.ps1
git diff --check
```

The three `Tests/ConstitutiveAgent*.lean` files contain positive constructions
and small code-generation checks. The public scenario obtains a missing target,
reuses it without another stage and distinguishes refusal reasons. These finite
evaluations are not a confirmatory complexity experiment.

The audit of commit `f6c6d2c051ae0886056d47cf5357253c137a1319` concludes
`AGENT TARGET REQUIRES CORRECTIONS` and `NO REGRESSION VERIFIED`. The agreements
above implement corrections to its seven findings; local verification is
distinct from a new independent verdict.

[Version française](agent-constitutif-et-persistance.fr.md)
