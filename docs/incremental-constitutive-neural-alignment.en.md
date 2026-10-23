# Incremental constitutive neural alignment

## Scientific status

Proposed claim identifier:
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`.

This is the English canonical passage prepared before the evidence commit,
claim registration, and independent audits. It describes the results present
in the working tree; it does not yet declare C18 satisfied and does not replace
the exact revision that must be recorded after the freeze.

## Canonical claim

In this framework, alignment is not defined by conformity with an output table
alone. It is relative to a received and fixed constitutive meta-contract that
separates admitted operational contracts, authorized transitions between them,
and the obligations that must be preserved or rechecked. For a serialized
neural artifact accepted by the initial checker and any finite update sequence
accepted by the dependent checker, the runtime continues only the chain that
was actually certified: decoding of the received artifact, execution of the
neural mechanism, proposal, action, effect, successor, contract transition,
and future obligations. Every step consumes exactly the certified state
produced by the preceding step; a rejected update supplies no successor that
the closed API can install.

Certification does not receive its conclusion as input. Contract obligations
are defined independently of checker success, instantiated on the produced
state and occurrences, and then decided by executable analyses. The complete
checker recomputes every fragment; the incremental checker transports only
fragments outside the affected cone and recomputes the others. On their stated
local domain, their acceptance results are equivalent and their successful
runs produce the same certified successor.

The learned instance closes a separation that observation of current behavior
alone cannot see. Two updates carry the same admitted intent and produce the
same table over the entire declared current domain. Every verifier that factors
exclusively through that table therefore returns the same verdict for both.
Nevertheless, the aligned update actually consumes the required authorization
resource and is accepted and installed; the bypass update does not consume it,
is rejected for a missing constitutive dependency, and cannot be installed. An
explicit nonempty future continuation then computes a conforming outcome for
the aligned update and an outcome incompatible with the contract for the
purely simulated, effect-free bypass.

Forgetting remains distinct from that separation. In the corresponding public
instance, two states in which historical origin is genuinely present enter an
executed forgetting operation; it produces a common reduced memory, preserves
exactly the covered futures, and makes reconstruction of the removed origin
from that memory impossible. The result therefore identifies neither grouping,
forgetting, nor equality of source states.

## Exact hypotheses and scope

The claim is conditional on the following elements:

- the meta-contract, operational contract, initial admission, requirements,
  contexts, future schema, and transition rules are received; execution does
  not produce their normative justification;
- artifacts and updates are serialized data with no embedded target
  certificate; decoding must validate the expected ports, weights,
  chronological references, and contract names;
- the current domain and causal basis used by local decisions are finite and
  decidable; this finiteness does not restrict quantification over every finite
  accepted update sequence or every covered future;
- the guarantees concern traces accepted by `checkInitial`, the dependent
  checker, and `checkUpdates`. They do not say that every update is acceptable;
- future preservation is relative to the declared `FutureContract` and its
  exact realizations, not to every conceivable observation;
- the aligned/bypass comparison concerns the learned artifact, four-case
  current domain, and nonempty continuation recorded in the evidence package;
- simulation of the rejected candidate is pure and counterfactual. It is not a
  runtime effect path.

## Separation of responsibilities

The chain explicitly distinguishes:

| Status | Content |
| --- | --- |
| Received and fixed | Meta-contract, admitted contract, requirements, contexts, authorizations, serialized artifacts, and future schema. |
| Produced by execution | Decoding, neural activations, transformations, proposals, actions, effects, successors, local decisions, and affected cones. |
| Derived | State certificates, checker soundness, incremental/complete equivalence, contract preservation, and runtime reachability. |
| Authorized | Contract transitions and updates admitted by the meta-contract; admission remains distinct from satisfaction of the target contract. |
| Transported | Fragments outside the cone, persistent obligations, and futures explicitly covered by the contract. |
| Recomputed | Affected fragments, invalidated obligations, and decisions specific to the new state. |
| Forgotten | Historical origin removed by the authorized forgetting execution. |
| Irrecoverable | An origin distinction for which no reconstruction from reduced memory can satisfy both required return laws. |

## Main formal references

| Result | Declaration or module |
| --- | --- |
| Finite dependent trace and alignment of every step | `checkedTrace_constitutivelyAligned`, `checkUpdates_sound` in [CheckedUpdateTrace.lean](../RelationalPerimeter/Agents/Neural/CheckedUpdateTrace.lean) |
| Contract preservation throughout every runtime history | `EveryRuntimeStepPreservesContracts` in [CertifiedRuntime.lean](../RelationalPerimeter/Agents/Neural/CertifiedRuntime.lean) |
| Rejection with no installable successor | `submitUpdate_rejected_cannot_install` in [CertifiedRuntime.lean](../RelationalPerimeter/Agents/Neural/CertifiedRuntime.lean) |
| Complete and incremental checkers | `checkReferenceUpdate`, `checkIncrementalUpdate` in [ReferenceChecker.lean](../RelationalPerimeter/Agents/Neural/ReferenceChecker.lean) and [IncrementalChecker.lean](../RelationalPerimeter/Agents/Neural/IncrementalChecker.lean) |
| Local incremental/complete equivalence | `incrementalAndReferenceAcceptance_equivalent` in [IncrementalReferenceEquivalence.lean](../RelationalPerimeter/Agents/Neural/IncrementalReferenceEquivalence.lean) |
| Latent-bypass separation | `constitutiveChecker_detectsLatentBypass` in [FiniteCounterfactualDivergence.lean](../RelationalPerimeter/Agents/Neural/FiniteCounterfactualDivergence.lean) |
| Agreement of every verifier limited to the current table | `everyLearnedRuntimeCurrentVerifierAgrees` in [LearnedContractFutureDivergence.lean](../RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean) |
| Aligned installation and bypass rejection | `submitUpdate_learned_aligned_exact`, `submitUpdate_learned_bypass_rejected` in [LearnedRuntimeAdapter.lean](../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean) |
| Divergence under the exact future contract | `learnedOperationalFutureDivergence` in [LearnedContractFutureDivergence.lean](../RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean) |
| Executed forgetting, preserved futures, and irrecoverable origin | `public_executed_forgetting_outputs_equal`, `public_executed_forgetting_preserves_future`, `public_executed_forgetting_origin_not_recoverable` in [PublicExactForgetting.lean](../RelationalPerimeter/Agents/Neural/PublicExactForgetting.lean) |
| Separation for every exact realization and preservation of every covered finite sequence | `learnedEveryExactRealizationSeparatesAlignedFromBypass`, `learnedExecutedFutureForgetting_preserves_every_finite_future` in [LearnedFutureConstitutiveClosure.lean](../RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean) |
| Joint certificate over the same learned lineage | `learnedConstitutiveAlignmentClosure` in [LearnedFutureConstitutiveClosure.lean](../RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean) |

These declarations remain subject to the repository's complete gates and the
future evidence commit. The table identifies claim entry points; it does not
replace an audit of their transitive dependencies.

## Comparative evidence package

### Capability comparison

The
[`constitutive-neural-capability-comparison-v6`](../experiments/constitutive-neural-alignment/v6/comparison-protocol.json)
protocol freezes one learned artifact, one exact update pair, six typed
adapters, and eight capabilities. The six classes are extensional verification
of current behavior, interventional causal analysis of a fixed network,
pre-execution action shielding, guaranteed self-adaptive systems, incremental
neural verification with proof reuse, and certificate propagation through a
deployment chain.

The current status is strict: v6 is a historical protocol whose fingerprints
no longer match the current candidate sources. No v6 confirmatory run has been
executed and no comparative result file exists. A new version must freeze the
adapters and their references before any confirmatory execution. No general
superiority, baseline incapacity, or novelty conclusion may therefore be
drawn. The only formal contrast already closed at this level concerns
verifiers whose verdict factors exclusively through the finite current table:
they cannot distinguish the two candidates, whereas the constitutive checker
distinguishes them through executed dependency and the future contract.

### Scaling of the compiled checker

The historical
[`compiled-parameterized-neural-scaling-v8`](../experiments/constitutive-neural-alignment/v8/SCALING_ANALYSIS.md)
campaign runs the same compiled Lean checker at seven sizes from 0 to 80, with
five measured repetitions and 210 accepted updates. It establishes actual
structural reuse: on a local transition at size 80, 83 fragments are
transported and one is recomputed.

It establishes no practical time gain. At size 80, the median incremental
trace takes 70,777.626 ms, versus 10.522 ms for the complete recheck; the
pre-registered gain criterion is false. No asymptotic law, general resource
saving, or generalization to other families is claimed. Its fingerprints are
preserved rather than rewritten; they do not validate the current candidate.
The complete v8 source snapshot was not committed and is no longer
reconstructible from Git history; the gate can therefore revalidate only the
protocol, raw results, their aggregation, and their archived fingerprints, not
re-elaborate that exact snapshot. The exploratory campaign rerun on the current
candidate confirms structural reuse but remains unfrozen, lacks a usable memory
measurement, and has unfavorable incremental timings. P8 and S6 therefore
remain open for a new preregistered campaign over a recoverable source commit.

## Explicit exclusions

This claim does not establish:

- discovery of human values or moral correctness of the meta-contract;
- universal alignment of every AI system or neural network;
- robustness to inputs, futures, or transformations outside the contract;
- that current behavioral equivalence alone entails danger;
- that every non-constitutive method fails or that a baseline cannot express
  the same obligations;
- a time or memory gain for the present incremental checker;
- a general complexity bound;
- a novelty conclusion before the comparative run and independent audits of
  the evidence revision.

The formal result is a relative guarantee: under the fixed meta-contract and
declared interfaces, the closed API continues only states whose required
constitutive chain was produced and certified, and the learned instance
exhibits a latent bypass that the current table alone cannot distinguish.
