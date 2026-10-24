# Incremental constitutive neural alignment

## Scientific status

Registered claim identifier:
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`.

The registry already contains this identifier for a historical revision. The
changes in the current candidate nevertheless reopen the scientific reading,
translation comparison, and independent audit. This text describes the
results present in the working tree; it does not declare C18 satisfied and it
does not transfer any earlier verdict to the future evidence revision.

## Canonical claim

In this framework, alignment is not defined by conformity with an output table
alone. It is relative to a received and fixed constitutive meta-contract that
separates admitted operational contracts, authorized transitions between them,
and the obligations that must be preserved or rechecked. For a serialized
neural artifact accepted by the initial checker and any finite update sequence
accepted by the dependent checker, the formalized runtime continues only the
chain that was actually certified: decoding of the received artifact, execution of the
neural mechanism, proposal, action, effect, successor, contract transition,
and future obligations. Every step consumes exactly the certified state
produced by the preceding step; a rejected update supplies no successor that
the closed API can install.

Certification does not receive its conclusion as input. Contract obligations
are defined independently of checker success, instantiated on the produced
state and occurrences, and then decided by executable analyses. The independent
complete-reference checker reconstructs its fragments without receiving the
incremental path's verdict or fragments; the incremental checker transports
licensed fragments outside the affected cone and recomputes the others. On
their stated finite domain, their acceptance results are equivalent and their successful
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
| Produced by execution | Decoding, neural activations, transformations, proposals, actions, effects, successors, and local decisions; the affected cone is then computed from the decoded graph and delta. |
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

These declarations remain subject to the repository's complete gates, linkage
to an existing evidence revision, and distinct validity and scope audits. The
table identifies claim entry points; it replaces neither an audit of their
transitive dependencies nor a generalization beyond the interfaces and
quantifiers actually stated.

## Comparative evidence package

### Capability comparison

The frozen
[`constitutive-neural-oracle-independent-capability-comparison-v13`](../experiments/constitutive-neural-alignment/v13/comparison-protocol.json)
protocol compares nine repository-local computations: six typed adapters, the
relational method, an explicit reference combination, and the independent
complete recheck. Each method receives the interventions, futures, contracts,
and versions that its declared interface can consume. The reference
combination computes its observations without receiving the final verdict or
target certificate as an oracle.

The [v13 confirmatory run](../experiments/constitutive-neural-alignment/v13/COMPARISON_ANALYSIS.md)
emitted all nine preregistered rows and rejected all seventeen semantic
ablations. P2 carries one genuinely changed admissible consumer and one
forbidden consumer from the same exact network execution through the generic
incremental checker and an independent complete recheck; both agree on the
accepted successor and certificate. P3, P4, P5 and P6 also emit their declared
positive and negative outcomes. Competing successes remain visible: the
explicit reference combination and complete recheck also distinguish the
aligned update from the bypass. This closes P7 in its declared
repository-local scope. It establishes neither equivalence with every external
method in the named classes, nor general superiority, baseline incapacity or
scientific novelty.

### Scaling of the compiled checker

The frozen
[`compiled-causal-complete-property-scaling-v12`](../experiments/constitutive-neural-alignment/v12/scaling-protocol.json)
campaign measures the same compiled complete-property checker and an
independent complete recheck on a causal successor chain. Its graphs,
obligations and traces grow; it records every phase cost, memory, serialized
size and the fragments actually transported or recomputed. The
[confirmatory run](../experiments/constitutive-neural-alignment/v12/SCALING_ANALYSIS.md)
accepted all 25 preregistered repetitions across sizes 0, 4, 8, 16 and 32 and
rejected the negative control. Real reuse occurs: the first local transition
at size 32 transports 34 fragments and recomputes two, while an extended
transition transports one and recomputes 35.

The preregistered practical criterion is nevertheless false. Depending on
size, cumulative incremental median time is 3.865 to 760.445 times the
complete-recheck median. P8 is therefore evaluated and P8/S6 are unfavorable
for this implementation; no time or memory gain is claimed. This observational
campaign is neither a Lean theorem nor an asymptotic complexity result.

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
