# Oracle-independent complete comparison v13

V13 preserves the acquired oracle-independence correction without rewriting
v10.  The reference combination is computed from four declared local
observations and its transitive generated-code closure is rejected if it
reaches the runtime, incremental or complete checker verdicts.  The executable
emits only values recomputed during its run.  Consequences available solely as
Lean proofs are listed by declaration in `evidence-ledger.json` and are not
presented as IO observations.

`probe-specification.json` fixes P1--P8 before observation.
`capability-matrix.json` distinguishes certified, observed, absent and
out-of-interface cells.  P2 uses one executed network output for canonical,
genuinely changed admissible, and contract-violating decoder/action paths.  The
admissible change rebuilds its decoder-indexed fragment and the forbidden
change is rejected.  The fragment's produced proposal supplies the action and
effect witnesses installed by the generic incremental checker; the complete
recheck decodes the consumer independently and reconstructs the same installed
chain.  Their accepted successors and certificates agree.  This certifies the
declared exact execution, not installation of a globally changed decoder for
all possible future inputs.  Negative fixtures forbid cross-version fragment
reuse and a forbidden decoder on the canonical path.  P3 uses an exact
artifact-held transition pair.  P4 distinguishes
valid executed forgetting from an incorrect collapse refuted by the produced
nonempty future separator.  P5 uses the installed post-forgetting contract
change and its refusal without successor, not ordinary continuation or
permission alone.  P6 emits incremental and full-recheck observations from one
exact successive update package and binds its fragment assembly, successor and
certificate proofs to that same execution.  P7 and P8 remain not certified
until their respective preregistered runs exist.

`authorized-ablations.json` names semantic exact-diagnostic mutations.  The
campaign does not accept changes to labels as evidence.  The independent
reference method is also subjected to the transitive generated-code oracle
mutation.

The protocol is currently a draft.  No confirmatory result is present or
claimed.  After an explicitly authorized, pushed stable source commit, the
freeze command computes the complete repository-local Lean import closure of
both primary programs and every registered semantic-ablation fixture, plus all
repository-local Python import dependencies of the executable scientific
support scripts, writes their immutable snapshot, and seals the protocol.  The
runner verifies that exact snapshot rather than requiring a later evidence
commit to equal the source commit.  It refuses any modified transitive
dependency before building or executing, rechecks the snapshot after execution,
and requires the execution commit to be recoverable from the frozen remote ref.
It also elaborates
`Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean` under
the 8192 MB Lean limit.  Fully qualified evidence references and their
`#print axioms` checks are therefore executed obligations of the confirmatory
run rather than textual markers accepted only by the JSON validator.
The frozen protocol must be reviewed, committed and pushed before the one-shot
confirmatory run.
Existing v10 inputs and outputs remain hash-pinned historical evidence.
