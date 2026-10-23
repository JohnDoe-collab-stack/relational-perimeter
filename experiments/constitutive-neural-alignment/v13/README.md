# Oracle-independent complete comparison v13

V13 corrects the two F5 defects without rewriting v10.  The reference
combination is computed from four declared local observations and its
transitive generated-code closure is rejected if it reaches the runtime,
incremental or complete checker verdicts.  The executable emits only values
recomputed during its run.  Consequences available solely as Lean proofs are
listed by declaration in `evidence-ledger.json` and are not presented as IO
observations.

The protocol is currently a draft.  No confirmatory result is present or
claimed.  After an explicitly authorized stable source commit, run the freeze
command recorded in `comparison-protocol.json`, review and commit the frozen
protocol, and only then run its one-shot confirmatory command.  Existing v10
inputs and outputs remain hash-pinned historical evidence.
