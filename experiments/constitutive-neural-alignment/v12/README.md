# Causal complete-property scaling v12

This directory defines the successor to the historical v11 campaign. The v11
result remains unchanged and negative for causal succession: its measured state
obligations were substantive, but its transition relation did not produce the
next state from the preceding one.

V12 measures a distinct compiled family. Its command contains no target state.
The transition kernel executes an action from the exact checked source memory,
produces an effect from that action, constructs the successor from that effect,
and gives the same source and command independently to the incremental checker
and full recheck. The next trace step consumes the installed incremental
successor. The effective transition executes exactly one live step: the
protocol rejects any accepted observation whose target register length is not
the source register length plus one.

This generated family is only the workload of the scaling campaign. It does
not replace the repository's independent learned artifact and establishes no
claim about how that learned artifact was produced.

The protocol is presently a draft. It must be frozen by
`scripts/freeze-causal-complete-property-scaling-v12.py` at a clean, recoverable
commit before any confirmatory run. Until then, executable invocations are
smoke tests only and no `scaling-results.json` may be created here.
