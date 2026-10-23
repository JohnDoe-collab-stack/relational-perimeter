# V11 complete-property scaling result

## Frozen identity

- protocol: `compiled-complete-property-scaling-v11`
- frozen source revision: `f9471ceab8d1af85d51eae8d2c6ab31959f41686`
- protocol-freeze revision: `bdf4a0136b366bceed409c3bd99c1459fa89cd9b`
- protocol SHA-256: `3123982e2ec5da661cceb57e6bb8bed51c0d3633dda7d40602d3b148f1ed14fd`
- result SHA-256: `8438e66f5aab002c78a3b538ef187e4f412fa36c889564c54b08245be8d80048`
- result status: `confirmatory-complete`
- repetitions: 25 accepted out of 25 attempted

The negative control was rejected. Every measured run reports the paired
incremental and independent-full-recheck paths on the same source and complete
property. No measured row was removed.

## Measured medians

| size | trace | incremental cumulative ns | full recheck cumulative ns | incremental / full |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 3 | 257,700 | 68,500 | 3.76 |
| 4 | 6 | 2,358,400 | 154,600 | 15.25 |
| 8 | 9 | 13,710,900 | 307,800 | 44.54 |
| 16 | 12 | 161,963,300 | 892,300 | 181.51 |
| 32 | 15 | 3,475,853,300 | 3,289,900 | 1,056.52 |

The neural-node count, causal-graph node and edge counts, complete obligations,
future trace, and serialized certificate sizes grow across the registered
points. Local cases transport a nonempty fragment set and extended cases
recompute a nonempty fragment set. Peak resident memory is recorded for every
accepted run.

## Preregistered decision

`pre_registered_practical_gain` is `false`. The incremental checker is slower
than the complete recheck at every registered size, so the preregistered P8/S6
practical-gain criterion is not met. This unfavorable observation is retained
unchanged. It does not weaken the formal soundness, relative completeness, or
equivalence theorems, and it establishes no asymptotic law.

Structural proof reuse is measured, but it is not a time or memory economy in
this implementation and campaign. No document may present fragment transport
counts as a practical gain.
