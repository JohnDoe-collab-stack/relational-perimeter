# Compiled parameterized checker scaling campaign (v7)

This version is the confirmatory P8 cost campaign for the parameterized family
compiled from the Lean repository. It is distinct from the fixed-artifact v5
measurement and from the Python-model v2/v3 campaigns.

The frozen protocol precedes the run. Each process initializes one master
checked agent, then successively consumes six updates. At every step the
incremental and complete checker receive the same target artifact and the same
source state; the next source is the accepted incremental successor. The Lean
type of the paired result identifies the incremental and complete successors.

The campaign reports all observations, including unfavorable ones. In
particular, structural certificate reuse and a practical elapsed-time gain are
different claims. The latter is accepted only by the rule fixed in
`scaling-protocol.json`.

Frozen command:

```text
py -3 scripts/run-compiled-parameterized-neural-scaling-v7.py --protocol experiments/constitutive-neural-alignment/v7/scaling-protocol.json --output experiments/constitutive-neural-alignment/v7/scaling-results.json
```

Validation command:

```text
py -3 scripts/check-compiled-parameterized-neural-scaling-v7.py --self-test
```
