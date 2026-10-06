# One master, one integrated execution

## What is constructed

The machine receives the existing master, a SAT formula, a frontier of
constituted contexts and read permissions. It receives neither a branch
partition nor an expected width.

An advance makes one live production. Its discovered selector opens the
received SAT contexts. Relation search on those contexts constructs both the
retained frontier and its routing program. The next memory keeps that frontier:
the next search therefore reads what the preceding search actually retained.

The program configures finite gates. Later packets use those gates and routes,
without restarting SAT relation search or historical assignment readers.

## Chain and files

```text
Four unchanged primitive files
  -> constitution and role history
  -> UnifiedMaster.publicInstance
       -> received live state
       -> received SAT context as input to that same master
            -> shared live production
            -> opening
            -> context relation search
            -> typed transport code
            -> retained frontier + configured circuit
            -> next memory
            -> subsequent requests
```

Production lives in `RelationalPerimeter/Computation/Machine/`:

- `FrontierCircuit.lean` realizes typed reduction code as routing and gates.
- `MasterRuntime.lean` initializes from the master and connects search,
  circuit and successor.
- `MasterContract.lean` fixes the combined contract and shared execution.
- The other modules supply the live-contract and canonical-memory proofs.
  Their production roots import no tests.

Checks live in `Tests/Machine/`. The older direct demonstration remains a
separate check, not a second production entry.

## What the proofs establish

`AcceptedFrontierCode` is indexed by source and target contexts. Absorption
constructors contain the relation witness actually found. The normalizer
produces the code inside its search branches. Preservation is derived from
that code, not supplied as an independent record field.

`lowerFrontier_exact` proves, for every admissible typed continuation,
equality between the circuit acting on its readings and the readings of its
transported continuation. `ScopedProblemProduction.route_exact` connects this
equality to the packet actually returned by the installed routing.
`circuit_preserves_SAT` separately connects that
action to criterion preservation. This transport is not source equality.

`advance_exact` connects the new runtime to the rich contract.
`advance_frontier_is_produced` pins the next frontier to the actual reduction.
`advance_preserves_SAT` preserves viability in both directions.

`all_futures_exact` covers every finite request list, including arbitrary
interleavings of advances, samples, pulses, SAT routes and refusals.
`run` uses one paired transition per request. The split `next` and
`event` callbacks are only the comparison specification.

This exactness compares the rich live engine and its reduction, with the same
SAT algorithm in both contracts. SAT routing correctness is proved separately
by the action theorems above, not inferred from equal measured widths.

## One and two branches on the same master

`Tests/Machine/MasterIntegration.lean` uses one
`UnifiedMaster.publicInstance 0`, the same formula
`[[positive 12, positive 1, positive 2]]`, selector 12 and finder.
Only the received decision on variable 1 differs.

When that decision is true, search retains one branch, and the circuit routes
the transformed branch's packet to its retained slot. When it is false,
both directed searches fail and two branches remain; the circuit preserves
two slots. Every child is proved viable. Failure of this particular finder
does not imply impossibility of every future relation.

The checks also prove that sources remain distinct, later packets use the
produced circuit, and all futures remain exact.

## Contract, memory and width

The combined contract adds `route slot bits` and `sampleProblem` to the
existing live requests. Routing is admitted when the source slot exists and
the bit count respects the read permissions. This does not certify SAT for
every arbitrary packet: the semantic theorem concerns typed continuation
readings.

The complete SAT frontier remains in memory because later search reads its
residual formulas and decisions. The existing live reduction still applies to
the engine. Minimality under its own contract does not automatically establish
minimality of the combined memory.

Three readings remain distinct:

| Reading | Measured object |
| --- | --- |
| 2^n | Constituted profiles of the binary master |
| Retained SAT frontier | Contexts carried after local relation search |
| Bank cells | Finite outputs of the live contract |

The original master's exponential results and `iff` are preserved. This SAT
extension is not presented as width one for every formula or a complete
polynomial-time SAT solver.

## Verification and hardware boundary

From the root: `lake build`, then `scripts/verify.ps1` or
`bash scripts/verify.sh`. Both include
`scripts/check-integrated-machine-codegen.py`.

The compiled-C check covers named local producer boundaries: one live and one
SAT production per advance, one opening, normalization and configuration per
SAT production, and one paired transition per request. It excludes SAT search
and assignment callbacks from configured packet handling. It proves neither
total physical cost, a global memory bound nor hardware realization.

This is a software runtime with finite circuits represented by constructors,
not an FPGA or already constructed new hardware. Routing is still structurally
interpreted. Physical incarnation and its cost remain separate obligations.
