# Frozen capacity-comparison protocol (v4)

This directory freezes a new comparison protocol after completion of the
generic checked runtime and its exact learned future divergence. It contains
no confirmatory result.

The protocol corrects three mismatches in v1 without rewriting v1:

- the exact aligned and bypass updates now exist and are named;
- the four-case declared current domain is separated from the eight-case
  learning domain;
- the nonempty future request, target contract, closed runtime API and terminal
  certificate are fixed as shared material.

The six baseline interfaces and eight reported capacities are fixed before
adapter implementation. A later confirmatory run is forbidden until a new
adapter manifest pins six executable adapters, their single command, the
repository commit and every shared-material hash. The output must validate
against `comparison-result-schema.json`.

The protocol compares capacities, not execution cost. It permits only the
already proved factorization limitation for current-table-only extensional
verifiers. A missing adapter, an interface that does not express a capability,
or a missing certificate is never promoted to a universal negative claim.

Validate the frozen pre-confirmatory package from the repository root:

```text
python3 scripts/check-neural-comparison-protocol-v4.py
```
