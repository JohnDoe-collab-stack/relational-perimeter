# Local-certificate-reuse scaling campaign (v3)

Version 2 is preserved unchanged. It conservatively compared every declared
reused fragment and therefore measured only a roughly twofold work reduction.
Version 3 matches the source-indexed incremental runtime: the accepted source
certificate belongs to the exact source object, and the target is formed only
by applying a serialized suffix delta to that source. The unchanged prefix is
transported; only the affected suffix is rechecked.

The complete path validates the same well-formedness property on the same
materialized target from zero. Deterministic checked units are the primary
measure. Timings remain platform-dependent observations.

The protocol was frozen before the v3 confirmatory run. Its manifest records
the protocol, runner, results, and the preserved final mutation campaign.
