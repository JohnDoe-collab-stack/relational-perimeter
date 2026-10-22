# Confirmatory v7 run outcome

The single v7 confirmatory command was executed on 2026-10-22. The generated
family members through size 80 completed, but the warmup process for size 160
exceeded the frozen 120-second per-process budget. Its observed resident memory
remained below the two-gigabyte limit. The runner therefore stopped with:

```text
PARAMETERIZED_NEURAL_SCALING_V7_ERROR: warmup failed at size 160
```

No `scaling-results.json` was created. Partial in-memory observations were not
reclassified as confirmatory evidence. The frozen v7 protocol, runner and input
manifest remain unchanged. A later protocol version is required for any new
campaign.
