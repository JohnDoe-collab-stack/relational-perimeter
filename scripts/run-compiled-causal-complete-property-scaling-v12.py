#!/usr/bin/env python3
"""Run the frozen v12 causal complete-property campaign.

The aggregation and resource-monitoring machinery is deliberately reused from
the already audited v11 runner.  Only the protocol identity, executable, and
the additional causal observation fields change.  The Lean binary remains the
sole implementation of both checkers.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEGACY = ROOT / "scripts/run-compiled-complete-property-scaling-v11.py"
SPEC = importlib.util.spec_from_file_location("complete_property_v11_runner", LEGACY)
if SPEC is None or SPEC.loader is None:
    raise SystemExit("CAUSAL_COMPLETE_PROPERTY_SCALING_V12_ERROR: v11 runner unavailable")
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)

RUNNER.PROTOCOL_ID = "compiled-causal-complete-property-scaling-v12"
RUNNER.EXECUTABLE_NAME = "compiled_causal_complete_property_neural_scaling"
RUNNER.__file__ = str(Path(__file__).resolve())
RUNNER.INTEGER_FIELDS = RUNNER.INTEGER_FIELDS + (
    "source_register_length", "target_register_length",
    "transition_force_checksum",
)

if __name__ == "__main__":
    RUNNER.main()
