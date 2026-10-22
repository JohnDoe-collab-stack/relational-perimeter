#!/usr/bin/env python3
"""Versioned entrypoint for the v8 compiled Lean scaling campaign.

The measurement implementation is the content-frozen v7 runner.  This wrapper
changes only the accepted protocol identifier and is itself hash-frozen by v8.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


RUNNER = Path(__file__).with_name(
    "run-compiled-parameterized-neural-scaling-v7.py")
SPEC = importlib.util.spec_from_file_location("scaling_v7_engine", RUNNER)
if SPEC is None or SPEC.loader is None:
    raise SystemExit("PARAMETERIZED_NEURAL_SCALING_V8_ERROR: cannot load runner")
ENGINE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ENGINE)
ENGINE.PROTOCOL_ID = "compiled-parameterized-neural-scaling-v8"
ENGINE.__file__ = str(Path(__file__).resolve())
ENGINE.main()
