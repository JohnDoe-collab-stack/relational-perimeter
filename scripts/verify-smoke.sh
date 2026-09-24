#!/usr/bin/env bash
set -euo pipefail

temporary=$(mktemp)
trap 'rm -f "$temporary"' EXIT

lake env lean Smoke/EndogenousOperationalTrace.lean 2>&1 | tee "$temporary"
observed=$(grep '^SMOKE_TRACE_V1 ' "$temporary" || true)
expected=$(tr -d '\r\n' < Smoke/endogenous-operational-trace-v1.expected)

if [[ $(grep -c '^SMOKE_TRACE_V1 ' "$temporary" || true) -ne 1 ]] ||
   [[ "$observed" != "$expected" ]]; then
  echo "The executable smoke trace does not match its frozen output." >&2
  exit 1
fi

echo "Non-confirmatory executable smoke trace passed."
