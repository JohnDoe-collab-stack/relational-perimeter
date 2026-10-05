#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
if command -v lake >/dev/null 2>&1; then
  lake_path="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_path="$HOME/.elan/bin/lake"
elif [[ -n "${USERPROFILE:-}" ]] && command -v cygpath >/dev/null 2>&1 &&
    [[ -x "$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe" ]]; then
  lake_path="$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe"
else
  echo 'lake was not found' >&2
  exit 1
fi
python_path="${RELATIONAL_PERIMETER_PYTHON:-python3}"
# One parser and one frozen diagnostic inventory for both entry points.
exec "$python_path" scripts/expected_failure_diagnostics.py --lake "$lake_path"
