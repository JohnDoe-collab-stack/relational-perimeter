#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -n "${RELATIONAL_PERIMETER_PYTHON:-}" ]]; then
  python_command=("$RELATIONAL_PERIMETER_PYTHON")
elif command -v python3 >/dev/null 2>&1; then
  python_command=(python3)
else
  echo 'Python 3 is required for import-boundary checks' >&2
  exit 1
fi
exec "${python_command[@]}" "$repo_root/scripts/check-import-boundaries.py" "$@"
