#!/usr/bin/env bash
set -euo pipefail

temporary=$(mktemp)
trap 'rm -f "$temporary"' EXIT
bash scripts/update-manifest.sh --print-only > "$temporary"

if ! cmp -s "$temporary" MANIFEST.sha256; then
  echo "MANIFEST.sha256 does not match the published working tree." >&2
  exit 1
fi

echo "Manifest passed with $(wc -l < "$temporary" | tr -d ' ') entries."
