#!/usr/bin/env bash
set -euo pipefail

failure=0
while IFS= read -r -d '' file; do
  begin_count=$(grep -c 'AXIOM_AUDIT_BEGIN' "$file" || true)
  end_count=$(grep -c 'AXIOM_AUDIT_END' "$file" || true)
  final_line=$(awk 'NF { line=$0 } END { print line }' "$file")
  if [[ "$begin_count" -ne 1 || "$end_count" -ne 1 ||
        "$final_line" != '/- AXIOM_AUDIT_END -/' ]]; then
    echo "$file: begin=$begin_count end=$end_count final=$final_line" >&2
    failure=1
  fi
done < <(find . -path './.lake' -prune -o -name '*.lean' -print0)

if [[ "$failure" -ne 0 ]]; then
  exit 1
fi

build_log=$(mktemp)
trap 'rm -f "$build_log"' EXIT
if ! lake build 2>&1 | tee "$build_log"; then
  exit 1
fi
if grep -q 'depends on axioms:' "$build_log"; then
  echo "At least one audited declaration depends on axioms." >&2
  exit 1
fi
if grep -q '^warning:' "$build_log"; then
  echo "The Lean build emitted at least one warning." >&2
  exit 1
fi

echo "Axiom-audit structure and warning-free build output passed."
