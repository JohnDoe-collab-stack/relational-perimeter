#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if command -v lake >/dev/null 2>&1; then
  lake_command=(lake)
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_command=("$HOME/.elan/bin/lake")
elif [[ -n "${USERPROFILE:-}" ]] && command -v cygpath >/dev/null 2>&1 &&
    [[ -x "$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe" ]]; then
  lake_command=("$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe")
else
  echo 'lake was not found in PATH or in the default elan installation' >&2
  exit 1
fi

mapfile -t lean_files < <(find . -path './.lake' -prune -o -type f -name '*.lean' -print | sort)

for file in "${lean_files[@]}"; do
  begin_count="$(grep -cF -- '/- AXIOM_AUDIT_BEGIN -/' "$file" || true)"
  end_count="$(grep -cF -- '/- AXIOM_AUDIT_END -/' "$file" || true)"
  if [[ "$begin_count" != 1 || "$end_count" != 1 ]]; then
    echo "$file: expected exactly one AXIOM_AUDIT block" >&2
    exit 1
  fi
  last_nonempty="$(awk 'NF { line=$0 } END { print line }' "$file" | tr -d '\r')"
  if [[ "$last_nonempty" != '/- AXIOM_AUDIT_END -/' ]]; then
    echo "$file: AXIOM_AUDIT block is not at end of file" >&2
    exit 1
  fi
done

forbidden_terms='^[[:space:]]*(axiom|unsafe)[[:space:]]|\b(noncomputable|Classical|propext|Quot\.sound|native_decide|implemented_by|sorry|admit)\b'
if grep -nER "$forbidden_terms" --include='*.lean' --exclude-dir='.lake' .; then
  echo 'forbidden Lean construct detected' >&2
  exit 1
fi

forbidden_architecture='\b(NPAndOrP|RequestProject|LoggedAlgebra|ConstitutivePersistence|IteratedConstitutivePersistence|StructuralEntrypoint)\b|^[[:space:]]*(import|open)[[:space:]]+(Alignment|Foundations)(\.|[[:space:]]|$)'
if grep -nER "$forbidden_architecture" --include='*.lean' --exclude-dir='.lake' .; then
  echo 'rejected migration dependency detected' >&2
  exit 1
fi

build_log="$(mktemp)"
trap 'rm -f "$build_log"' EXIT
"${lake_command[@]}" build 2>&1 | tee "$build_log"
if grep -F 'warning:' "$build_log"; then
  echo 'Lean warning detected in lake build output' >&2
  exit 1
fi
if grep -E 'depends on axioms:|sorryAx' "$build_log"; then
  echo 'axiom audit failure detected in lake build output' >&2
  exit 1
fi

for file in "${lean_files[@]}"; do
  relative="${file#./}"
  olean=".lake/build/lib/lean/${relative%.lean}.olean"
  if [[ ! -f "$olean" ]]; then
    echo "$file: lake build produced no corresponding olean" >&2
    exit 1
  fi
done

if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git diff --check
elif command -v git.exe >/dev/null 2>&1 && command -v wslpath >/dev/null 2>&1; then
  git.exe -C "$(wslpath -w "$repo_root")" diff --check
else
  echo 'git worktree metadata could not be resolved' >&2
  exit 1
fi
echo "Verified ${#lean_files[@]} Lean files: build, constructivity, audit blocks, and migration boundaries are clean."
