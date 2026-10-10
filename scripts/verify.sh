#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if [[ -n "${RELATIONAL_PERIMETER_PYTHON:-}" ]]; then
  python_command=("$RELATIONAL_PERIMETER_PYTHON")
elif command -v python3 >/dev/null 2>&1; then
  python_command=(python3)
else
  echo 'Python 3 is required for documentation and compiled-code checks' >&2
  exit 1
fi
"${python_command[@]}" scripts/check-scientific-docs.py --self-test
"${python_command[@]}" scripts/check-scientific-docs.py --static

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

mapfile -t tracked_lean_files < <(git ls-files --cached --others --exclude-standard -- '*.lean' | sort)
lean_files=()
for file in "${tracked_lean_files[@]}"; do
  [[ -f "$file" ]] || continue
  lean_files+=("$file")
done

bash scripts/check-import-boundaries.sh --self-test
bash scripts/check-import-boundaries.sh
bash scripts/check-import-boundaries.sh scripts/constitutive-normalizer-core-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/executed-history-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/measured-accounting-import-boundaries.txt
bash scripts/check-stratification.sh --self-test
bash scripts/check-stratification.sh

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

forbidden_terms='\b(axiom|unsafe|noncomputable|Classical|propext|Quot\.sound|native_decide|implemented_by|sorry|admit)\b'
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

expected_modules=$((${#lean_files[@]} - 1))
if [[ "$(grep -c 'ALL_CONSTANTS_OK ' "$build_log" || true)" != 1 ]] ||
    ! grep -Eq "ALL_CONSTANTS_OK constants=[0-9]+ modules=$expected_modules generatedExceptions=[0-9]+ writtenExceptions=0$" <(tr -d '\r' < "$build_log"); then
  echo 'Missing or incomplete exhaustive constant audit (including all test modules)' >&2
  exit 1
fi
"${python_command[@]}" scripts/check-scientific-docs.py --lean
"${python_command[@]}" scripts/check-unified-codegen.py
"${python_command[@]}" scripts/check-agent-codegen.py
"${python_command[@]}" scripts/check-documentary-codegen.py
"${python_command[@]}" scripts/run-documentary-smoke.py
"${python_command[@]}" scripts/check-documentary-master-codegen.py
"${python_command[@]}" scripts/run-documentary-master-smoke.py
"${python_command[@]}" scripts/check-documentary-dossier-codegen.py
"${python_command[@]}" scripts/run-documentary-dossier-smoke.py
"${python_command[@]}" scripts/check-documentary-deduction-codegen.py
"${python_command[@]}" scripts/run-documentary-deduction-smoke.py
"${python_command[@]}" scripts/check-documentary-program-codegen.py
"${python_command[@]}" scripts/run-documentary-program-smoke.py
"${python_command[@]}" scripts/check-documentary-adaptive-codegen.py
"${python_command[@]}" scripts/run-documentary-adaptive-smoke.py
"${python_command[@]}" scripts/check-documentary-memory-codegen.py
"${python_command[@]}" scripts/run-documentary-memory-smoke.py
"${python_command[@]}" scripts/check-documentary-checkpoint-codegen.py
"${python_command[@]}" scripts/run-documentary-checkpoint-smoke.py
"${python_command[@]}" scripts/check-documentary-portable-store-codegen.py
"${python_command[@]}" scripts/run-documentary-portable-store-smoke.py
"${python_command[@]}" scripts/check-restoration-components-codegen.py
"${python_command[@]}" scripts/run-restoration-components-smoke.py
"${python_command[@]}" scripts/check-documentary-control-codegen.py
"${python_command[@]}" scripts/run-documentary-control-smoke.py
"${python_command[@]}" scripts/check-master-recipes-codegen.py
"${python_command[@]}" scripts/run-master-recipes-smoke.py
"${python_command[@]}" scripts/check-assignment-codegen.py
"${python_command[@]}" scripts/run-assignment-restart-smoke.py
"${python_command[@]}" scripts/check-sequential-codegen.py
"${python_command[@]}" scripts/run-sequential-restart-smoke.py
"${python_command[@]}" scripts/check-state-assembly-codegen.py
"${python_command[@]}" scripts/run-state-assembly-smoke.py
"${python_command[@]}" scripts/check-continuation-signature-codegen.py
"${python_command[@]}" scripts/check-variable-master-codegen.py
"${python_command[@]}" scripts/check-integrated-machine-codegen.py

bash scripts/check-expected-failures.sh

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
echo "Verified ${#lean_files[@]} Lean files: build, constructivity, audit blocks, import boundaries, and migration boundaries are clean."
