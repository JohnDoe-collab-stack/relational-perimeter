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
"${python_command[@]}" scripts/check-neural-c1-c17-regression-floor.py
"${python_command[@]}" scripts/check-neural-g1-g10-regression-floor.py
"${python_command[@]}" scripts/check-neural-block-negative-fixtures.py
"${python_command[@]}" scripts/check-neural-comparison-protocol-v4.py --self-test
"${python_command[@]}" scripts/check-neural-comparison-adapters-v6-archive.py --self-test
"${python_command[@]}" scripts/check-neural-comparison-adapters-v6-archive.py
"${python_command[@]}" scripts/check-neural-v9-v10-archive.py --self-test
"${python_command[@]}" scripts/check-neural-v9-v10-archive.py
"${python_command[@]}" scripts/check-compiled-neural-checker-measurement.py --self-test
"${python_command[@]}" scripts/check-compiled-neural-checker-measurement.py
"${python_command[@]}" scripts/check-compiled-parameterized-neural-scaling-v8.py --archive-metadata --self-test
"${python_command[@]}" scripts/check-compiled-parameterized-neural-scaling-v8.py --archive-metadata
"${python_command[@]}" scripts/check-complete-property-scaling-v11.py --allow-draft --self-test
"${python_command[@]}" scripts/check-causal-complete-property-scaling-v12.py --require-results --self-test
"${python_command[@]}" scripts/check-independent-capability-comparison-v13.py --allow-results --self-test
"${python_command[@]}" scripts/check-independent-capability-comparison-v13.py --allow-results
"${python_command[@]}" scripts/check-independent-neural-artifact.py
"${python_command[@]}" scripts/check-final-neural-campaign.py

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
bash scripts/check-import-boundaries.sh scripts/godel-runtime-core-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/godel-positive-core-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/godel-operational-h1-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/godel-operational-closure-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/godel-perimetral-import-boundaries.txt
bash scripts/check-import-boundaries.sh scripts/godel-theory-progression-foundation-import-boundaries.txt
for boundary in tarski-continuation tarski-diagonal tarski-operational-closure tarski-ha; do
  bash scripts/check-import-boundaries.sh "scripts/$boundary-import-boundaries.txt"
done
bash scripts/check-import-boundaries.sh scripts/continuation-exact-separation-import-boundaries.txt
for boundary in continuation-directed-incompatibility continuation-directed-obstruction positive-directed-composition; do
  bash scripts/check-import-boundaries.sh "scripts/$boundary-import-boundaries.txt"
done
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
"${lake_command[@]}" -K 'moreLeanArgs=["-M=8192"]' build 2>&1 | tee "$build_log"
if grep -F 'warning:' "$build_log"; then
  echo 'Lean warning detected in lake build output' >&2
  exit 1
fi
if grep -E 'depends on axioms:|sorryAx' "$build_log"; then
  echo 'axiom audit failure detected in lake build output' >&2
  exit 1
fi

if [[ "$(grep -c 'ALL_CONSTANTS_OK ' "$build_log" || true)" != 1 ]] ||
    ! grep -Eq 'ALL_CONSTANTS_OK constants=[0-9]+ modules=[0-9]+ generatedExceptions=[0-9]+ writtenExceptions=0$' <(tr -d '\r' < "$build_log"); then
  echo 'Missing or incomplete primary exhaustive constant audit' >&2
  exit 1
fi
"${python_command[@]}" scripts/check-executable-constant-audits.py --self-test
"${python_command[@]}" scripts/check-executable-constant-audits.py
"${python_command[@]}" scripts/check-scientific-docs.py --lean
"${python_command[@]}" scripts/check-unified-codegen.py
"${python_command[@]}" scripts/check-agent-codegen.py
"${python_command[@]}" scripts/check-continuation-signature-codegen.py
"${python_command[@]}" scripts/check-variable-master-codegen.py
"${python_command[@]}" scripts/check-integrated-machine-codegen.py
"${python_command[@]}" scripts/check-independent-comparison-codegen.py

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
