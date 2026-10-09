#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
manifest="scripts/stratification.tsv"

if [[ -n "${RELATIONAL_PERIMETER_PYTHON:-}" ]]; then
  python_command=("$RELATIONAL_PERIMETER_PYTHON")
elif command -v python3 >/dev/null 2>&1; then
  python_command=(python3)
else
  echo 'Python 3 is required for stratification checks' >&2
  exit 1
fi

lean_imports() {
  "${python_command[@]}" "$repo_root/scripts/lean_imports.py" "$1"
}

if [[ "${1:-}" == "--self-test" ]]; then
  fixture="$(mktemp)"
  trap 'rm -f "$fixture"' EXIT
  printf '%s\n' \
    '/- import Forbidden.Direct /- import Forbidden.Nested -/ -/' \
    '-- import Forbidden.Line' \
    'import' \
    '  Allowed.Split' \
    '/- comment -/' \
    'import Allowed.Direct -- import Forbidden.Trailing' > "$fixture"
  parsed="$(lean_imports "$fixture")" || exit 1
  mapfile -t actual <<< "$parsed"
  [[ "${actual[*]}" == 'Allowed.Split Allowed.Direct' ]] || {
    echo "stratification parser self-test failed: ${actual[*]}" >&2
    exit 1
  }
  exit 0
fi

declare -A stratum status responsibility file_for imports
line_number=0
while IFS=$'\t' read -r module layer migration role extra; do
  line_number=$((line_number + 1))
  module="${module%$'\r'}"; layer="${layer%$'\r'}"; migration="${migration%$'\r'}"; role="${role%$'\r'}"
  [[ -z "$module" || "${module:0:1}" == '#' ]] && continue
  [[ -z "${extra:-}" && -n "$role" ]] || { echo "$manifest:$line_number: expected four tab-separated fields" >&2; exit 1; }
  [[ -z "${stratum[$module]+x}" ]] || { echo "$manifest:$line_number: duplicate module $module" >&2; exit 1; }
  [[ " U F G S B E M R X P K D Q N API A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 " == *" $layer "* || "$layer" =~ ^M([0-9]|1[0-9])$ || "$layer" =~ ^T[0-7]$ || "$layer" =~ ^H([0-9]|1[0-9]|2[0-9]|3[0-2])$ ]] || { echo "$manifest:$line_number: unknown stratum $layer" >&2; exit 1; }
  [[ "$migration" == enforced ]] || { echo "$manifest:$line_number: every production module must be enforced, found $migration" >&2; exit 1; }
  if [[ "$layer" == API ]]; then
    [[ "$module" == RelationalPerimeter ]] || { echo "$manifest:$line_number: API is reserved for the public root" >&2; exit 1; }
  elif [[ "$module" == RelationalPerimeter ]]; then
    echo "$manifest:$line_number: public root must use API" >&2; exit 1
  fi
  if [[ "$layer" =~ ^T[0-7]$ ]]; then
    [[ "$module" == RelationalPerimeter.Relativity.ExactArithmetic || "$module" == RelationalPerimeter.Relativity.Arithmetic.* || "$module" == RelationalPerimeter.Relativity.Analysis.* ]] || { echo "$manifest:$line_number: numerical stratum outside numerical modules" >&2; exit 1; }
  elif [[ "$module" == RelationalPerimeter.Relativity.ExactArithmetic || "$module" == RelationalPerimeter.Relativity.Arithmetic.* || "$module" == RelationalPerimeter.Relativity.Analysis.* ]]; then
    echo "$manifest:$line_number: unclassified numerical relativity module" >&2; exit 1
  fi
  if [[ "$layer" =~ ^H([0-9]|1[0-9]|2[0-9]|3[0-2])$ ]]; then
    [[ "$module" == RelationalPerimeter.Relativity || "$module" == RelationalPerimeter.Relativity.Production.* || "$module" == RelationalPerimeter.Relativity.Reconstruction.* || "$module" == RelationalPerimeter.Relativity.Continuation.* ]] || { echo "$manifest:$line_number: local-production stratum outside its modules" >&2; exit 1; }
  elif [[ "$module" == RelationalPerimeter.Relativity || "$module" == RelationalPerimeter.Relativity.Production.* || "$module" == RelationalPerimeter.Relativity.Reconstruction.* || "$module" == RelationalPerimeter.Relativity.Continuation.* ]]; then
    echo "$manifest:$line_number: unclassified local-production module" >&2; exit 1
  fi
  stratum[$module]="$layer"; status[$module]="$migration"; responsibility[$module]="$role"
done < "$manifest"

mapfile -t tracked_production_files < <(git ls-files --cached --others --exclude-standard -- '*.lean' | grep -v '^Tests/' | sort)
production_files=()
for relative in "${tracked_production_files[@]}"; do
  [[ -f "$relative" ]] || continue
  production_files+=("$relative")
done
for relative in "${production_files[@]}"; do
  module="${relative%.lean}"; module="${module//\//.}"; module="${module//\\/.}"
  file_for[$module]="$relative"
  parsed="$(lean_imports "$relative")" || exit 1
  direct=()
  if [[ -n "$parsed" ]]; then mapfile -t direct <<< "$parsed"; fi
  for dependency in "${direct[@]}"; do
    if [[ "$module" == RelationalPerimeter.Relativity.Production.* && ( "$dependency" == RelationalPerimeter.Relativity.Reconstruction.* || "$dependency" == RelationalPerimeter.Relativity.Continuation.* ) ]] ||
        [[ "$module" == RelationalPerimeter.Relativity.Reconstruction.* && "$dependency" == RelationalPerimeter.Relativity.Continuation.* ]]; then
      echo "reversed encounter layer: $module -> $dependency" >&2
      exit 1
    fi
    [[ "$dependency" != Tests && "$dependency" != Tests.* ]] || {
      echo "production module imports a test: $module -> $dependency" >&2
      exit 1
    }
  done
  imports[$module]="$(printf '%s\n' "${direct[@]:-}")"
done

missing=(); stale=()
for module in "${!file_for[@]}"; do [[ -n "${stratum[$module]+x}" ]] || missing+=("$module"); done
for module in "${!stratum[@]}"; do [[ -n "${file_for[$module]+x}" ]] || stale+=("$module"); done
[[ ${#missing[@]} -eq 0 ]] || { echo "unclassified production modules: ${missing[*]}" >&2; exit 1; }
[[ ${#stale[@]} -eq 0 ]] || { echo "manifest modules without source: ${stale[*]}" >&2; exit 1; }

allowed_dependency() {
  if [[ "$1" == API ]]; then
    [[ "$2" != API ]]
    return
  fi
  if [[ "$1" =~ ^T[0-7]$ ]]; then
    local numerical_rank="${1#T}"
    [[ "$2" =~ ^T[0-7]$ ]] && (( ${2#T} < numerical_rank ))
    return
  fi
  if [[ "$1" =~ ^H([0-9]|1[0-9]|2[0-9]|3[0-2])$ ]]; then
    local physical_rank="${1#H}"
    if [[ "$2" =~ ^H([0-9]|1[0-9]|2[0-9]|3[0-2])$ ]]; then
      (( ${2#H} < physical_rank ))
    else
      [[ "$2" == U || "$2" == F || "$2" =~ ^T[0-6]$ ]]
    fi
    return
  fi
  # Machine layers cannot depend on themselves or later machine layers.
  if [[ "$1" =~ ^M([0-9]|1[0-9])$ ]]; then
    local rank="${BASH_REMATCH[1]}"
    if [[ "$2" =~ ^M([0-9]|1[0-9])$ ]]; then
      (( BASH_REMATCH[1] < rank ))
    else
      [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 " == *" $2 "* ]]
    fi
    return
  fi
  case "$1" in
    U) [[ "$2" == U ]] ;;
    F) [[ " U F " == *" $2 "* ]] ;;
    G) [[ " U G " == *" $2 "* ]] ;;
    S) [[ " U G S " == *" $2 "* ]] ;;
    B) [[ " U F G S B " == *" $2 "* ]] ;;
    E) [[ " U G S B E " == *" $2 "* ]] ;;
    M) [[ " U G S B E M " == *" $2 "* ]] ;;
    R) [[ " U F G S B E R " == *" $2 "* ]] ;;
    X) [[ " U G S R X " == *" $2 "* ]] ;;
    P) [[ " U G S E R X P " == *" $2 "* ]] ;;
    K) [[ " U K " == *" $2 "* ]] ;;
    D) [[ " U G S E R X P K D " == *" $2 "* ]] ;;
    Q) [[ " U F G S B E M R X P K D Q " == *" $2 "* ]] ;;
    N) [[ " U G S B E M R X P K D Q N " == *" $2 "* ]] ;;
    A0) [[ " U F G S B E M R X P K D Q N " == *" $2 "* ]] ;;
    A1) [[ " U F G S B E M R X P K D Q N A0 " == *" $2 "* ]] ;;
    A2) [[ " U F G S B E M R X P K D Q N A0 A1 " == *" $2 "* ]] ;;
    A3) [[ " U F G S B E M R X P K D Q N A0 A1 A2 " == *" $2 "* ]] ;;
    A4) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 " == *" $2 "* ]] ;;
    A5) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 " == *" $2 "* ]] ;;
    A6) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 " == *" $2 "* ]] ;;
    A7) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 " == *" $2 "* ]] ;;
    A8) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 " == *" $2 "* ]] ;;
    A9) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 " == *" $2 "* ]] ;;
    A10) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 " == *" $2 "* ]] ;;
    A11) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 " == *" $2 "* ]] ;;
    A12) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 " == *" $2 "* ]] ;;
    A13) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 " == *" $2 "* ]] ;;
    A14) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 " == *" $2 "* ]] ;;
    A15) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 " == *" $2 "* ]] ;;
    A16) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 " == *" $2 "* ]] ;;
    A17) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 " == *" $2 "* ]] ;;
    *) return 1 ;;
  esac
}

for root in "${!stratum[@]}"; do
  queue=("$root"); head=0
  declare -A seen_path=(["$root"]="$root")
  while (( head < ${#queue[@]} )); do
    current="${queue[$head]}"; head=$((head + 1))
    while IFS= read -r dependency; do
      [[ -n "$dependency" && -n "${stratum[$dependency]+x}" ]] || continue
      path="${seen_path[$current]} -> $dependency"
      allowed_dependency "${stratum[$current]}" "${stratum[$dependency]}" || {
        echo "forbidden stratification path (${stratum[$current]} -> ${stratum[$dependency]}): $path" >&2
        exit 1
      }
      if [[ -z "${seen_path[$dependency]+x}" ]]; then seen_path[$dependency]="$path"; queue+=("$dependency"); fi
    done <<< "${imports[$current]}"
  done
  unset seen_path
done

public_roots=(SegmentedResidualRole AbstractSegmentedTurning ExactTypeTransport StrongPerimetralTurning RelationalPerimeter)
declare -A reachable=()
queue=(); head=0
for root in "${public_roots[@]}"; do
  [[ -n "${stratum[$root]+x}" ]] || { echo "missing public root in manifest: $root" >&2; exit 1; }
  reachable[$root]=1; queue+=("$root")
done
while (( head < ${#queue[@]} )); do
  current="${queue[$head]}"; head=$((head + 1))
  while IFS= read -r dependency; do
    [[ -n "$dependency" && -n "${stratum[$dependency]+x}" ]] || continue
    if [[ -z "${reachable[$dependency]+x}" ]]; then reachable[$dependency]=1; queue+=("$dependency"); fi
  done <<< "${imports[$current]}"
done
orphans=()
for module in "${!stratum[@]}"; do [[ -n "${reachable[$module]+x}" ]] || orphans+=("$module"); done
[[ ${#orphans[@]} -eq 0 ]] || { echo "production modules unreachable from public Lake roots: ${orphans[*]}" >&2; exit 1; }

echo "Verified stratification inventory: ${#stratum[@]} production modules, all enforced, no orphan."
