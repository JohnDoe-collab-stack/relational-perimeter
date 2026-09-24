#!/usr/bin/env bash
set -euo pipefail

temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT

heading_shape() {
  awk '
    /^#+ / {
      match($0, /^#+/)
      depth = RLENGTH
      rest = substr($0, depth + 2)
      number = "-"
      if (match(rest, /^[0-9]+(\.[0-9]+)*\./)) {
        number = substr(rest, 1, RLENGTH - 1)
      }
      print depth ":" number
    }
  ' "$1"
}

code_references() {
  grep -Eo '`[A-Za-z][A-Za-z0-9_./:-]*(\.[A-Za-z0-9_]+)*`' "$1" |
    tr -d '`' |
    LC_ALL=C sort -u
}

verify_pair() {
  local left=$1
  local right=$2
  local name=$3

  heading_shape "$left" > "$temporary/${name}-left-headings"
  heading_shape "$right" > "$temporary/${name}-right-headings"
  if ! cmp -s "$temporary/${name}-left-headings" \
      "$temporary/${name}-right-headings"; then
    echo "Heading structure differs between $left and $right." >&2
    exit 1
  fi

  code_references "$left" > "$temporary/${name}-left-references"
  code_references "$right" > "$temporary/${name}-right-references"
  if ! cmp -s "$temporary/${name}-left-references" \
      "$temporary/${name}-right-references"; then
    echo "Lean/file references differ between $left and $right." >&2
    exit 1
  fi
}

verify_pair \
  docs/relations-primitives-constitution-perimetre.fr.md \
  docs/primitive-relations-and-perimeter-constitution.en.md \
  perimeter
verify_pair \
  docs/decomposition-operationnelle-endogene.fr.md \
  docs/endogenous-operational-decomposition.en.md \
  computation

echo "French/English document structure and code references passed."
