#!/usr/bin/env bash
set -euo pipefail

pattern='(^|[^[:alnum:]_])(noncomputable|unsafe|axiom|sorry|admit|Classical|propext|Quot\.sound)([^[:alnum:]_]|$)'

if find . -path './.lake' -prune -o -name '*.lean' -print0 |
    xargs -0 grep -nE "$pattern"; then
  echo "Constructivity scan failed." >&2
  exit 1
fi

echo "Constructivity scan passed."

