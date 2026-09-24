#!/usr/bin/env bash
set -euo pipefail

failure=0
while IFS= read -r -d '' document; do
  while IFS= read -r markdown_link; do
    target=${markdown_link#*](}
    target=${target%)}
    target=${target#<}
    target=${target%>}
    path_part=${target%%#*}
    case "$path_part" in
      ''|http://*|https://*|mailto:*) continue ;;
    esac
    if [[ ! -e "$(dirname "$document")/$path_part" ]]; then
      echo "$document: missing local target $target" >&2
      failure=1
    fi
  done < <(grep -oE '\[[^]]+\]\([^)]+\)' "$document" || true)
done < <(find . -path './.lake' -prune -o -name '*.md' -print0)

if [[ "$failure" -ne 0 ]]; then
  exit 1
fi

echo "Local Markdown links passed."
