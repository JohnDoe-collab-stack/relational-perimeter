#!/usr/bin/env bash
set -euo pipefail

print_only=false
if [[ "${1:-}" == "--print-only" ]]; then
  print_only=true
fi

render() {
  git ls-files --cached --others --exclude-standard |
    LC_ALL=C sort |
    while IFS= read -r path; do
      case "$path" in
        MANIFEST.sha256|.lake/*|*/.lake/*|.git/*|*/.git/*) continue ;;
      esac
      [[ -f "$path" ]] || continue
      hash=$(sed 's/\r$//' "$path" | sha256sum | awk '{print $1}')
      printf '%s  %s\n' "$hash" "$path"
    done
}

if [[ "$print_only" == true ]]; then
  render
else
  temporary=$(mktemp)
  trap 'rm -f "$temporary"' EXIT
  render > "$temporary"
  mv "$temporary" MANIFEST.sha256
  trap - EXIT
  echo "Wrote MANIFEST.sha256 with $(wc -l < MANIFEST.sha256 | tr -d ' ') entries."
fi
