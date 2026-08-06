#!/usr/bin/env bash
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

tmp="${TMPDIR:-/tmp}/csd-module-coverage.$$"
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT

git ls-files 'CsdLean4/**/*.lean' 'CsdLean4/Basic.lean' | sort -u > "$tmp/all"

# Import closure from the four declared library/test roots.
printf '%s\n' CsdLean4.lean CsdLean4/Basic.lean CsdLean4/Tests/AxiomAudit.lean CsdLean4/Tests/Examples.lean > "$tmp/queue"
: > "$tmp/seen"
while read -r file; do
  grep -Fxq "$file" "$tmp/seen" && continue
  echo "$file" >> "$tmp/seen"
  [ -f "$file" ] || { echo "FAIL missing declared/imported module file: $file"; exit 1; }
  sed -nE 's/^(public )?(meta )?import (CsdLean4(\.[A-Za-z0-9_]+)+).*$/\3/p' "$file" \
    | tr '.' '/' | sed 's/$/.lean/' >> "$tmp/queue"
done < "$tmp/queue"

sort -u "$tmp/seen" > "$tmp/reachable"
comm -23 "$tmp/all" "$tmp/reachable" > "$tmp/missing"
if [ -s "$tmp/missing" ]; then
  echo 'FAIL Lean files outside the union of declared library/test roots:'
  sed 's/^/  /' "$tmp/missing"
  exit 1
fi
echo "check-module-coverage: OK ($(wc -l < "$tmp/all" | tr -d ' ') modules reachable)"
