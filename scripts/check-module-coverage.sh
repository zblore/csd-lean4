#!/usr/bin/env bash
# check-module-coverage.sh — every tracked Lean file is reachable from a declared root.
#
# Cost (2026-11-05): the closure walk used to test membership with `grep -Fxq` on a growing
# "seen" file and run `sed | tr | sed` per module — four process spawns per module, quadratic
# in the seen-file scan. At 1,021 modules that passed 580 s on Windows Git Bash. Membership is
# now a bash associative array and the imports of every file are read in ONE pass, so the walk
# spawns a fixed number of processes. Same roots, same import regex, same output and exit codes.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

tmp="${TMPDIR:-/tmp}/csd-module-coverage.$$"
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT

git ls-files 'CsdLean4/**/*.lean' 'CsdLean4/Basic.lean' | sort -u > "$tmp/all"

# Imports of every tracked file plus the roots, in one pass: "file<TAB>imported/file.lean".
declare -A imports_of
roots=(CsdLean4.lean CsdLean4/Basic.lean CsdLean4/Tests/AxiomAudit.lean CsdLean4/Tests/Examples.lean)
while IFS=$'\t' read -r f g; do
  imports_of["$f"]+="$g"$'\n'
done < <(cat "$tmp/all" <(printf '%s\n' "${roots[@]}") | sort -u \
  | xargs -d '\n' grep -HE '^(public )?(meta )?import CsdLean4(\.[A-Za-z0-9_]+)+' 2>/dev/null \
  | sed -nE 's/^([^:]*):(public )?(meta )?import (CsdLean4(\.[A-Za-z0-9_]+)+).*$/\1\t\4/p' \
  | awk -F'\t' '{ gsub(/\./, "/", $2); print $1 "\t" $2 ".lean" }')

# Import closure from the four declared library/test roots.
declare -A seen
queue=("${roots[@]}")
i=0
while [ "$i" -lt "${#queue[@]}" ]; do
  file="${queue[$i]}"; i=$((i+1))
  [ -n "${seen[$file]:-}" ] && continue
  seen["$file"]=1
  [ -f "$file" ] || { echo "FAIL missing declared/imported module file: $file"; exit 1; }
  while IFS= read -r g; do
    [ -n "$g" ] && [ -z "${seen[$g]:-}" ] && queue+=("$g")
  done <<< "${imports_of[$file]:-}"
done

printf '%s\n' "${!seen[@]}" | sort -u > "$tmp/reachable"
comm -23 "$tmp/all" "$tmp/reachable" > "$tmp/missing"
if [ -s "$tmp/missing" ]; then
  echo 'FAIL Lean files outside the union of declared library/test roots:'
  sed 's/^/  /' "$tmp/missing"
  exit 1
fi
echo "check-module-coverage: OK ($(wc -l < "$tmp/all" | tr -d ' ') modules reachable)"
