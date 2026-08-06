#!/usr/bin/env bash
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
ledger="specs/validation-claims.tsv"
fail=0

[ -f "$ledger" ] || { echo "FAIL missing $ledger"; exit 1; }

header="id	module	constant	status	claim_kind	load_bearing	independent_check	finding"
[ "$(head -n 1 "$ledger")" = "$(printf "$header")" ] || { echo "FAIL invalid ledger header"; fail=1; }

dups="$(tail -n +2 "$ledger" | cut -f1 | sort | uniq -d)"
[ -z "$dups" ] || { echo "FAIL duplicate claim ids: $dups"; fail=1; }

while IFS=$'\t' read -r id module constant status kind load check finding extra; do
  [ "$id" = "id" ] && continue
  if [ -n "${extra:-}" ] || [ -z "$finding" ]; then echo "FAIL $id must have exactly 8 populated columns"; fail=1; fi
  case "$status" in validated|qualified|needs-change|specialist-review) ;; *) echo "FAIL $id invalid status $status"; fail=1;; esac
  file="CsdLean4/$module"
  [ -f "$file" ] || { echo "FAIL $id missing module $file"; fail=1; continue; }
  leaf="${constant##*.}"
  if ! grep -Eq "^[[:space:]]*(public[[:space:]]+)?(noncomputable[[:space:]]+)?(theorem|lemma|def|structure|abbrev)[[:space:]]+([A-Za-z0-9_]+\.)*$leaf([[:space:]({:]|$)" "$file"; then
    echo "FAIL $id constant leaf $leaf not declared in $file"
    fail=1
  fi
  [ -n "$load" ] && [ -n "$check" ] || { echo "FAIL $id lacks validation evidence fields"; fail=1; }
  if [ "$status" = "needs-change" ] && [ "$finding" = "-" ]; then echo "FAIL $id needs-change without finding"; fail=1; fi
done < "$ledger"

# G8 facade sync: every ledger module must be imported by the Headlines facade.
while IFS= read -r module; do
  mod="CsdLean4.$(printf '%s' "${module%.lean}" | tr '/' '.')"
  grep -q "^public import $mod\$" CsdLean4/Headlines.lean     || { echo "FAIL Headlines facade missing import of ledger module $mod"; fail=1; }
done < <(tail -n +2 "$ledger" | cut -f2 | sort -u)

count="$(tail -n +2 "$ledger" | wc -l | tr -d ' ')"
[ "$count" -ge 30 ] || { echo "FAIL only $count headline claims; expected at least 30"; fail=1; }

[ "$fail" -eq 0 ] || exit 1
echo "check-validation-ledger: OK ($count linked headline claims)"
