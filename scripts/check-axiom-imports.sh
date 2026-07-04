#!/usr/bin/env bash
# check-axiom-imports.sh
#
# Fast pre-commit safeguard against the recurring CI failure where AxiomAudit.lean
# gains a `#print axioms Foo.bar` pin for a module that is NOT in AxiomAudit's
# import closure (the "pins added, import forgotten" bug). The library fast-path
# build does not compile AxiomAudit, so the resulting "Unknown constant" only
# surfaces in the slow CsdLeanTests / CI run.
#
# This checks, statically (grep only, no Lean build, a few seconds), that every
# constant pinned in AxiomAudit.lean has a defining file inside AxiomAudit's
# TRANSITIVE import closure (matching how Lean actually resolves names, so no
# false positives on transitively-imported modules).
#
# It is a heuristic (locates the leaf declaration name by grep); it does NOT
# verify #guard_msgs axiom strings -- CI, or a local `lake build
# CsdLean4.Tests.AxiomAudit`, remains the definitive pin gate.
#
# Usage:  bash scripts/check-axiom-imports.sh
# Exit 0 = every pinned constant is reachable from AxiomAudit's imports.
# Exit 1 = a pinned constant's module is not in the import closure.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
AA="CsdLean4/Tests/AxiomAudit.lean"

# --- Transitive import closure of AxiomAudit, as repo-relative file paths. ---
declare -A inclosure
queue=()
imp_to_file() { sed 's/^import //; s/\./\//g; s/$/.lean/'; }
while read -r f; do
  [ -n "$f" ] || continue
  inclosure["$f"]=1; queue+=("$f")
done < <(grep -E '^import CsdLean4' "$AA" | imp_to_file)

i=0
while [ "$i" -lt "${#queue[@]}" ]; do
  f="${queue[$i]}"; i=$((i+1))
  [ -f "$f" ] || continue
  while read -r g; do
    [ -n "$g" ] || continue
    if [ -z "${inclosure[$g]:-}" ]; then inclosure["$g"]=1; queue+=("$g"); fi
  done < <(grep -E '^import CsdLean4' "$f" | imp_to_file)
done

# --- Check every pinned constant's defining module is in the closure. ---
failures=0
while read -r name; do
  [ -n "$name" ] || continue
  leaf="${name##*.}"
  deffiles="$(git grep -lE "^(theorem|lemma|def|noncomputable def|abbrev|structure|inductive|instance)[[:space:]]+${leaf}([[:space:](:{]|$)" -- CsdLean4 2>/dev/null || true)"
  [ -z "$deffiles" ] && continue          # unlocatable form -> cannot adjudicate
  ok=0
  while read -r f; do
    [ -n "${inclosure[$f]:-}" ] && { ok=1; break; }
  done <<< "$deffiles"
  if [ "$ok" -eq 0 ]; then
    printf 'MISSING IMPORT: pinned constant %s\n   defined in: %s\n   -> add its module (or a module importing it) to %s\n' \
      "$name" "$(echo "$deffiles" | tr '\n' ' ')" "$AA"
    failures=$((failures+1))
  fi
done < <(grep -oE '#print axioms[[:space:]]+[A-Za-z0-9_.]+' "$AA" | awk '{print $NF}' | sort -u)

if [ "$failures" -gt 0 ]; then
  echo "check-axiom-imports: FAIL ($failures pinned constant(s) not in AxiomAudit's import closure)"
  exit 1
fi
echo "check-axiom-imports: OK (every locatable pinned constant is in AxiomAudit's import closure)"
