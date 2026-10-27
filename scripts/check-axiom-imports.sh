#!/usr/bin/env bash
# check-axiom-imports.sh
#
# Fast pre-commit safeguard against the recurring CI failure where an AxiomAudit
# file gains a `#print axioms Foo.bar` pin for a module that is NOT in the audit's
# import closure (the "pins added, import forgotten" bug). Since the G9 split
# (2026-08-06) pins live in the per-part files under Tests/AxiomAudit/; the
# closure starts at the umbrella (which imports every part; parts import the
# CsdLean4 root), and pins are collected from umbrella + parts. The library fast-path
# build does not compile AxiomAudit, so the resulting "Unknown constant" only
# surfaces in the slow CsdLeanTests / CI run.
#
# This checks, statically (grep only, no Lean build), that every constant pinned in
# AxiomAudit.lean has a defining file inside AxiomAudit's TRANSITIVE import closure
# (matching how Lean actually resolves names, so no false positives on
# transitively-imported modules).
#
# Cost: one `git grep` over CsdLean4 builds a definition index (declaration name ->
# defining files), and each pin is a lookup in it. Until 2026-10-27 the script ran one
# full-tree `git grep` PER PIN; at 6,865 pins that was ~1,480 s of every CI run
# (the "a few seconds" this header used to promise had stopped being true). The index
# reproduces the old per-pin match exactly: the old pattern
#   ^(theorem|...|instance)[[:space:]]+<leaf>([[:space:](:{]|$)
# matches a line iff the maximal run of characters after the keyword and its
# whitespace that contains none of space, `(`, `:`, `{` is exactly <leaf>; that run
# is the index key. Same output, same exit codes.
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
# Match legacy `import`, and the Lean 4 module-system forms `public import` / `meta import`
# / `public meta import`, stripping the modifier prefix before turning the module path into a file.
imp_re='^(public )?(meta )?import CsdLean4'
imp_to_file() { sed -E 's/^(public )?(meta )?import //; s/\./\//g; s/$/.lean/'; }
while read -r f; do
  [ -n "$f" ] || continue
  inclosure["$f"]=1; queue+=("$f")
done < <(grep -E "$imp_re" "$AA" | imp_to_file)

i=0
while [ "$i" -lt "${#queue[@]}" ]; do
  f="${queue[$i]}"; i=$((i+1))
  [ -f "$f" ] || continue
  while read -r g; do
    [ -n "$g" ] || continue
    if [ -z "${inclosure[$g]:-}" ]; then inclosure["$g"]=1; queue+=("$g"); fi
  done < <(grep -E "$imp_re" "$f" | imp_to_file)
done

# --- The definition index, built once: declaration name -> defining files. ---
# Keys are restricted to the leaf alphabet [A-Za-z0-9_]: a pin's leaf is drawn from it (the
# pin regex below), so a token outside it can never be looked up, and the restriction keeps
# every key safe as a bash associative-array subscript. Files per key are newline-joined in
# byte order, the order `git grep -l` printed them in.
kw_re='^(theorem|lemma|def|noncomputable def|abbrev|structure|inductive|instance)[[:space:]]+'
declare -A deffiles_of
while IFS=$'\t' read -r tok file; do
  [ -n "$tok" ] || continue
  if [ -n "${deffiles_of[$tok]:-}" ]; then
    deffiles_of["$tok"]+=$'\n'"$file"
  else
    deffiles_of["$tok"]="$file"
  fi
done < <(git grep -E "${kw_re}[^[:space:](:{]" -- CsdLean4 2>/dev/null \
  | sed -nE 's/^([^:]*):(theorem|lemma|def|noncomputable def|abbrev|structure|inductive|instance)[[:space:]]+([^[:space:](:{]+).*$/\3\t\1/p' \
  | grep -E $'^[A-Za-z0-9_]+\t' \
  | LC_ALL=C sort -u)

# --- Check every pinned constant's defining module is in the closure. ---
failures=0
while read -r name; do
  [ -n "$name" ] || continue
  leaf="${name##*.}"
  if [ -n "$leaf" ]; then
    deffiles="${deffiles_of[$leaf]:-}"
  else
    # A pin ending in `.` has an empty leaf; the index cannot key it, so fall back to the
    # original per-pin search for this one name (never taken on the current pins).
    deffiles="$(git grep -lE "${kw_re}([[:space:](:{]|$)" -- CsdLean4 2>/dev/null || true)"
  fi
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
done < <(grep -ohE '#print axioms[[:space:]]+[A-Za-z0-9_.]+' "$AA" CsdLean4/Tests/AxiomAudit/*.lean | awk '{print $NF}' | sort -u)

if [ "$failures" -gt 0 ]; then
  echo "check-axiom-imports: FAIL ($failures pinned constant(s) not in AxiomAudit's import closure)"
  exit 1
fi
echo "check-axiom-imports: OK (every locatable pinned constant is in AxiomAudit's import closure)"
