#!/usr/bin/env bash
# check-vacuity.sh
#
# Finds declarations that NOTHING CONSUMES — the defect class where a statement is
# true, machine-checked, correctly documented, and bears no load.
#
# Motivating case (2026-07-27): `QEC/ErrorDiscretization.lean` landed proving "an
# arbitrary error is a combination of four Paulis" while `QEC/ThreeQubit.lean`
# proved "each of the four is corrected", with NOTHING joining them. Both files
# built, were axiom-pinned, and read correctly. The gap was only visible by asking
# what consumed what. (It was closed by `QEC/SyndromeCollapse.lean`.)
#
# The related historical case is the `:= True` placeholder sweep — vacuity by
# construction. check-claims.sh (2) already guards that. This guards the subtler
# form: a real definition or field that no proof ever mentions.
#
# WHAT IT REPORTS
#   (A) dead definitions   — `def` / `abbrev` names never mentioned outside their
#                            own declaration line
#   (B) dead fields        — `structure` fields never mentioned anywhere
#
# WHAT IT DELIBERATELY DOES NOT REPORT
#   Leaf THEOREMS. A capstone consumed by nothing is the normal, intended shape of
#   a headline result — flagging them would bury the signal. Only *definitions* and
#   *fields* are reported, where "nothing uses this" is genuinely suspicious.
#
# Tests/AxiomAudit.lean is excluded from the "is it used" search ON PURPOSE: an
# axiom pin mentions every headline, so counting pins as consumers would make the
# scan vacuous itself.
#
# Usage:  bash scripts/check-vacuity.sh          (awk only, no Lean build)
#         bash scripts/check-vacuity.sh --strict (exit 1 on findings)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SRC="CsdLean4"
STRICT=0
[ "${1:-}" = "--strict" ] && STRICT=1

echo "check-vacuity: looking for declarations nothing consumes…"

FILES="$(git ls-files "$SRC/**/*.lean" | grep -v 'Tests/AxiomAudit.lean')"
[ -z "$FILES" ] && { echo "  FAIL  no source files found"; exit 1; }

# One pass. Phase 1 records declarations (name -> file:line, kind). Phase 2 walks
# every non-declaration token and marks names used. Anything unmarked is dead.
printf '%s\n' $FILES | xargs awk '
  # ---- declarations ----------------------------------------------------------
  /^[[:space:]]*(public[[:space:]]+)?(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+[A-Za-z_]/ {
      line=$0
      sub(/^[[:space:]]*(public[[:space:]]+)?(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+/,"",line)
      name=line; sub(/[^A-Za-z0-9_'"'"'].*$/,"",name)
      if (name != "" && !(name in declfile)) {
        declfile[name]=FILENAME; declline[name]=FNR; kind[name]="def"
      }
      # The REST of a declaration line is a type signature and legitimately uses
      # other names — mark those used, just not the name being declared.
      rest=$0; gsub(/[^A-Za-z0-9_'"'"']/," ",rest)
      n=split(rest,tok," ")
      for(i=1;i<=n;i++) if (tok[i] != name) used[tok[i]]=1
      next
  }
  # structure / class opens a field block
  /^[[:space:]]*(public[[:space:]]+)?(structure|class)[[:space:]]+[A-Za-z_]/ { instruct=1; next }
  # a blank line or a top-level declaration closes it
  instruct && /^[^[:space:]]/ { instruct=0 }
  instruct && /^[[:space:]]+[a-zA-Z_][A-Za-z0-9_'"'"']*[[:space:]]*:/ {
      f=$0
      sub(/^[[:space:]]+/,"",f); sub(/[[:space:]]*:.*$/,"",f)
      if (f != "" && !(f in declfile)) {
        declfile[f]=FILENAME; declline[f]=FNR; kind[f]="field"
      }
      rest=$0; gsub(/[^A-Za-z0-9_'"'"']/," ",rest)
      n=split(rest,tok," ")
      for(i=1;i<=n;i++) if (tok[i] != f) used[tok[i]]=1
      next
  }
  # ---- usage -----------------------------------------------------------------
  {
      s=$0
      gsub(/[^A-Za-z0-9_'"'"']/," ",s)
      n=split(s,tok," ")
      for(i=1;i<=n;i++) used[tok[i]]=1
  }
  END {
      dead_def=0; dead_field=0
      for (nm in declfile) {
        if (nm in used) continue
        if (kind[nm]=="def")   { print "DEF|"   declfile[nm] ":" declline[nm] "|" nm; dead_def++ }
        else                   { print "FIELD|" declfile[nm] ":" declline[nm] "|" nm; dead_field++ }
      }
  }
' > /tmp/_vacuity.txt 2>/dev/null

# A declaration is only reported once, and usage was marked corpus-wide, so a name
# used in ANY other file (or elsewhere in its own) is already excluded above.
n_def="$(grep -c '^DEF|'   /tmp/_vacuity.txt || true)"
n_fld="$(grep -c '^FIELD|' /tmp/_vacuity.txt || true)"

if [ "$n_def" -gt 0 ]; then
  echo
  echo "  (A) definitions nothing consumes — $n_def:"
  grep '^DEF|' /tmp/_vacuity.txt | sort -t'|' -k2 | while IFS='|' read -r _ loc nm; do
    printf '        %-58s %s\n' "$loc" "$nm"
  done
fi

if [ "$n_fld" -gt 0 ]; then
  echo
  echo "  (B) structure fields nothing consumes — $n_fld:"
  grep '^FIELD|' /tmp/_vacuity.txt | sort -t'|' -k2 | while IFS='|' read -r _ loc nm; do
    printf '        %-58s %s\n' "$loc" "$nm"
  done
fi

echo
total=$((n_def + n_fld))
if [ "$total" -eq 0 ]; then
  echo "check-vacuity: PASS — every definition and field is consumed somewhere"
  exit 0
fi
echo "check-vacuity: $total unconsumed declaration(s)."
echo "  These are NOT automatically defects. Each is a question: is this load-bearing,"
echo "  or is it a statement that reads well and proves nothing downstream?"
[ "$STRICT" -eq 1 ] && exit 1
exit 0
