#!/usr/bin/env bash
# check-import-negative.sh
#
# Asserts that certain modules are ABSENT from another module's transitive import
# closure. The Lean/Mathlib idiom for this is `assert_not_exists`; this repository used
# none, and paid for it -- see below.
#
# WHY. `docs/C1-FORMAL-SUPPORT.md` and `specs/c1-closure-report.md` both state that
# `EffectGleason` is NOT in the transitive import closure of
# `LF6/LocalDeisolationFlow.lean`, so the Born-volume route "never reaches Busch at all".
# That is a load-bearing claim -- it is the difference between "clean axiom bookkeeping"
# and "the route structurally cannot depend on the effect-Gleason result" -- and it was
# established by a ONE-OFF CHECK and then written into prose. Nothing re-checked it. One
# added `public import` would have made both documents false, silently.
#
# This is the same failure this repository keeps finding in different clothes: a true
# claim, checked once, recorded in prose, with no mechanism to notice when it stops being
# true. An import-closure fact is trivially mechanisable, so there is no excuse for
# leaving it to prose.
#
# Declared inventory below is the single source of truth, in the house style.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# "root-module|forbidden-module|why"
PAIRS='
CsdLean4.LF6.LocalDeisolationFlow|CsdLean4.LF2.EffectGleason|C1 Born-volume route must not reach Busch/effect-Gleason
'

fail=0

# Adjacency: "Module<TAB>Import" for every tracked Lean module, in one awk pass.
adj="$(git ls-files 'CsdLean4/**/*.lean' | xargs awk '
  FNR == 1 {
    mod = FILENAME
    sub(/\.lean$/, "", mod)
    gsub(/\//, ".", mod)
  }
  /^[ \t]*(public |private |meta )*import / {
    line = $0
    sub(/^[ \t]*(public |private |meta )*import[ \t]+/, "", line)
    sub(/[ \t]*$/, "", line)
    if (line != "") print mod "\t" line
  }
')"

while IFS='|' read -r root forbidden why; do
  [ -z "${root:-}" ] && continue
  # BFS over the adjacency list.
  reached="$(printf '%s\n' "$adj" | awk -v root="$root" -v target="$forbidden" '
    { edge[$1] = edge[$1] " " $2 }
    END {
      n = 1; queue[1] = root; seen[root] = 1
      for (i = 1; i <= n; i++) {
        split(edge[queue[i]], outs, " ")
        for (j in outs) {
          m = outs[j]
          if (m == "" || seen[m]) continue
          if (m == target) { print "YES"; exit }
          seen[m] = 1; queue[++n] = m
        }
      }
      print "NO"
    }')"
  if [ "$reached" = "YES" ]; then
    if [ "$fail" -eq 0 ]; then
      echo 'FAIL a module reaches a forbidden import. A documented independence claim is'
      echo '     now false. Fix the import, or correct every document asserting it.'
    fi
    echo "  $root  ->  $forbidden"
    echo "      why this was asserted: $why"
    fail=1
  fi
done <<EOF
$(printf '%s\n' "$PAIRS" | grep -v '^[[:space:]]*$')
EOF

if [ "$fail" -eq 0 ]; then
  echo "check-import-negative: OK (all declared import-independence claims hold)"
fi
exit "$fail"
