#!/usr/bin/env bash
# check-labels.sh
#
# CONVENTIONS.md §12 reserves identifier prefixes so that a label means one thing. The paper side
# owns `A D G P R E`; the repository side owns `Q CV CL R- HY TH CR`. Five identifiers (`D1`, `D4`,
# `G6`, `E1`, `C1`) were already carrying two meanings when the policy was written, and they are
# GRANDFATHERED, not renamed — see the ledger in CONVENTIONS §12 for why, and for what each one
# means on each side.
#
# WHY A RATCHET AND NOT A SWEEP. The five collisions have ~790 occurrences across ~150 files, and
# most of them are on labels that are now historical (the D4/G6 composite-tensor debt is resolved —
# Posit 7 / `R-017`; the E1–E5 equilibration arc is complete). Worse, the same strings appear in
# contexts that are not labels at all: `C1`/`C2` are live Lean identifiers (carry chains in the
# adder circuits) and `v1.4.1-c1-complete` is a release tag that `check-claims.sh` verifies against
# CITATION.cff. A regex rename would break compiled code and a guard, to tidy nomenclature on
# retired rows. So this guard stops the problem GROWING instead: new paper-prefixed row ids in the
# repository's own registries fail, and the existing ones are pinned.
#
# Same discipline as check-terms.sh and check-std-lint.sh: pinned in `docs/labels-baseline.txt`,
# may shrink, never grow.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline="docs/labels-baseline.txt"
[ -f "$baseline" ] || { echo "FAIL missing baseline $baseline"; exit 1; }

# The repository's OWN registries. A row id here is a repository label and must use a repository
# prefix; a paper prefix in this position is the collision the policy exists to prevent.
REGISTRIES="specs/BACKLOG.md specs/future-work.md"

fail=0
for f in $REGISTRIES; do
  [ -f "$f" ] || { echo "FAIL registry missing: $f"; fail=1; continue; }
  # row-id position: start of a (possibly quoted) markdown table row, allowing ** and ~~ decoration
  found="$(grep -ohE "^> ?\| \*{0,2}~{0,2}\*{0,2}([ADGPRE])-?[0-9]+[a-z]?\b" "$f" 2>/dev/null \
    | grep -ohE "([ADGPRE])-?[0-9]+[a-z]?" | sort -u)"
  n=$(printf '%s' "$found" | grep -c . || true)
  pin=$(sed -nE "s#^${f}[[:space:]]+([0-9]+)\$#\1#p" "$baseline")
  if [ -z "$pin" ]; then
    echo "FAIL $baseline has no pin for $f"; fail=1; continue
  fi
  if [ "$n" -gt "$pin" ]; then
    echo "FAIL $f: paper-prefixed row ids grew $pin -> $n."
    echo "     A row id in a repository registry must use a repository prefix"
    echo "     (Q, CV, CL, R-, HY, TH, CR) — CONVENTIONS.md §12. Paper prefixes are A D G P R E."
    printf '%s\n' "$found" | sed 's/^/       /'
    fail=1
  elif [ "$n" -lt "$pin" ]; then
    echo "  ratchet $f shrank: $pin -> $n — re-pin $baseline in this commit."
  else
    echo "  ok      $f $n paper-prefixed row id(s) (pinned, grandfathered)"
  fi
done

# `claims.yaml` has never existed; the register is the TSV pair plus the guard. Both surviving
# mentions say so explicitly, and this check keeps it that way: a mention that does NOT deny the
# file's existence would be a fresh error.
bad_yaml="$(git ls-files '*.md' '*.sh' '*.lean' '*.tsv' \
  | xargs grep -lF 'claims.yaml' 2>/dev/null \
  | while read -r f; do
      grep -F 'claims.yaml' "$f"         | grep -qiE "no .claims\.yaml|there is no|does not exist|never existed|never has"         || echo "$f"
    done)"
if [ -n "$bad_yaml" ]; then
  echo "FAIL a reference to claims.yaml does not say the file does not exist:"
  printf '%s\n' "$bad_yaml" | sed 's/^/       /'
  echo "     Ground truth is specs/validation-claims.tsv + specs/residues.tsv + scripts/check-claims.sh."
  fail=1
else
  echo "  ok      no claims.yaml reference implies the file exists"
fi

if [ "$fail" -ne 0 ]; then
  echo "check-labels: FAIL (see CONVENTIONS.md §12)"
  exit 1
fi
echo "check-labels: OK"
exit 0
