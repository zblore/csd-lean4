#!/usr/bin/env bash
# brief-eponym.sh
#
# Assembles the EVIDENCE PACK for one glossary entry, so the entry is written from
# what this corpus actually does with a concept rather than from what the concept
# means in general.
#
# Motivating case (2026-08-19): the risk in an auto-drafted glossary is not that
# the prose is wrong about mathematics -- an encyclopaedia gets Gleason's theorem
# right. It is that the `in_csd` register comes out generic, saying what any
# textbook would say and nothing about what turns on the concept HERE. That is the
# difference between a reference site worth publishing and 53 pages of filler, and
# it is exactly the "claim-surface multiplication" objection that nearly killed
# this whole idea.
#
# So: read the corpus first. Every declaration that names the concept, every module
# docstring that discusses it, and its standing in the axiom ledger and the gap
# register. Draft from that.
#
# WHAT IT REPORTS
#   (1) declarations   -- name, file and line for every declaration containing the
#                         eponym. The suggested lean.theorem anchor is the one a
#                         reader should be sent to, usually the capstone rather
#                         than a helper.
#   (2) modules        -- files whose PATH names the concept: it owns those.
#   (3) docstrings     -- module-doc and declaration-doc lines mentioning it. This
#                         is the raw material for `in_csd`, and it is usually
#                         already written, honestly, by the author.
#   (4) ledgers        -- AXIOMS.md, MATHLIB-GAPS.md, CONVENTIONS.md and the
#                         connectivity manifest. Decides `status` and surfaces any
#                         caveat that must appear in the entry.
#   (5) glossary state -- whether it is already an entry, or only an external ref.
#
# WHAT IT DELIBERATELY DOES NOT DO
#   It does not write the entry, and it does not decide whether the concept
#   DESERVES one. Many eponyms here (Pauli, Hilbert, Borel, Cauchy-Schwarz,
#   Kronecker) are standard vocabulary that CSD uses without doing anything
#   particular to them. Those belong in `refs:` as an outward link, not as an
#   entry. The test is simple and it is editorial: does this corpus do something
#   specific with the concept? If not, link it and move on.
#
# Usage:  bash scripts/brief-eponym.sh Duistermaat
#         bash scripts/brief-eponym.sh Luders
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SRC="CsdLean4"

E="${1:-}"
[ -z "$E" ] && { echo "usage: bash scripts/brief-eponym.sh <Eponym>"; exit 1; }

FILES="$(git ls-files "$SRC/**/*.lean")"
DECLRE='^(public |private |protected |noncomputable |scoped |partial |unsafe |nonrec )*(def|abbrev|structure|class|inductive|instance|theorem|lemma) '

echo "======================================================================"
echo "  EVIDENCE PACK: $E"
echo "======================================================================"

echo
echo "(1) DECLARATIONS naming it"
echo "---------------------------------------------------------------------"
DECLS="$(printf '%s\n' $FILES | xargs grep -nHE "$DECLRE" 2>/dev/null \
  | sed -E 's/:([0-9]+):[[:space:]]*(public |private |protected |noncomputable |scoped |partial |unsafe |nonrec )*(def|abbrev|structure|class|inductive|instance|theorem|lemma) +/:\1:/' \
  | grep -i "$E" || true)"
if [ -z "$DECLS" ]; then
  echo "      none — the concept is discussed but never named in a declaration."
else
  printf '%s\n' "$DECLS" | sed -E 's/^/      /' | head -40
  n=$(printf '%s\n' "$DECLS" | grep -c . || true)
  echo
  echo "      $n declaration(s). Suggested anchor = the one a reader should land on,"
  echo "      normally the capstone, not a helper lemma:"
  printf '%s\n' "$DECLS" | grep -iE "(capstone|main|unique|theorem|_eq_|forced)" \
    | head -3 | sed -E 's/^/        -> /'
fi

echo
echo "(2) MODULES it owns (path names the concept)"
echo "---------------------------------------------------------------------"
printf '%s\n' $FILES | grep -i "$E" | sed -E 's/^/      /' | head -20 || echo "      none"

echo
echo "(3) DOCSTRING LINES — raw material for the in_csd register"
echo "---------------------------------------------------------------------"
printf '%s\n' $FILES | xargs grep -nH -i -- "$E" 2>/dev/null \
  | grep -E ':[0-9]+:\s*(--|/-|\*|[A-Z*`\[])' \
  | grep -viE "$DECLRE" \
  | cut -c1-200 | sed -E 's/^/      /' | head -25 || echo "      none"

echo
echo "(4) LEDGERS — decides status, and surfaces caveats that must be disclosed"
echo "---------------------------------------------------------------------"
for f in AXIOMS.md MATHLIB-GAPS.md CONVENTIONS.md specs/connectivity-manifest.md; do
  [ -f "$f" ] || continue
  hits="$(grep -n -i -- "$E" "$f" | cut -c1-190 || true)"
  [ -z "$hits" ] && continue
  echo "      --- $f"
  printf '%s\n' "$hits" | sed -E 's/^/        /' | head -8
done

echo
echo "(5) GLOSSARY STATE"
echo "---------------------------------------------------------------------"
if grep -qi "eponyms:.*$E" docs/glossary.yaml 2>/dev/null; then
  echo "      already an ENTRY."
elif grep -qi "^  \"$E" docs/glossary.yaml 2>/dev/null; then
  echo "      currently an external REF only. Promote to an entry only if the"
  echo "      corpus does something specific with it."
else
  echo "      neither an entry nor a ref. If it stays unexplained, a reader meeting"
  echo "      it in the prose has nowhere to go."
fi

echo
echo "======================================================================"
echo "  Draft from the above, not from memory. The guard will check the"
echo "  anchors; nothing checks whether the mathematics is right but you."
echo "======================================================================"
