#!/usr/bin/env bash
# check-duplicates.sh — is a statement proved twice in this corpus?
#
# Runs scripts/duplicate-scan.lean, which groups every hand-written CSD theorem by its
# statement with binder names erased. A group of two or more is one statement proved under
# several names.
#
# WHY IT EXISTS. On 2026-10-12 a lemma was written that already existed four files away
# (`arenaKick_mk`), and two Mathlib-shaped facts were being re-derived inline at each site.
# `check-mathlib-absence.sh` asks whether a staged name exists UPSTREAM; nothing asked whether
# it exists HERE, twice.
#
# RATCHET. Three classes come out of the scan and only one is a finding:
#   * Empirical TWINS — a `CSDBridge` theorem beside its `Empirical.QM` original. Those having
#     the same statement is the point of those files, not a defect.
#   * in-namespace ALIASES — a headline name beside its internal one, deliberate.
#   * TO REVIEW — two namespaces, neither a twin nor an alias. This is the pinned count: a NEW
#     one fails this guard, which is the whole purpose.
#
# Lower the pin when a duplicate is retired; raising it needs a reason in the commit message.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"

PINNED_REVIEW=42

out="$(lake env lean scripts/duplicate-scan.lean 2>&1)" || {
  echo "$out"
  echo "check-duplicates: FAIL the scan did not run (build the corpus first)"
  exit 1
}
echo "$out"

n="$(printf '%s\n' "$out" | sed -n 's/.*+ \([0-9][0-9]*\) TO REVIEW.*/\1/p' | head -1)"
if [ -z "$n" ]; then
  echo "check-duplicates: FAIL could not read the TO REVIEW count — the scan's output shape changed"
  exit 1
fi

if [ "$n" -gt "$PINNED_REVIEW" ]; then
  echo "check-duplicates: FAIL $n statements proved twice, pinned at $PINNED_REVIEW."
  echo "  A statement listed under TO REVIEW is proved in two namespaces. Generalise one and"
  echo "  delete the other, or say in its docstring why both are wanted — and only then move"
  echo "  the pin."
  exit 1
fi
echo "check-duplicates: OK ($n to review, pinned at $PINNED_REVIEW)"
