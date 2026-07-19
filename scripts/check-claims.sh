#!/usr/bin/env bash
# check-claims.sh
#
# Machine-enforces the QUANTITATIVE / SEMANTIC honesty claims that the other
# guards (check-connectivity / check-sector-linkage / check-axiom-imports) do
# NOT check — the drift surface where the "nine vs eleven" and "hpos" desyncs
# lived. The canonical facts are the CLAIMS block below (single source of truth,
# version-controlled, diffable); the checks assert the CODE matches them.
#
# It checks:
#   (1) the imported-axiom SET (real `axiom` declarations, comments stripped)
#       equals the declared set  — the "exactly one axiom" claim.
#   (2) the `:= True` placeholder SET equals the declared inventory
#       — catches new vacuity regressions.
#   (3) FiniteQMClosure has the declared number of fields
#       — catches the "nine vs eleven" class of drift.
#   (4) every declared backing theorem still EXISTS as a declaration
#       — catches a rename/deletion silently orphaning a CONNECTED claim.
#   (5) the forbidden A5-overclaim phrases are absent from the forward-claim docs.
#
# Scope: the core QM library only; `CsdLean4/Ecdsafail` (the ecdsa.fail track) is
# excluded — it is a separate project with no honesty ledger here.
#
# Usage:  bash scripts/check-claims.sh   (grep/awk only, no Lean build; seconds)

set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SRC="CsdLean4"
EXCLUDE_DIR="CsdLean4/Ecdsafail"

# ------------------------------------------------------------------ CLAIMS ----
# THE canonical source of truth. Update HERE when the code legitimately changes;
# the checks below fail loudly if code and these facts disagree.
DECLARED_AXIOMS="busch_effect_gleason"

# All Kähler `:= True` placeholders were de-vacuumed 2026-07-19 (IsKahlerSector →
# IsFubiniStudyKahler, the proved pointwise FS Kähler compatibility; the trivial
# witness's IsLiouvilleKahlerVolume → IsProbabilityMeasure). Inventory now empty:
# a new `:= True` anywhere is a fresh vacuity regression the check below catches.
DECLARED_PLACEHOLDERS=""

FINITEQMCLOSURE_FIELDS=11

DECLARED_BACKING_THEOREMS="unifiedFiniteQMClosure
unified_choiceA_capstone
manyToOneSchrodingerSetup_both_pillars
manyToOneSchrodingerSetup_schrodinger_derived
bornRegion_fs_measure
born_frequency_convergence_N
conditioning_luders_effect_equivalence
flow_admits_invariant_ne_fubiniStudy
compositeAlgReconstruction"

FORBIDDEN_PHRASES=(
  "A5 is closed"
  "the sector is no longer posited"
  "derives the sector from the deterministic flow"
)
# Docs that make FORWARD claims and so must never contain the overclaims — even
# as text. (connectivity-manifest.md legitimately QUOTES them in its ❌ list, so
# it is deliberately NOT scanned here; check-connectivity covers README/INDEX.)
FORWARD_DOCS=("README.md" "specs/reconstruction-status.md")
# ------------------------------------------------------------------------------

fail=0
say_fail() { echo "  FAIL  $1"; fail=1; }
say_ok()   { echo "  ok    $1"; }

# Strip Lean block comments (/- .. -/, /-- .. --/, /-! .. -/) so docstring prose
# beginning with a keyword is not mistaken for a declaration.
strip_comments() {
  awk '
    { line = $0
      while (length(line) > 0) {
        if (inc) { i = index(line, "-/"); if (i == 0) { line=""; break }
                   line = substr(line, i+2); inc = 0 }
        else     { i = index(line, "/-"); if (i == 0) break
                   pre = substr(line, 1, i-1); line = substr(line, i+2); inc = 1
                   printf "%s\n", pre }
      }
      if (!inc && length(line) > 0) print line
    }' "$1"
}

srcfiles() { git ls-files "$SRC/**/*.lean" 2>/dev/null | grep -v "^$EXCLUDE_DIR/"; }

echo "check-claims: verifying code against the canonical claims block…"

# (1) axiom set
found_ax="$(srcfiles | while read -r f; do
    strip_comments "$f" | grep -oE '^axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_'\'']*' \
      | awk '{print $2}'
  done | sort -u)"
if [ "$found_ax" = "$(printf '%s\n' "$DECLARED_AXIOMS" | sort -u)" ]; then
  say_ok "imported axioms == { $DECLARED_AXIOMS }"
else
  say_fail "axiom set mismatch. declared: [$DECLARED_AXIOMS]  found: [$(echo "$found_ax" | tr '\n' ' ')]"
fi

# (2) := True placeholder inventory
found_ph="$(srcfiles | while read -r f; do
    grep -nE '[A-Za-z_][A-Za-z0-9_]*[[:space:]]*:=[[:space:]]*True([[:space:]]|$)' "$f" \
      | sed -E "s|^[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*:=.*|$f:\1|"
  done | sort -u)"
decl_ph="$(printf '%s\n' "$DECLARED_PLACEHOLDERS" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_ph" = "$decl_ph" ]; then
  if [ -z "$found_ph" ]; then
    say_ok ":= True placeholders: none remain (all de-vacuumed)"
  else
    say_ok ":= True placeholders == declared inventory ($(printf '%s\n' "$decl_ph" | grep -c .) sites)"
  fi
else
  say_fail "placeholder set mismatch (new/removed := True — fix code or update the CLAIMS block)."
  echo "        declared:"; printf '%s\n' "$decl_ph"   | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_ph"  | sed 's/^/          /'
fi

# (3) FiniteQMClosure field count
FQC="$SRC/FND/FiniteQMClosure.lean"
n_fields="$(awk '/^structure FiniteQMClosure/{s=1;next} /^theorem unifiedFiniteQMClosure/{s=0} s' "$FQC" \
            | grep -cE '^  [a-z_]+ :')"
if [ "$n_fields" = "$FINITEQMCLOSURE_FIELDS" ]; then
  say_ok "FiniteQMClosure has $FINITEQMCLOSURE_FIELDS fields"
else
  say_fail "FiniteQMClosure field count: declared $FINITEQMCLOSURE_FIELDS, found $n_fields"
fi

# (4) backing theorems exist
while read -r thm; do
  [ -z "$thm" ] && continue
  if srcfiles | xargs grep -lE "^(theorem|lemma|def|noncomputable def)[[:space:]]+([A-Za-z0-9_'.]+\.)?$thm([[:space:](:{]|\$)" >/dev/null 2>&1; then
    :
  else
    say_fail "backing theorem '$thm' not found as a declaration (CONNECTED claim orphaned?)"
  fi
done <<< "$DECLARED_BACKING_THEOREMS"
[ "$fail" -eq 0 ] && say_ok "all $(printf '%s\n' "$DECLARED_BACKING_THEOREMS" | grep -c .) backing theorems exist" || true

# (5) forbidden phrases in forward-claim docs
for doc in "${FORWARD_DOCS[@]}"; do
  [ -f "$doc" ] || { say_fail "forward-claim doc missing: $doc"; continue; }
  for phrase in "${FORBIDDEN_PHRASES[@]}"; do
    if grep -Fq "$phrase" "$doc"; then
      say_fail "forbidden phrase in $doc: \"$phrase\""
    fi
  done
done
[ "$fail" -eq 0 ] && say_ok "no forbidden A5-overclaim phrases in forward-claim docs" || true

echo
if [ "$fail" -eq 0 ]; then echo "check-claims: PASS"; exit 0
else echo "check-claims: FAIL — code and the canonical claims block disagree (fix code or update the CLAIMS block)"; exit 1; fi
