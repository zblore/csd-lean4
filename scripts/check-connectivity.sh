#!/usr/bin/env bash
# check-connectivity.sh
#
# Guard against SECTOR-ORIGIN (A5) OVERCLAIM.
#
# History: written 2026-07-07 when the connectivity chain was BROKEN (Kähler
# fields unconsumed, Schrödinger instantiated only on the Φ=id witness, Born on a
# separate engine). It then enforced a "NOT yet realized end-to-end" banner. That
# era is over. As of fixes C1–C7 and the FND "Choice A" layer (2026-07), the
# FORWARD chain is CONNECTED on genuine objects: a single posited Kähler sector
# yields BOTH pillars at general N (`manyToOneSchrodingerSetup_both_pillars`), and
# ONE ontic model `(Σ, μL, Φ, π)` carries isolated dynamics + de-isolating
# measurement + time-indexed records + Born + the conditional/Lüders state update
# (`unified_choiceA_capstone`, manifest link L9). The guard is therefore repurposed
# to the CURRENT frontier: the ONE remaining deep gap is A5 / FND-1 — the sector
# and its Born weights are POSITED (the trials SAMPLE μL i.i.d.), NOT derived from
# the deterministic flow. `specs/connectivity-manifest.md` is the single source of
# truth; this script enforces the statically-checkable honesty at that frontier.
#
# It checks:
#   (1) the connectivity manifest exists;
#   (2) README carries the A5 honesty banner (a pointer to the manifest AND the
#       caveat that the sector itself is posited) — the deep caveat may not be
#       silently deleted while A5 is open;
#   (3) README / specs/INDEX.md assert NONE of the A5 overclaims (that the sector
#       or the Born weights are DERIVED from the flow, or that A5 is closed);
#   (4) reports the genuine non-trivial `KahlerOnticSetup` inhabitants — now the
#       healthy, expected state (the Schrödinger chain runs off the trivial witness).
#
# This does NOT prove connectivity (only the manifest's CONNECTED rows, each backed
# by a named theorem, do that). It prevents the prose from claiming the DEEP
# reverse — that the sector is derived from the dynamics — which is still open.
#
# Usage:  bash scripts/check-connectivity.sh
# Exit 0 = docs honest at the current (A5) frontier.
# Exit 1 = an A5 overclaim was introduced, or the honesty banner/manifest is gone.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

MANIFEST="specs/connectivity-manifest.md"
fail=0

echo "== connectivity guard =="

# --- (1) manifest exists -----------------------------------------------------
if [ -f "$MANIFEST" ]; then
  echo "  OK    $MANIFEST present."
else
  echo "  FAIL  $MANIFEST is missing — the connectivity source of truth was deleted."
  fail=1
fi

# --- (2) README A5 honesty banner --------------------------------------------
banner_ok=1
grep -Fq "connectivity-manifest.md" README.md || banner_ok=0
grep -Fq "the sector itself is posited" README.md || banner_ok=0
if [ "$banner_ok" -eq 1 ]; then
  echo "  OK    README carries the A5 honesty banner (manifest link + sector-posited caveat)."
else
  echo "  FAIL  README is missing the honesty banner (a link to $MANIFEST AND the phrase"
  echo "        \"the sector itself is posited\"). The A5 / FND-1 caveat may not be removed"
  echo "        while the sector is posited (the trials sample muL; the sector is not derived)."
  fail=1
fi

# --- (3) forbidden A5 overclaim phrases (README + INDEX; NOT the manifest) ----
# Exact strings that only a genuine sector-origin derivation (A5 closed) would
# justify. The manifest is excluded because it quotes these in order to forbid them.
FORBIDDEN=(
  "A5 is closed"
  "the sector is no longer posited"
  "derives the sector from the deterministic flow"
)
scan_files=(README.md specs/INDEX.md)
overclaim=0
for phrase in "${FORBIDDEN[@]}"; do
  hits="$(grep -Fn "$phrase" "${scan_files[@]}" 2>/dev/null || true)"
  if [ -n "$hits" ]; then
    echo "  FAIL  A5 overclaim phrase present: \"$phrase\""
    printf '%s\n' "$hits" | sed 's/^/          /'
    overclaim=1
    fail=1
  fi
done
[ "$overclaim" -eq 0 ] && echo "  OK    no A5 overclaim phrases in README / INDEX."

# --- (4) non-trivial KahlerOnticSetup inhabitant report ----------------------
# Genuine inhabitants: a `def` whose RETURN type is `KahlerOnticSetup N` — i.e.
# `: KahlerOnticSetup N where` or `: KahlerOnticSetup N :=`. This is distinct from a
# CONSUMER `def foo (d : KahlerOnticSetup N) … : <other>`. An awk pass associates
# each such return type with its `def` name and lists the non-trivial ones. Since
# C1/C7, several genuine Φ≠id inhabitants exist — the healthy, expected state.
inhabitants="$(for f in $(grep -rlE "KahlerOnticSetup" --include='*.lean' CsdLean4 2>/dev/null); do
  awk -v F="$f" '
    /^(noncomputable )?def [A-Za-z0-9_]+/ {
      name=$0; sub(/^.*def /,"",name); sub(/[ (:].*/,"",name); sig=$0; cap=1; next
    }
    cap==1 {
      sig=sig " " $0
      if (sig ~ /: *KahlerOnticSetup [A-Za-z0-9]+ +(where|:=)/) { print F": "name; cap=0 }
      else if ($0 ~ /:=/ || $0 ~ /\<where\>/) cap=0
    }
  ' "$f"
done || true)"
nontrivial="$(printf '%s' "$inhabitants" | grep -viE ": *trivial" | grep -c . || true)"
if [ "$nontrivial" -gt 0 ]; then
  echo "  INFO  $nontrivial non-trivial KahlerOnticSetup inhabitant(s) — the healthy state:"
  echo "        the Schrödinger chain is instantiated off the trivial witness (C1/C7)."
  printf '%s\n' "$inhabitants" | grep -viE ": *trivial" | sed 's/^/          /'
else
  echo "  WARN  0 non-trivial KahlerOnticSetup inhabitants found — a REGRESSION from the"
  echo "        C1/C7 state (rotationSetup / manyToOneSetup). Check the awk scan / the code."
fi

if [ "$fail" -ne 0 ]; then
  echo "== connectivity guard: FAIL =="
  echo "   See $MANIFEST for the per-link status (L1–L9) and the A5 frontier."
  exit 1
fi
echo "== connectivity guard: OK =="
exit 0
