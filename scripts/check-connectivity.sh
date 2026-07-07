#!/usr/bin/env bash
# check-connectivity.sh
#
# Guard against END-TO-END CONNECTIVITY OVERCLAIM: the failure where the docs
# assert that "one posited Kähler ontic sector yields both the Born rule and
# Schrödinger dynamics" while the code proves no such connected chain. A
# 2026-07-07 provenance audit found exactly this: the Kähler fields are
# unconsumed placeholders, the Schrödinger chain is instantiated only on the
# identity-flow (Φ = id, H = 0) witness, and the Born chain runs on a separate
# abstract measure-space engine with no sector object. The single source of
# truth for what actually connects is `specs/connectivity-manifest.md`; this
# script enforces the statically-checkable parts of that discipline.
#
# It checks four things:
#   (1) the connectivity manifest exists;
#   (2) README carries the honesty banner (a pointer to the manifest + the
#       "NOT yet realized end-to-end" statement) — you cannot silently delete
#       the caveat;
#   (3) README / specs/INDEX.md contain NONE of the retracted overclaim phrases
#       — you cannot re-assert the connected chain in prose;
#   (4) the non-trivial-inhabitant reality check: it counts genuine
#       `KahlerOnticSetup` inhabitants other than the trivial witness. If there
#       are NONE (the current honest state), the overclaim phrases in (3) MUST
#       stay forbidden and the banner in (2) MUST stay — which (2)+(3) already
#       enforce. If a non-trivial inhabitant IS added later, this reports it so
#       the manifest/README can be upgraded deliberately.
#
# This does NOT prove connectivity (only the manifest's CONNECTED rows, each
# backed by a named theorem, do that). It prevents the prose from claiming more
# than the code delivers — the exact hole that produced the overclaim.
#
# Usage:  bash scripts/check-connectivity.sh
# Exit 0 = docs are consistent with the (broken) connectivity reality.
# Exit 1 = an overclaim was reintroduced, or the honesty banner/manifest is gone.

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

# --- (2) README honesty banner ----------------------------------------------
banner_ok=1
grep -Fq "connectivity-manifest.md" README.md || banner_ok=0
grep -Fq "NOT yet realized end-to-end" README.md || banner_ok=0
if [ "$banner_ok" -eq 1 ]; then
  echo "  OK    README carries the connectivity honesty banner."
else
  echo "  FAIL  README is missing the honesty banner (a link to $MANIFEST AND"
  echo "        the phrase \"NOT yet realized end-to-end\"). The connectivity"
  echo "        caveat may not be silently removed while the chain is broken."
  fail=1
fi

# --- (3) forbidden overclaim phrases (README + INDEX; NOT the manifest) ------
# Exact strings that only a genuine end-to-end connection would justify. The
# manifest is excluded because it quotes these in order to forbid them.
FORBIDDEN=(
  "theorems of a single posited object"
  "single posited object"
  "on the same sector interface"
  "Both load-bearing pillars of quantum mechanics"
  "put the Born rule and the Schrödinger equation on the same"
)
scan_files=(README.md specs/INDEX.md)
overclaim=0
for phrase in "${FORBIDDEN[@]}"; do
  hits="$(grep -Fn "$phrase" "${scan_files[@]}" 2>/dev/null || true)"
  if [ -n "$hits" ]; then
    echo "  FAIL  retracted overclaim phrase reintroduced: \"$phrase\""
    printf '%s\n' "$hits" | sed 's/^/          /'
    overclaim=1
    fail=1
  fi
done
[ "$overclaim" -eq 0 ] && echo "  OK    no retracted overclaim phrases in README / INDEX."

# --- (4) non-trivial KahlerOnticSetup inhabitant reality check ---------------
# Genuine inhabitants: a `def` whose RETURN type is `KahlerOnticSetup N` — i.e.
# `: KahlerOnticSetup N where` or `: KahlerOnticSetup N :=`. This is distinct
# from a CONSUMER `def foo (d : KahlerOnticSetup N) … : <other>`, whose
# `KahlerOnticSetup` sits in a `(…)` binder (followed by `)`), never by
# `where`/`:=`. An awk pass associates each such return type with its `def`
# name (the signature may span lines) and lists the non-trivial ones.
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
nontrivial="$(printf '%s' "$inhabitants" | grep -viE "trivial" | grep -c . || true)"
if [ "$nontrivial" -gt 0 ]; then
  echo "  INFO  $nontrivial non-trivial KahlerOnticSetup inhabitant(s) found —"
  echo "        the Schrödinger chain may now be instantiated off the trivial"
  echo "        witness. Update $MANIFEST (link L4) and the README claim to match:"
  printf '%s\n' "$inhabitants" | grep -viE "trivial" | sed 's/^/          /'
else
  echo "  INFO  0 non-trivial KahlerOnticSetup inhabitants (only the trivial"
  echo "        witness Φ=id). Manifest L4 = BROKEN; the overclaim guard (2)+(3)"
  echo "        keeps the docs honest. Fix C1 (build a Φ≠id instance) flips this."
fi

if [ "$fail" -ne 0 ]; then
  echo "== connectivity guard: FAIL =="
  echo "   See $MANIFEST for the per-link status and the fix course."
  exit 1
fi
echo "== connectivity guard: OK =="
exit 0
