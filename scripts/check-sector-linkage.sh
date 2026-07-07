#!/usr/bin/env bash
# check-sector-linkage.sh
#
# Guard against the "carried-but-unused sector object" vacuity: a structure that
# packages the CSD ontic substrate (`KahlerOnticSetup`: the state space `Sigma`,
# the deterministic `flow`, the projection `pi`, and the descent equation
# `projectable : pi (flow t x) = projectedFlow t (pi x)`) is threaded through a
# theorem's signature, but the theorem only ever destructures `.projectedFlow`
# (the already-induced ray-space map) and never the substrate fields. When that
# happens the theorem is really a statement about an arbitrary self-map on
# `ℙ ℂ (EuclideanSpace ℂ (Fin N))`, and the "dynamics from the posited ontic
# sector" reading is unearned scaffolding -- the substrate is inert.
#
# This checks, statically (grep only, a few seconds), that each LINKAGE field
# below is CONSUMED by at least one genuine declaration OUTSIDE its defining
# file (the struct definition + the trivial inhabitation witness live there and
# do not count). The critical one is `projectable`: it is the ONLY field tying
# `projectedFlow` back to the Σ-level `flow` via `pi`, so if it is consumed
# nowhere, no theorem in the corpus actually lands the dynamics on the substrate.
#
# It is a heuristic: it looks for a `.<field>` PROJECTION applied to arguments on
# a non-comment, non-docstring line (prose mentions the bare word `projectable`
# without a leading dot; backtick-quoted `d.projectable` in a docstring is
# excluded). `lake build` remains the definitive correctness gate; this only
# guards the substrate-linkage invariant a plain build cannot see.
#
# Usage:  bash scripts/check-sector-linkage.sh
# Exit 0 = every linkage field is consumed by a real declaration.
# Exit 1 = a linkage field is carried-but-unused (vacuity); the sector object is
#          threaded through signatures but never lands on the substrate.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# Linkage requirements: "DefFile|field|description".
# `field` must appear as a `.field` projection in some .lean file OTHER than
# DefFile, on a line of actual code. Add rows here as new sector interfaces land.
#
# We guard on `projectable` (the descent equation) and `flow` (the ontic flow),
# NOT on `pi`: `.pi` is an un-greppable substring (it collides with `Real.pi`,
# `Measure.pi`, `Set.pi`, `ContinuousLinearMap.pi`, …), so a bare grep for it is
# all false positives. This is not a gap: `projectable`'s type is
# `pi (flow t x) = projectedFlow t (pi x)`, so ANY theorem that consumes
# `.projectable` necessarily consumes `.flow` and `.pi` in the same step. The
# descent equation is the exact linkage whose absence makes the sector object
# inert, so guarding it is both necessary and sufficient.
LINKAGE=(
  "CsdLean4/LF4/KahlerOnticSetup.lean|projectable|descent equation pi(flow t x)=projectedFlow t (pi x) -- the tie from the Σ-flow to the ray-space flow"
  "CsdLean4/LF4/KahlerOnticSetup.lean|flow|the deterministic ontic Σ-flow"
)

# Fields whose absence is a HARD failure (the load-bearing linkage).
CRITICAL="projectable"

fail=0

# A "code" occurrence of `.field arg`: a dot-projection followed by whitespace or
# an opening paren, on a line that is not a `--` line comment, not a `/-! /--`
# docstring opener, and does not carry a backtick (backticks fence doc prose that
# quotes code like `d.projectable`). This is deliberately conservative: it can
# miss an exotic usage, but it will not count a docstring mention as consumption.
code_uses() {
  local field="$1" deffile="$2"
  # shellcheck disable=SC2016
  grep -rnE "\.${field}( |\()" --include='*.lean' CsdLean4 2>/dev/null \
    | grep -v "^${deffile}:" \
    | grep -vE ':[0-9]+:[[:space:]]*--' \
    | grep -vE ':[0-9]+:.*/-[!-]' \
    | grep -v '`'
}

echo "== sector-linkage guard =="
for row in "${LINKAGE[@]}"; do
  IFS='|' read -r deffile field desc <<< "$row"
  hits="$(code_uses "$field" "$deffile")"
  n="$(printf '%s' "$hits" | grep -c . || true)"
  if [ "$n" -gt 0 ]; then
    printf '  OK    .%s consumed by %s declaration(s):\n' "$field" "$n"
    printf '%s\n' "$hits" | sed 's/^/          /'
  else
    if printf '%s' "$CRITICAL" | grep -qw "$field"; then
      printf '  FAIL  .%s is CARRIED-BUT-UNUSED (%s).\n' "$field" "$desc"
      printf '        No declaration outside %s consumes it: the sector object\n' "$deffile"
      printf '        is threaded through signatures but the dynamics never land\n'
      printf '        on the Σ substrate. Add a theorem that consumes .%s\n' "$field"
      printf '        (e.g. sigmaFlow_schrodinger_form), or the pillar is vacuous scaffolding.\n'
      fail=1
    else
      printf '  warn  .%s not directly consumed outside %s (%s).\n' "$field" "$deffile" "$desc"
    fi
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "== sector-linkage guard: FAIL =="
  exit 1
fi
echo "== sector-linkage guard: OK =="
exit 0
