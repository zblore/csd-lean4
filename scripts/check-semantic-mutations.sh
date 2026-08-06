#!/usr/bin/env bash
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
fail=0

require_between() {
  file="$1" start="$2" end="$3" pattern="$4" label="$5"
  block="$(awk -v s="$start" -v e="$end" '$0 ~ s {on=1} on {print} on && $0 ~ e {exit}' "$file")"
  printf '%s\n' "$block" | grep -Eq "$pattern" || { echo "FAIL $label"; fail=1; }
}

# SSA is intentionally conditional. If hDPI disappears, the claim must be re-reviewed,
# not silently promoted by documentation drift.
require_between CsdLean4/Mathlib/QuantumInfo/StrongSubadditivity.lean \
  'theorem strong_subadditivity_of_relEntropy_monotone' ':=' 'hDPI' \
  'SSA mutation guard: explicit hDPI premise missing'

# F-01 state as of 2026-08-06 (G1 discharge): fromPreparation still carries the bridge
# type-level only (its #print-axioms hygiene note depends on that), while the transport
# theorems MeasureBridgeData.integral_comp_pi and fromPreparation_liouville_apply are
# where bridge_eq is extensionally consumed. Guard all three facts: if any changes,
# CL-003's disposition must be re-reviewed, not silently drifted.
block="$(awk '/noncomputable def OperationalPackage.fromPreparation/{on=1} on{print} on && /^end /{exit}' CsdLean4/LF2/Preparation.lean)"
printf '%s\n' "$block" | grep -q 'bridge : MeasureBridgeData' || { echo 'FAIL LF2 bridge parameter disappeared; re-review CL-003'; fail=1; }
if printf '%s\n' "$block" | grep -Eq 'bridge\.(bridge_eq|equivariant|invariant)'; then
  echo 'FAIL LF2 fromPreparation body now consumes the bridge; CL-003 and F-01 must be re-reviewed'
  fail=1
fi
tblock="$(awk '/theorem integral_comp_pi/{on=1} on{print} on && /^end MeasureBridgeData/{exit}' CsdLean4/LF2/Preparation.lean)"
printf '%s\n' "$tblock" | grep -q 'bridge.bridge_eq' \
  || { echo 'FAIL LF2 transport theorem integral_comp_pi missing or no longer consumes bridge_eq; F-01 regresses to phantom-bridge state — re-review CL-003'; fail=1; }
grep -q 'theorem OperationalPackage.fromPreparation_liouville_apply' CsdLean4/LF2/Preparation.lean \
  || { echo 'FAIL LF2 fromPreparation_liouville_apply missing; F-01 discharge incomplete — re-review CL-003'; fail=1; }

# Prevent reintroduction of trivial proof placeholders in executable source.
if git grep -nE ':=[[:space:]]*True([[:space:]]|$)' -- 'CsdLean4/**/*.lean'; then
  echo 'FAIL executable := True placeholder introduced'
  fail=1
fi

[ "$fail" -eq 0 ] || exit 1
echo 'check-semantic-mutations: OK (known semantic boundaries unchanged)'
