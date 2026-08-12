#!/usr/bin/env bash
# check-import-hygiene.sh
#
# Import-hygiene rules for the production tree (validation-hardening WS-L,
# specs/validation-hardening-plan.md, 2026-08-12). Three rules, all cheap greps over
# tracked files:
#
#   (1) NO BARE `import Mathlib`. A whole-Mathlib import in a production module hides
#       the real dependency surface and roughly maximises rebuild cost. The corpus is
#       clean today; this ratchets that state.
#
#   (2) PRODUCTION NEVER IMPORTS Tests. The Tests/ subtree (AxiomAudit pins, Examples,
#       the Witnesses suite) is validation machinery; if a production module imported
#       it, validation-only material would enter the scientific dependency graph and
#       the "witness =/= result" separation would be structurally violated.
#
#   (3) INCUBATOR SEAMS ARE DECLARED. Incubator/ is class-3 staging behind replaceable
#       interfaces (specs/external-library-map.md); stable layers MAY bind to those
#       interfaces, but only at declared seam files, so a new leak is a visible diff
#       here rather than a silent architecture change. Same declared-inventory
#       discipline as check-claims (7a/7c/7d).
#
# Guard-of-guards: mutation probes for all three rules live in check-guards.sh.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

fail=0

# ---------------------------------------------------------------------------
# (1) No bare `import Mathlib` in any tracked production module.
# ---------------------------------------------------------------------------
bare="$(git ls-files 'CsdLean4/**/*.lean' 'CsdLean4.lean' \
  | xargs grep -ln '^[ \t]*\(public \|private \|meta \)*import[ \t]\+Mathlib[ \t]*$' 2>/dev/null || true)"
if [ -n "$bare" ]; then
  echo "  FAIL  bare \`import Mathlib\` in production modules (import the specific files):"
  printf '%s\n' "$bare" | sed 's/^/          /'
  fail=1
else
  echo "  ok    no bare \`import Mathlib\` in the production tree"
fi

# ---------------------------------------------------------------------------
# (2) Production (non-Tests) modules never import CsdLean4.Tests.*.
# ---------------------------------------------------------------------------
prod_tests="$(git ls-files 'CsdLean4/**/*.lean' 'CsdLean4.lean' \
  | grep -v '^CsdLean4/Tests/' \
  | xargs grep -ln '^[ \t]*\(public \|private \|meta \)*import[ \t]\+CsdLean4\.Tests' 2>/dev/null || true)"
if [ -n "$prod_tests" ]; then
  echo "  FAIL  production modules import the Tests subtree (validation must stay out of the scientific graph):"
  printf '%s\n' "$prod_tests" | sed 's/^/          /'
  fail=1
else
  echo "  ok    no production module imports CsdLean4.Tests.*"
fi

# ---------------------------------------------------------------------------
# (3) Stable-layer imports of Incubator match the declared seam inventory.
# ---------------------------------------------------------------------------
# Declared seams (2026-08-12): the SH quantum-chaos workstream binds the stable
# Empirical/CV layers to the Incubator FloquetEvolution / Diagnostics interfaces
# by design (specs/external-library-map.md, BACKLOG SH). Each file below is such
# a deliberate seam. Adding a new stable->Incubator import requires adding it
# here in the same commit -- that is the point.
DECLARED_INCUBATOR_SEAMS="CsdLean4/CV/ChaosBounds.lean
CsdLean4/CV/FreeFieldFloquet.lean
CsdLean4/Empirical/CSD/QuantumChaos/Capstone.lean
CsdLean4/Empirical/CSD/QuantumChaos/OnticLift.lean"

actual_seams="$(git ls-files 'CsdLean4/**/*.lean' \
  | grep -v '^CsdLean4/Incubator/' | grep -v '^CsdLean4/Tests/' \
  | xargs grep -ln '^[ \t]*\(public \|private \|meta \)*import[ \t]\+CsdLean4\.Incubator' 2>/dev/null \
  | sort || true)"
declared_sorted="$(printf '%s\n' "$DECLARED_INCUBATOR_SEAMS" | sort)"
# Compare as sets, but only fail on UNDECLARED seams (a declared file that drops
# its import is fine -- the inventory is a ceiling, pruned on touch).
undeclared="$(comm -13 <(printf '%s\n' "$declared_sorted") <(printf '%s\n' "$actual_seams") || true)"
if [ -n "$undeclared" ]; then
  echo "  FAIL  undeclared stable->Incubator imports (declare the seam in check-import-hygiene.sh or remove the import):"
  printf '%s\n' "$undeclared" | sed 's/^/          /'
  fail=1
else
  echo "  ok    stable->Incubator imports all match the declared seam inventory"
fi

if [ "$fail" -ne 0 ]; then
  echo "check-import-hygiene: FAIL"
  exit 1
fi
echo "check-import-hygiene: OK"
