#!/usr/bin/env bash
# check-guards.sh — mutation testing for the guards themselves.
#
# WHO WATCHES THE WATCHMEN. Every guard here is a lexical or environment rule, and a rule
# that stops matching does not announce itself: it just reports OK. A silently-broken
# guard is indistinguishable from a clean repository, which is the worst failure mode
# available to this framework.
#
# This is not hypothetical. THREE checkers in this repository have had exactly that bug:
#
#   * check-citation-use, first version — `ConstantInfo.value?` returns none for theorems
#     under the module system, so it reported EVERY citation as unused. Caught only
#     because a known-good case was checked by hand.
#   * check-claim-provenance mode 4, first version — its citation regex rejected
#     NAMESPACED identifiers, producing a false positive on a correctly-cited site.
#   * check-claim-provenance mode 1 — required the declaration on the very NEXT line, so
#     any docstring followed by a blank line was silently skipped. It had been passing
#     while not checking a large fraction of the corpus.
#
# Each was found by planting a defect by hand. This encodes those plants so they run
# every time, which is the standard practice equivalent of mutation testing.
#
# CONTRACT. For each probe: the guard must FAIL with the probe present, and PASS with it
# absent. A guard that passes with the probe present is broken, and so is one that fails
# without it.
#
# SCOPE. Covers the text-based guards, which need no rebuild. The two Lean-based checkers
# (citation-use, axiom-sweep) need the probe compiled into the environment first, so their
# probes require a `lake build` cycle; run `--with-lean` for those (slow, minutes).
#
# SELF-REFERENCE. This file contains defect text as literals, so it must be excused in
# check-claim-provenance's mode-2 allowlist. That was not obvious in testing: while this
# script was UNTRACKED it was invisible to `git ls-files`, so every guard passed locally
# and CI failed on the first push after it became tracked. The same trap voided the first
# negative test written for check-claim-provenance mode 4 — guards see tracked files only,
# so anything guard-relevant must be re-checked AFTER `git add`, not before.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

WITH_LEAN=0
[ "${1:-}" = "--with-lean" ] && WITH_LEAN=1

PROBE="CsdLean4/SigmaLayer/GuardSelfTestProbe.lean"
fail=0
pass=0

ROOT="CsdLean4.lean"
ROOTBAK="${TMPDIR:-/tmp}/csd-guardtest-root.$$"

cleanup() {
  git rm -q --cached "$PROBE" >/dev/null 2>&1 || true
  rm -f "$PROBE" "${TMPDIR:-/tmp}"/csd-guardtest.* 2>/dev/null || true
  # The axiom-sweep probe imports itself from the root module; put the root back.
  [ -f "$ROOTBAK" ] && mv -f "$ROOTBAK" "$ROOT"
  rm -f "docs/std-lint-baseline.txt.guardbak" "scripts/gleason-free.lean.guardbak" 2>/dev/null || true
}
trap cleanup EXIT

# plant <content>  — writes the probe and makes it visible to `git ls-files`.
plant() {
  printf '%s\n' "$1" > "$PROBE"
  git add -N "$PROBE" >/dev/null 2>&1
}

unplant() { cleanup; }

# expect_fail <name> <guard> <probe-content>
expect_fail() {
  local name="$1" guard="$2" content="$3"
  plant "$content"
  bash "scripts/$guard.sh" >/dev/null 2>&1
  local rc=$?
  unplant
  if [ "$rc" -eq 0 ]; then
    echo "  BROKEN  $name — $guard did NOT fire on a planted defect"
    fail=1
  else
    pass=$((pass + 1))
  fi
}

echo "check-guards: mutation-testing the guards…"

# --- check-claim-provenance mode 1: property claim, WRAPPED, blank line before the def.
# Both halves matter: the wrap defeats a line-by-line rule, the blank line defeated the
# original block rule.
expect_fail "mode1 (unwitnessed property claim, wrapped + blank line)" check-claim-provenance \
'/-- The prepared state here is the singlet
transformed by
the local wing rotations. -/

noncomputable def guardSelfTestMode1 : Nat := 0'

# --- mode 2: type-level claim carrying mathematical content, WRAPPED across lines.
expect_fail "mode2 (type separation carries content, wrapped)" check-claim-provenance \
'/-- Note that these being different
types carries the Bell-consistency content of the argument. -/
noncomputable def guardSelfTestMode2 : Nat := 0'

# --- mode 3: over-broad "every Bell-test setting" attached to an hgen-restricted claim.
expect_fail "mode3 (every Bell-test setting, wrapped)" check-claim-provenance \
'/-- This holds at every
Bell-test setting, given `hgen`. -/
noncomputable def guardSelfTestMode3 : Nat := 0'

# --- mode 4: a REASON for a restriction that names no witness. This is the wording of
# the original C1 defect.
expect_fail "mode4 (unwitnessed reason)" check-claim-provenance \
'/-- The result is restricted to non-collinear settings because the collinear
case carries no physical information. -/
noncomputable def guardSelfTestMode4 : Nat := 0'

# --- check-doc-promises: a module PATH named in prose that does not exist must fail.
# (2026-09-04: the SigmaLayer -> RecordLayer split had left 303 such references in 87
# headers, and this guard only checked declaration NAMES.)
plant '/-!
# Probe

References: `RecordLayer/NoSuchModuleProbe.lean`.
-/'
if bash scripts/check-doc-promises.sh >/dev/null 2>&1; then
  echo "  BROKEN  doc-promises — did NOT fire on a module path that does not exist"
  fail=1
else
  pass=$((pass + 1))
fi
unplant

# --- check-terms: an unmarked use of a restricted term sense must fail when the count grows.
# (Written with awk, not sed: every earlier attempt to put a backreference through a heredoc
#  landed a literal control byte in this file and the probe passed while mutating nothing.)
tb="docs/terms-baseline.txt"
cp "$tb" "$tb.guardbak"
k=$(awk '$1=="Kahler"{print $2}' "$tb")
awk -v n="$((k - 1))" '$1=="Kahler"{print $1, n; next} {print}' "$tb" > "$tb.tmp"
mv "$tb.tmp" "$tb"
bash scripts/check-terms.sh >/dev/null 2>&1
rc=$?
mv "$tb.guardbak" "$tb"
if [ "$rc" -eq 0 ]; then
  echo "  BROKEN  terms — ratchet did NOT fire on a term over its pin"
  fail=1
else
  pass=$((pass + 1))
fi

# --- check-references: a `[Key]` citation with no entry must fail.
plant '/-!
# Probe

Cited as `[NoSuchKey2020]`.
-/'
if bash scripts/check-references.sh >/dev/null 2>&1; then
  echo "  BROKEN  references — did NOT fire on a citation key with no entry"
  fail=1
else
  pass=$((pass + 1))
fi
unplant

# --- check-import-negative: point the declared pair at a module that IS reachable.
# Done on a copy, since the probe is in the script rather than the corpus.
tmpg="${TMPDIR:-/tmp}/csd-guardtest.$$.sh"
sed 's#^CsdLean4.LF6.LocalDeisolationFlow|CsdLean4.LF2.EffectGleason|.*#CsdLean4.LF6.LocalDeisolationFlow|CsdLean4.LF4.MomentMap|selftest#' \
  scripts/check-import-negative.sh > "$tmpg"
if bash "$tmpg" >/dev/null 2>&1; then
  echo "  BROKEN  import-negative — did NOT fire on a reachable forbidden import"
  fail=1
else
  pass=$((pass + 1))
fi
rm -f "$tmpg"

# --- check-import-negative: a declared root that no longer exists must FAIL, not pass
# quietly. A renamed module used to leave its independence claim silently unchecked
# (2026-09-04, when the inventory grew from 1 pair to 46).
sed 's#^CsdLean4.LF6.LocalDeisolationFlow|#CsdLean4.LF6.RenamedAway|#'   scripts/check-import-negative.sh > "$tmpg"
if bash "$tmpg" >/dev/null 2>&1; then
  echo "  BROKEN  import-negative — did NOT fire on a declared root that is not a module"
  fail=1
else
  pass=$((pass + 1))
fi
rm -f "$tmpg"

# --- check-import-hygiene (WS-L, 2026-08-12): three probes, one per rule.
# (10a) a bare whole-Mathlib import in a production module;
expect_fail "hygiene-10a (bare import Mathlib)" check-import-hygiene \
'import Mathlib
def guardSelfTestHygieneA : Nat := 0'

# (10b) a production module importing the Tests subtree;
expect_fail "hygiene-10b (production imports Tests)" check-import-hygiene \
'import CsdLean4.Tests.Witnesses
def guardSelfTestHygieneB : Nat := 0'

# (10c) an UNDECLARED stable->Incubator seam (the probe lives in SigmaLayer, which is
# not in the declared seam inventory).
expect_fail "hygiene-10c (undeclared Incubator seam)" check-import-hygiene \
'import CsdLean4.Incubator.QuantumChaos.FloquetInterface
def guardSelfTestHygieneC : Nat := 0'

# --- Lean-based checkers: need the probe COMPILED, so they cost a build cycle.
if [ "$WITH_LEAN" -eq 1 ]; then
  echo "  (--with-lean: rebuilding for the environment-based checkers, minutes…)"

  # The probe must look like a corpus module: `module` (the tree rejects a non-`module`
  # import) and `@[expose] public section` (without it the proof term is not exported and
  # the sweep cannot see the sorry — the coverage precondition check-axiom-sweep now
  # enforces). Both were missing until 2026-09-04, which is why this probe passed
  # vacuously: the planted file did not even compile.
  plant 'module

@[expose] public section

namespace CSD.GuardSelfTest
/-- Placeholder. -/
theorem guard_self_test_sorry : 2 + 2 = 5 := by sorry
end CSD.GuardSelfTest'
  git add "$PROBE" >/dev/null 2>&1
  # The lib target has ROOTS (lakefile.toml), not a glob: a file nothing imports is never
  # compiled, so `axiom-sweep.lean` (which does `import CsdLean4`) would never see the
  # planted sorry and the probe would report BROKEN for the wrong reason. Import it from
  # the root module for the duration. (Found 2026-09-04: the probe had been passing
  # vacuously — it is `--with-lean` only, which CI does not run.)
  cp "$ROOT" "$ROOTBAK"
  # Insert AFTER the last import: Lean rejects an import that follows other commands,
  # and a root module that does not parse would fail the sweep for the wrong reason.
  lastimp=$(grep -n '^public import ' "$ROOT" | tail -1 | cut -d: -f1)
  sed -i "${lastimp}a public import CsdLean4.SigmaLayer.GuardSelfTestProbe" "$ROOT"
  lake build >/dev/null 2>&1
  bash scripts/check-axiom-sweep.sh >/dev/null 2>&1
  rc=$?
  mv -f "$ROOTBAK" "$ROOT"
  git rm -q --cached "$PROBE" >/dev/null 2>&1; rm -f "$PROBE"; lake build >/dev/null 2>&1
  if [ "$rc" -eq 0 ]; then
    echo "  BROKEN  axiom-sweep — did NOT fire on a planted sorry"
    fail=1
  else
    pass=$((pass + 1))
  fi

  # (11b) check-gleason-free must fire when a declared module's proofs DO reach Busch.
  # Adding a module that provably does (LF2/Preparation consumes the Busch step) is the same
  # defect as a re-route through the Busch-mediated twin.
  gf="scripts/gleason-free.lean"
  cp "$gf" "$gf.guardbak"
  sed -i 's#CsdLean4.LF4.SingletKahler,#CsdLean4.LF2.Preparation,#' "$gf"
  bash scripts/check-gleason-free.sh >/dev/null 2>&1
  rc=$?
  mv "$gf.guardbak" "$gf"
  if [ "$rc" -eq 0 ]; then
    echo "  BROKEN  gleason-free — did NOT fire on a module whose proofs reach Busch"
    fail=1
  else
    pass=$((pass + 1))
  fi

  # (11) the std-lint RATCHET must fire when a class grows past its pin. Mutating the
  # baseline down by one is the same defect as a new finding appearing, and costs one
  # linter run instead of a rebuild.
  bl="docs/std-lint-baseline.txt"
  cp "$bl" "$bl.guardbak"
  sed -i -E 's/^(unusedArguments[[:space:]]+)([0-9]+)$/\1'"$(( $(sed -nE 's/^unusedArguments[[:space:]]+([0-9]+)$/\1/p' "$bl") - 1 ))"'/' "$bl"
  bash scripts/check-std-lint.sh >/dev/null 2>&1
  rc=$?
  mv "$bl.guardbak" "$bl"
  if [ "$rc" -eq 0 ]; then
    echo "  BROKEN  std-lint — ratchet did NOT fire on a class over its pin"
    fail=1
  else
    pass=$((pass + 1))
  fi
else
  echo "  (skipping axiom-sweep / citation-use / std-lint probes: need --with-lean)"
fi

# --- Every guard must also PASS on the clean tree; a guard stuck at FAIL is equally bad.
for g in check-claim-provenance check-import-negative check-import-hygiene; do
  if ! bash "scripts/$g.sh" >/dev/null 2>&1; then
    echo "  BROKEN  $g — fails on the CLEAN tree"
    fail=1
  else
    pass=$((pass + 1))
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "check-guards: OK ($pass probes; every guard fired on its defect and passed clean)"
else
  echo "check-guards: FAILED — a guard is not detecting what it claims to detect."
fi
exit "$fail"
