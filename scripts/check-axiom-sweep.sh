#!/usr/bin/env bash
# check-axiom-sweep.sh
#
# Runs scripts/axiom-sweep.lean: every CSD declaration, not just the pinned ones, must
# depend only on [propext, Classical.choice, Quot.sound].
#
# WHY THIS EXISTS. `lake build` EXITS 0 ON A `sorry` -- it is a warning, not an error
# (verified 2026-08-11 by planting one). The AxiomAudit pins catch a sorry as `sorryAx`,
# but only for PINNED constants: 1843 pins is a curated subset, not a cover. A sorry in
# an unpinned lemma passed every gate.
#
# COVERAGE PRECONDITION (added 2026-09-04, the hardening session). The sweep runs on the
# environment of `import CsdLean4`, so it can only see what that import EXPORTS. Under the
# module system a theorem's proof term is exported only from an `@[expose] public section`;
# verified by planting one: a module-private `theorem … := by sorry` consumed by a public
# theorem in a module WITHOUT that section passes the sweep clean. Every declaring module in
# this corpus has the section (583 of 583 on 2026-09-04) — that is what makes the sweep a
# cover, and it is now checked here rather than assumed. The three modules without it
# (`CsdLean4/Basic.lean` and the two `Tests/` umbrellas) declare nothing.
#
# Requires a built tree; elaboration only, no rebuild.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# One `grep -L` pass for the modules WITHOUT the section, then keep only those that
# actually declare something (the three umbrellas declare nothing and are fine).
unexposed=$(git ls-files 'CsdLean4/*.lean' 'CsdLean4/**/*.lean' \
  | xargs grep -L '@\[expose\] public section' \
  | xargs -r grep -l -E '^(public )?(noncomputable )?(theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom) ')
if [ -n "$unexposed" ]; then
  echo "FAIL these modules declare something but have no \`@[expose] public section\`, so their"
  echo "     proof terms are not exported and this sweep cannot see a \`sorry\` inside them:"
  printf '%s\n' "$unexposed" | sed 's/^/       /'
  exit 1
fi

if ! lake env lean scripts/axiom-sweep.lean; then
  echo "check-axiom-sweep: FAILED"
  exit 1
fi
exit 0
