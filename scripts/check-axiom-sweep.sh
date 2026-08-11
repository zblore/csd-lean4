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
# Requires a built tree; elaboration only, no rebuild.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

if ! lake env lean scripts/axiom-sweep.lean; then
  echo "check-axiom-sweep: FAILED"
  exit 1
fi
exit 0
