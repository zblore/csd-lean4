#!/usr/bin/env bash
# check-citation-use.sh
#
# Runs scripts/citation-use.lean, which checks that a theorem named in a REASON clause is
# actually used by the proof of the declaration whose restriction it explains.
#
# This is the mechanisable part of the residue check-claim-provenance.sh mode 4 leaves:
# mode 4 forces a reason to name a witness, and this checks the witness does the work.
# What remains unmechanised is a citation that IS used but does not establish the stated
# reason -- that needs a reader. See specs/prose-audit.md.
#
# It needs proof terms, so unlike every other guard here it runs inside Lean rather than
# over text. Requires a built tree (it imports CsdLean4); elaboration only, no rebuild.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

if ! lake env lean scripts/citation-use.lean; then
  echo "check-citation-use: FAILED"
  exit 1
fi
exit 0
