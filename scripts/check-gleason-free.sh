#!/usr/bin/env bash
# check-gleason-free.sh
#
# Runs scripts/gleason-free.lean: for every module whose header claims its PROOFS avoid the
# Gleason/Busch reconstruction, no declaration in it may transitively reference one of the
# forbidden roots.
#
# WHY THIS EXISTS. 56 module headers in this corpus assert Gleason-freeness. For 44 of them
# the claim is structural — `LF2/EffectGleason.lean` is not in the transitive import closure —
# and `check-import-negative.sh` checks that (46 declared pairs). The rest sit downstream of
# LF2/LF3, DO import it, and claim only that their proof terms route around it:
#
#     SingletKahler.lean: "the LF3 chain's `weight_eq_P_st` routes through the Busch-free
#     `OP_p_at_jointEig_eq_P_st_direct` ... not through the Busch-mediated twin"
#
# That claim is invisible to an import guard. It was checked by hand on 2026-09-04 (259
# declarations, none reaching the constant) and was true then — which is exactly the state
# `check-import-negative.sh`'s own header warns about: a true claim, checked once, recorded in
# prose, with nothing to notice when it stops being true. One re-route through the
# Busch-mediated twin would falsify eleven headers silently, and the corpus's headline
# framing with them: `docs/glossary.yaml` (`gleason-theorem`) tells readers that CSD's Born
# derivation "never touches this theorem".
#
# WHAT THE 2026-09-29 REVIEW CHANGED (CR-GLEASON-005, `specs/reviews/`). The guard used to
# forbid the Busch headline alone and to recurse through `CSD.*` constants only, so a route
# through `qdensity`, through row 57's projection-valued Gleason, or through a helper in
# another namespace was invisible to it. It now checks eight reconstruction roots, traverses
# every local and `CsdLean4.*` declaration whatever its namespace, covers the SingletBell
# witness that the old scope note excluded, and self-tests before the scan: six alias routes
# must be caught and one benign scalar lemma must not be.
#
# Requires a built tree (`CsdLean4` and `CsdLeanTests`); elaboration only, no rebuild.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

if ! lake env lean scripts/gleason-free.lean; then
  echo "check-gleason-free: FAILED"
  exit 1
fi
exit 0
