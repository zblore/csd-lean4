#!/usr/bin/env bash
# export-physlib.sh
#
# The Physlib export of the Fubini–Study geometry of ℂℙⁿ and its Fisher–Rao bridge
# (Physlib PR #1652, Nava-Hernandez; specs/… and CsdLean4/Interop/Physlib/).
#
# WHAT IT DOES. The root module CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean imports
# exactly the closure Physlib is offered. This script (logic in scripts/export_physlib.py):
#
#   1. computes that closure within CsdLean4/Mathlib/ and cuts it into slices in dependency
#      order (slice k depends only on slices 1..k-1), each a Physlib PR readable in a sitting;
#   2. writes slice N to export/physlib/slice-N/ with the module rename to the Physlib
#      layout (Analysis/InformationGeometry/* -> QuantumInfo/ForMathlib/*, beside PR #1652's
#      own file; everything else -> PhyslibAlpha/* by default, QuantumInfo/ForMathlib/* with
#      --target quantuminfo);
#   3. scans the exported text for CSD-specific vocabulary outside provenance paragraphs and
#      reports it (--strict fails on any hit);
#   4. builds slices 1..N against Physlib's Mathlib pin in a scratch Lake project under
#      export/physlib/build-N/ (--no-build skips). When Physlib's pin equals this repository's
#      the scratch project shares .lake/packages with it (a junction / symlink), so no
#      download and no second Mathlib; otherwise it requires Mathlib at Physlib's rev;
#   5. runs scripts/physlib-axiom-sweep.lean (every declaration of the closure, foundational
#      triple only) and writes CsdLean4/Interop/Physlib/MANIFEST.md (--manifest).
#
# export/ is git-ignored. The Physlib PR is this script's output: when csd-lean4 moves, the
# PR regenerates rather than drifting.
#
# Usage:
#   scripts/export-physlib.sh --table                 # the slice table and hygiene count
#   scripts/export-physlib.sh --slice 1               # export + build slice 1
#   scripts/export-physlib.sh --all --manifest        # everything, then the manifest
#   scripts/export-physlib.sh --slice 6 --no-build --manifest
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# python3 on a Windows box may be the Store alias stub; prefer whichever interpreter runs.
if python3 -c 'import sys' >/dev/null 2>&1; then PY=python3; else PY=python; fi

SLICE=""; ALL=0; TARGET="alpha"; BUILD=1; STRICT=""; MANIFEST=0; TABLE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --slice) SLICE="$2"; shift 2 ;;
    --all) ALL=1; shift ;;
    --target) TARGET="$2"; shift 2 ;;
    --no-build) BUILD=0; shift ;;
    --strict) STRICT="--strict"; shift ;;
    --manifest) MANIFEST=1; shift ;;
    --table) TABLE=1; shift ;;
    *) echo "export-physlib: unknown argument $1" >&2; exit 2 ;;
  esac
done

if [ "$TABLE" -eq 1 ]; then
  "$PY" scripts/export_physlib.py --table --target "$TARGET"
  exit 0
fi

OUT="export/physlib"
args=(--target "$TARGET" --out "$OUT" --local-packages)
if [ "$ALL" -eq 1 ]; then args+=(--all); elif [ -n "$SLICE" ]; then args+=(--slice "$SLICE"); fi
[ -n "$STRICT" ] && args+=("$STRICT")
"$PY" scripts/export_physlib.py "${args[@]}"

# Which slices exist now?
slices=()
if [ "$ALL" -eq 1 ] || [ -n "$SLICE" ]; then
  for d in "$OUT"/build-*; do
    [ -d "$d" ] || continue
    n="${d##*/build-}"
    if [ "$ALL" -eq 1 ] || [ "$n" = "$SLICE" ]; then slices+=("$n"); fi
  done
fi

link_packages() {
  # Share this repository's .lake/packages with the scratch project when the manifests agree.
  local bdir="$1"
  if [ ! -f "$bdir/lake-manifest.json" ]; then return 0; fi   # git require: lake fetches
  mkdir -p "$bdir/.lake"
  if [ -e "$bdir/.lake/packages" ]; then return 0; fi
  local src; src="$(pwd)/.lake/packages"
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
      MSYS_NO_PATHCONV=1 cmd /c mklink /J "$(cygpath -w "$bdir/.lake/packages")" "$(cygpath -w "$src")" > /dev/null ;;
    *) ln -s "$src" "$bdir/.lake/packages" ;;
  esac
}

# Build results persist across invocations in export/physlib/build-results.json, so a manifest
# can report slice 1 and the full tree without rebuilding the cumulative projects in between.
RESULTS="$OUT/build-results.json"
[ -f "$RESULTS" ] || echo "{}" > "$RESULTS"
record() {  # record <slice> <result>
  "$PY" - "$RESULTS" "$1" "$2" <<'EOF'
import json, sys
p, n, r = sys.argv[1:4]
d = json.load(open(p, encoding="utf-8")); d[n] = r
json.dump(d, open(p, "w", encoding="utf-8"), indent=1, sort_keys=True)
EOF
}

for n in "${slices[@]}"; do
  bdir="$OUT/build-$n"
  if [ "$BUILD" -eq 1 ]; then
    link_packages "$bdir"
    echo "export-physlib: building slices 1..$n in $bdir …"
    if (cd "$bdir" && lake build 2>&1 | tail -3); then res="built clean"; else res="BUILD FAILED"; fi
    echo "export-physlib: slice $n: $res"
    record "$n" "$res ($(date -u +%Y-%m-%d))"
  else
    echo "export-physlib: slice $n: exported, not built (--no-build)"
  fi
done

if [ "$MANIFEST" -eq 1 ]; then
  sweep_out="$(mktemp)"
  echo "export-physlib: running scripts/physlib-axiom-sweep.lean …"
  # (no `| head` here: under pipefail a closed pipe would abort the script before the manifest)
  lake env lean scripts/physlib-axiom-sweep.lean > "$sweep_out"
  sed -n '1p' "$sweep_out"
  "$PY" scripts/export_physlib.py --manifest --target "$TARGET" --out "$OUT" \
    --build-results "$(cat "$RESULTS")" --sweep-output "$sweep_out"
  rm -f "$sweep_out"
fi
echo "export-physlib: done"
