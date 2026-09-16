#!/usr/bin/env bash
# export-physlib.sh
#
# The Physlib export of the Fubini–Study geometry of ℂℙⁿ and its Fisher–Rao bridge
# (Physlib PR #1652, Nava-Hernandez; CsdLean4/Interop/Physlib/).
#
# WHAT IT DOES. The root module CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean imports
# exactly the closure Physlib is offered. This script (logic in scripts/export_physlib.py):
#
#   1. computes that closure within CsdLean4/Mathlib/ and groups it into the concept slices of
#      scripts/physlib-slices.txt, validated against the import graph (slice k depends only on
#      slices 1..k-1), each a Physlib PR (or several, per their ~200-line guideline);
#   2. writes slice N to export/physlib/slice-N/ with the module rename to the Physlib layout
#      (Analysis/InformationGeometry/* -> QuantumInfo/ForMathlib/*, beside PR #1652's own file;
#      everything else -> PhyslibAlpha/* by default, QuantumInfo/ForMathlib/* with
#      --target quantuminfo) and this repository's convention paragraphs stripped; the mirror
#      of PR #1652's file is never in a slice;
#   3. scans the exported text for repository-specific vocabulary outside provenance paragraphs
#      and reports it (--strict fails on any hit);
#   4. checks that every closure module has an `@[expose] public section` (without it the module
#      system hides proof terms from the axiom sweep);
#   5. builds slices 1..N against Physlib's Mathlib pin in a scratch Lake project under
#      export/physlib/build-N/ with `lake build --wfail` (--no-build skips). When Physlib's pin
#      equals this repository's the scratch project shares .lake/packages with it (a junction /
#      symlink), so no download and no second Mathlib; otherwise it requires Mathlib at Physlib's
#      rev. A failed build fails this script. Every result is recorded against a hash of the
#      exported sources, toolchain, Mathlib rev and layout (INPUTS.sha256), so a stale result
#      never stands in for a build of the current export;
#   6. runs scripts/physlib-axiom-sweep.lean (every constant of the closure, foundational
#      triple only) and writes CsdLean4/Interop/Physlib/MANIFEST.md (--manifest).
#
# export/ is git-ignored. The Physlib PR is this script's output: when csd-lean4 moves, the
# PR regenerates rather than drifting.
#
# Usage:
#   scripts/export-physlib.sh --table                 # the slice table and hygiene count
#   scripts/export-physlib.sh --slice 2               # export + build slices 1..2
#   scripts/export-physlib.sh --all --manifest        # everything, then the manifest
#   scripts/export-physlib.sh --slice 9 --no-build --manifest
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

"$PY" scripts/export_physlib.py --self-test

if [ "$TABLE" -eq 1 ]; then
  "$PY" scripts/export_physlib.py --table --target "$TARGET"
  exit 0
fi

OUT="export/physlib"
args=(--target "$TARGET" --out "$OUT" --local-packages)
if [ "$ALL" -eq 1 ]; then args+=(--all); elif [ -n "$SLICE" ]; then args+=(--slice "$SLICE"); fi
[ -n "$STRICT" ] && args+=("$STRICT")
"$PY" scripts/export_physlib.py "${args[@]}"

# (4) exposure precondition of the sweep: every closure module has `@[expose] public section`.
unexposed="$("$PY" - <<'EOF'
import sys; sys.path.insert(0, "scripts"); import export_physlib as ex
deps, _ = ex.closure(ex.ROOT_MODULE)
for m in sorted(deps):
    if "@[expose] public section" not in ex.read(ex.mod_to_path(m)):
        print(ex.mod_to_path(m))
EOF
)"
if [ -n "$unexposed" ]; then
  echo "export-physlib: FAIL closure modules without @[expose] public section (the sweep cannot see their proofs):"
  printf '%s\n' "$unexposed" | sed 's/^/    /'
  exit 1
fi

# Which build projects does this invocation cover?
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

# Build results persist in export/physlib/build-results.json, keyed by "slices 1..N @ <hash>",
# where the hash covers everything that determines the build. A manifest run reports only the
# results whose hash matches the current export; the driver never reuses a stale one.
RESULTS="$OUT/build-results.json"
[ -f "$RESULTS" ] || echo "{}" > "$RESULTS"
record() {  # record <key> <result>
  "$PY" - "$RESULTS" "$1" "$2" <<'EOF'
import json, sys
p, k, r = sys.argv[1:4]
d = json.load(open(p, encoding="utf-8")); d[k] = r
json.dump(d, open(p, "w", encoding="utf-8"), indent=1, sort_keys=True)
EOF
}

failed=0
for n in "${slices[@]}"; do
  bdir="$OUT/build-$n"
  key="slices 1..$n @ $(cat "$bdir/INPUTS.sha256")"
  if [ "$BUILD" -eq 1 ]; then
    link_packages "$bdir"
    echo "export-physlib: building slices 1..$n in $bdir (lake build --wfail) …"
    if (cd "$bdir" && lake build --wfail 2>&1 | tail -3); then
      res="built clean ($(date -u +%Y-%m-%d))"
    else
      res="BUILD FAILED ($(date -u +%Y-%m-%d))"; failed=1
    fi
    echo "export-physlib: $key: $res"
    record "$key" "$res"
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
  # Only results whose hash matches the CURRENT export are reported.
  current="$("$PY" - "$RESULTS" "$TARGET" <<'EOF'
import json, subprocess, sys
p, target = sys.argv[1:3]
d = json.load(open(p, encoding="utf-8"))
sys.path.insert(0, "scripts"); import export_physlib as ex
deps, _ = ex.closure(ex.ROOT_MODULE); slices = ex.load_slices(deps)
rev = ex.physlib_mathlib_rev() or ex.local_mathlib_rev()
tgt = ex.TARGETS[target]
keep = {}
for k, v in d.items():
    n = int(k.split("..")[1].split(" @")[0])
    h = ex.build_inputs_hash([m for _, ms in slices[:n] for m in ms], tgt, rev)
    if k.endswith("@ " + h):
        keep[k] = v
print(json.dumps(keep))
EOF
)"
  "$PY" scripts/export_physlib.py --manifest --target "$TARGET" --out "$OUT" \
    --build-results "$current" --sweep-output "$sweep_out"
  rm -f "$sweep_out"
fi
if [ "$failed" -ne 0 ]; then
  echo "export-physlib: FAIL (a scratch build failed; see above)"
  exit 1
fi
echo "export-physlib: done"
