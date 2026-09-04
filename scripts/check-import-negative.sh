#!/usr/bin/env bash
# check-import-negative.sh
#
# Asserts that certain modules are ABSENT from another module's transitive import
# closure. The Lean/Mathlib idiom for this is `assert_not_exists`; this repository used
# none, and paid for it -- see below.
#
# WHY. `docs/C1-FORMAL-SUPPORT.md` and `specs/c1-closure-report.md` both state that
# `EffectGleason` is NOT in the transitive import closure of
# `LF6/LocalDeisolationFlow.lean`, so the Born-volume route "never reaches Busch at all".
# That is a load-bearing claim -- it is the difference between "clean axiom bookkeeping"
# and "the route structurally cannot depend on the effect-Gleason result" -- and it was
# established by a ONE-OFF CHECK and then written into prose. Nothing re-checked it. One
# added `public import` would have made both documents false, silently.
#
# This is the same failure this repository keeps finding in different clothes: a true
# claim, checked once, recorded in prose, with no mechanism to notice when it stops being
# true. An import-closure fact is trivially mechanisable, so there is no excuse for
# leaving it to prose.
#
# Declared inventory below is the single source of truth, in the house style.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# "root-module|forbidden-module|why"
#
# THE GLEASON-FREE FAMILY (added 2026-09-04). 56 module headers assert Gleason-freeness.
# The 44 below plus GlobalRecordClosure make that claim STRUCTURALLY: `LF2/EffectGleason`
# is absent from their transitive import closure, so no proof of theirs can reach Busch
# whatever anyone edits inside them. That is the strong form, and it is what this guard
# checks. `GlobalRecordClosure` (CL-011, the Sigma-side Born road) is listed although its
# header does not use the phrase: the claim is made ABOUT it, in `docs/glossary.yaml`
# (`gleason-theorem`: "CSD's own Born derivation ... never touches this theorem") and in the
# reports, so it needs the same cover.
#
# NOT LISTED, and NOT covered by this guard: 12 modules whose headers claim the WEAKER,
# proof-term form -- they do import `EffectGleason` transitively and route around Busch
# inside their proofs (`MalusVolume`, `MachZehnderVolume`, `SternGerlachVolume`,
# `VolumeCanonical`, `KS18Volume`, `MerminPeresVolume`, `KCBSVolume`,
# `ElitzurVaidmanVolume`, `Metrology/Ramsey`, `SingletKahler`, `SingletKahlerFlow`,
# `Tests/Witnesses/SingletBell`). Their headers are careful about this (`SingletKahler`:
# "routes through the Busch-free `OP_p_at_jointEig_eq_P_st_direct` ... not through the
# Busch-mediated twin"). Checked by hand 2026-09-04 with a constant-graph walk -- 259
# declarations, none reaching `effect_gleason_representation` -- and TRUE THEN. An
# import-closure guard cannot see it; one re-route through the Busch-mediated twin would
# make 12 headers false silently. That is now checked, at the constant-graph level, by
# `scripts/check-gleason-free.sh` (2026-09-04) — the two guards are complementary: this one
# says a proof CANNOT reach Busch, that one says it DOES not.
PAIRS='
CsdLean4.LF6.LocalDeisolationFlow|CsdLean4.LF2.EffectGleason|C1 Born-volume route must not reach Busch/effect-Gleason
CsdLean4.Empirical.CSD.BellVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.ContextVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.GHZVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.HardyVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.LeggettGargVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.MUB3Volume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.MixedStateBornVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.QuantumZeno|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.QutritPOVMVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.SIC3Volume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.SICVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.TrineVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.USDVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.UncertaintyVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.CSD.WeakMeasurement|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Empirical.QM.Algorithms.ShorCapstone|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.BornFS|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.BornFlowLinkage|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.BornFrequencyPartition|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.BornRegionUncond|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.BothPillars|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.ManyToOnePillars|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.MomentBornN|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.ObservableCorrespondenceN|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.POVMVolume|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF4.TrialWitness|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF5.Capstone|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF5.CapstoneCanonical|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF5.DilationFromFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF5.FlowBornFrequency|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF5.SyndromeFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF5.SyndromeOutcome|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.CGLMPQudit|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.CGLMPQutrit|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.Decoherence|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.GHZDeisolationFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.GHZLocalFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.GHZMerminCarve|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.GHZnDeisolationFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.LocalDeisolationFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.MaxEntangledCGLMPCapstone|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.MaxEntangledDeisolationFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.LF6.SingletDeisolationFlow|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.Thermo.CanonicalTypicality|CsdLean4.LF2.EffectGleason|header asserts Gleason-free
CsdLean4.RecordLayer.GlobalRecordClosure|CsdLean4.LF2.EffectGleason|CL-011 cited as the Gleason-free Sigma-side road
'

fail=0

# Adjacency: "Module<TAB>Import" for every tracked Lean module, in one awk pass.
adj="$(git ls-files 'CsdLean4/**/*.lean' | xargs awk '
  FNR == 1 {
    mod = FILENAME
    sub(/\.lean$/, "", mod)
    gsub(/\//, ".", mod)
  }
  /^[ \t]*(public |private |meta )*import / {
    line = $0
    sub(/^[ \t]*(public |private |meta )*import[ \t]+/, "", line)
    sub(/[ \t]*$/, "", line)
    if (line != "") print mod "\t" line
  }
')"

# ONE awk pass for every declared pair: build the adjacency once, BFS per pair. (Per-pair
# awk invocations cost ~0.6 s each once the inventory grew past 40 rows; this is ~3 s total.)
violations="$(printf '%s\n' "$adj" | awk -v pairs="$PAIRS" '
  { edge[$1] = edge[$1] " " $2 }
  END {
    n = split(pairs, lines, "\n")
    for (p = 1; p <= n; p++) {
      if (lines[p] ~ /^[ \t]*$/) continue
      split(lines[p], f, "|")
      root = f[1]; target = f[2]; why = f[3]
      delete seen; delete queue
      cnt = 1; queue[1] = root; seen[root] = 1; hit = 0
      for (i = 1; i <= cnt && !hit; i++) {
        split(edge[queue[i]], outs, " ")
        for (j in outs) {
          m = outs[j]
          if (m == "" || seen[m]) continue
          if (m == target) { hit = 1; break }
          seen[m] = 1; queue[++cnt] = m
        }
      }
      if (hit) print root "|" target "|" why
    }
  }')" || { echo "FAIL the BFS pass errored — the guard cannot report a clean tree."; exit 1; }

# A guard that reports nothing because its own machinery broke is worse than no guard: the
# BFS must have SEEN every declared root. (2026-09-04: an escaping slip made awk abort, and
# the empty result read as "all claims hold".)
missing="$(comm -23 \
  <(printf '%s\n' "$PAIRS" | grep '|' | cut -d'|' -f1 | sort -u) \
  <(printf '%s\n' "$adj" | cut -f1 | sort -u))"
if [ -n "$missing" ]; then
  echo 'FAIL a declared root is not a tracked Lean module — a renamed or deleted module'
  echo '     leaves its independence claim unchecked:'
  printf '%s\n' "$missing" | sed 's/^/       /'
  exit 1
fi

if [ -n "$violations" ]; then
  echo 'FAIL a module reaches a forbidden import. A documented independence claim is'
  echo '     now false. Fix the import, or correct every document asserting it.'
  printf '%s
' "$violations" | while IFS='|' read -r root forbidden why; do
    echo "  $root  ->  $forbidden"
    echo "      why this was asserted: $why"
  done
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "check-import-negative: OK (all declared import-independence claims hold)"
fi
exit "$fail"
