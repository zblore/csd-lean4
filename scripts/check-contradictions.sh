#!/usr/bin/env bash
# check-contradictions.sh
#
# Finds the same subject assigned OPPOSITE status in two different places.
#
# Motivating case (2026-07-28): `specs/record-layer-plan.md` said, of the de-isolation
# wall, both "The wall that remains" (line 240) and "DISSOLVED — not a research
# problem" (line 368) — in ONE document — while `SigmaLayer/DeIsolationFlow.lean`
# called it "the open research obligation". An external review found it by reading.
# Nothing mechanical could have: every guard checks a document against the CODE, and
# none checks documents against EACH OTHER.
#
# METHOD. Status claims in this corpus are almost always attached to a backticked
# Lean identifier (`DeIsolationInteraction`, `bornRegion`, `qubitBorn`, …). So key on
# those rather than on a curated topic list: for every identifier mentioned in the
# ledger set, collect the status tokens on the lines where it appears. If the same
# identifier is called SETTLED somewhere and OPEN somewhere else — in different
# files, and neither line is a retraction — report the pair.
#
# It scans BOTH the spec/status docs and the Lean docstrings, because the sharpest
# contradiction in the motivating case was between a plan table and a source file.
#
# ============================ HONEST LIMITS — READ THIS ======================
# THIS IS AN ADVISORY READING LIST, NOT A GATE. Do not treat a PASS as coverage.
#
# 1. IT DOES NOT CATCH ITS OWN MOTIVATING CASE. The row was
#        | ~~2b' feature (A) - "the wall"~~ | **DISSOLVED ...
#    Its SUBJECT is literally named "the wall", so the row trips the open-token
#    test by itself and is discarded as a nuanced single line. Every tuning step
#    that cut the noise (69 -> 15 -> 8 hits) also cut this signal. A grep cannot
#    distinguish "the subject is called the wall" from "the status is open".
#
# 2. PRECISION IS LOW. Of the surviving hits, both that were spot-checked were
#    false positives of the same benign kind: a result proved CONDITIONALLY and
#    described as open UNCONDITIONALLY (`BornFromFlow` - proved given a Birkhoff
#    hypothesis, open because Mathlib lacks it), or a theorem that is proved but
#    has a known open extension (`fs_born_volume_ratio_N` and the `hpos` boundary
#    gap). Those are compatible statements, not contradictions.
#
# 3. WHAT ACTUALLY FOUND THE DEFECT was a human reading the document. That is the
#    honest conclusion: the contradiction class resists mechanisation, which is an
#    argument for the Tier-0 review pass, not a substitute for it.
#
# Use it as: a shortlist of identifiers whose status descriptions are worth
# re-reading. Nothing more.
# =============================================================================
#
# Usage:  bash scripts/check-contradictions.sh          (grep/awk only)
#         bash scripts/check-contradictions.sh --strict (exit 1 on findings)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
STRICT=0
[ "${1:-}" = "--strict" ] && STRICT=1

DOCS="README.md EMPIRICAL.md AXIOMS.md specs/BACKLOG.md specs/record-layer-plan.md
specs/active-todo.md specs/CSD-CHARTER.md specs/reconstruction-status.md
specs/connectivity-manifest.md specs/future-work.md specs/INDEX.md"

SETTLED='DONE|BUILT|DISSOLVED|discharged|DISCHARGED|is complete|CLOSED|closed|settled|SETTLED|proved|PROVED|NOT A TARGET|no longer open'
# 'not proved|NOT proved' added 2026-08-13 (D5 sweep): "What is NOT proved here" was
# classifying as SETTLED via the bare 'proved' token — negation-blindness. With both in
# OPENISH such lines carry both tokens and are skipped as nuanced, which is correct.
OPENISH='OPEN|open item|remains open|the wall|still open|not constructed|not derived|not formalized|not formalised|not proved|NOT proved|is a hypothesis|hypothesis field|residual|RESIDUAL|deferred|blocked|TODO'
# Lines that are self-corrections legitimately mention both sides.
EXEMPT='retracted|RETRACTED|overclaim|overstated|was wrong|is lifted|previously read|previously ended|corrected 20|CORRECTED 20|Corrected 20|Corrected 2026'

echo "check-contradictions: cross-checking status claims between documents…"

# Ledger docs + Lean sources (docstring prose lives in the .lean files).
FILES="$DOCS $(git ls-files 'CsdLean4/**/*.lean' | grep -v 'Tests/AxiomAudit.lean')"

found=0
# Single awk pass: per line, classify status and harvest backticked identifiers.
report="$(printf '%s\n' $FILES | xargs awk -v SET="$SETTLED" -v OPN="$OPENISH" -v EX="$EXEMPT" '
  {
    if ($0 ~ EX) next
    st = ($0 ~ SET); op = ($0 ~ OPN)
    if (!st && !op) next
    # A line carrying BOTH tokens is a nuanced sentence ("X is DONE; Y remains
    # open"), not a verdict. Counting it produced 69 hits, essentially all noise.
    # Only single-verdict lines can contradict each other.
    if (st && op) next
    full=$0
    line=$0; base=0
    while (match(line, /`[A-Za-z][A-Za-z0-9_.]{5,}`/)) {
      id = substr(line, RSTART+1, RLENGTH-2)
      # PROXIMITY. Ledger rows here are single lines carrying many identifiers and
      # several verdicts; line-level keying misattributes them (both spot-checked
      # hits at the line level were false positives for exactly this reason). Only
      # count a verdict that occurs within a window around THIS identifier.
      abspos = base + RSTART
      wstart = abspos - 120; if (wstart < 1) wstart = 1
      win = substr(full, wstart, 240 + RLENGTH)
      wst = (win ~ SET); wop = (win ~ OPN)
      base = base + RSTART + RLENGTH - 1
      if (wst && wop) { line = substr(line, RSTART+RLENGTH); continue }
      if (!wst && !wop) { line = substr(line, RSTART+RLENGTH); continue }
      st = wst; op = wop
      loc = FILENAME ":" FNR
      if (st && index(Sloc[id], loc)==0 && Sn[id] < 3) { Sloc[id] = Sloc[id] " " loc; Sn[id]++ }
      if (op && index(Oloc[id], loc)==0 && On[id] < 3) { Oloc[id] = Oloc[id] " " loc; On[id]++ }
      if (st) Sfile[id] = Sfile[id] " " FILENAME
      if (op) Ofile[id] = Ofile[id] " " FILENAME
      line = substr(line, RSTART+RLENGTH)
    }
  }
  END {
    for (id in Sloc) {
      if (!(id in Oloc)) continue
      # require the two verdicts to come from DIFFERENT files
      diff=0
      n=split(Sfile[id], sf, " ")
      m=split(Ofile[id], of, " ")
      for(i=1;i<=n;i++){ if(sf[i]=="") continue
        for(j=1;j<=m;j++){ if(of[j]=="") continue
          if (sf[i] != of[j]) { diff=1 } } }
      if (!diff) continue
      printf "  CONFLICT  `%s`\n      settled at:%s\n      open at:   %s\n\n", id, Sloc[id], Oloc[id]
    }
  }
')"
if [ -n "$report" ]; then printf '%s\n' "$report"; found=$(printf '%s' "$report" | grep -c 'CONFLICT'); fi

echo
if [ "$found" -eq 0 ]; then
  echo "check-contradictions: PASS — no identifier is called settled in one place and open in another"
  exit 0
fi
echo "check-contradictions: $found identifier(s) carry contradictory status."
echo "  Each is a question: which document is right? Fix the wrong one — do not"
echo "  soften both until they agree."
[ "$STRICT" -eq 1 ] && exit 1
exit 0
