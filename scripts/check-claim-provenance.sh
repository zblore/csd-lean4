#!/usr/bin/env bash
# check-claim-provenance.sh
#
# Catches the two failure modes found on 2026-08-10, neither of which any
# existing guard, the axiom audit, or Lean itself could see. Both were prose
# claims made in places where no proposition could carry them.
#
#   MODE 1 — an UNVERIFIED PROPERTY CLAIM on a definition.
#     `nudgedSinglet` was documented as "the singlet transformed by local basis
#     rotations". It is not: it is the vector of sqrt(P_st), every phase
#     stripped, and at a perp b it is a PRODUCT state while the singlet is
#     maximally entangled. Lean cannot help — a definition is true by fiat,
#     every theorem ABOUT it was true, and the false claim lived only in a
#     docstring. It survived because every consumer used only norms, so any
#     phase-representative passed every proof.
#
#   MODE 2 — a CATEGORY ERROR about what formalisation does.
#     `ContextMap.lean` claimed "type-level separation alone carries the
#     Bell-consistency content; no Fine axiom is needed". Different structures
#     establish only DEFINITIONAL separation: type distinctions are stipulations,
#     not discoveries. Worse, the separation did not prove the no-go — it
#     PREVENTED the no-go from being stated, since per-context domains make the
#     comparison inexpressible. The gap was invisible because the modelling
#     choice hid it.
#
# The unifying rule enforced here:
#
#     Every claim of the form "X establishes Y" must name the theorem that IS Y.
#     If Y cannot be stated as a Lean proposition, that is the signal it is a
#     category error: delete it, or demote it to an explicitly labelled
#     intuition.
#
# Both checks are ALLOWLIST-based in the house style: the declared inventories
# are the single source of truth, and an undeclared occurrence fails.
#
# KNOWN LIMIT — like check-claims.sh these are lexical co-occurrence rules. They
# narrow the surface; they do not close it. A claim phrased in words outside the
# pattern list is invisible. Extend the patterns when a new phrasing is found in
# the wild, and say so in the commit message.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

fail=0
tmp="${TMPDIR:-/tmp}/csd-claim-prov.$$"
trap 'rm -f "$tmp".*' EXIT

# ---------------------------------------------------------------------------
# MODE 2: a structural/type-level fact asserted to carry mathematical content.
# Declared entries are "path|substring"; a hit is permitted only if it is in
# that file AND the line contains the substring. Each carries its reason.
# ---------------------------------------------------------------------------
# 'carries the ... architectural point' and 'structure != structure' were found in the
# wild in specs/LF3-plan.md on 2026-08-10, AFTER the first version of this guard passed
# clean -- exactly the documented failure mode of a lexical rule. Pattern extended.
STRUCTURAL_PATTERN='type-level separation|different types.{0,40}carries|carries the [A-Za-z-]+ (content|architectural point)|no [A-Za-z-]+ axiom is needed|architectural point.{0,40}carries|structure . structure'

cat > "$tmp".allow <<'ALLOW'
CsdLean4/Empirical/QM/Crypto/WiesnerProtocol.lean|non-orthogonality
CsdLean4/SigmaLayer/MixedOntic.lean|PURE states only
CsdLean4/Empirical/CSD/NoCloning.lean|realisability content
CsdLean4/LF6/C1BellConsistency.lean|being different types
CsdLean4/LF3/ContextMap.lean|Type separation alone does NOT
CsdLean4/Tests/AxiomAudit/Dynamics.lean|That is false
scripts/check-claim-provenance.sh|
specs/c1-correction-plan.md|
specs/LF3-plan.md|Corrected 2026-08-10
docs/C1-FORMAL-SUPPORT.md|
specs/publication-errata.md|
specs/VALIDATION-LEDGER.md|Different structures give definitional
specs/c1-closure-report.md|
ALLOW

git ls-files 'CsdLean4/**/*.lean' '*.md' 'specs/*.md' 'docs/*.md' 'scripts/*.sh' \
  | xargs grep -niE "$STRUCTURAL_PATTERN" 2>/dev/null > "$tmp".hits || true

while IFS= read -r hit; do
  [ -z "$hit" ] && continue
  file="${hit%%:*}"; rest="${hit#*:}"; line="${rest#*:}"
  ok=0
  while IFS='|' read -r dfile dsub; do
    [ "$file" = "$dfile" ] || continue
    if [ -z "$dsub" ] || printf '%s' "$line" | grep -qF -- "$dsub"; then ok=1; break; fi
  done < "$tmp".allow
  if [ "$ok" -eq 0 ]; then
    if [ "$fail" -eq 0 ]; then
      echo 'FAIL a structural/type-level fact is claimed to carry mathematical content.'
      echo '     Type distinctions are stipulations, not discoveries. Name the theorem'
      echo '     that establishes the content, or delete the claim.'
    fi
    echo "  $hit"
    fail=1
  fi
done < "$tmp".hits

# ---------------------------------------------------------------------------
# MODE 1: a definition's docstring makes a strong property claim, with neither a
# theorem cited (a backticked snake_case identifier) nor an honesty marker.
#
# The pattern is deliberately NARROW. Phrasings like "rotated by X" or "is
# unitary" describe what a definition CONSTRUCTS, which is self-evident and
# needs no theorem; including them produced only false positives (checked
# 2026-08-10 against ProjectedDynamics, NullSeamWitness, PointerWeights,
# ManyToOnePillars). What is dangerous is asserting IDENTITY with a structural
# object the definition does not manifestly have -- "transformed by", "is the
# image of", "factorises as" -- which is exactly how nudgedSinglet went wrong.
#
# All filtering happens inside ONE awk pass: per-block greps made this guard
# take minutes on Windows.
# ---------------------------------------------------------------------------
git ls-files 'CsdLean4/**/*.lean' | xargs awk '
  BEGIN {
    prop  = "transformed by|is the image of|is a local-unitary|factorises as|is canonical|is the unique"
    mark  = "not proved|NOT proved|posited|by construction|not claimed|open |scope|WARN"
    cite  = "`[a-zA-Z][a-zA-Z0-9]*_[a-zA-Z0-9_]*`"
    skip  = "LF6/SingletDeisolationFlow.lean|LF6/NudgeLocality.lean"
  }
  FNR == 1 { inblk = 0; buf = "" }
  FILENAME ~ skip { next }
  /^\/--/ { buf = $0; inblk = 1; if ($0 ~ /-\//) inblk = 2; next }
  inblk == 1 { buf = buf " " $0; if ($0 ~ /-\//) inblk = 2; next }
  inblk == 2 {
    if ($0 ~ /^(noncomputable )?(def|structure|abbrev) /) {
      if (buf ~ prop && buf !~ mark && buf !~ cite && buf !~ /⚠/)
        print FILENAME "\t" substr(buf, 1, 120)
    }
    inblk = 0; buf = ""
  }
' > "$tmp".props 2>/dev/null || true

while IFS= read -r p; do
  [ -z "$p" ] && continue
  if [ "$fail" -eq 0 ]; then
    echo 'FAIL a definition claims a structural property with no witnessing theorem'
    echo '     and no honesty marker. State the property as a theorem, cite the one'
    echo '     that proves it, or mark it explicitly unproved.'
  fi
  echo "  $p"
  fail=1
done < "$tmp".props

if [ "$fail" -eq 0 ]; then
  echo "check-claim-provenance: OK (no unwitnessed property claims, no type-level content claims)"
fi
exit "$fail"
