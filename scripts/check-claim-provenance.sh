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
scripts/check-guards.sh|
specs/c1-correction-plan.md|
specs/LF3-plan.md|Corrected 2026-08-10
docs/C1-FORMAL-SUPPORT.md|
specs/publication-errata.md|
specs/VALIDATION-LEDGER.md|Different structures give definitional
specs/c1-closure-report.md|
ALLOW

# MULTILINE (2026-08-11). This was a line-by-line grep, carrying exactly the wrapping
# weakness that let an instance slip past mode 3: `different types.{0,40}carries` cannot
# match when the phrase wraps, and doc comments wrap. Now PARAGRAPH-scoped -- lines are
# joined up to a blank line, which is the right unit for both Lean doc blocks and Markdown
# prose, and keeps the allowlist meaningful (a whole-file join would let one excusing
# phrase anywhere excuse everything in the file).
git ls-files 'CsdLean4/**/*.lean' '*.md' 'specs/*.md' 'docs/*.md' 'scripts/*.sh' \
  | xargs awk -v pat="$STRUCTURAL_PATTERN" '
      function flush() {
        if (fname != "" && buf != "" && tolower(buf) ~ tolower(pat))
          print fname "\t" buf
        buf = ""
      }
      FNR == 1 { flush(); fname = FILENAME }
      /^[ \t]*$/ { flush(); next }
      { buf = (buf == "" ? $0 : buf " " $0) }
      END { flush() }
    ' 2>/dev/null > "$tmp".hits || true

while IFS= read -r hit; do
  [ -z "$hit" ] && continue
  file="${hit%%$'\t'*}"; line="${hit#*$'\t'}"
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
    echo "  $file: $(printf '%s' "$line" | cut -c1-110)"
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
  # The block match above is already multiline -- buf holds the WHOLE doc block, so a
  # wrapped phrase matches. The bug fixed here (2026-08-11) was on the other side: this
  # used to demand that the VERY NEXT line be the declaration, so a docstring followed by
  # a blank line, an attribute, or an `omit ... in` was silently discarded and never
  # checked at all. Skip over those instead, and accept the modifiers actually used here.
  inblk == 2 {
    if ($0 ~ /^[ \t]*$/ || $0 ~ /^@\[/ || $0 ~ /^omit / || $0 ~ /^open / || $0 ~ /^variable /) next
    if ($0 ~ /^(private |protected |public |noncomputable |partial |unsafe )*(def|structure|abbrev|instance) /) {
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

# ---------------------------------------------------------------------------
# MODE 3: "every/all Bell-test setting" attached to an hgen-restricted claim.
#
# Added 2026-08-11 after an external verification of 7347e62 found this wording
# surviving in JointEig.lean, SingletDeisolationFlow.lean and specs/LF4-todo.md
# -- places the item-31 sweep did not reach. `hgen` excludes the collinear
# settings a.b = +-1, so "every Bell-test setting" is false: Bell experiments
# routinely discuss aligned and anti-aligned axes. Correct wording is "the
# generic non-collinear contexts" or "the four canonical CHSH-optimal pairs".
# ---------------------------------------------------------------------------
# WARNING - MULTILINE. A line-by-line grep MISSED an instance in
# LocalDeisolationFlow.lean on 2026-08-11 because the phrase was wrapped across
# two lines. Doc comments wrap, so any prose rule that greps line-by-line is
# unreliable by construction. This joins each file's lines with awk before
# matching, and reports the file (a joined stream has no useful line number).
# ONE awk pass: buffers each file, joins its lines, matches on the joined text.
# Per-file awk spawns took 8 minutes on Windows; this takes seconds.
git ls-files 'CsdLean4/**/*.lean' '*.md' 'specs/*.md' 'docs/*.md' \
  | grep -v 'check-claim-provenance' \
  | xargs awk '
      function flush(   s, low, seg, from) {
        if (fname == "") return
        s = buf; low = tolower(s)
        while (match(low, /(all|every)[ \t]+bell-test[ \t]+setting/)) {
          from = (RSTART > 80) ? RSTART - 80 : 1
          seg = substr(s, from, 130)
          if (tolower(seg) !~ /too broad|was false|corrected 20|previously|excluded here/)
            print "  " fname ": " seg
          s = substr(s, RSTART + RLENGTH); low = tolower(s)
        }
      }
      FNR == 1 { flush(); fname = FILENAME; buf = "" }
      { buf = buf " " $0 }
      END { flush() }
    ' > "$tmp".bell 2>/dev/null || true

while IFS= read -r b; do
  [ -z "$b" ] && continue
  if [ "$fail" -eq 0 ]; then
    echo 'FAIL "every/all Bell-test setting" attached to a genericity-restricted claim.'
    echo '     hgen excludes the collinear settings a.b = +-1. Say "the generic'
    echo '     non-collinear contexts" or "the four canonical CHSH-optimal pairs".'
  fi
  echo "$b"
  fail=1
done < "$tmp".bell

# ---------------------------------------------------------------------------
# MODE 4: an UNWITNESSED REASON for a formal restriction.
#
# Added 2026-08-11. The C1 correction and the prose audit both found defects of
# a shape modes 1-3 cannot see: prose giving a REASON for a formal fact, where
# the theorem is true and only the explanation is false. Modes 1-3 target claims
# ABOUT OBJECTS, so a wrong reason attached to a true statement trips nothing,
# and Lean cannot help -- nothing in Lean states reasons, so nothing can
# disagree with one.
#
# Retroactively detecting a WRONG reason is not mechanisable. But requiring a
# reason to NAME ITS WITNESS when written is, and that is enough: a wrong reason
# then has nothing to point at. The two known instances both fail this rule.
#
#   - "hgen excludes collinear settings because ..." -- the real cause was
#     division by sqrt(P_st), named nowhere.
#   - "restricted to [0,1) because Lebesgue measure on the line is infinite" --
#     fibreTypicality is a PROBABILITY measure and the restriction was not
#     forced (fibreTypicality_uncovered_univ). Neither fact was cited, because
#     citing either would have exposed the reason as false.
#
# RULE. A doc block that gives a causal reason (because / since / the reason)
# for a restriction (restrict / excluded / by hand / genericity / hgen /
# degenerate) must EITHER cite a theorem (a backticked snake_case identifier)
# OR carry an explicit marker that the reason is unwitnessed (a warning sign,
# "not proved", "posited", "intuition", "informal", "motivation").
#
# Measured cost when introduced: 67 reason-blocks corpus-wide, 7 unwitnessed.
# All 7 were resolved rather than grandfathered, so this needs no ratchet and
# has no legacy allowlist. Keep it that way -- an allowlist here would re-admit
# exactly the class the rule exists to exclude.
#
# ONE awk pass, for the Windows performance reasons documented above.
git ls-files 'CsdLean4/**/*.lean' | xargs awk '
  BEGIN {
    cause = "because|since |the reason|owing to|which is why"
    restr = "restrict|excluded|only holds|by hand|genericity|hgen|must be stated|degenerate"
    # NOTE the dots. Mode 1 uses `[a-zA-Z][a-zA-Z0-9]*_...`, which rejects NAMESPACED
    # identifiers -- and namespaced is the norm here. When mode 4 was first run that regex
    # produced a false positive on ContextFixedA7FS.lean, which was correctly citing
    # `ContextFixedA7.joint_degenerate_of_sum_eq_one` all along. A guard that cannot recognise
    # a normal Lean name would train authors to write worse citations to appease it.
    cite  = "`[A-Za-z][A-Za-z0-9.]*_[A-Za-z0-9_.]*`"
    mark  = "not proved|NOT proved|posited|intuition|informal|motivation"
  }
  function flush(   low) {
    if (fname == "" || buf == "") return
    low = tolower(buf)
    if (low ~ cause && low ~ restr && buf !~ cite && buf !~ mark && buf !~ /⚠/)
      print "  " fname ": " substr(buf, 1, 110)
  }
  FNR == 1 { flush(); fname = FILENAME; buf = ""; inblk = 0 }
  /^\/-[-!]/ { flush(); buf = $0; inblk = 1; if ($0 ~ /-\//) { flush(); inblk = 0; buf = "" } next }
  inblk { buf = buf " " $0; if ($0 ~ /-\//) { flush(); inblk = 0; buf = "" } }
  END { flush() }
' > "$tmp".reason 2>/dev/null || true

while IFS= read -r r; do
  [ -z "$r" ] && continue
  if [ "$fail" -eq 0 ]; then
    echo 'FAIL a doc block gives a REASON for a formal restriction without naming its'
    echo '     witness. Cite the theorem that establishes the reason, or mark the reason'
    echo '     explicitly unwitnessed. A reason that can cite nothing is the shape both'
    echo '     known prose defects had.'
  fi
  echo "$r"
  fail=1
done < "$tmp".reason

if [ "$fail" -eq 0 ]; then
  echo "check-claim-provenance: OK (no unwitnessed property claims, no type-level content claims, no unwitnessed reasons)"
fi
exit "$fail"
