#!/usr/bin/env bash
# check-review-surface.sh
#
# Triages the corpus for an EXPERT-REVIEW pass — the defect class where everything
# compiles, is axiom-pinned, and reads correctly, but the DEFINITIONS, STATEMENTS,
# and API SURFACE would not survive a library reviewer.
#
# Motivating case: Ilin & Nugent, "Sorries Are Not the Hard Part: An Expert-Review
# Case Study of a Semi-Autonomous Formalization" (arXiv 2606.13925, June 2026). A
# semi-autonomous Lean proof of Grothendieck's vanishing theorem compiled sorry-free;
# a mathlib expert then reviewed it as library code and found that of 62
# agent-generated definitions exactly ONE was written correctly. Their categories:
# file structure, definitions, theorem statements, API design, proof style. Their
# model was one expert-week of review for ONE theorem. This corpus has ~1,300
# definitions and ~4,100 statements — roughly 25 expert-weeks at that rate — so the
# review must be triaged mechanically first: this script RANKS candidates, a human
# decides. That division is also what their paper found: agents handle local
# mechanically-checkable feedback well and global design badly.
#
# ⚠️ EVERY METRIC HERE IS A PROXY. The paper's own warning is that a mechanical
# gate is powerful when it matches the quality target and dangerous when it is only
# a proxy for it. Reference counts, unfold counts, name lengths and have densities
# CORRELATE with review findings; none of them IS one. The script reports
# questions, not verdicts, and must never be read as a quality score.
#
# STATUS UPGRADE (2026-08-06): library-grade code is now an ADOPTED STANDARD
# (CONVENTIONS.md §9, work queue BACKLOG §F), so the findings are ranked work
# against a real target rather than a hypothetical one. Enforcement is the §9.5
# DIFF DISCIPLINE — baseline re-captured per release tag; landings that increase
# the (B) no-API count or add theorem-style def names must justify it in the
# commit message. The script itself stays NON-BLOCKING: the counts still include
# by-design patterns (obligation Props, blessed physics notation), and a blocking
# gate on a proxy remains the failure mode this header warns against.
#
# WHAT IT REPORTS
#   (A) thin definitions    — defs/abbrevs referenced only 1–2 times outside their
#                             own declaration (the zero case is check-vacuity's)
#   (B) defs with no API    — definitions that proofs reach THROUGH (unfold/delta/
#                             simp [name]) versus lemmas stated ABOUT them; a def
#                             unfolded repeatedly with no lemma interface is the
#                             paper's central API finding
#   (C) over-specialised    — theorems/lemmas referenced EXACTLY ONCE corpus-wide:
#       statements            "the agent proved exactly what it needed and nothing
#                             more". AxiomAudit-PINNED names are treated as declared
#                             headlines and excluded (a pin is the corpus's own
#                             top-level-result registry)
#   (D) proof-style         — per-file `have` density and longest proof blocks,
#       outliers              as outliers against the corpus distribution ("long
#                             walls of have statements")
#   (E) name shape          — def names unusually long / unusually many underscore
#                             segments against the corpus distribution (their
#                             example: sheafH_filtered_colimit_h1_sectionsFunctor)
#
# WHAT IT DELIBERATELY DOES NOT REPORT
#   * Zero-reference definitions and fields — that is check-vacuity.sh's job; run
#     it first. This script starts at count 1.
#   * Leaf THEOREMS (referenced zero times) — a capstone consumed by nothing is the
#     normal, intended shape of a headline result (check-vacuity precedent), and
#     (C) additionally excludes anything pinned in Tests/AxiomAudit.lean, so a
#     headline cited once by a downstream module is not flagged either.
#   * Tests/AxiomAudit.lean as a consumer — an axiom pin mentions every headline,
#     so counting pins as references would blind (A) and (C). It is read ONLY to
#     harvest the pin registry.
#
# NOT COVERED — signals grep cannot extract reliably; needing Lean, not shipped weak
#   * Definitionally-equal DUPLICATE definitions (the paper found several). Needs
#     elaboration; out of scope here.
#   * `show ... from` / `rfl` used AGAINST a definition — not attributable to a
#     name by grep, so (B) undercounts reach-through sites. Stated, not faked.
#   * Statement-level mentions across arbitrarily re-formatted signatures: (B)/(C)
#     parse a declaration's signature as decl-line..`:=` capped at 40 lines. Odd
#     layouts escape; the counts are floors, not truths.
#   * Whether a STATEMENT says what its docstring claims — the paper's theorem-
#     statement category is human review; connectivity-manifest.md governs the
#     corpus's own claim discipline.
#   * File structure / namespace design — partially check-connectivity.sh's ground;
#     not duplicated here.
#
# Method notes: single awk pass over `git ls-files`; comments and docstrings are
# stripped before counting, so a prose mention is NOT a reference (stricter than
# check-vacuity, which needs only zero/nonzero). Token matching is exact-token;
# same-name declarations in different namespaces merge onto the first (stated
# imprecision). `delta` is counted at tactic position only (6 sites today; a looser
# prose-inclusive count reads ~11).
#
# Usage:  bash scripts/check-review-surface.sh           (awk only, no Lean build)
#         bash scripts/check-review-surface.sh --full    (uncapped lists)
#         bash scripts/check-review-surface.sh --strict  (exit 1 on A/B/C findings)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SRC="CsdLean4"
STRICT=0
FULL=0
for a in "$@"; do
  [ "$a" = "--strict" ] && STRICT=1
  [ "$a" = "--full" ]   && FULL=1
done

echo "check-review-surface: triaging the expert-review surface…"

FILES="$(git ls-files "$SRC/**/*.lean")"
[ -z "$FILES" ] && { echo "  FAIL  no source files found"; exit 1; }

OUT="${TMPDIR:-/tmp}/_review_surface.txt"

# One pass. AxiomAudit.lean contributes ONLY its pin registry; every other file
# contributes declarations, reference counts, reach-through sites, signature
# mentions, and per-file style metrics.
printf '%s\n' $FILES | xargs awk '
  function tokenize(s, tok,   t) { gsub(/[^A-Za-z0-9_'"'"']/," ",s); return split(s,tok," ") }

  FNR==1 { incomment=0; insig=0; prevthm=""; prevthmline=0 }

  { isaudit = (FILENAME ~ /Tests\/AxiomAudit\.lean$/) }

  # ---- pin registry (AxiomAudit only) ---------------------------------------
  isaudit && /#print axioms/ {
      nm=$0; sub(/^.*#print axioms[[:space:]]+/,"",nm); sub(/[^A-Za-z0-9_.'"'"'].*$/,"",nm)
      n=split(nm,seg,"."); if (n>0) pinned[seg[n]]=1
      next
  }
  isaudit { next }

  # ---- strip comments and docstrings BEFORE any counting --------------------
  {
      s=$0
      if (incomment) {
        if (match(s, /-\//)) { s=substr(s, RSTART+2); incomment=0 } else next
      }
      while (match(s, /\/-/)) {
        pre=substr(s,1,RSTART-1); rest=substr(s,RSTART+2)
        if (match(rest, /-\//)) { s=pre substr(rest, RSTART+2) }
        else { s=pre; incomment=1; break }
      }
      if (match(s, /--/)) s=substr(s,1,RSTART-1)
      if (s ~ /^[[:space:]]*$/) next
  }

  # ---- per-file line bookkeeping --------------------------------------------
  { fileline[FILENAME]=FNR }

  # ---- def / abbrev declarations --------------------------------------------
  s ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(public[[:space:]]+)?(protected[[:space:]]+)?(private[[:space:]]+)?(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+[A-Za-z_]/ {
      line=s
      sub(/^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(public[[:space:]]+)?(protected[[:space:]]+)?(private[[:space:]]+)?(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+/,"",line)
      name=line; sub(/[^A-Za-z0-9_'"'"'].*$/,"",name)
      if (name != "" && !(name in dkind)) { dkind[name]="def"; dloc[name]=FILENAME ":" FNR }
      # rest of the line legitimately references other names
      n=tokenize(s,tok); for(i=1;i<=n;i++) if (tok[i]!=name) ref[tok[i]]++
      insig=0
      if (prevthm!="" && FNR-prevthmline>=60) print "BLOCK|" FILENAME "|" prevthmline "|" prevthm "|" FNR-prevthmline
      prevthm=""; decl=1
  }

  # ---- theorem / lemma declarations -----------------------------------------
  !decl && s ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(public[[:space:]]+)?(protected[[:space:]]+)?(private[[:space:]]+)?(noncomputable[[:space:]]+)?(theorem|lemma)[[:space:]]+[A-Za-z_]/ {
      line=s
      sub(/^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(public[[:space:]]+)?(protected[[:space:]]+)?(private[[:space:]]+)?(noncomputable[[:space:]]+)?(theorem|lemma)[[:space:]]+/,"",line)
      name=line; sub(/[^A-Za-z0-9_'"'"'].*$/,"",name)
      if (name != "" && !(name in tkind)) { tkind[name]="thm"; tloc[name]=FILENAME ":" FNR }
      thms[FILENAME]++
      if (prevthm!="" && FNR-prevthmline>=60) print "BLOCK|" FILENAME "|" prevthmline "|" prevthm "|" FNR-prevthmline
      prevthm=name; prevthmline=FNR
      # signature starts here; the decl line itself may already close it
      cursig=name; insig=1; siglines=0
      delete seensig
      n=tokenize(s,tok)
      for(i=1;i<=n;i++) {
        if (tok[i]==name) continue
        ref[tok[i]]++
        if (!(tok[i] in seensig)) { seensig[tok[i]]=1; sigpair[tok[i] SUBSEP name]=1 }
      }
      if (s ~ /:=/) insig=0
      decl=1
  }

  # ---- signature continuation lines -----------------------------------------
  !decl && insig {
      siglines++
      n=tokenize(s,tok)
      for(i=1;i<=n;i++) {
        ref[tok[i]]++
        if (!(tok[i] in seensig)) { seensig[tok[i]]=1; sigpair[tok[i] SUBSEP cursig]=1 }
      }
      if (s ~ /:=/ || siglines>40) insig=0
      next
  }

  # ---- reach-through sites: unfold / delta / simp [..] ----------------------
  !decl {
      if (match(s, /(^|[^A-Za-z0-9_'"'"'])(unfold|delta)[[:space:]]/)) {
        t=substr(s, RSTART+RLENGTH)
        sub(/ at .*$/,"",t)
        n=tokenize(t,tok); for(i=1;i<=n;i++) thru[tok[i]]++
      }
      if (s ~ /simp/ && match(s, /\[[^]]*\]/)) {
        t=substr(s, RSTART+1, RLENGTH-2)
        n=tokenize(t,tok); for(i=1;i<=n;i++) simps[tok[i]]++
      }
  }

  # ---- generic reference counting + have census -----------------------------
  !decl {
      n=tokenize(s,tok)
      for(i=1;i<=n;i++) { ref[tok[i]]++; if (tok[i]=="have") haves[FILENAME]++ }
  }
  { decl=0 }

  END {
      for (nm in dkind) {
        api_sig=0; api_named=0
        for (t in tkind) {
          if (index(t, nm) > 0 && t != nm) api_named++
          if ((nm SUBSEP t) in sigpair) api_sig++
        }
        print "DEFROW|" dloc[nm] "|" nm "|" (nm in ref ? ref[nm] : 0) "|" \
              (nm in thru ? thru[nm] : 0) + (nm in simps ? simps[nm] : 0) "|" api_sig "|" api_named
      }
      for (nm in tkind)
        print "THMROW|" tloc[nm] "|" nm "|" (nm in ref ? ref[nm] : 0) "|" (nm in pinned ? 1 : 0)
      for (f in fileline)
        print "FILE|" f "|" (f in thms ? thms[f] : 0) "|" (f in haves ? haves[f] : 0) "|" fileline[f]
  }
' > "$OUT" 2>/dev/null

cap () {  # cap <n> — passthrough under --full, else head -n with a trailer
  if [ "$FULL" -eq 1 ]; then cat; else
    awk -v n="$1" 'NR<=n {print} END {if (NR>n) printf "        … and %d more (--full to list)\n", NR-n}'
  fi
}

# ---------- (A) thin definitions ---------------------------------------------
echo
n_thin="$(awk -F'|' '$1=="DEFROW" && $4>=1 && $4<=2' "$OUT" | wc -l)"
echo "  (A) thin definitions — referenced once or twice outside their declaration — $n_thin:"
echo "      (zero-reference is check-vacuity.sh territory and is not repeated here)"
awk -F'|' '$1=="DEFROW" && $4>=1 && $4<=2 {printf "        %-62s %-34s refs=%s\n",$2,$3,$4}' "$OUT" \
  | sort -t= -k2 -n | cap 30

# ---------- (B) definitions with no API --------------------------------------
echo
n_noapi="$(awk -F'|' '$1=="DEFROW" && $5>=1 && ($6+$7)==0' "$OUT" | wc -l)"
n_thru="$(awk -F'|' '$1=="DEFROW" && $5>=1' "$OUT" | wc -l)"
echo "  (B) reach-through vs lemma interface — $n_thru defs are reached through;"
echo "      $n_noapi of them have NO lemma interface at all. Ranked worst-first by"
echo "      through/(api+1):"
echo "      (reach-through = unfold/delta/simp-bracket sites; api = lemmas naming it"
echo "       or mentioning it in their statement; show-from/rfl sites are NOT counted"
echo "       — see header — so reach-through is a floor)"
awk -F'|' '$1=="DEFROW" && $5>=1 {printf "%06d|        %-62s %-34s through=%-3s api=%s\n", ($5*1000)/($6+$7+1), $2, $3, $5, $6+$7}' "$OUT" \
  | sort -t'|' -k1 -rn | cut -d'|' -f2- | cap 25

# ---------- (C) over-specialised statements ----------------------------------
echo
n_once="$(awk -F'|' '$1=="THMROW" && $4==1 && $5==0' "$OUT" | wc -l)"
echo "  (C) theorems/lemmas referenced exactly once, not AxiomAudit-pinned — $n_once:"
echo "      (leaf capstones — zero references — are the intended shape of a headline"
echo "       and are not reported; pinned names are declared headlines, excluded)"
awk -F'|' '$1=="THMROW" && $4==1 && $5==0 {printf "        %-62s %s\n",$2,$3}' "$OUT" \
  | sort | cap 40

# ---------- (D) proof-style outliers -----------------------------------------
echo
echo "  (D) proof-style outliers:"
awk -F'|' '$1=="FILE" {t+=$3; h+=$4} END {if (t>0) printf "      corpus: %d have across %d theorems/lemmas = %.2f have/theorem\n", h, t, h/t}' "$OUT"
echo "      top files by have density (≥5 theorems; walls of have live here):"
awk -F'|' '$1=="FILE" && $3>=5 {printf "        %-62s %4d have / %3d thm = %5.2f\n", $2, $4, $3, $4/$3}' "$OUT" \
  | sort -t= -k2 -rn | head -10
echo "      top files by absolute have count:"
awk -F'|' '$1=="FILE" {printf "        %-62s %4d have in %5d lines\n", $2, $4, $5}' "$OUT" \
  | sort -k2 -rn | head -5
echo "      longest proof blocks (decl → next decl, ≥60 lines; includes any trailing"
echo "      prose — a crude length proxy, see header):"
grep '^BLOCK|' "$OUT" | sort -t'|' -k5 -rn | head -10 \
  | awk -F'|' '{printf "        %-62s %-34s %s lines\n", $2 ":" $3, $4, $5}'

# ---------- (E) name shape ----------------------------------------------------
echo
echo "  (E) name-shape outliers (defs beyond mean+2σ of the corpus distribution):"
awk -F'|' '$1=="DEFROW" {n=$3; s=gsub(/_/,"",n)+1; print length($3) "|" s "|" $3 "|" $2}' "$OUT" > "${OUT}.names"
awk -F'|' '
  { sl+=$1; ss+=$2; sl2+=$1*$1; ss2+=$2*$2 }
  END {
    if (NR==0) exit
    ml=sl/NR; ms=ss/NR
    sdl=sqrt(sl2/NR-ml*ml); sds=sqrt(ss2/NR-ms*ms)
    printf "      corpus: %d defs, name length %.1f±%.1f chars, %.2f±%.2f segments —\n", NR, ml, sdl, ms, sds
    printf "      the def norm is single-segment camelCase, so an underscored DEF name\n"
    printf "      (theorem-style) is itself the off-norm signal here\n"
  }' "${OUT}.names"
awk -F'|' '
  { L[NR]=$1; S[NR]=$2; N[NR]=$3; LOC[NR]=$4
    sl+=$1; ss+=$2; sl2+=$1*$1; ss2+=$2*$2 }
  END {
    if (NR==0) exit
    ml=sl/NR; ms=ss/NR
    sdl=sqrt(sl2/NR-ml*ml); sds=sqrt(ss2/NR-ms*ms)
    for (i=1;i<=NR;i++)
      if (L[i]>ml+2*sdl || S[i]>ms+2*sds)
        printf "        %-62s %-44s len=%d seg=%d\n", LOC[i], N[i], L[i], S[i]
  }' "${OUT}.names" | sort -k1

# ---------- closing -----------------------------------------------------------
echo
total=$((n_thin + n_noapi + n_once))
echo "check-review-surface: $n_thin thin defs, $n_noapi no-API defs, $n_once single-use statements."
echo "  Every number above is a PROXY ranked for a human review pass, not a verdict:"
echo "  a thin def may be a deliberate seam, an unfolded def may be honest transparency,"
echo "  a single-use lemma may be exactly the right factoring. Each is a question:"
echo "  would this survive a library reviewer, and if not, which is wrong — the"
echo "  surface or the metric?"
[ "$STRICT" -eq 1 ] && [ "$total" -gt 0 ] && exit 1
exit 0
