#!/usr/bin/env bash
# check-category-tags.sh
#
# CONVENTIONS.md §2: every module declares `**Category:** <Tag> (<rationale>)` in its module
# docstring, and §4 fixes the tag BY LOCATION — a module is tagged for where it lives, not for
# what it might become. The allowed tags are `1-Mathlib`, `2-Framework`, `3-Local`, `7-SigmaLayer`
# and `Special`, and the directory decides which one:
#
#   CsdLean4/Mathlib/**                        1-Mathlib
#   CsdLean4/Framework/**                      2-Framework
#   CsdLean4/SigmaLayer/**, CsdLean4/RecordLayer/**   7-SigmaLayer  (one stratum, two namespaces
#                                                      since the 2026-08-13 Q15 split)
#   CsdLean4/Tests/**, CsdLean4/Incubator/**, CsdLean4/Interop/** (2026-09-16, the Physlib
#   export root), CsdLean4.lean, CsdLean4/Basic.lean,
#   CsdLean4/Headlines.lean                    Special
#   everything else (LF*/, Empirical/, CV/, Thermo/, LF6/, …)   3-Local
#
# WHY. Before 2026-09-12 the corpus carried 28 different spellings in this slot (`6-Local`,
# `CV`, `dynamical measurement`, `conceptually 1-Mathlib`, `2-LF4`, …) and six modules had no
# tag at all; the line had become free prose. The 2026-09-12 sweep folded every informative
# phrase into the rationale parenthetical and put the canonical tag in front. This guard keeps
# it that way. It checks the TAG only; the rationale text stays review-enforced.
#
# Exactly one `**Category:**` line per module; a module docstring with none fails.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# One awk pass over every module (650 files; a per-file shell loop with grep/sed/awk spawns
# take minutes on Windows, this takes seconds). The tag is the first whitespace-delimited token
# after `**Category:**`, with trailing `.`, `,`, `;`, `(` stripped — byte-safe, so 4-byte glyphs
# elsewhere on the line cannot derail it.
git ls-files 'CsdLean4/**/*.lean' 'CsdLean4.lean' | awk '
function expected(f) {
  if (f == "CsdLean4.lean" || f == "CsdLean4/Basic.lean" || f == "CsdLean4/Headlines.lean") return "Special"
  if (f ~ /^CsdLean4\/(Tests|Incubator|Interop)\//) return "Special"
  if (f ~ /^CsdLean4\/Mathlib\//) return "1-Mathlib"
  if (f ~ /^CsdLean4\/Framework\//) return "2-Framework"
  if (f ~ /^CsdLean4\/(SigmaLayer|RecordLayer)\//) return "7-SigmaLayer"
  return "3-Local"
}
{
  file = $0; cnt = 0; tag = ""
  while ((getline line < file) > 0) {
    if (line ~ /^\*\*Category:\*\*/) {
      cnt++
      if (cnt == 1) {
        sub(/^\*\*Category:\*\*[ \t]*/, "", line)
        split(line, a, /[ \t]/); tag = a[1]
        sub(/[.,;(].*$/, "", tag)
      }
    }
  }
  close(file)
  n++
  if (cnt != 1) {
    print "FAIL " file ": " cnt " \047**Category:**\047 line(s), expected exactly 1 (CONVENTIONS.md §2)"; fail = 1
  } else if (tag != expected(file)) {
    print "FAIL " file ": tag \047" tag "\047, expected \047" expected(file) "\047 by location (CONVENTIONS.md §2, §4)"; fail = 1
  }
}
END {
  if (!fail) print "  ok      check-category-tags: " n " module(s), every tag canonical and by location"
  exit fail
}'
