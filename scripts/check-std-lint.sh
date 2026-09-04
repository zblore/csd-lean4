#!/usr/bin/env bash
# check-std-lint.sh
#
# Standard Lean environment linters (Batteries `runLinter`) over the corpus root
# (validation-hardening WS-K, specs/validation-hardening-plan.md, 2026-08-12).
#
# WHAT THIS ADDS over the bespoke guards: the std env linters catch library-engineering
# defect classes none of the CSD-specific scripts look for — `simpNF` (simp lemmas whose
# LHS is not in normal form), `unusedArguments`, `docBlame`-class problems, dup
# namespaces, etc. This complements check-review-surface.sh (proxy metrics) with the
# ecosystem's own declaration-level rules.
#
# RATCHET, not a sweep (adopted 2026-09-04, the hardening session; supersedes the
# pure-advisory mode of 2026-08-12). Per-class counts are pinned in
# `docs/std-lint-baseline.txt` and this script FAILS when a class GROWS. It never
# fails on the existing findings, so the two reasons the original decision gave for
# staying advisory still hold:
#   (1) F3 (CONVENTIONS.md §9.2) settled naming/doc defects are rename-on-touch, never
#       swept; a blocking linter on the existing list would force exactly that sweep.
#   (2) The corpus carries deliberate literature-notation exceptions (documented in
#       CONVENTIONS.md §9.2) that std rules cannot know about.
# What the ratchet adds is regression cover: `simpNF` and `docBlame` are at ZERO as of
# 2026-09-04, so a newly dead simp lemma (one whose LHS is not in normal form, which
# silently never fires) or a new undocumented definition fails CI on the commit that
# introduces it, instead of joining a list nobody reads. The two open classes shrink
# on touch and can never grow.
#
# WHEN A COUNT DROPS: re-pin the baseline in the same commit (the script tells you).
# WHEN A COUNT MUST GROW: it must not — fix the finding, or, if the finding is a
# deliberate exception, record it as such at the declaration (a docstring sentence
# saying why, as `shor_phase_estimation_lower_bound` and `cfullAdder_correct_general`
# do for their uniform hypothesis bundles) and re-pin with the reason in the commit.
#
# Requires a built tree (`lake build`) — runLinter loads oleans.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline="docs/std-lint-baseline.txt"
out="${TMPDIR:-/tmp}/csd-std-lint.$$"
trap 'rm -f "$out"' EXIT

echo "check-std-lint: Batteries runLinter over the CsdLean4 root (ratchet)…"
lake exe runLinter CsdLean4 > "$out" 2>&1
lint_rc=$?

if [ ! -s "$out" ] && [ $lint_rc -ne 0 ]; then
  echo "FAIL runLinter produced no output (exit $lint_rc). Is the tree built (\`lake build\`)?"
  exit 1
fi

# Per-class counts, one per flagged DECLARATION (the `error:` lines; the indented
# `argument N: …` detail lines are not counted).
count_class() {
  grep -c -E "error: .*$1" "$out"
}
simpnf=$(( $(count_class "Left-hand side simplifies") + $(count_class "simp can prove this") ))
unused=$(count_class "unused argument")
docblame=$(count_class "missing documentation string")
underscore=$(count_class "contains an underscore")
total=$(grep -c "error: " "$out")
known=$(( simpnf + unused + docblame + underscore ))

if [ ! -f "$baseline" ]; then
  echo "FAIL missing baseline $baseline"
  exit 1
fi

get_pin() { sed -nE "s/^$1[[:space:]]+([0-9]+)$/\\1/p" "$baseline"; }
fail=0
warn=0

for cls in simpNF unusedArguments docBlame defsWithUnderscore; do
  case "$cls" in
    simpNF)             now=$simpnf ;;
    unusedArguments)    now=$unused ;;
    docBlame)           now=$docblame ;;
    defsWithUnderscore) now=$underscore ;;
  esac
  pin=$(get_pin "$cls")
  if [ -z "$pin" ]; then
    echo "FAIL $baseline has no pin for $cls"
    fail=1
    continue
  fi
  if [ "$now" -gt "$pin" ]; then
    echo "FAIL $cls grew: $pin -> $now. Fix the new finding(s) below, or record the"
    echo "     deliberate exception at the declaration and re-pin $baseline in this commit."
    fail=1
  elif [ "$now" -lt "$pin" ]; then
    echo "  ratchet $cls shrank: $pin -> $now — re-pin $baseline in this commit."
    warn=1
  else
    echo "  ok      $cls $now (pinned)"
  fi
done

# A class this script does not know about (a linter newly enabled upstream) must not
# slip through the arithmetic.
if [ "$total" -gt "$known" ]; then
  echo "FAIL $(( total - known )) finding(s) outside the four pinned classes — a linter this"
  echo "     script does not classify is reporting. Read the output and extend the ratchet."
  fail=1
fi

if [ $fail -ne 0 ]; then
  echo
  sed -n '1,400p' "$out"
  echo
  echo "check-std-lint: FAIL (ratchet; see docs/std-lint-baseline.txt)"
  exit 1
fi

if [ $warn -ne 0 ]; then
  echo "check-std-lint: OK, baseline is loose (re-pin it)"
  exit 0
fi

echo "check-std-lint: OK ($total finding(s), all pinned; simpNF and docBlame at zero)"
exit 0
