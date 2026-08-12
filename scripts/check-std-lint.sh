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
# ADVISORY, deliberately. Two reasons, recorded so the decision is visible:
#   (1) F3 (CONVENTIONS.md §9.2) settled naming/doc defects as rename-on-touch, never
#       swept; a blocking linter would force exactly the sweep that decision rejects.
#   (2) The corpus carries deliberate literature-notation exceptions (documented in
#       CONVENTIONS.md §9.2) that std rules cannot know about.
# It runs in CI's advisory step next to check-vacuity / check-review-surface. Promote a
# rule to blocking only via an explicit CONVENTIONS decision.
#
# Requires a built tree (`lake build`) — runLinter loads oleans.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

echo "check-std-lint: Batteries runLinter over the CsdLean4 root (advisory)…"
if lake exe runLinter CsdLean4; then
  echo "check-std-lint: OK"
else
  echo "check-std-lint: FINDINGS (advisory — see above; fix on touch per CONVENTIONS §9)"
  # Advisory: report, never block.
  exit 0
fi
