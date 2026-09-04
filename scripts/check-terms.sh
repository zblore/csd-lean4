#!/usr/bin/env bash
# check-terms.sh
#
# CONVENTIONS.md §8.3a rules that a word carrying mathematical content must be honest about the
# object it names. `specs/TERMS.md` says what each such word MEANS in this corpus and what backs
# it. This guard enforces the part a machine can see: wherever a module uses the **restricted**
# sense of a term — the part TERMS.md records as NOT established — it must carry the marker
# `TERM-SCOPE(<Term>)`.
#
# WHY IT IS SHAPED THIS WAY. A first draft flagged every declaration whose NAME contains a
# content-carrying word. That was wrong twice over, and the wrongness is instructive:
#
#   * "Hamiltonian" has TWO senses here. The operator sense (a Hermitian `H` generating
#     `exp(-itH)`) is fully backed — `HasHamiltonianRealisation`, `schrodingerUnitary`, the
#     `_isHermitian` theorems. Only the vector-field sense `X_H = ω⁻¹dH` is restricted. Flagging
#     the name would have raised 37 declarations of which ~0 are defects.
#   * A companion scan for uniqueness claims without `∃!` returned 34 hits that were almost all
#     ordinary English ("the only nonalgebraic fact used below"). Not gated, deliberately.
#
#   * A first pattern for Kähler included `closed .{0,12}form`, which matched the ordinary English
#     "closed form" and raised 40 modules including `MeasurementAdder.lean`. Patterns here must be
#     phrases that CANNOT mean anything else.
#
# So this guard keys on the RESTRICTED VOCABULARY — the phrases that can only mean the unbacked
# sense — not on names. That keeps it precise, which is the difference between a guard and noise.
#
# RATCHET, not a sweep: unmarked uses are pinned in `docs/terms-baseline.txt` and may shrink,
# never grow. Same discipline as `check-std-lint.sh`.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline="docs/terms-baseline.txt"
[ -f "$baseline" ] || { echo "FAIL missing baseline $baseline"; exit 1; }

# "Term|restricted-vocabulary regex" — a phrase that can only mean the sense TERMS.md records as
# NOT established. Keep these narrow; a loose pattern here makes the guard useless.
TERMS='
Kahler|dω = 0|dω=0|top-power identity|top power identity|ω^{∧
Hamiltonian|X_H|ω⁻¹dH|Hamiltonian vector field|symplectic gradient|globally Hamiltonian
Liouville|top-power volume|ω^{∧n}/n!
'

fail=0
report=""
for term in Kahler Hamiltonian Liouville; do
  pat=$(printf '%s\n' "$TERMS" | grep "^${term}|" | cut -d'|' -f2- | tr '|' '\n' | paste -sd'|' -)
  [ -z "$pat" ] && continue
  # modules using the restricted vocabulary
  users=$(git ls-files 'CsdLean4/**/*.lean' | xargs grep -lE "$pat" 2>/dev/null || true)
  unmarked=""
  for f in $users; do
    grep -q "TERM-SCOPE($term)" "$f" || unmarked="$unmarked$f"$'\n'
  done
  n=$(printf '%s' "$unmarked" | grep -c . || true)
  pin=$(sed -nE "s/^${term}[[:space:]]+([0-9]+)$/\1/p" "$baseline")
  if [ -z "$pin" ]; then
    echo "FAIL $baseline has no pin for $term"; fail=1; continue
  fi
  if [ "$n" -gt "$pin" ]; then
    echo "FAIL $term: unmarked uses of the restricted sense grew $pin -> $n."
    echo "     Add \`TERM-SCOPE($term)\` to the module docstring, or use the backed sense."
    echo "     specs/TERMS.md says what each sense means."
    printf '%s' "$unmarked" | sed 's/^/       /'
    fail=1
  elif [ "$n" -lt "$pin" ]; then
    echo "  ratchet $term shrank: $pin -> $n — re-pin $baseline in this commit."
  else
    echo "  ok      $term $n unmarked (pinned)"
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "check-terms: FAIL (see specs/TERMS.md)"
  exit 1
fi
echo "check-terms: OK"
exit 0
