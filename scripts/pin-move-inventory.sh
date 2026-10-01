#!/usr/bin/env bash
# pin-move-inventory.sh — the live inventory for the Mathlib pin-move sweep (BACKLOG HY-6, row 27).
#
# WHY THIS EXISTS. HY-6 lists what the next Mathlib pin move owes: Lean-core lemma renames,
# import moves, a handful of one-line renames, and one real rework. Those lists were measured
# once by hand from a Compat-canary run (2026-09-14), and the corpus has grown since. Measured
# again on 2026-10-01, five of the rows had drifted:
#
#   * the Lean-core count, ~1,300 -> 1,564 sites;
#   * `stdSimplex`, one file -> three, and four of the new sites are AXIOM PINS, whose names
#     change with the declaration;
#   * `Data.Complex.BigOperators`, one importer -> two;
#   * `Data.Complex.Basic`, six importers -> seven;
#   * `.lipschitz`, never spelled the way the table said: the qualified name
#     `ContinuousLinearMap.lipschitz` appears NOWHERE, so a sed on it would have matched nothing
#     and reported success.
#
# A hand-maintained inventory of a moving corpus is wrong by construction, so this script
# measures it instead, and HY-6 points here for the numbers.
#
# ZERO IS LOUD. Every row prints its count, and a row that finds nothing is flagged, because on
# this corpus a zero means a wrong pattern far more often than a clean sweep — that is exactly how
# the `.lipschitz` row went stale unnoticed, and how the first draft of this script reported three
# silent zeros of its own (`$` without re.M; `\b` after a name ending in an apostrophe).
#
# This is an INVENTORY, not a guard: it always exits 0 and gates nothing. Run it when the pin
# moves and read it against HY-6 for what to do with each row.
#
# Sweep discipline (validation-hardening-plan.md row M, learned the hard way): fix by
# corpus-wide word-boundary regex sweep, never by a reported-site list; verify with an
# untruncated grep that returns empty.
set -uo pipefail
cd "$(dirname "$0")/.."

python -X utf8 - <<'PY'
import re, subprocess

files = subprocess.run(['git', 'ls-files', 'CsdLean4/**/*.lean', 'CsdLean4/Basic.lean'],
                       capture_output=True, text=True).stdout.split()
src = {}
for f in sorted(set(files)):
    try:
        src[f] = open(f, encoding='utf-8', errors='replace').read()
    except OSError:
        pass

empty_rows = []


def tally(pattern, label, note='', flags=0):
    rx = re.compile(pattern, flags)
    hits = {f: len(rx.findall(t)) for f, t in src.items()}
    hits = {f: n for f, n in hits.items() if n}
    total = sum(hits.values())
    mark = '  <-- ZERO: check the pattern' if total == 0 else ''
    if total == 0:
        empty_rows.append(label)
    print(f'  {label:<44} {total:>5} site(s) in {len(hits):>3} file(s)'
          + (f'  — {note}' if note else '') + mark)
    return hits, total


def listing(hits, limit=12):
    for f, n in sorted(hits.items(), key=lambda kv: (-kv[1], kv[0]))[:limit]:
        print(f'        {n:>4}  {f}')
    if len(hits) > limit:
        print(f'        ...   and {len(hits) - limit} more file(s)')


print('pin-move inventory (BACKLOG HY-6) — measured now, not remembered\n')

print('(1) Lean-core renames — same signatures, so a word-boundary sed suffices:')
grand = 0
for old, new in [('if_pos', 'ite_eq_left'), ('if_neg', 'ite_eq_right'),
                 ('dif_pos', 'dite_eq_left'), ('dif_neg', 'dite_eq_right'),
                 ('if_true', 'ite_true'), ('if_false', 'ite_false')]:
    _, n = tally(rf'\b{old}\b', f'{old} -> {new}')
    grand += n
print(f'  {"TOTAL":<44} {grand:>5} site(s)\n')

print('(2) Import moves — Mathlib.Data.* became Mathlib.Basic.*:')
for old in ['Mathlib.Data.Complex.Basic', 'Mathlib.Data.Complex.BigOperators',
            'Mathlib.Data.Real.Basic', 'Mathlib.Data.ENNReal.Basic']:
    hits, _ = tally(rf'import {re.escape(old)}\s*$', old, 'line-anchored', re.M)
    listing(hits)
print()

print('(3) One-line renames:')
hits, _ = tally(r'\.lipschitz\b', '.lipschitz -> .lipschitzWith',
                'DOT NOTATION: the qualified name never appears')
listing(hits)
hits, _ = tally(r'\bFilter\.eventuallyEq_set\b', 'Filter.eventuallyEq_set -> eventuallyEqSet_iff')
listing(hits)
hits, _ = tally(r"isQuotientMap_mk'\.secondCountableTopology",
                "isQuotientMap_mk'.secondCountableTopology")
listing(hits)
print()

print('(4) The real rework — stdSimplex (a Set) became the structure StdSimplex:')
hits, _ = tally(r'stdSimplex', 'stdSimplex -> StdSimplex (substring)',
                'NOT word-boundary: it occurs inside longer identifiers too')
listing(hits)
idents = sorted({m for t in src.values()
                 for m in re.findall(r'[A-Za-z0-9_.\']*stdSimplex[A-Za-z0-9_\']*', t)})
print('        identifiers containing it (each needs its own decision):')
for i in idents:
    print(f'          {i}')
print()

print('(5) The MapProbability shim — delete it and collapse the call sites:')
hits, _ = tally(r"isProbabilityMeasure_map'", "isProbabilityMeasure_map'",
                "name ends in an apostrophe: no trailing \\b")
listing(hits, limit=25)
hits, _ = tally(r"Measure\.map_smul'", "Measure.map_smul' (the other shim)")
listing(hits, limit=25)
print()

print('(6) Pin-only tactic steps to re-check after the move:')
found = False
for f, t in src.items():
    for i, line in enumerate(t.splitlines(), start=1):
        if 'all_goals try rfl' in line:
            print(f'        {f}:{i}  all_goals try rfl')
            found = True
if not found:
    print('        none found  <-- ZERO: check the pattern')
print()

if empty_rows:
    print('ROWS THAT FOUND NOTHING — on this corpus that usually means a wrong pattern,')
    print('not a clean sweep. Confirm each by hand before trusting it:')
    for r in empty_rows:
        print(f'  * {r}')
    print()

print('None of this is executable on the pin: the replacement names do not exist here.')
print('HY-6 in specs/BACKLOG.md section D carries what to do with each row.')
PY
