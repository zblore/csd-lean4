#!/usr/bin/env bash
# check-mathlib-absence.sh — the "wall has fallen" alarm.
#
# Motivating case (2026-09-01): a sweep of the gap register against the actual pin
# found FIVE rows asserting walls that no longer stood, all in the same direction.
# `CFC.concaveOn_log` (operator concavity of log) had been upstream since April and
# was missed by two successive probes, while the corpus quoted an upstream TODO
# verbatim as evidence of its absence. `Matrix.instCStarAlgebra` existed as a scoped
# instance while the plan recorded "Matrix n n C is NOT a CStarAlgebra" as a wall.
# `MonoidHom.measurePreserving` supplied exactly the Haar invariance the toral row
# called absent. The pattern: a claim about a dependency that moves weekly, written
# as prose, re-affirmed by triage without re-probing.
#
# THE MECHANIC. A claim that Mathlib lacks something names the token it asserts
# absent, in a machine-checkable tag:
#
#     Mathlib has no partial-trace construction. MATHLIB-ABSENT(Matrix.partialTrace)
#
# The guard then looks for each token IN THE PIN and **fails when it is found** —
# the alarm fires the week upstream lands it, instead of years later during an audit.
#
# TOKEN FORMS
#   Name.With.Dots  — searched as literal text anywhere in the pin's source. Use this
#                     whenever a namespace is available: it is the precise form, and
#                     it discriminates (`ContinuousAlternatingMap.domCoprod` absent
#                     vs `AlternatingMap.domCoprod` present).
#   bareName        — searched as a DECLARATION name (theorem/lemma/def/abbrev/
#                     instance/structure/class/opaque). Use when the namespace is
#                     unknown or the name is distinctive enough on its own.
#   file:Path/Pre   — fires when any file under that path prefix appears. The right
#                     form for an AREA absence (no manifold differential forms) where
#                     no single declaration name captures the gap.
#
# ⚠️ `@[to_additive]` twins are NOT in the source under their additive name. Tag the
# MULTIPLICATIVE source declaration (`MonoidHom.measurePreserving`, not
# `AddMonoidHom.measurePreserving`) or the check silently passes forever.
#
# WHAT IT CHECKS
#   A. Every MATHLIB-ABSENT token is genuinely absent from the pin. A found token
#      fails: the claim around it is now false and must be re-probed.
#   B. Every live row of MATHLIB-GAPS.md's "Genuine absences" table carries a tag.
#      Rows struck through (~~...~~) or marked CLOSED/DISSOLVED/NOT A GAP/WRONG are
#      exempt — they are history, not claims.
#   C. WARNING (non-fatal): untagged "Mathlib has no/lacks/does not provide" prose
#      elsewhere in the corpus, so the untagged surface stays visible without
#      blocking. Tag opportunistically when you touch a file.
#
# WHAT IT DELIBERATELY DOES NOT DO
#   - It does not judge whether a found token actually closes the gap. A sentinel is
#     a proxy: firing means "the world moved here, go look", not "the gap is closed".
#   - It does not check the corpus side (that a declaration this repo claims to have
#     exists) — check-doc-promises.sh and check-residues.sh already do.
#   - It does not parse Lean or elaborate anything. Text-level, same fidelity as the
#     other guards, and fast enough to run on every commit.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python - <<'PY'
import re, sys, pathlib

root = pathlib.Path('.')
pin = root / '.lake' / 'packages' / 'mathlib' / 'Mathlib'

def safe(s):
    """Strip non-ASCII: this guard's output must survive a cp1252 console."""
    return s.encode('ascii', 'replace').decode('ascii')

fails, warns, checked = [], [], []

if not pin.is_dir():
    print('check-mathlib-absence: SKIP (no Mathlib pin at .lake/packages/mathlib)')
    sys.exit(0)

# ---- load the pin's source once ----
pin_files = list(pin.rglob('*.lean'))
pin_text = []
for f in pin_files:
    try:
        pin_text.append(f.read_text(encoding='utf-8', errors='replace'))
    except OSError:
        pass
pin_blob = '\n'.join(pin_text)
pin_paths = {f.as_posix() for f in pin_files}

DECL = r'(?:theorem|lemma|def|abbrev|instance|structure|class|opaque|inductive)'

def token_found(tok):
    """Return a short reason string if the token IS present upstream, else None."""
    if tok.startswith('file:'):
        prefix = 'mathlib/' + tok[5:].lstrip('/')
        hits = [p for p in pin_paths if ('.lake/packages/' + prefix.lower()) in p.lower()
                or prefix.lower() in p.lower()]
        return f'{len(hits)} file(s) under {tok[5:]}' if hits else None
    if '.' in tok:
        n = pin_blob.count(tok)
        return f'{n} textual occurrence(s)' if n else None
    pat = re.compile(r'^[ ]*(?:@\[[^\]]*\][ ]*)?(?:private |protected |noncomputable |public |scoped )*'
                     + DECL + r'[ ]+' + re.escape(tok) + r"(?![\w'])", re.M)
    n = len(pat.findall(pin_blob))
    return f'{n} declaration site(s)' if n else None

# ---- A: scan every tag in the repo ----
tag_re = re.compile(r'MATHLIB-ABSENT\(([^)]*)\)')
sources = sorted(root.glob('CsdLean4/**/*.lean')) + sorted(root.glob('specs/**/*.md')) \
    + sorted(root.glob('*.md'))
for f in sources:
    rel = f.as_posix()
    try:
        text = f.read_text(encoding='utf-8', errors='replace')
    except OSError:
        continue
    for i, line in enumerate(text.splitlines()):
        for m in tag_re.finditer(line):
            toks = [t.strip() for t in m.group(1).split(',') if t.strip()]
            if not toks:
                fails.append(f'A: {rel}:{i+1}: empty MATHLIB-ABSENT() tag')
            for tok in toks:
                checked.append(tok)
                if tok.startswith('AddMonoidHom.') or tok.startswith('AddEquiv.') \
                        or tok.startswith('AddSubgroup.'):
                    warns.append(f'A: {rel}:{i+1}: `{tok}` looks like a @[to_additive] twin — '
                                 f'those are absent from source under the additive name; '
                                 f'tag the multiplicative declaration instead')
                why = token_found(tok)
                if why:
                    fails.append(f'A: {rel}:{i+1}: THE WALL HAS FALLEN — `{tok}` is now IN the pin '
                                 f'({why}). Re-probe and correct the claim on this line.')

# ---- B: MATHLIB-GAPS.md live rows must carry a tag ----
reg = root / 'MATHLIB-GAPS.md'
if reg.exists():
    lines = reg.read_text(encoding='utf-8', errors='replace').splitlines()
    in_table = False
    for i, line in enumerate(lines):
        if line.startswith('## '):
            in_table = 'Genuine absences' in line
            continue
        if not in_table or not line.startswith('|'):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if len(cells) < 2 or set(cells[0]) <= set('-: '):
            continue                      # separator row
        if cells[0].lower().startswith('gap'):
            continue                      # header row
        dead = ('~~' in cells[0]) or re.search(
            r'CLOSED|DISSOLVED|NOT A GAP|WAS FACTUALLY WRONG|ROW WAS', line)
        if dead:
            continue
        if 'MATHLIB-ABSENT(' not in line:
            name = safe(re.sub(r'[*`~]', '', cells[0]))[:52]
            fails.append(f'B: MATHLIB-GAPS.md:{i+1}: live absence row "{name}" carries no '
                         f'MATHLIB-ABSENT(...) tag — name a sentinel so the row is checkable')

# ---- C: untagged availability prose (warning only) ----
claim_re = re.compile(r'Mathlib (?:has no|has NO|lacks|does not have|does not provide)', re.I)
untagged = 0
for f in sorted(root.glob('CsdLean4/**/*.lean')):
    text = f.read_text(encoding='utf-8', errors='replace')
    flines = text.splitlines()
    for i, line in enumerate(flines):
        if claim_re.search(line):
            window = '\n'.join(flines[max(0, i - 2):i + 3])
            if 'MATHLIB-ABSENT(' not in window:
                untagged += 1

# ---- report ----
print(f'mathlib-absence: {len(checked)} sentinel(s) checked against the pin '
      f'({len(pin_files)} files); {untagged} untagged availability claim(s) in CsdLean4/')
for w in warns:
    print(f'WARN {safe(w)}')
if untagged:
    print(f'WARN C: {untagged} untagged "Mathlib has no/lacks ..." claim(s) remain in CsdLean4/ — '
          f'not checked by this guard; tag them opportunistically when you touch the file')
if fails:
    for f_ in fails:
        print(f'FAIL {safe(f_)}')
    print(f'check-mathlib-absence: {len(fails)} failure(s)')
    sys.exit(1)
print('check-mathlib-absence: OK')
PY
