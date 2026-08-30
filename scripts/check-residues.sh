#!/usr/bin/env bash
# check-residues.sh — the residue registry guard.
#
# Motivating case (2026-08-30): eleven random-file correctness audits found ZERO
# mathematical errors and SIX files whose status-bearing prose had silently gone
# stale — headers still calling landed phases "later phases", discharged items
# "open upstream-prep work", proved dictionaries "undischarged pre-LF5". The
# common failure mode: a status claim written as free prose has no machine-readable
# identity, so nothing forces an update when the world changes. The fix is
# EXTRACTION, not annotation: each open residue gets an ID and a row in
# specs/residues.tsv (statement, carriers, dates, discharge conditions); the
# carrier file keeps ONE timeless line ending in `RESIDUE(R-###)`. History lives
# in git and the registry — never in accreting header parentheticals.
#
# WHAT IT CHECKS
#   A. Every RESIDUE(R-###) tag in CsdLean4/**.lean has a registry row.
#   B. Open/boundary rows: the set of files carrying the tag EQUALS the row's
#      declared carriers (both directions — a missing tag and an undeclared
#      carrier both fail). Carrier files must exist.
#   C. Closed rows: no file may still carry the tag, and the discharging
#      declaration must exist in the corpus as a real theorem/lemma/def.
#   D. Status-lexicon lint: the phrases "undischarged", "open work",
#      "later phase", "on next touch", "open upstream" are world-state claims
#      that go stale. A line using one must be governed by an identity system:
#      a RESIDUE tag within 2 lines, the LF4 realisability formula
#      ("load-bearing, externally supplied" — Framework.lean's mandated wording,
#      tracked by LF4-todo section numbers), a file-level LF4-todo reference
#      (for "undischarged" only — that system's vocabulary), or negation
#      ("no undischarged"). CsdLean4/Tests/ is exempt (pin comments are
#      historical narratives by design — but they must not use tag SYNTAX
#      for closed residues, which check C catches).
#   E. Triggers: a row with trigger consumer-count:NAME:N fails once NAME
#      occurs >= N times in the corpus — the rule-of-two alarm for staged
#      duplicates that must be folded when consumers appear.
#   F. Staleness (WARNING, non-fatal): an open row whose last_review is more
#      than 120 days old. Boundary rows are permanent and exempt.
#
# WHAT IT DELIBERATELY DOES NOT DO
#   - It does not police timeless file-scope phrasing ("not attempted",
#     "not formalised", "NOT built here"): a statement about what THIS FILE
#     contains cannot go stale and needs no tag. Only world-state phrasing
#     (what the REPO/world still lacks) needs an identity.
#   - It does not require closed rows to be deleted: they are the record that
#     the residue was once real and how it died.
#   - It does not parse Lean. Declaration existence is a text-level check,
#     same fidelity as check-doc-promises.sh.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python - <<'PY'
import re, sys, datetime, pathlib

root = pathlib.Path('.')
reg_path = root / 'specs' / 'residues.tsv'
fails, warns = [], []

# ---- parse registry ----
rows = {}
lines = reg_path.read_text(encoding='utf-8').splitlines()
header = lines[0].split('\t')
expected = ['id','status','statement','carriers','discharged_by','trigger',
            'opened','closed','last_review','notes']
if header != expected:
    fails.append(f'registry header mismatch: {header}')
for ln in lines[1:]:
    if not ln.strip():
        continue
    parts = ln.split('\t')
    if len(parts) != len(expected):
        fails.append(f'registry row has {len(parts)} columns (want {len(expected)}): {ln[:60]}')
        continue
    row = dict(zip(expected, parts))
    rid = row['id']
    if not re.fullmatch(r'R-\d{3}', rid):
        fails.append(f'bad residue id: {rid}')
    if rid in rows:
        fails.append(f'duplicate residue id: {rid}')
    if row['status'] not in ('open', 'closed', 'boundary'):
        fails.append(f'{rid}: bad status {row["status"]!r}')
    rows[rid] = row

# ---- scan corpus for tags ----
lean_files = sorted(root.glob('CsdLean4/**/*.lean'))
tag_re = re.compile(r'RESIDUE\((R-\d{3})\)')
tags = {}          # id -> set of repo-relative posix paths
file_text = {}     # path -> text (cache for later checks)
for f in lean_files:
    t = f.read_text(encoding='utf-8', errors='replace')
    rel = f.as_posix()
    file_text[rel] = t
    for m in tag_re.finditer(t):
        tags.setdefault(m.group(1), set()).add(rel)

# ---- A: every tag has a row ----
for rid, where in sorted(tags.items()):
    if rid not in rows:
        for w in sorted(where):
            fails.append(f'A: tag RESIDUE({rid}) in {w} has no registry row')

# ---- B / C per row ----
corpus_all = '\n'.join(file_text.values())
def decl_exists(name):
    pat = re.compile(
        r'\b(?:theorem|lemma|def|abbrev|instance|structure)\s+' +
        re.escape(name) + r"(?![\w'])")
    return bool(pat.search(corpus_all))

for rid, row in sorted(rows.items()):
    status = row['status']
    carriers = set() if row['carriers'] in ('-', '') else set(row['carriers'].split(';'))
    found = tags.get(rid, set())
    if status in ('open', 'boundary'):
        for c in sorted(carriers):
            if not (root / c).exists():
                fails.append(f'B: {rid} carrier does not exist: {c}')
        for c in sorted(carriers - found):
            fails.append(f'B: {rid} ({status}) declared carrier {c} does not carry the tag')
        for c in sorted(found - carriers):
            fails.append(f'B: {rid} tag found in undeclared file {c} — add it to carriers or remove the tag')
    else:  # closed
        for c in sorted(found):
            fails.append(f'C: {rid} is CLOSED but {c} still carries the tag — update the header')
        d = row['discharged_by']
        if d in ('-', ''):
            fails.append(f'C: {rid} is closed with no discharging declaration')
        elif not decl_exists(d):
            fails.append(f'C: {rid} discharging declaration `{d}` not found in corpus')

# ---- D: status-lexicon lint ----
terms = ['undischarged', 'open work', 'later phase', 'on next touch', 'open upstream']
term_re = re.compile('|'.join(re.escape(t) for t in terms), re.IGNORECASE)
for rel, t in sorted(file_text.items()):
    if rel.startswith('CsdLean4/Tests/'):
        continue
    flines = t.splitlines()
    has_lf4todo = 'LF4-todo' in t
    for i, ln in enumerate(flines):
        m = term_re.search(ln)
        if not m:
            continue
        term = m.group(0).lower()
        window = '\n'.join(flines[max(0, i - 2):i + 3])
        if 'RESIDUE(' in window:
            continue
        if 'load-bearing, externally supplied' in window:
            continue
        if re.search(r'no undischarged', ln, re.IGNORECASE):
            continue
        if term == 'undischarged' and has_lf4todo:
            continue
        fails.append(f'D: {rel}:{i+1}: status phrase "{term}" with no governing identity '
                     f'(RESIDUE tag / LF4 formula) — register it or rephrase timelessly')

# ---- E: triggers ----
for rid, row in sorted(rows.items()):
    trig = row['trigger']
    if trig in ('-', ''):
        continue
    m = re.fullmatch(r'consumer-count:([^:]+):(\d+)', trig)
    if not m:
        fails.append(f'E: {rid} unparseable trigger {trig!r}')
        continue
    name, thresh = m.group(1), int(m.group(2))
    pat = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
    n = len(pat.findall(corpus_all))
    if row['status'] == 'open' and n >= thresh:
        fails.append(f'E: {rid} trigger fired — `{name}` has {n} occurrences (threshold {thresh}); '
                     f'fold/promote per the rule of two, then close or re-baseline the row')

# ---- F: staleness (non-fatal) ----
today = datetime.date.today()
for rid, row in sorted(rows.items()):
    if row['status'] != 'open':
        continue
    try:
        lr = datetime.date.fromisoformat(row['last_review'])
    except ValueError:
        fails.append(f'F: {rid} bad last_review date {row["last_review"]!r}')
        continue
    age = (today - lr).days
    if age > 120:
        warns.append(f'F: {rid} last reviewed {age} days ago ({row["last_review"]}) — re-verify the row still holds')

# ---- report ----
n_open = sum(1 for r in rows.values() if r['status'] == 'open')
n_closed = sum(1 for r in rows.values() if r['status'] == 'closed')
n_bound = sum(1 for r in rows.values() if r['status'] == 'boundary')
print(f'residue registry: {len(rows)} rows ({n_open} open, {n_bound} boundary, {n_closed} closed); '
      f'{sum(len(v) for v in tags.values())} tags in {len(lean_files)} files')
for w in warns:
    print(f'WARN {w}')
if fails:
    for f_ in fails:
        print(f'FAIL {f_}')
    print(f'check-residues: {len(fails)} failure(s)')
    sys.exit(1)
print('check-residues: OK')
PY
