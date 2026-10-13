# -*- coding: utf-8 -*-
"""Triage `check-glossary`'s staleness list: which entries can a reader's eye skip?

`check-glossary` flags an entry whose anchored module has a commit newer than the entry's
`reviewed:` date. That is the right question to *ask* and a blunt way to answer it: a corpus-wide
mechanical rename moves every module, so after one pin move the list is dominated by entries whose
prose cannot have gone stale, and a signal that cries wolf stops being read.

This script answers the sharper question. For each flagged entry it diffs the module from its state
at review time to `HEAD`, normalises away edits that **cannot** change what the entry says, and
reports whether anything is left:

* the Lean-core `if_*`/`dif_*` family renamed on 2026-07-21 (`if_pos` -> `ite_eq_left` and friends),
  each an exact substitution;
* `deprecated_module` import moves, `Mathlib.Data.*` -> `Mathlib.Basic.*`;
* whole import lines added or removed.

If the added and removed lines agree once those are undone, the module's content is the content the
entry was reviewed against and the entry is reported as `rename-only`. Everything else is reported
as `read` and needs a human.

**It does not bump any date, and it is not a licence to skip a read.** It partitions the list so a
reviewer spends their attention on the entries that moved. The author's rule stands: re-read, then
bump. What this removes is the pretence that a rename constitutes a move.

Run it through `scripts/glossary-staleness-triage.sh`.
"""
import io
import os
import re
import subprocess
import sys

try:
    import yaml
except ImportError:  # pragma: no cover - the wrapper installs it
    print('glossary-staleness-triage: PyYAML not available', file=sys.stderr)
    sys.exit(2)

ROOT = os.environ.get('CSD_ROOT', '.')
GLOSSARY = os.path.join(ROOT, 'docs', 'glossary.yaml')

# Lean core, deprecated 2026-07-21: each name is defined AS its replacement, same binders
CORE_RENAMES = {
    'if_pos': 'ite_eq_left', 'if_neg': 'ite_eq_right',
    'if_true': 'ite_true', 'if_false': 'ite_false',
    'dif_pos': 'dite_eq_left', 'dif_neg': 'dite_eq_right',
}
# `deprecated_module` shims: the old module imports exactly the new one
MODULE_MOVES = {
    'Mathlib.Data.Complex.Basic': 'Mathlib.Basic.Complex.Basic',
    'Mathlib.Data.Complex.BigOperators': 'Mathlib.Basic.Complex.BigOperators',
    'Mathlib.Data.ENNReal.Basic': 'Mathlib.Basic.ENNReal.Basic',
    'Mathlib.Data.Real.Basic': 'Mathlib.Basic.Real.Basic',
}
IMPORT_LINE = re.compile(r'^\s*(?:public |meta )*import \S+\s*$')


def _git(*args):
    return subprocess.run(['git'] + list(args), capture_output=True, text=True,
                          encoding='utf-8', errors='replace', cwd=ROOT, check=False).stdout


def normalise(text):
    """Undo the edits that cannot change what a glossary entry says."""
    for old, new in CORE_RENAMES.items():
        text = re.sub(r"(?<![A-Za-z0-9_'.])" + old + r"(?![A-Za-z0-9_'])", new, text)
    for old, new in MODULE_MOVES.items():
        text = text.replace(old, new)
    return text


def module_state_at(module, date):
    """The module's last commit on or before `date` — what the entry was reviewed against."""
    sha = _git('log', '-1', '--format=%H', '--before=' + str(date) + ' 23:59:59',
               '--', module).strip()
    return sha or None


def classify(module, reviewed):
    """`rename-only`, `read`, or a reason the question cannot be answered."""
    base = module_state_at(module, reviewed)
    if base is None:
        return 'read', 'no commit at or before the review date'
    diff = _git('diff', '-U0', base + '..HEAD', '--', module)
    adds, dels = [], []
    for line in diff.split('\n'):
        if line.startswith('+++') or line.startswith('---'):
            continue
        if line.startswith('+'):
            body = line[1:]
            if not IMPORT_LINE.match(body):
                adds.append(normalise(body))
        elif line.startswith('-'):
            body = line[1:]
            if not IMPORT_LINE.match(body):
                dels.append(normalise(body))
    if sorted(adds) == sorted(dels):
        return 'rename-only', 'content identical once the renames and imports are undone'
    return 'read', '%d line(s) changed beyond the renames' % abs(len(adds) - len(dels) or 1)


def main():
    entries = (yaml.safe_load(io.open(GLOSSARY, encoding='utf-8')) or {}).get('entries') or []
    stale = []
    for e in entries:
        module = (e.get('lean') or {}).get('module')
        reviewed = e.get('reviewed')
        if not module or not reviewed:
            continue
        last = _git('log', '-1', '--format=%cs', '--', module).strip()
        if last and str(reviewed) < last:
            stale.append((e.get('slug'), module, str(reviewed), last))

    print('glossary staleness triage: %d flagged entr%s'
          % (len(stale), 'y' if len(stale) == 1 else 'ies'))
    if not stale:
        print('  nothing flagged; the prose is level with every module it anchors to.')
        return 0

    skip, read = [], []
    for slug, module, reviewed, last in sorted(stale):
        verdict, why = classify(module, reviewed)
        (skip if verdict == 'rename-only' else read).append((slug, module, reviewed, last, why))

    print('\n  RENAME-ONLY (%d) — the module\'s content is what the entry was reviewed against:'
          % len(skip))
    for slug, module, reviewed, _last, _why in skip:
        print('    %-34s %s (reviewed %s)' % (slug, module.replace('CsdLean4/', ''), reviewed))
    print('\n  READ (%d) — something moved beyond a rename:' % len(read))
    for slug, module, reviewed, last, why in read:
        print('    %-34s %s changed %s, reviewed %s'
              % (slug, module.replace('CsdLean4/', ''), last, reviewed))
        print('      %s' % why)
    print('\n  This partitions the list. It does not bump a date and does not excuse a read:')
    print('  the author\'s rule is re-read, then bump.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
