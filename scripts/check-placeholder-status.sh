#!/usr/bin/env bash
# check-placeholder-status.sh
#
# `PLACEHOLDERS.md` §1 is the ledger of claim-shaped `Prop` definitions: declarations a
# reader could mistake for proved content. Each one carries a banner in its own docstring
# (`**PLACEHOLDER (Prop definition, not proved).**`) plus a `TODO(...)` line. The ledger and
# the banners are two records of one fact, kept in different files, by hand.
#
# MOTIVATING DEFECT (2026-09-07). The nine gate realisability Props were DISCHARGED
# 2026-07-19 (`Gates/{SingleQubit,TwoQubit,MultiQubit,BellPrep}Discharge.lean`) and the §1
# TABLE was updated the same day. Nothing else was. Seven weeks later:
#
#   * all nine defining docstrings still opened with "PLACEHOLDER (Prop definition, not
#     proved)" and still carried "TODO(LF4 §13.2): construct a witness bundle";
#   * `Gates/BellPrep.lean` contradicted itself INSIDE ONE DOCSTRING — banner "not proved",
#     body "**Status: DISCHARGED 2026-07-19**";
#   * the §1 header paragraph still said "partially discharged … the remaining five … are
#     the mechanical continuation", directly above the table saying all nine were done;
#   * `BRIDGE-OBLIGATIONS.md` §2.6 still said "pre-LF4, no concrete `D` exists for which any
#     of them is shown to hold".
#
# That is the rare ledger error that is dishonest in the *understating* direction, in the
# files whose entire job is to say what is not proved. `check-contradictions.sh` cannot see
# it: it keys on backticked identifiers sharing a line with a status token, and these
# banners name no identifier. So this guard keys on the ledger row instead.
#
# WHAT IT CHECKS, both ways:
#   (1) every §1 row's file is tracked and declares the Prop it names;
#   (2) a row marked DISCHARGED must name at least one witness declaration, each of which
#       must exist — a rename away from the discharge is the same defect in reverse;
#   (3) a DISCHARGED row's Prop must NOT still wear a placeholder banner or a TODO line;
#   (4) a row NOT marked DISCHARGED must STILL wear the banner — so a warning cannot be
#       quietly dropped from an unproved Prop;
#   (5) no orphan banners: a placeholder banner anywhere in the corpus must belong to a
#       Prop that has a §1 row.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

python - <<'PY'
import io, re, subprocess, sys

BANNER = "PLACEHOLDER (Prop definition, not proved)"
STALE = [BANNER, "TODO(LF4", "claim-shaped, undischarged"]

tracked = set(subprocess.check_output(
    ["git", "ls-files"], text=True).splitlines())
lean = [f for f in tracked if f.startswith("CsdLean4/") and f.endswith(".lean")]

def read(path):
    return io.open(path, encoding="utf-8").read()

sources = {f: read(f) for f in lean}
findings = []

# ---- the §1 rows -----------------------------------------------------------
ledger = read("PLACEHOLDERS.md")
sec = ledger.split("## 1.")[1].split("## 2.")[0]
tick = re.compile("`([^`]+)`")
rows = []
for line in sec.splitlines():
    if not line.startswith("|"):
        continue
    cells = [c.strip() for c in line.split("|")[1:-1]]
    if len(cells) != 4 or cells[0].startswith("---") or cells[0] == "File":
        continue
    fm, pm = tick.search(cells[0]), tick.search(cells[1])
    if not fm or not pm or not fm.group(1).endswith(".lean"):
        continue
    rows.append(("CsdLean4/" + fm.group(1), pm.group(1), cells[3]))

if not rows:
    findings.append("PLACEHOLDERS.md §1: no table rows parsed — the ledger's shape changed "
                    "and this guard is now checking nothing")

def block_of(text, prop):
    """The docstring + comment lines immediately above `def <prop>`."""
    lines = text.splitlines()
    for i, ln in enumerate(lines):
        if re.match("^(noncomputable )?def " + re.escape(prop) + "([ (:]|$)", ln):
            j = i
            while j > 0 and "/--" not in lines[j]:
                j -= 1
            return "\n".join(lines[j:i + 1])
    return None

declared = {}
for path, prop, status in rows:
    if path not in tracked:
        findings.append("%s: §1 row names an untracked file" % path)
        continue
    blk = block_of(sources[path], prop)
    if blk is None:
        findings.append("%s: §1 row names `%s`, which is not declared there" % (path, prop))
        continue
    declared[prop] = "DISCHARGED" in status
    if "DISCHARGED" in status:
        witnesses = [w for w in tick.findall(status) if w.endswith("_cpSector")]
        if not witnesses:
            findings.append("%s `%s`: row says DISCHARGED but names no `*_cpSector` witness"
                            % (path, prop))
        for w in witnesses:
            pat = re.compile("^(theorem|lemma|def|noncomputable def) " + re.escape(w) + "([ (:]|$)",
                             re.M)
            if not any(pat.search(s) for s in sources.values()):
                findings.append("%s `%s`: witness `%s` is not declared anywhere "
                                "(renamed away? the row is now unchecked)" % (path, prop, w))
        for tok in STALE:
            if tok in blk:
                findings.append("%s `%s`: DISCHARGED in PLACEHOLDERS.md §1, but its docstring "
                                "still says \"%s\"" % (path, prop, tok))
    else:
        if BANNER not in blk:
            findings.append("%s `%s`: §1 row is NOT discharged, but the docstring has lost its "
                            "placeholder banner" % (path, prop))

# ---- (5) orphan banners ----------------------------------------------------
for path, text in sources.items():
    lines = text.splitlines()
    for i, ln in enumerate(lines):
        if BANNER not in ln:
            continue
        name = None
        for ahead in lines[i:i + 25]:
            m = re.match("^(?:noncomputable )?def ([A-Za-z_][A-Za-z0-9_']*)", ahead)
            if m:
                name = m.group(1)
                break
        if name is None:
            findings.append("%s:%d: placeholder banner over no `def`" % (path, i + 1))
        elif name not in declared:
            findings.append("%s:%d: `%s` wears a placeholder banner with no PLACEHOLDERS.md "
                            "§1 row" % (path, i + 1, name))

if findings:
    print("check-placeholder-status: FAILED")
    for f in findings:
        print("    " + f)
    sys.exit(1)

n = len(rows)
d = sum(1 for v in declared.values() if v)
print("check-placeholder-status: OK (%d §1 rows: %d discharged with live witnesses, "
      "%d still bannered)" % (n, d, n - d))
PY
