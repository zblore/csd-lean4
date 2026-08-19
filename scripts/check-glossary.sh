#!/usr/bin/env bash
# check-glossary.sh
#
# Guards the ONE hand-written prose layer in this repo against the corpus it
# describes.
#
# Motivating case (2026-08-13): LF2's published Zenodo abstract said the Busch
# effect-Gleason theorem was "an imported" external input. It was proved on
# 2026-07-21 as `OperationalPackage.effect_gleason_representation`. The prose was
# still valid English and still wrong, on a record with a DOI, while three
# reviewers were being pointed at the file that contradicted it. No build failure
# can catch that, because prose does not compile.
#
# Every other guard in scripts/ protects the Lean tree from itself. This one
# protects the public from the Lean tree moving underneath the words.
#
# WHAT IT REPORTS
#   (A) schema        — missing required fields, unknown status values
#   (B) dead anchors  — a module path or theorem name in glossary.yaml that no
#                       longer exists in the tree, or a `sha` that is not a commit
#   (C) one-way links — a glossary entry whose Lean module does not link back, or a
#                       Lean header linking to a slug that is not in glossary.yaml.
#                       Both directions, because a dead link in the Lean source is
#                       worse than one on a website: the source is what reviewers read.
#   (D) dangling refs — `related:` slugs with no entry yet
#
# WHAT IT DELIBERATELY DOES NOT DO
#   It does not check whether the mathematics is RIGHT. It cannot. An AI-drafted
#   statement of Gleason's theorem can be fluent and false, and a wrong statement on
#   an indexed page under this domain is worse than no page. That is a human pass
#   over ~50 entries, once, and it is exactly the "expert review of definitions"
#   that Ilin & Nugent (arXiv 2606.13925) identify as the part agents cannot do.
#   Section (D) is a WARNING, not a failure: forward references to unwritten entries
#   are the normal shape of a glossary under construction.
#
# Usage:  bash scripts/check-glossary.sh            (report)
#         bash scripts/check-glossary.sh --strict   (exit 1 on any finding in A-C)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
STRICT=0
[ "${1:-}" = "--strict" ] && STRICT=1

[ -f docs/glossary.yaml ] || { echo "check-glossary: FAIL — docs/glossary.yaml not found"; exit 1; }

echo "check-glossary: verifying the prose layer against the corpus…"
echo

python - "$STRICT" <<'PY'
import re, subprocess, sys, os, yaml

STRICT = sys.argv[1] == "1"
STATUSES = {
    # Vocabulary follows AXIOMS.md §0 so the glossary cannot disagree with the ledger.
    "standard-mathematics",   # not CSD's claim; cite outward
    "proved-in-corpus",       # a theorem here, axiom-free
    "imported-result",        # AXIOMS.md §2 — currently empty, kept so it stays visible
    "physical-postulate",     # AXIOMS.md §3 — carried as hypothesis, not `axiom`
    "definition",             # a definition, no claim attached
    "open",                   # named, not settled
}
REQUIRED = ("slug", "term", "status", "hook", "layman", "in_csd", "mathematical")
# `lean` is required for every entry that makes a CSD claim, and optional for
# `standard-mathematics` — the vocabulary this corpus uses without doing anything
# particular to it. Those entries exist so a reader meeting the name has somewhere
# to land; they cite outward and anchor nothing, and demanding a theanchor for them
# would either block them or invite a decorative one, which is worse. Entries that
# DO carry `lean` are still checked for a live anchor and for link symmetry below.
# `standard-mathematics` — vocabulary the corpus uses without doing anything particular
# to it. `definition` — a term with no claim attached, which for the curated half means
# the positional and interpretive entries (Copenhagen, Many-Worlds, psi-epistemic): they
# state where this programme stands, and no theorem says that. Both cite outward and
# anchor nothing. Every OTHER status asserts something about the corpus and must name the
# constant that carries it.
LEAN_OPTIONAL_STATUSES = {"standard-mathematics", "definition"}
# How far the pinned sha may fall behind HEAD before it is worth saying so. Small
# enough to catch a pin left behind across a working session, large enough that a
# couple of unrelated commits do not nag.
STALE_LIMIT = 10

d = yaml.safe_load(open("docs/glossary.yaml", encoding="utf-8"))
entries = d.get("entries") or []
meta = d.get("meta") or {}
A, B, C, D = [], [], [], []

# --- (A) schema ------------------------------------------------------------
slugs = set()
for e in entries:
    s = e.get("slug", "<no slug>")
    for f in REQUIRED:
        if not e.get(f):
            A.append(f"{s}: missing required field `{f}`")
    st = e.get("status")
    if st and st not in STATUSES:
        A.append(f"{s}: status `{st}` not in the controlled vocabulary")
    if not e.get("lean") and st not in LEAN_OPTIONAL_STATUSES:
        A.append(f"{s}: missing required field `lean` (only `standard-mathematics` "
                 f"entries may omit it; this one is `{st}`)")
    slugs.add(s)

# --- (B) dead anchors ------------------------------------------------------
sha = meta.get("sha", "")
if sha:
    r = subprocess.run(["git", "cat-file", "-t", sha], capture_output=True, text=True)
    if r.stdout.strip() != "commit":
        B.append(f"meta.sha {sha[:12]} is not a commit in this repo")
    else:
        # Staleness. The pinned sha is deliberately not HEAD — permalinks must not
        # move — but it must still be an ANCESTOR of HEAD, or the site links into a
        # branch this one never took. And if it has fallen far behind, the source
        # links show a tree older than the prose describing it: on 2026-08-19 the pin
        # was four commits stale and pointed at a tree predating two theorems the
        # entry discussed. A warning, not a failure: a few commits of lag is normal
        # between a content change and the next glossary edit.
        anc = subprocess.run(["git", "merge-base", "--is-ancestor", sha, "HEAD"],
                             capture_output=True, text=True)
        if anc.returncode != 0:
            B.append(f"meta.sha {sha[:12]} is not an ancestor of HEAD — the site would "
                     f"link into a branch this one never took")
        else:
            cnt = subprocess.run(["git", "rev-list", "--count", f"{sha}..HEAD"],
                                 capture_output=True, text=True).stdout.strip()
            behind = int(cnt) if cnt.isdigit() else 0
            if behind > STALE_LIMIT:
                D.append(f"meta.sha {sha[:12]} is {behind} commits behind HEAD "
                         f"(limit {STALE_LIMIT}) — source permalinks may predate the "
                         f"prose; re-pin with `git rev-parse HEAD`")
for e in entries:
    s, ln = e.get("slug"), (e.get("lean") or {})
    mod, thm = ln.get("module"), ln.get("theorem")
    if mod and not os.path.isfile(mod):
        B.append(f"{s}: lean.module does not exist — {mod}")
    elif mod and thm:
        src = open(mod, encoding="utf-8", errors="replace").read()
        if not re.search(r"(^|\s)(theorem|lemma|def|abbrev)\s+" + re.escape(thm) + r"\b", src, re.M):
            B.append(f"{s}: lean.theorem `{thm}` not declared in {mod}")

# --- (C) link symmetry -----------------------------------------------------
SITE = (meta.get("site") or "").rstrip("/")
files = subprocess.run(["git", "ls-files", "CsdLean4/**/*.lean"],
                       capture_output=True, text=True).stdout.split()
linked_from_source = {}
if SITE:
    pat = re.compile(re.escape(SITE) + r"/([a-z0-9][a-z0-9-]*)/?")
    for f in files:
        for m in pat.finditer(open(f, encoding="utf-8", errors="replace").read()):
            linked_from_source.setdefault(m.group(1), set()).add(f)
    for slug, srcs in sorted(linked_from_source.items()):
        if slug not in slugs:
            C.append(f"Lean source links to `{slug}` which has no entry — {sorted(srcs)[0]}")
    for e in entries:
        s, mod = e.get("slug"), (e.get("lean") or {}).get("module")
        if mod and s not in linked_from_source:
            C.append(f"{s}: no Lean file links back to it (expected in {mod})")
        elif mod and mod not in linked_from_source.get(s, ()):
            C.append(f"{s}: linked from elsewhere but not from its own module {mod}")

# --- (D) dangling related -------------------------------------------------
for e in entries:
    for r_ in (e.get("related") or []):
        if r_ not in slugs:
            D.append(f"{e.get('slug')}: related `{r_}` has no entry yet")

def show(title, items):
    if not items:
        return
    print(f"  ({title}) — {len(items)}:")
    for i in items:
        print(f"        {i}")
    print()

show("A) schema", A)
show("B) dead anchors", B)
show("C) one-way links", C)
show("D) dangling related — WARNING only", D)

hard = len(A) + len(B) + len(C)
print(f"check-glossary: {len(entries)} entr{'y' if len(entries)==1 else 'ies'}, "
      f"{hard} hard finding{'' if hard==1 else 's'}, {len(D)} warning{'' if len(D)==1 else 's'}.")
if hard == 0:
    print("  PASS — every anchor resolves and every link is symmetric.")
    print("  NOTE: this says nothing about whether the mathematics is correct.")
else:
    print("  FAIL — a dead anchor or an asymmetric link. The site would ship a lie.")
print()
# Hard findings fail ALWAYS, not only under --strict. An earlier revision gated
# this on STRICT, so the guard reported "1 hard finding" and exited 0; CI wired to
# it would have gone green over a dead theorem anchor. --strict now escalates the
# (D) warnings instead, which is what an optional flag should be for.
sys.exit(1 if (hard or (STRICT and D)) else 0)
PY
