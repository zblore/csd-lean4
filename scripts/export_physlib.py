#!/usr/bin/env python3
"""export_physlib.py — the Physlib export of the Fubini–Study geometry (logic).

Driven by scripts/export-physlib.sh; see that file for the contract. This module:

  1. reads the root CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean and computes its
     transitive import closure within CsdLean4/Mathlib/. Any import of another CsdLean4
     subtree from inside the closure is an error (rule 4 of check-import-hygiene, re-checked
     here with the same import grammar: `public`/`private`/`meta` modifiers, `import all`,
     leading whitespace);
  2. groups the closure into named CONCEPT slices from scripts/physlib-slices.txt, checks that
     every module is assigned and that every dependency lies in the same or an earlier slice
     (so slice k builds on slices 1..k-1), and reports each slice's size against Physlib's
     preference for small, single-concept PRs;
  3. writes slice N to <out>/slice-N/ with the module rename (Analysis/InformationGeometry/*
     → QuantumInfo/ForMathlib/*, beside Physlib PR #1652's own file; everything else →
     PhyslibAlpha/* by default) applied to module paths, import lines and path strings, and
     with this repository's conventions stripped (the `**Category:**`, `**Glossary:**` and
     `**TERM-SCOPE(…)**` lines). The mirror of PR #1652's file is never part of a PR slice
     (Physlib has the original); it is included in the scratch build projects so they compile
     while the PR is open;
  4. scans the exported text for repository-specific vocabulary outside provenance paragraphs
     and reports it (--strict fails on any hit);
  5. writes the scratch Lake project for slices 1..N under <out>/build-N/ and a content hash
     of everything that determines the build (exported sources, toolchain, Mathlib rev,
     layout), so the driver can bind "built clean" to exactly those inputs;
  6. writes CsdLean4/Interop/Physlib/MANIFEST.md when asked.

Pure text processing; no Lean is run here. `--self-test` exercises the parsing and rewriting
rules on synthetic inputs, including the cases a review found unhandled (2026-09-16).
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT_MODULE = "CsdLean4.Interop.Physlib.FubiniStudyGeometry"
CAT1_PREFIX = "CsdLean4.Mathlib."
SLICES_FILE = "scripts/physlib-slices.txt"
TARGETS = {"alpha": "PhyslibAlpha", "quantuminfo": "QuantumInfo.ForMathlib"}
# The information-geometry files (the mirror of PR #1652 and the vector-level bridge) always go
# beside Nava-Hernandez's FisherRao.lean in QuantumInfo/ForMathlib/, whatever the geometry target:
# QuantumInfo may not import PhyslibAlpha, but Alpha may import QuantumInfo.
INFOGEO_PREFIX = "CsdLean4.Mathlib.Analysis.InformationGeometry."
INFOGEO_TARGET = "QuantumInfo.ForMathlib"
MIRROR_MODULE = "CsdLean4.Mathlib.Analysis.InformationGeometry.FisherRao"
PHYSLIB_PR_LINES = 200  # Physlib's review guidelines prefer PRs of roughly this size

# Lean import grammar as this repository uses it: optional leading whitespace, optional
# `public` / `private` / `meta` modifiers, optional `all`, then the module name.
IMPORT_RE = re.compile(r"^[ \t]*((?:(?:public|private|meta)[ \t]+)*)import[ \t]+((?:all[ \t]+)?)([\w.]+)",
                       re.M)

# Hygiene: vocabulary that must not appear in Physlib-bound files outside a provenance paragraph.
HYGIENE = [
    ("CsdLean4", re.compile(r"CsdLean4")),
    ("CSD", re.compile(r"\bCSD\b|CSD\.|CSD-")),
    ("LF-layer", re.compile(r"\bLF[1-6]\b")),
    ("SigmaLayer/RecordLayer", re.compile(r"SigmaLayer|RecordLayer")),
    ("ontic", re.compile(r"\bontic\b")),
    ("sector", re.compile(r"\bsector\b")),
    ("specs/", re.compile(r"\bspecs/")),
    ("BACKLOG", re.compile(r"\bBACKLOG\b")),
    ("repo document", re.compile(r"completed-work ledger|\bthe backlog\b|terms register|"
                                 r"generator-layer plan|top-power plan|exterior-derivative plan|"
                                 r"Mathlib-gaps (?:plan|register)|connectivity manifest|"
                                 r"validation-hardening plan|reconstruction-status ledger|"
                                 r"programme's posits")),
    ("repo marker", re.compile(r"TERM-SCOPE|\*\*Category:\*\*|\*\*Glossary:\*\*|constraintsurfacedynamics")),
    # Planning vocabulary of this repository (added 2026-09-16 after external review): a Physlib
    # reader has no corpus, no milestones and no posits to refer to.
    ("planning vocabulary", re.compile(r"\bcorpus\b|\b[Mm]ilestones?\b|\b[Pp]osits?\b")),
]
PROVENANCE_RE = re.compile(r"\*\*Provenance( and references)?\.?\*\*|Provenance:")
# This repository's convention paragraphs: a line opening with one of these markers, together
# with its continuation lines up to the next blank line, is stripped from the export.
STRIP_PARA_RE = re.compile(
    r"^\*\*(?:Category|Glossary):\*\*.*?(?:\n(?=\n)|\Z)|^\*\*TERM-SCOPE\(.*?(?:\n(?=\n)|\Z)",
    re.M | re.S)


def repo_root() -> str:
    return subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                          check=True).stdout.strip()


def mod_to_path(mod: str) -> str:
    return mod.replace(".", "/") + ".lean"


def read(path: str) -> str:
    with open(path, encoding="utf-8", newline="") as f:
        return f.read()


def imports_in(src: str) -> list[str]:
    """Module names imported by `src`, with the modifiers and `all` stripped."""
    return [m.group(3) for m in IMPORT_RE.finditer(src)]


def closure(root_mod: str) -> tuple[dict[str, list[str]], dict[str, int]]:
    """Transitive closure within CsdLean4.Mathlib.*; deps map and line counts. Every import of
    a CsdLean4 module outside that tree, from any module of the closure, is an error."""
    deps: dict[str, list[str]] = {}
    lines: dict[str, int] = {}
    stack = [root_mod]
    while stack:
        m = stack.pop()
        if m in deps:
            continue
        src = read(mod_to_path(m))
        ims = imports_in(src)
        if m != root_mod:
            bad = [d for d in ims if d.startswith("CsdLean4.") and not d.startswith(CAT1_PREFIX)]
            if bad:
                sys.exit(f"export_physlib: {m} imports outside CsdLean4.Mathlib: {bad}")
        cat1 = [d for d in ims if d.startswith(CAT1_PREFIX)]
        deps[m] = cat1
        lines[m] = src.count("\n")
        stack.extend(cat1)
    deps.pop(root_mod, None)
    lines.pop(root_mod, None)
    return deps, lines


def load_slices(deps: dict[str, list[str]]) -> list[tuple[str, list[str]]]:
    """Concept slices from SLICES_FILE: `slice-name<TAB>module` lines, slices in file order.
    Every closure module must be assigned; every dependency must lie in the same or an
    earlier slice; modules listed but not in the closure are reported and dropped."""
    order: list[str] = []
    members: dict[str, list[str]] = defaultdict(list)
    for raw in read(SLICES_FILE).split("\n"):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        name, mod = line.split("\t") if "\t" in line else line.split(None, 1)
        mod = CAT1_PREFIX + mod.strip() if not mod.startswith("CsdLean4.") else mod.strip()
        if name not in order:
            order.append(name)
        members[name].append(mod)
    listed = {m for ms in members.values() for m in ms}
    missing = sorted(set(deps) - listed)
    if missing:
        sys.exit("export_physlib: modules in the closure but not in scripts/physlib-slices.txt: "
                 + ", ".join(m[len(CAT1_PREFIX):] for m in missing))
    extra = sorted(listed - set(deps))
    for m in extra:
        print(f"export_physlib: note: {m} is listed in {SLICES_FILE} but not in the closure; ignored")
    slices = [(name, [m for m in members[name] if m in deps]) for name in order]
    slices = [(n, ms) for n, ms in slices if ms]
    where = {m: i for i, (_, ms) in enumerate(slices) for m in ms}
    bad = [(m, d) for m, ds in deps.items() for d in ds if where[d] > where[m]]
    if bad:
        sys.exit("export_physlib: slices are not in dependency order: "
                 + "; ".join(f"{m[len(CAT1_PREFIX):]} needs {d[len(CAT1_PREFIX):]} (later slice)" for m, d in bad))
    # within a slice, list modules in dependency order (Kahn, name tie-break)
    out = []
    for name, ms in slices:
        s = set(ms)
        indeg = {m: len([d for d in deps[m] if d in s]) for m in ms}
        rev = defaultdict(list)
        for m in ms:
            for d in deps[m]:
                if d in s:
                    rev[d].append(m)
        ready = sorted(m for m in ms if indeg[m] == 0)
        seq = []
        while ready:
            m = ready.pop(0)
            seq.append(m)
            for n2 in rev[m]:
                indeg[n2] -= 1
                if indeg[n2] == 0:
                    ready.append(n2)
            ready.sort()
        out.append((name, seq))
    return out


def rename(mod: str, target: str) -> str:
    assert mod.startswith(CAT1_PREFIX)
    if mod.startswith(INFOGEO_PREFIX):
        return INFOGEO_TARGET + "." + mod[len(INFOGEO_PREFIX):]
    return target + "." + mod[len(CAT1_PREFIX):]


def rewrite(src: str, target: str) -> str:
    """Rename imports and path strings, strip this repository's convention lines."""
    def fix_import(m: re.Match) -> str:
        mod = m.group(3)
        new = rename(mod, target) if mod.startswith(CAT1_PREFIX) else mod
        return m.group(0)[: m.start(3) - m.start(0)] + new
    src = IMPORT_RE.sub(fix_import, src)
    src = src.replace("CsdLean4/Mathlib/Analysis/InformationGeometry/", INFOGEO_TARGET.replace(".", "/") + "/")
    src = src.replace("CsdLean4/Mathlib/", target.replace(".", "/") + "/")
    src = src.replace("`" + INFOGEO_PREFIX, "`" + INFOGEO_TARGET + ".")
    src = src.replace("`CsdLean4.Mathlib.", "`" + target + ".")
    src = STRIP_PARA_RE.sub("", src)
    src = re.sub(r"\n{3,}", "\n\n", src)
    return src


def hygiene_hits(src: str) -> list[tuple[int, str, str]]:
    """Hits outside provenance text, as (line, category, text). Provenance text is a
    `## Provenance` section (to the next `## ` heading or the closing `-/`) or an inline
    `**Provenance.**` / `**Provenance and references.**` paragraph (to the next blank line or
    the closing `-/`, whichever comes first)."""
    hits: list[tuple[int, str, str]] = []
    in_section = in_para = False
    for i, line in enumerate(src.split("\n"), 1):
        stripped = line.strip()
        if line.startswith("## Provenance"):
            in_section = True
            continue
        if in_section and (line.startswith("## ") or stripped == "-/"):
            in_section = False
        if in_para and (stripped == "" or stripped == "-/" or stripped.endswith("-/")):
            in_para = False
            if stripped.endswith("-/") and stripped != "-/":
                continue  # the closing line of the exempt paragraph
        if PROVENANCE_RE.search(line) and not line.startswith("## "):
            in_para = True
        if in_section or in_para:
            continue
        for name, rx in HYGIENE:
            if rx.search(line):
                hits.append((i, name, line))
    return hits


def hygiene(src: str) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for _, name, _ in hygiene_hits(src):
        counts[name] += 1
    return dict(counts)


def join(*parts: str) -> str:
    return "/".join(p.strip("/") for p in parts)


def write(path: str, content: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(content)


def physlib_mathlib_rev() -> str | None:
    """Physlib's pinned Mathlib rev, from its lake-manifest.json via gh; None if unreachable."""
    try:
        out = subprocess.run(
            ["gh", "api", "repos/leanprover-community/physlib/contents/lake-manifest.json",
             "--jq", ".content"], capture_output=True, text=True, timeout=60)
        if out.returncode != 0:
            return None
        import base64
        m = json.loads(base64.b64decode(out.stdout))
        for p in m["packages"]:
            if p["name"] == "mathlib":
                return p["rev"]
    except Exception:
        return None
    return None


def local_mathlib_rev() -> str:
    m = json.load(open("lake-manifest.json", encoding="utf-8"))
    for p in m["packages"]:
        if p["name"] == "mathlib":
            return p["rev"]
    raise SystemExit("no mathlib in lake-manifest.json")


def build_inputs_hash(mods: list[str], target: str, rev: str) -> str:
    """Everything that determines whether the scratch build of `mods` passes."""
    h = hashlib.sha256()
    h.update(read("lean-toolchain").encode())
    h.update(rev.encode())
    h.update(target.encode())
    for m in mods:
        h.update(m.encode())
        h.update(rewrite(read(mod_to_path(m)), target).encode())
    return h.hexdigest()[:16]


def write_build_project(out: str, n: int, slices, target: str, rev: str, use_local_packages: bool):
    """Scratch Lake project containing slices 1..n (plus the mirror, which Physlib has and a
    PR omits, so the project compiles while PR #1652 is open) under <out>/build-n/."""
    bdir = join(out, f"build-{n}")
    src_mods = [m for _, ms in slices[:n] for m in ms]
    mods = [rename(m, target) for m in src_mods]
    for m in src_mods:
        write(join(bdir, mod_to_path(rename(m, target))), rewrite(read(mod_to_path(m)), target))
    libs = sorted({m.split(".")[0] for m in mods})
    for lib in libs:
        write(join(bdir, lib + ".lean"),
              "module\n\n" + "".join(f"public import {m}\n" for m in mods if m.startswith(lib + ".")))
    write(join(bdir, "lean-toolchain"), read("lean-toolchain"))
    lakefile = f'''name = "physlib_export_slice_{n}"
defaultTargets = {json.dumps(libs)}
leanOptions = {{ autoImplicit = false, relaxedAutoImplicit = false }}

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "{rev}"
''' + "".join(f'''
[[lean_lib]]
name = "{lib}"
''' for lib in libs)
    write(join(bdir, "lakefile.toml"), lakefile)
    if use_local_packages:
        write(join(bdir, "lake-manifest.json"), read("lake-manifest.json"))
    write(join(bdir, "INPUTS.sha256"), build_inputs_hash(src_mods, target, rev) + "\n")
    return bdir


def manifest(deps, lines, slices, target, phys_rev, local_rev, hyg, build_results, sweep_text):
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = bool(subprocess.run(["git", "status", "--porcelain", "--", "CsdLean4", "scripts"],
                                capture_output=True, text=True).stdout.strip())
    pr_mods = [m for _, ms in slices for m in ms if m != MIRROR_MODULE]
    total_files, total_lines = len(pr_mods), sum(lines[m] for m in pr_mods)
    today = _dt.date.today().isoformat()
    L = []
    L.append("# Physlib export manifest — the Fubini–Study geometry of `ℂℙⁿ` and its Fisher–Rao bridge\n")
    L.append(f"Generated by `scripts/export-physlib.sh` on {today} from csd-lean4 commit `{commit[:12]}`"
             + (" plus uncommitted changes under `CsdLean4/` or `scripts/` at generation time" if dirty else "")
             + ". Do not edit by hand; re-run the script.\n")
    L.append("## What this is\n")
    L.append("The transitive import closure, within `CsdLean4/Mathlib/`, of the root module "
             "`CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean`: everything a reviewer needs for the "
             "theorem `Projectivization.fsMetric_eq_fisherRaoInner` (the Fubini–Study metric of `ℂℙⁿ` "
             "pushes forward to Fisher–Rao along the Born-weight map, constant one) and its vector-level form "
             "`FisherRao.fisherRaoInner_bornDeriv`. The closure imports Mathlib and itself only "
             "(`scripts/check-import-hygiene.sh` rule 4, re-checked by the exporter with the same import "
             "grammar).\n")
    L.append(f"* Offered to Physlib: **{total_files} files, {total_lines:,} lines**, in **{len(slices)} "
             f"concept slices** (`scripts/physlib-slices.txt`, validated: every dependency lies in the same or an "
             f"earlier slice). The mirror of PR #1652's `FisherRao.lean` is not offered (Physlib has it); the "
             f"scratch builds include it so they compile while the PR is open.")
    L.append(f"* Physlib layout: `CsdLean4.Mathlib.Analysis.InformationGeometry.X` → `{INFOGEO_TARGET}.X` "
             f"(beside PR #1652's `FisherRao.lean`); every other `CsdLean4.Mathlib.X` → `{target}.X`. "
             "`QuantumInfo` may not import `PhyslibAlpha`; `PhyslibAlpha` imports `QuantumInfo`, so the "
             "manifold bridge in Alpha consumes the vector-level bridge in QuantumInfo.")
    L.append(f"* Physlib's review guidelines prefer single-concept PRs of roughly {PHYSLIB_PR_LINES} lines; the "
             "slices are concepts, not PR sizes, and several will be split further at PR time.")
    L.append(f"* Mathlib pin: csd-lean4 `{local_rev[:12]}`; Physlib `{(phys_rev or 'unreachable')[:12]}`"
             + (" — **identical**." if phys_rev == local_rev else " — **differ**; the build used csd-lean4's pin." if phys_rev else "."))
    L.append("* Lean toolchain: `" + read("lean-toolchain").strip() + "`.")
    L.append("* Normalisation: `Projectivization.fsMetric` has Gram matrix `4 • 1` at a chart origin (the round unit "
             "sphere for `ℂℙ¹`); in that normalisation the Fubini–Study metric of a pure-state family is its quantum "
             "Fisher information (`FisherRao.fsInnerHom_self_of_norm_eq_one`). The Hamiltonian of the torus action "
             "for this form is `2 Σ θₖ Φₖ`, so `Φ` (the Born weights, `Projectivization.momentMap`) is the moment map "
             "in the Hamiltonian sense up to that factor 2; the bridge is stated for `Φ`.\n")
    L.append("## Axiom profile\n")
    L.append("`scripts/physlib-axiom-sweep.lean` walks every constant declared by every module in the closure — "
             "public, private and auxiliary alike — and fails on any axiom outside "
             "`[propext, Classical.choice, Quot.sound]`. Trusted boundary: the walk recurses through the "
             "closure's own constants and inspects every axiom they reference directly, but does not re-walk the "
             "interior of Mathlib constants; `scripts/export-physlib.sh` also checks that every closure module has "
             "an `@[expose] public section`, without which the module system would hide proof terms from the walk.\n")
    L.append("```\n" + sweep_text.strip() + "\n```\n")
    L.append("## Builds against the pin\n")
    if build_results:
        for key, res in sorted(build_results.items()):
            L.append(f"* {key}: **{res}**")
        L.append("")
        L.append("Each result is keyed by the slice range and a hash of everything that determines the build "
                 "(exported sources after the rename, toolchain, Mathlib rev, layout); a result whose hash no "
                 "longer matches the current export is stale and the driver rebuilds. Builds use "
                 "`lake build --wfail` (warnings fatal).\n")
    else:
        L.append("(no build recorded)\n")
    L.append("## Slices\n")
    L.append("| Slice | Concept | Module (csd-lean4) | Physlib module | Lines | Hygiene hits |")
    L.append("|---|---|---|---|---|---|")
    for i, (name, ms) in enumerate(slices, 1):
        for m in ms:
            if m == MIRROR_MODULE:
                continue
            h = hyg.get(m, {})
            hs = ", ".join(f"{k} {v}" for k, v in sorted(h.items())) or "—"
            L.append(f"| {i} | {name} | `{m[len('CsdLean4.'):]}` | `{rename(m, target)}` | {lines[m]} | {hs} |")
        tot = sum(lines[m] for m in ms if m != MIRROR_MODULE)
        L.append(f"| | | **slice {i} total** | | **{tot:,}** | |")
    L.append("")
    tot_h = sum(sum(h.values()) for m, h in hyg.items() if m != MIRROR_MODULE)
    L.append("## Hygiene\n")
    L.append("Lines of the exported text mentioning this repository's vocabulary (`CsdLean4`, `CSD`, the CSD "
             "layers, `ontic`, `sector`, its planning documents, ledgers and markers) outside provenance "
             f"paragraphs: **{tot_h}** across {sum(1 for m, h in hyg.items() if h and m != MIRROR_MODULE)} files. "
             + ("None remain. The `**Provenance and references.**` paragraphs, which name where each module came "
                "from in this repository, are kept in the export as attribution; a Physlib PR may keep or drop "
                "them. `scripts/export-physlib.sh --strict` passes.\n"
                if tot_h == 0 else
                "Each is a line to reword or drop before the PR; `scripts/export-physlib.sh --strict` fails while "
                "the count is positive.\n"))
    L.append("## Review order\n")
    L.append("1. `FubiniStudyFisherRao.lean` — the vector-level bridge, Mathlib-only, stated against PR #1652's "
             "`OpenSimplex`; the first Physlib PR, into `QuantumInfo/ForMathlib/`, once #1652 merges.")
    L.append("2. `Geometry/Manifold/Instances/ProjectiveSpaceFisherRao.lean` — the manifold bridge, a corollary of 1 "
             "through `fsMetric_eq_fsInnerHom`; injective on the horizontal space.")
    L.append("3. The concept slices, in order, for the geometry the manifold statement stands on.\n")
    return "\n".join(L) + "\n"


def self_test() -> None:
    src = ("module\n\npublic import CsdLean4.Mathlib.A.B\nimport all CsdLean4.Mathlib.C\n"
           "  private import   CsdLean4.Mathlib.D.E\nmeta import Mathlib.X\n/-! import CsdLean4.LF1.Fake -/\n")
    ims = imports_in(src)
    # modifiers, `all`, leading whitespace and repeated spaces are all parsed; an `import` inside
    # a comment is not (the grammar anchors at the line start, so it can only over-approximate)
    assert ims == ["CsdLean4.Mathlib.A.B", "CsdLean4.Mathlib.C", "CsdLean4.Mathlib.D.E", "Mathlib.X"], ims
    out = rewrite(src, "PhyslibAlpha")
    assert "public import PhyslibAlpha.A.B\n" in out and "import all PhyslibAlpha.C\n" in out
    assert "private import   PhyslibAlpha.D.E" in out and "meta import Mathlib.X" in out, out
    assert [h[1] for h in hygiene_hits(out)] == ["CsdLean4", "LF-layer"], hygiene_hits(out)  # the comment text
    doc = ("/-!\n# T\n\n**Category:** 1-Mathlib (CSD-free).\n\n**TERM-SCOPE(Kahler)** — x.\n\n"
           "**Provenance and references.** the backlog; CSD.LF2.foo.\nsecond line CsdLean4. -/\n\n"
           "theorem t : True := trivial -- CSD\n")
    out = rewrite(doc, "PhyslibAlpha")
    assert "**Category:**" not in out and "TERM-SCOPE" not in out, out
    hits = hygiene_hits(out)
    assert [h[1] for h in hits] == ["CSD"], hits  # the trailing code comment, not the paragraph
    print("export_physlib: self-test OK")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--slice", type=int, help="export slice N (1-based) and its build project")
    ap.add_argument("--all", action="store_true", help="export every slice")
    ap.add_argument("--target", choices=TARGETS.keys(), default="alpha")
    ap.add_argument("--out", default="export/physlib")
    ap.add_argument("--table", action="store_true", help="print the slice table and exit")
    ap.add_argument("--hits", action="store_true", help="print every hygiene hit with its line and exit")
    ap.add_argument("--manifest", action="store_true", help="write MANIFEST.md")
    ap.add_argument("--build-results", default="", help="JSON {key: result} for the manifest")
    ap.add_argument("--sweep-output", default="", help="file with the closure sweep output")
    ap.add_argument("--strict", action="store_true", help="fail on any hygiene hit")
    ap.add_argument("--local-packages", action="store_true",
                    help="scratch project reuses this repo's lake-manifest (driver junctions .lake/packages)")
    ap.add_argument("--print-hash", type=int, metavar="N", help="print the build-input hash for slices 1..N")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return
    os.chdir(repo_root())
    target = TARGETS[args.target]
    deps, lines = closure(ROOT_MODULE)
    slices = load_slices(deps)
    hyg = {m: hygiene(rewrite(read(mod_to_path(m)), target)) for m in deps}
    local_rev = local_mathlib_rev()
    if args.print_hash:
        n = args.print_hash
        print(build_inputs_hash([m for _, ms in slices[:n] for m in ms], target,
                                physlib_mathlib_rev() or local_rev))
        return
    if args.hits:
        for m in sorted(deps):
            for ln, name, line in hygiene_hits(rewrite(read(mod_to_path(m)), target)):
                print(f"{mod_to_path(m)}:{ln}: [{name}] {line.strip()}")
        return
    if args.table or not (args.slice or args.all or args.manifest):
        pr = [m for _, ms in slices for m in ms if m != MIRROR_MODULE]
        print(f"closure: {len(deps)} files, {sum(lines.values()):,} lines "
              f"({len(pr)} files / {sum(lines[m] for m in pr):,} lines offered; the mirror is not), "
              f"{len(slices)} concept slices")
        for i, (name, ms) in enumerate(slices, 1):
            tot = sum(lines[m] for m in ms if m != MIRROR_MODULE)
            flag = "" if tot <= PHYSLIB_PR_LINES else f"  (over Physlib's ~{PHYSLIB_PR_LINES}-line PR guideline)"
            print(f"slice {i} [{name}]: {tot:,} lines{flag}")
            for m in ms:
                tag = "  (mirror; build only)" if m == MIRROR_MODULE else ""
                print(f"    {m[len(CAT1_PREFIX):]} ({lines[m]}){tag}")
        tot = sum(sum(h.values()) for h in hyg.values())
        print(f"hygiene hits outside provenance paragraphs: {tot}")
        if args.table:
            return
    phys_rev = physlib_mathlib_rev()
    rev = phys_rev or local_rev
    use_local = args.local_packages and (phys_rev is None or phys_rev == local_rev)
    todo = range(1, len(slices) + 1) if args.all else ([args.slice] if args.slice else [])
    for n in todo:
        if not 1 <= n <= len(slices):
            sys.exit(f"export_physlib: no slice {n} (there are {len(slices)})")
        name, ms = slices[n - 1]
        sdir = join(args.out, f"slice-{n}")
        for m in ms:
            if m == MIRROR_MODULE:
                continue
            write(join(sdir, mod_to_path(rename(m, target))), rewrite(read(mod_to_path(m)), target))
        bdir = write_build_project(args.out, n, slices, target, rev, use_local)
        print(f"slice {n} [{name}]: {len([m for m in ms if m != MIRROR_MODULE])} files -> {sdir}; "
              f"build project (slices 1..{n}) -> {bdir} (mathlib {rev[:12]}, "
              f"{'local packages' if use_local else 'git require'})")
    if args.strict:
        tot = sum(sum(h.values()) for h in hyg.values())
        if tot:
            for m, h in sorted(hyg.items()):
                if h:
                    print(f"  hygiene {m[len(CAT1_PREFIX):]}: {h}")
            sys.exit(f"export_physlib: {tot} hygiene hit(s); reword or drop them before the PR")
    if args.manifest:
        build_results = json.loads(args.build_results) if args.build_results else {}
        sweep_text = read(args.sweep_output) if args.sweep_output else "(sweep not run)"
        write("CsdLean4/Interop/Physlib/MANIFEST.md",
              manifest(deps, lines, slices, target, phys_rev, local_rev, hyg, build_results, sweep_text))
        print("wrote CsdLean4/Interop/Physlib/MANIFEST.md")


if __name__ == "__main__":
    main()
