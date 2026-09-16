#!/usr/bin/env python3
"""export_physlib.py — the Physlib export of the Fubini–Study geometry (logic).

Driven by scripts/export-physlib.sh; see that file for the contract. This module:

  1. reads the root CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean and computes its
     transitive import closure within CsdLean4/Mathlib/ (aborting if the closure reaches any
     other CsdLean4 subtree — rule 4 of check-import-hygiene, re-checked here);
  2. orders the closure topologically (Kahn, deterministic tie-break) and cuts it into slices
     of at most MAX_SLICE_LINES lines, each closed under "depends only on earlier slices";
  3. writes slice N to <out>/slice-N/<Target>/... with the module rename
     CsdLean4.Mathlib.X -> <Target>.X applied to module paths, import lines and the
     CsdLean4/Mathlib/ path strings in docstrings;
  4. runs the hygiene scan (CSD-specific vocabulary outside provenance paragraphs) and
     reports it per file;
  5. writes the scratch Lake project for slices 1..N under <out>/build-N/ (lakefile,
     toolchain, manifest, root module) for the shell driver to build;
  6. writes CsdLean4/Interop/Physlib/MANIFEST.md when asked.

Pure text processing; no Lean is run here.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT_MODULE = "CsdLean4.Interop.Physlib.FubiniStudyGeometry"
CAT1_PREFIX = "CsdLean4.Mathlib."
MAX_SLICE_LINES = 2600
TARGETS = {"alpha": "PhyslibAlpha", "quantuminfo": "QuantumInfo.ForMathlib"}
# The information-geometry files (the mirror of PR #1652 and the vector-level bridge) always go
# beside Nava-Hernandez's FisherRao.lean in QuantumInfo/ForMathlib/, whatever the geometry target:
# QuantumInfo may not import PhyslibAlpha, but Alpha may import QuantumInfo.
INFOGEO_PREFIX = "CsdLean4.Mathlib.Analysis.InformationGeometry."
INFOGEO_TARGET = "QuantumInfo.ForMathlib"
IMPORT_RE = re.compile(r"^(?:public\s+|private\s+|meta\s+)*import\s+([\w.]+)", re.M)

# Hygiene: vocabulary that must not appear in Physlib-bound files outside a provenance note.
HYGIENE = [
    ("CSD.", re.compile(r"CSD\.")),
    ("LF-layer", re.compile(r"\bLF[1-6]\b")),
    ("ontic", re.compile(r"\bontic\b")),
    ("sector", re.compile(r"\bsector\b")),
    ("specs/", re.compile(r"\bspecs/")),
    ("BACKLOG", re.compile(r"\bBACKLOG\b")),
]
PROVENANCE_RE = re.compile(r"\*\*Provenance\.?\*\*|## Provenance|Provenance:")


def repo_root() -> str:
    out = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                         check=True).stdout.strip()
    return out


def mod_to_path(mod: str) -> str:
    return mod.replace(".", "/") + ".lean"


def read(path: str) -> str:
    with open(path, encoding="utf-8", newline="") as f:
        return f.read()


def imports_of(path: str) -> list[str]:
    return IMPORT_RE.findall(read(path))


def closure(root_mod: str) -> tuple[dict[str, list[str]], dict[str, int]]:
    """Transitive closure within CsdLean4.Mathlib.*; deps map and line counts."""
    deps: dict[str, list[str]] = {}
    lines: dict[str, int] = {}
    stack = [root_mod]
    while stack:
        m = stack.pop()
        if m in deps:
            continue
        p = mod_to_path(m)
        src = read(p)
        ims = IMPORT_RE.findall(src)
        bad = [d for d in ims if d.startswith("CsdLean4.") and not d.startswith(CAT1_PREFIX)
               and d != root_mod and not d.startswith("CsdLean4.Interop.")]
        if bad and m != root_mod:
            sys.exit(f"export_physlib: {m} imports outside CsdLean4.Mathlib: {bad}")
        cat1 = [d for d in ims if d.startswith(CAT1_PREFIX)]
        deps[m] = cat1
        lines[m] = src.count("\n")
        stack.extend(cat1)
    deps.pop(root_mod, None)
    lines.pop(root_mod, None)
    return deps, lines


def layer(deps: dict[str, list[str]], lines: dict[str, int]) -> list[list[str]]:
    """Kahn's algorithm with a deterministic tie-break (dependency depth, then name), cut
    greedily into slices of at most MAX_SLICE_LINES lines. Every module's dependencies lie in
    the same or an earlier slice, so slice k builds on slices 1..k-1."""
    depth: dict[str, int] = {}

    def d(m: str) -> int:
        if m not in depth:
            depth[m] = 1 + max((d(x) for x in deps[m]), default=0)
        return depth[m]

    for m in deps:
        d(m)
    indeg = {m: len(deps[m]) for m in deps}
    rev: dict[str, list[str]] = defaultdict(list)
    for m, ds in deps.items():
        for x in ds:
            rev[x].append(m)
    ready = sorted([m for m in deps if indeg[m] == 0], key=lambda m: (depth[m], m))
    order: list[str] = []
    while ready:
        m = ready.pop(0)
        order.append(m)
        for n in rev[m]:
            indeg[n] -= 1
            if indeg[n] == 0:
                ready.append(n)
        ready.sort(key=lambda m: (depth[m], m))
    slices: list[list[str]] = [[]]
    tot = 0
    for m in order:
        if tot + lines[m] > MAX_SLICE_LINES and slices[-1]:
            slices.append([])
            tot = 0
        slices[-1].append(m)
        tot += lines[m]
    # verify
    where = {m: i for i, s in enumerate(slices) for m in s}
    for m, ds in deps.items():
        for x in ds:
            assert where[x] <= where[m], (m, x)
    return slices


def rename(mod: str, target: str) -> str:
    assert mod.startswith(CAT1_PREFIX)
    if mod.startswith(INFOGEO_PREFIX):
        return INFOGEO_TARGET + "." + mod[len(INFOGEO_PREFIX):]
    return target + "." + mod[len(CAT1_PREFIX):]


def rewrite(src: str, target: str) -> str:
    src = src.replace("import " + INFOGEO_PREFIX, "import " + INFOGEO_TARGET + ".")
    src = src.replace("import " + CAT1_PREFIX, "import " + target + ".")
    src = src.replace("CsdLean4/Mathlib/Analysis/InformationGeometry/", INFOGEO_TARGET.replace(".", "/") + "/")
    src = src.replace("CsdLean4/Mathlib/", target.replace(".", "/") + "/")
    src = src.replace("`" + INFOGEO_PREFIX, "`" + INFOGEO_TARGET + ".")
    src = src.replace("`CsdLean4.Mathlib.", "`" + target + ".")
    return src


def hygiene(src: str) -> dict[str, int]:
    """Count hygiene hits outside provenance paragraphs. A paragraph is the run of lines from
    a line matching PROVENANCE_RE to the next blank line."""
    counts: dict[str, int] = defaultdict(int)
    in_prov = False
    for line in src.split("\n"):
        if PROVENANCE_RE.search(line):
            in_prov = True
        if in_prov and line.strip() == "":
            in_prov = False
        if in_prov:
            continue
        for name, rx in HYGIENE:
            if rx.search(line):
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


def write_build_project(out: str, n: int, slices: list[list[str]], target: str,
                        rev: str, use_local_packages: bool) -> str:
    """Scratch Lake project containing slices 1..n under <out>/build-n/. Returns its path."""
    bdir = join(out, f"build-{n}")
    mods = [rename(m, target) for s in slices[:n] for m in s]
    for s in slices[:n]:
        for m in s:
            write(join(bdir, mod_to_path(rename(m, target))),
                  rewrite(read(mod_to_path(m)), target))
    # One lean_lib per top-level namespace present (QuantumInfo and/or the geometry target).
    libs = sorted({m.split(".")[0] for m in mods})
    for lib in libs:
        write(join(bdir, lib + ".lean"),
              "module\n\n" + "".join(f"public import {m}\n" for m in mods if m.startswith(lib + ".")))
    toolchain = read("lean-toolchain")
    write(join(bdir, "lean-toolchain"), toolchain)
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
    return bdir


def manifest(deps, lines, slices, target, phys_rev, local_rev, hyg, build_results, sweep_text):
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    total_files = len(deps)
    total_lines = sum(lines.values())
    today = _dt.date.today().isoformat()
    L = []
    L.append("# Physlib export manifest — the Fubini–Study geometry of `ℂℙⁿ` and its Fisher–Rao bridge\n")
    L.append(f"Generated by `scripts/export-physlib.sh` on {today} from csd-lean4 commit `{commit[:12]}`. "
             "Do not edit by hand; re-run the script.\n")
    L.append("## What this is\n")
    L.append("The transitive import closure, within `CsdLean4/Mathlib/`, of the root module "
             "`CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean`: everything a reviewer needs for the "
             "theorem `Projectivization.fsMetric_eq_fisherRaoInner` (the Fubini–Study metric of `ℂℙⁿ` "
             "pushes forward to Fisher–Rao along the moment map, constant one) and its vector-level form "
             "`FisherRao.fisherRaoInner_bornDeriv`. The closure imports Mathlib and itself only "
             "(`scripts/check-import-hygiene.sh`, rule 4).\n")
    L.append(f"* Closure: **{total_files} files, {total_lines:,} lines**, in **{len(slices)} slices** "
             f"(dependency order, at most {MAX_SLICE_LINES:,} lines each; slice k depends only on slices 1..k-1).")
    L.append(f"* Physlib layout: `CsdLean4.Mathlib.Analysis.InformationGeometry.X` → `{INFOGEO_TARGET}.X` "
             f"(beside PR #1652's `FisherRao.lean`); every other `CsdLean4.Mathlib.X` → `{target}.X`. "
             "`QuantumInfo` may not import `PhyslibAlpha`; `PhyslibAlpha` imports `QuantumInfo`, so the "
             "manifold bridge in Alpha consumes the vector-level bridge in QuantumInfo.")
    L.append(f"* Mathlib pin: csd-lean4 `{local_rev[:12]}`; Physlib `{(phys_rev or 'unreachable')[:12]}`"
             + (" — **identical**." if phys_rev == local_rev else " — **differ**; the build used csd-lean4's pin." if phys_rev else "."))
    L.append("* Lean toolchain: `" + read("lean-toolchain").strip() + "`.\n")
    L.append("## Axiom profile\n")
    L.append("`scripts/physlib-axiom-sweep.lean` walks every declaration of every module in the closure "
             "(not only the pinned ones) and fails on any axiom outside `[propext, Classical.choice, Quot.sound]`:\n")
    L.append("```\n" + sweep_text.strip() + "\n```\n")
    L.append("## Builds against the pin\n")
    if build_results:
        for n, res in sorted(build_results.items(), key=lambda kv: int(kv[0])):
            n = int(n)
            L.append(f"* slice {n} (slices 1..{n} together, {sum(lines[m] for s in slices[:n] for m in s):,} lines): **{res}**")
        L.append("")
    else:
        L.append("(no build run in this invocation)\n")
    L.append("## Slices\n")
    L.append("| Slice | Module (csd-lean4) | Physlib module | Lines | Hygiene hits |")
    L.append("|---|---|---|---|---|")
    for i, s in enumerate(slices, 1):
        for m in s:
            h = hyg.get(m, {})
            hs = ", ".join(f"{k} {v}" for k, v in sorted(h.items())) or "—"
            L.append(f"| {i} | `{m[len('CsdLean4.'):]}` | `{rename(m, target)}` | {lines[m]} | {hs} |")
        L.append(f"| | **slice {i} total** | | **{sum(lines[m] for m in s):,}** | |")
    L.append("")
    tot_h = sum(sum(h.values()) for h in hyg.values())
    L.append("## Hygiene\n")
    L.append(f"Lines mentioning CSD-specific vocabulary (`CSD.`, `LF1`–`LF6`, `ontic`, `sector`, `specs/`, `BACKLOG`) "
             f"outside provenance paragraphs, after the rename: **{tot_h}** across "
             f"{sum(1 for h in hyg.values() if h)} files. These are docstring cross-references to the "
             "consumers in this repository, not code; each is a line to reword or drop at PR time. "
             "`scripts/export-physlib.sh --strict` fails while the count is positive.\n")
    L.append("## Review order\n")
    L.append("1. `FisherRao.lean` (mirror of Physlib PR #1652; dropped at PR time) and "
             "`FubiniStudyFisherRao.lean` — the vector-level bridge, Mathlib-only.")
    L.append("2. `Geometry/Manifold/Instances/ProjectiveSpaceFisherRao.lean` — the manifold bridge, "
             "a corollary of 1 through `fsMetric_eq_fsInnerHom`.")
    L.append("3. The slices, in order, for the geometry the manifold statement stands on.\n")
    return "\n".join(L) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--slice", type=int, help="export slice N (1-based) and its build project")
    ap.add_argument("--all", action="store_true", help="export every slice")
    ap.add_argument("--target", choices=TARGETS.keys(), default="alpha")
    ap.add_argument("--out", default="export/physlib")
    ap.add_argument("--table", action="store_true", help="print the slice table and exit")
    ap.add_argument("--manifest", action="store_true", help="write MANIFEST.md")
    ap.add_argument("--build-results", default="", help="JSON {slice: result} for the manifest")
    ap.add_argument("--sweep-output", default="", help="file with the closure sweep output")
    ap.add_argument("--strict", action="store_true", help="fail on any hygiene hit")
    ap.add_argument("--local-packages", action="store_true",
                    help="scratch project reuses this repo's lake-manifest (driver junctions .lake/packages)")
    args = ap.parse_args()
    os.chdir(repo_root())
    target = TARGETS[args.target]
    deps, lines = closure(ROOT_MODULE)
    slices = layer(deps, lines)
    hyg = {m: hygiene(rewrite(read(mod_to_path(m)), target)) for m in deps}
    if args.table or not (args.slice or args.all or args.manifest):
        print(f"closure: {len(deps)} files, {sum(lines.values()):,} lines, {len(slices)} slices")
        for i, s in enumerate(slices, 1):
            print(f"slice {i}: {sum(lines[m] for m in s):,} lines")
            for m in s:
                print(f"    {m[len(CAT1_PREFIX):]} ({lines[m]})")
        tot = sum(sum(h.values()) for h in hyg.values())
        print(f"hygiene hits outside provenance paragraphs: {tot}")
        if args.table:
            return
    local_rev = local_mathlib_rev()
    phys_rev = physlib_mathlib_rev()
    rev = phys_rev or local_rev
    use_local = args.local_packages and (phys_rev is None or phys_rev == local_rev)
    todo = range(1, len(slices) + 1) if args.all else ([args.slice] if args.slice else [])
    for n in todo:
        if not 1 <= n <= len(slices):
            sys.exit(f"export_physlib: no slice {n} (there are {len(slices)})")
        sdir = join(args.out, f"slice-{n}")
        for m in slices[n - 1]:
            write(join(sdir, mod_to_path(rename(m, target))), rewrite(read(mod_to_path(m)), target))
        bdir = write_build_project(args.out, n, slices, target, rev, use_local)
        print(f"slice {n}: {len(slices[n-1])} files -> {sdir}; build project -> {bdir} "
              f"(mathlib {rev[:12]}, {'local packages' if use_local else 'git require'})")
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
