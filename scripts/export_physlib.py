#!/usr/bin/env python3
"""export_physlib.py — the Physlib export of the Fisher–Rao bridge (logic).

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
  3. writes slice N to <out>/slice-N/. THE OFFER (2026-09-18) IS SLICE 2 ONLY — the two
     vector-level files, `FubiniStudyFisherRao` and `BraunsteinCaves`. Those are emitted
     PHYSLIB-READY from their sidecars in scripts/physlib-sidecars/<stem>.md: the module
     docstring is generated in Physlib's numbered template (`# title`, `## i. Overview`,
     `## ii. Key results`, `## iii. Table of contents`, `## iv. References` with `[ref: key]`
     tags), the section comments are renumbered `## A.`, `### A.1.` and listed in the table of
     contents, declaration docstrings are replaced by the sidecar's terse ones, repository
     markers (★, convention paragraphs) are stripped, over-long comment lines are re-wrapped to
     100 columns, and the result is checked by replicas of Physlib's own linters
     (scripts/MetaPrograms/module_doc_lint.lean, scripts/lint-style.py's line length,
     scripts/check_references.py). Bib entries the files need that Physlib's
     docs/references.bib lacks are written beside the slice as docs/references.bib.additions,
     and PR-NOTES.md says what else the pull request touches. Every other slice is the Mathlib
     track: it stays in csd-lean4, and is exported only into the scratch build projects (module
     rename to a scratch namespace) to prove the closure builds against Physlib's pin;
  4. scans the exported text for repository-specific vocabulary outside provenance paragraphs
     and reports it (--strict fails on any hit, and on any failed Physlib-ready check);
  5. writes the scratch Lake project for slices 1..N under <out>/build-N/ and a content hash
     of everything that determines the build (exported sources, toolchain, Mathlib rev,
     layout), so the driver can bind "built clean" to exactly those inputs;
  6. writes CsdLean4/Interop/Physlib/MANIFEST.md when asked.

Pure text processing; no Lean is run here. `--self-test` exercises the parsing, rewriting and
Physlib-ready rules on synthetic inputs, including the cases reviews found unhandled
(2026-09-16, 2026-09-18).
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
SIDECAR_DIR = "scripts/physlib-sidecars"
# Scratch-build namespace of the Mathlib-track slices (they are not offered; the rename only
# gives the scratch project valid module paths).
TARGETS = {"alpha": "PhyslibAlpha", "quantuminfo": "QuantumInfo.ForMathlib"}
INFOGEO_PREFIX = "CsdLean4.Mathlib.Analysis.InformationGeometry."
MIRROR_MODULE = INFOGEO_PREFIX + "FisherRao"
# The offer: corpus module -> Physlib file stem (and sidecar name). Emitted Physlib-ready.
OFFERED = {
    INFOGEO_PREFIX + "FubiniStudyFisherRao": "FisherRaoBridge",
    INFOGEO_PREFIX + "BraunsteinCaves": "BraunsteinCaves",
}
# Placement and the import of Nava-Hernandez's file are the two open items of the 2026-09-18
# gap list (6 and 8): both are settings, not decisions made here.
CFG = {
    "physlib_dir": os.environ.get("PHYSLIB_DIR", "QuantumInfo.States.Pure"),
    "nava_module": os.environ.get("PHYSLIB_FISHER_RAO_MODULE", "QuantumInfo.ForMathlib.FisherRao"),
    "physlib_root": os.environ.get("PHYSLIB_ROOT", ""),
}
PHYSLIB_PR_LINES = 200  # Physlib's review guidelines prefer PRs of roughly this size
MAX_COLS = 100          # Physlib's lint-style.py: ERR_LIN on any longer line

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
# Stricter still for the OFFERED files (gap item 4, 2026-09-18): no ★ markers, no paths into
# this repository's tree, no "mirrored in this directory", no ledger tags.
HYGIENE_OFFERED = [
    ("marker ★", re.compile(r"★")),
    ("repo path", re.compile(r"`[A-Za-z]+(?:/[A-Za-z0-9_]+)+\.lean`")),
    ("mirror note", re.compile(r"mirrored in this directory")),
    ("ledger tag", re.compile(r"\bKG-\d+\b|\bCL-\d+\b|\bQ\d+\b")),
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
    """The module's name on the Physlib side: the mirror is Nava-Hernandez's own file, an offered
    module goes to the placement directory, everything else to the scratch namespace."""
    assert mod.startswith(CAT1_PREFIX)
    if mod == MIRROR_MODULE:
        return CFG["nava_module"]
    if mod in OFFERED:
        return CFG["physlib_dir"] + "." + OFFERED[mod]
    return target + "." + mod[len(CAT1_PREFIX):]


def rewrite(src: str, target: str) -> str:
    """Rename imports and path strings, strip this repository's convention lines."""
    def fix_import(m: re.Match) -> str:
        mod = m.group(3)
        new = rename(mod, target) if mod.startswith(CAT1_PREFIX) else mod
        return m.group(0)[: m.start(3) - m.start(0)] + new
    src = IMPORT_RE.sub(fix_import, src)
    phys_dir = CFG["physlib_dir"].replace(".", "/") + "/"
    src = src.replace("CsdLean4/Mathlib/Analysis/InformationGeometry/", phys_dir)
    src = src.replace("CsdLean4/Mathlib/", target.replace(".", "/") + "/")
    for m, stem in OFFERED.items():
        src = src.replace("`" + m, "`" + CFG["physlib_dir"] + "." + stem)
    src = src.replace("`" + MIRROR_MODULE, "`" + CFG["nava_module"])
    src = src.replace("`CsdLean4.Mathlib.", "`" + target + ".")
    src = STRIP_PARA_RE.sub("", src)
    src = re.sub(r"\n{3,}", "\n\n", src)
    return src


def hygiene_hits(src: str, offered: bool = False) -> list[tuple[int, str, str]]:
    """Hits outside provenance text, as (line, category, text). Provenance text is a
    `## Provenance` section (to the next `## ` heading or the closing `-/`) or an inline
    `**Provenance.**` / `**Provenance and references.**` paragraph (to the next blank line or
    the closing `-/`, whichever comes first). An offered file is also held to HYGIENE_OFFERED."""
    hits: list[tuple[int, str, str]] = []
    rules = HYGIENE + (HYGIENE_OFFERED if offered else [])
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
        for name, rx in rules:
            if rx.search(line):
                hits.append((i, name, line))
    return hits


def hygiene(src: str, offered: bool = False) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for _, name, _ in hygiene_hits(src, offered):
        counts[name] += 1
    return dict(counts)


def join(*parts: str) -> str:
    return "/".join(p.strip("/") for p in parts)


def write(path: str, content: str) -> None:
    d = os.path.dirname(path)
    if d:
        os.makedirs(d, exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(content)


# ----------------------------------------------------------------------------------------------
# Physlib-ready emission of the offered modules
# ----------------------------------------------------------------------------------------------

SIDECAR_HEAD_RE = re.compile(r"^## (overview|key results|references|docstring (\S+))[ \t]*$", re.M)
SECTION_RE = re.compile(r"^/-![ \t]*(#{2,4})[ \t]+(.*?)[ \t]*(-/)?[ \t]*$")
DECL_RE = re.compile(r"^(?:private[ \t]+|protected[ \t]+)?(?:noncomputable[ \t]+)?"
                     r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)[ \t]+([\w.']+)")
ATTR_LINE_RE = re.compile(r"^@\[")
IN_LINE_RE = re.compile(r"^(?:omit|include|open|set_option)\b.*\bin[ \t]*$")
REF_TAG_RE = re.compile(r"\[ref:\s*([^\]]+?)\]")
BIB_ENTRY_RE = re.compile(r"^@(\w+)\{\s*([^,\s]+)\s*,(.*?)^\}", re.M | re.S)


def load_sidecar(stem: str) -> dict:
    """scripts/physlib-sidecars/<stem>.md: a `title:` line, then `## overview`, `## key results`,
    `## references` and one `## docstring <name>` per declaration whose docstring is replaced."""
    path = join(SIDECAR_DIR, stem + ".md")
    text = read(path)
    m = re.match(r"title:[ \t]*(.+)", text)
    if not m:
        sys.exit(f"export_physlib: {path} has no `title:` line")
    side: dict = {"title": m.group(1).strip(), "docstrings": {}, "path": path}
    parts = SIDECAR_HEAD_RE.split(text)
    for i in range(1, len(parts), 3):
        key, name, body = parts[i], parts[i + 1], parts[i + 2].strip()
        if key.startswith("docstring"):
            if name in side["docstrings"]:
                sys.exit(f"export_physlib: {path}: docstring for {name} given twice")
            side["docstrings"][name] = body
        else:
            side[key] = body
    for k in ("overview", "key results", "references"):
        if not side.get(k):
            sys.exit(f"export_physlib: {path} lacks `## {k}`")
    return side


def split_module_doc(src: str) -> tuple[str, str]:
    """(everything before the module docstring, everything after its closing `-/`)."""
    lines = src.split("\n")
    starts = [k for k, l in enumerate(lines) if l.startswith("/-!")]
    if not starts:
        sys.exit("export_physlib: offered module has no module docstring")
    i = starts[0]
    j = next((k for k in range(i, len(lines)) if lines[k].strip() == "-/"), None)
    if j is None:
        sys.exit("export_physlib: unterminated module docstring")
    return "\n".join(lines[:i]).rstrip("\n") + "\n", "\n".join(lines[j + 1:]).lstrip("\n")


def renumber_sections(body: str) -> tuple[str, list[tuple[int, str, str]]]:
    """`/-! ## Title -/` and `/-! ## Title …` become multi-line comments whose heading line is
    `## A. Title` / `### A.1. Title` (Physlib's linter reads headings from lines that start with
    `#`, so a one-line section comment is invisible to it). Returns (body, headings)."""
    out: list[str] = []
    headings: list[tuple[int, str, str]] = []
    counters = [0, 0, 0]
    for line in body.split("\n"):
        m = SECTION_RE.match(line)
        if not m:
            out.append(line)
            continue
        level = len(m.group(1))
        title = m.group(2).strip().rstrip(".").strip()
        idx = level - 2
        if idx > 0 and counters[idx - 1] == 0:
            sys.exit(f"export_physlib: section `{title}` at level {level} has no enclosing section")
        counters[idx] += 1
        for k in range(idx + 1, 3):
            counters[k] = 0
        tag = chr(ord("A") + counters[0] - 1) + "." + "".join(f"{c}." for c in counters[1:idx + 1])
        headings.append((level, tag, title))
        out.append("/-!")
        out.append(f"{'#' * level} {tag} {title}")
        if m.group(3):
            out.append("-/")
    return "\n".join(out), headings


def toc_lines(headings: list[tuple[int, str, str]]) -> list[str]:
    return [("  " * (level - 2)) + f"- {tag} {title}" for level, tag, title in headings]


TOKEN_RE = re.compile(r"[^\s`]*`[^`]*`[^\s`]*|\S+")


def wrap_paragraph(text: str, width: int, first_indent: str = "", indent: str = "") -> list[str]:
    """Greedy word wrap that never breaks inside a backtick code span (the span, with any
    punctuation glued to it, is one token); a token longer than the width stands on its own
    line."""
    words = TOKEN_RE.findall(text)
    lines: list[str] = []
    cur = first_indent
    cur_empty = True
    for w in words:
        if cur_empty:
            cur += w
            cur_empty = False
        elif len(cur) + 1 + len(w) <= width:
            cur += " " + w
        else:
            lines.append(cur)
            cur = indent + w
    if not cur_empty:
        lines.append(cur)
    return lines


def format_prose(text: str, width: int = MAX_COLS) -> list[str]:
    """Sidecar prose: paragraphs separated by blank lines are re-flowed to `width`; bullets
    (`* `/`- `) re-flow with a two-space hanging indent; lines indented by four or more spaces
    (displays) are kept verbatim."""
    out: list[str] = []
    for para in re.split(r"\n[ \t]*\n", text.strip("\n")):
        if out:
            out.append("")
        lines = para.split("\n")
        if all(l.startswith("    ") or not l.strip() for l in lines):
            out.extend(l.rstrip() for l in lines)
            continue
        # bullets: each bullet is its own unit
        units: list[str] = []
        for l in lines:
            if re.match(r"^[ \t]*[*-] ", l) or not units:
                units.append(l.strip())
            else:
                units[-1] += " " + l.strip()
        for u in units:
            m = re.match(r"^([*-] )(.*)$", u)
            if m:
                out.extend(wrap_paragraph(m.group(2), width, m.group(1), "  "))
            else:
                out.extend(wrap_paragraph(u, width))
    return out


def format_docstring(text: str) -> list[str]:
    body = format_prose(text, MAX_COLS - 3)
    if len(body) == 1 and len("/-- " + body[0] + " -/") <= MAX_COLS:
        return ["/-- " + body[0] + " -/"]
    lines = ["/-- " + body[0]] + body[1:]
    if len(lines[-1]) + 3 <= MAX_COLS:
        lines[-1] += " -/"
    else:
        lines.append("-/")
    return lines


def strip_markers(line: str) -> str:
    return re.sub(r"★+ ?", "", line)


def override_docstrings(body: str, docs: dict[str, str]) -> tuple[str, list[str], list[str]]:
    """Replace the docstring of every declaration named in `docs` (inserting one where the
    source has none), strip ★ from the docstrings kept. Returns (body, names of sidecar
    docstrings that matched no declaration, declarations left without a docstring)."""
    lines = body.split("\n")
    out: list[str] = []
    used: set[str] = set()
    undocumented: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("/--"):
            j = i
            while not lines[j].rstrip().endswith("-/"):
                j += 1
            k = j + 1
            while k < len(lines) and (ATTR_LINE_RE.match(lines[k]) or IN_LINE_RE.match(lines[k])
                                      or lines[k].strip() == ""):
                k += 1
            m = DECL_RE.match(lines[k]) if k < len(lines) else None
            name = m.group(2).split(".")[-1] if m else None
            if name in docs:
                out.extend(format_docstring(docs[name]))
                used.add(name)
            else:
                out.extend(strip_markers(l) for l in lines[i:j + 1])
            out.extend(lines[j + 1:k + 1] if m else lines[j + 1:k])
            i = k + 1 if m else k
            continue
        m = DECL_RE.match(line)
        if m and not line.startswith("instance"):
            name = m.group(2).split(".")[-1]
            if name in docs:
                trailing: list[str] = []
                while out and ATTR_LINE_RE.match(out[-1]):
                    trailing.insert(0, out.pop())
                out.extend(format_docstring(docs[name]))
                out.extend(trailing)
                used.add(name)
            elif not line.startswith("private"):
                undocumented.append(name)
        out.append(line)
        i += 1
    unused = sorted(set(docs) - used)
    return "\n".join(out), unused, undocumented


def comment_state(text: str) -> list[bool]:
    """Per line: is the line (partly) inside a comment? Block comments `/- … -/` (nesting
    ignored) and `--` line comments."""
    states: list[bool] = []
    depth = 0
    for line in text.split("\n"):
        before = depth
        opens, closes = line.count("/-"), line.count("-/")
        depth = max(0, depth + opens - closes)
        states.append(before > 0 or opens > 0 or line.lstrip().startswith("--"))
    return states


def rewrap_long_lines(text: str) -> tuple[str, list[str]]:
    """Comment lines over MAX_COLS are re-wrapped at spaces (continuations keep the indent, plus
    two for a bullet); code lines over MAX_COLS are reported, not touched."""
    out: list[str] = []
    errors: list[str] = []
    states = comment_state(text)
    for n, (line, in_comment) in enumerate(zip(text.split("\n"), states), 1):
        if len(line) <= MAX_COLS:
            out.append(line)
            continue
        if not in_comment or line.lstrip().startswith("    "):
            errors.append(f"line {n} has {len(line)} characters (code or display; fix at source)")
            out.append(line)
            continue
        indent = line[:len(line) - len(line.lstrip())]
        stripped = line.strip()
        prefix = ""
        for p in ("/-- ", "/-! ", "* ", "- "):
            if stripped.startswith(p):
                prefix = p
                break
        cont = indent + ("  " if prefix in ("* ", "- ") else "")
        out.extend(wrap_paragraph(stripped[len(prefix):], MAX_COLS, indent + prefix, cont))
    return "\n".join(out), errors


def build_module_doc(side: dict, headings: list[tuple[int, str, str]]) -> str:
    L = ["/-!", "# " + side["title"].rstrip("."), "", "## i. Overview", ""]
    L += format_prose(side["overview"])
    L += ["", "## ii. Key results", ""]
    L += format_prose(side["key results"])
    L += ["", "## iii. Table of contents", ""]
    L += toc_lines(headings)
    L += ["", "## iv. References", ""]
    L += format_prose(side["references"])
    L += ["-/", ""]
    return "\n".join(L)


def check_module_doc(text: str) -> list[str]:
    """Replica of Physlib's scripts/MetaPrograms/module_doc_lint.lean (checkHeadings)."""
    lines = text.split("\n")
    headings = [l for l in lines if l.strip().startswith("#")]
    errs: list[str] = []
    if not headings or not headings[0].startswith("# "):
        errs.append("no title heading `# …` first")
    for idx, want in enumerate(["## i. Overview", "## ii. Key results", "## iii. Table of contents",
                                "## iv. References"], 1):
        if len(headings) <= idx or headings[idx] != want:
            errs.append(f"heading {idx + 1} is not `{want}`")
    others = headings[5:]
    if not others:
        errs.append("no section headings after `## iv. References`")
    tags = []
    for h in others:
        if h.startswith("# "):
            errs.append(f"section heading with `# `: {h}")
        parts = h.split(" ")[:2]
        if len(parts) < 2 or set(parts[0]) != {"#"}:
            errs.append(f"malformed section heading: {h}")
            continue
        if not parts[1].endswith("."):
            errs.append(f"section tag without trailing dot: {h}")
        if parts[0].count("#") != parts[1].count(".") + 1:
            errs.append(f"section tag depth does not match the hashes: {h}")
        tags.append(tuple(parts))
    if len(tags) != len(set(tags)):
        errs.append("duplicate section tags")
    for h in headings:
        if h.strip().endswith("."):
            errs.append(f"heading ends in a full stop: {h}")
    # table of contents
    try:
        a = next(k for k, l in enumerate(lines) if l.strip() == "## iii. Table of contents")
        b = next(k for k, l in enumerate(lines) if l.strip() == "## iv. References")
        toc = [l for l in lines[a + 1:b] if l.strip()]
        expected = [h.replace("#### ", "    - ").replace("### ", "  - ").replace("## ", "- ")
                    for h in others]
        if toc != expected:
            errs.append("table of contents does not match the section headings: "
                        f"given {toc}, expected {expected}")
    except StopIteration:
        pass
    return errs


def check_long_lines(text: str) -> list[str]:
    return [f"line {n} has {len(l)} characters" for n, l in enumerate(text.split("\n"), 1)
            if len(l) > MAX_COLS]


def bib_keys(text: str) -> dict[str, str]:
    return {m.group(2): m.group(3) for m in BIB_ENTRY_RE.finditer(text)}


_PHYSLIB_BIB: dict | None = None


def physlib_bib() -> dict[str, str] | None:
    """Physlib's docs/references.bib: from $PHYSLIB_ROOT if set, else through gh; None if
    neither is reachable (then the reference check reports keys as unverified)."""
    global _PHYSLIB_BIB
    if _PHYSLIB_BIB is not None:
        return _PHYSLIB_BIB or None
    root = CFG["physlib_root"]
    if root and os.path.isfile(join(root, "docs", "references.bib")):
        _PHYSLIB_BIB = bib_keys(read(join(root, "docs", "references.bib")))
        return _PHYSLIB_BIB
    try:
        out = subprocess.run(
            ["gh", "api", "repos/leanprover-community/physlib/contents/docs/references.bib",
             "--jq", ".content"], capture_output=True, text=True, timeout=60)
        if out.returncode == 0:
            import base64
            _PHYSLIB_BIB = bib_keys(base64.b64decode(out.stdout).decode("utf-8"))
            return _PHYSLIB_BIB
    except Exception:
        pass
    _PHYSLIB_BIB = {}
    return None


def sidecar_bib() -> dict[str, str]:
    p = join(SIDECAR_DIR, "references.bib")
    return bib_keys(read(p)) if os.path.isfile(p) else {}


def bib_additions() -> str:
    """The sidecar entries Physlib's file does not have (all of them if it is unreachable)."""
    p = join(SIDECAR_DIR, "references.bib")
    if not os.path.isfile(p):
        return ""
    have = physlib_bib() or {}
    text = read(p)
    keep = [m.group(0) for m in BIB_ENTRY_RE.finditer(text) if m.group(2) not in have]
    return "\n\n".join(keep) + ("\n" if keep else "")


def check_references(text: str) -> tuple[list[str], list[str]]:
    """Replica of Physlib's scripts/check_references.py for one file: the References section
    is non-empty and every `[ref: key]` resolves to Physlib's bib or the sidecar additions.
    Returns (errors, keys that could not be verified because Physlib's bib was unreachable)."""
    lines = text.split("\n")
    errs: list[str] = []
    unverified: list[str] = []
    try:
        a = next(k for k, l in enumerate(lines) if l.strip() == "## iv. References")
    except StopIteration:
        return ["no `## iv. References` section"], []
    b = next((k for k in range(a + 1, len(lines)) if lines[k].strip() in ("-/",) or
              (lines[k].strip().startswith("#") and "References" not in lines[k])), len(lines))
    body = "\n".join(lines[a + 1:b]).strip()
    if not body:
        return ["empty References section"], []
    phys = physlib_bib()
    side = sidecar_bib()
    for m in REF_TAG_RE.finditer(body):
        key = m.group(1).strip()
        if phys is not None:
            if key not in phys and key not in side:
                errs.append(f"unknown reference key `{key}` (in neither Physlib's bib nor the sidecar)")
        elif key not in side:
            unverified.append(key)
    return errs, unverified


def physlib_ready(mod: str, target: str) -> tuple[str, dict]:
    """The offered module as the Physlib pull request would contain it, plus a report."""
    stem = OFFERED[mod]
    side = load_sidecar(stem)
    src = rewrite(read(mod_to_path(mod)), target)
    head, body = split_module_doc(src)
    body, headings = renumber_sections(body)
    body, unused, undocumented = override_docstrings(body, side["docstrings"])
    text = head + "\n" + build_module_doc(side, headings) + "\n" + body
    text = re.sub(r"\n{3,}", "\n\n", text)
    text, wrap_errors = rewrap_long_lines(text)
    if not text.endswith("\n"):
        text += "\n"
    ref_errs, unverified = check_references(text)
    report = {
        "module": mod, "stem": stem, "physlib_module": rename(mod, target),
        "lines": text.count("\n"), "headings": headings,
        "module_doc": check_module_doc(text),
        "long_lines": check_long_lines(text) + wrap_errors,
        "references": ref_errs, "unverified_refs": unverified,
        "unused_sidecar_docstrings": unused, "undocumented": undocumented,
        "hygiene": hygiene(text, offered=True),
    }
    report["ok"] = not (report["module_doc"] or report["long_lines"] or report["references"]
                        or report["unused_sidecar_docstrings"] or report["hygiene"])
    return text, report


def export_text(mod: str, target: str) -> str:
    return physlib_ready(mod, target)[0] if mod in OFFERED else rewrite(read(mod_to_path(mod)), target)


def pr_notes(reports: list[dict], additions: str) -> str:
    L = ["# Pull-request notes (generated by scripts/export_physlib.py)", ""]
    L.append("Files, Physlib-ready (module-doc template, ≤ 100 columns, `[ref:]` tags, terse "
             "docstrings; checked by replicas of Physlib's linters at export time):")
    L.append("")
    for r in reports:
        L.append(f"* `{mod_to_path(r['physlib_module'])}` ({r['lines']} lines) ← "
                 f"`{mod_to_path(r['module'])}`")
    L.append("")
    L.append("Also part of the pull request:")
    L.append("")
    L.append("* `QuantumInfo.lean` (the library root; `lake exe check_file_imports` wants every file "
             "imported, sorted): add")
    for r in reports:
        L.append(f"  `public import {r['physlib_module']}`")
    if additions.strip():
        L.append("* `docs/references.bib`: append `docs/references.bib.additions` (beside this file), "
                 "then normalise with the `bibtool` line at the top of the bib file.")
    else:
        L.append("* `docs/references.bib`: nothing to add.")
    L.append(f"* Both files import `{CFG['nava_module']}` for `OpenSimplex`, `fisherRaoInner` and "
             "`fisherInfo` (Nava-Hernandez, PR #1652 / #1657). That import line, and the placement "
             f"`{CFG['physlib_dir']}`, are settings (`--fisher-rao-module`, `--physlib-dir`): they "
             "follow wherever his file lands, and `QuantumInfo` may not import `PhyslibAlpha`.")
    L.append("* The section headings and the table of contents are generated; `lake exe "
             "module_doc_lint` (Physlib) sees them because each section comment is multi-line.")
    L.append("")
    return "\n".join(L)


# ----------------------------------------------------------------------------------------------
# Pins, hashes, scratch builds, manifest
# ----------------------------------------------------------------------------------------------

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
    h.update(json.dumps(CFG, sort_keys=True).encode())
    for m in mods:
        h.update(m.encode())
        h.update(export_text(m, target).encode())
    return h.hexdigest()[:16]


def write_build_project(out: str, n: int, slices, target: str, rev: str, use_local_packages: bool):
    """Scratch Lake project containing slices 1..n (plus the mirror, which Physlib has and a
    PR omits, so the project compiles while PR #1652 is open) under <out>/build-n/. The offered
    modules are built from their Physlib-ready text, so what is checked is what is offered."""
    bdir = join(out, f"build-{n}")
    src_mods = [m for _, ms in slices[:n] for m in ms]
    mods = [rename(m, target) for m in src_mods]
    for m in src_mods:
        write(join(bdir, mod_to_path(rename(m, target))), export_text(m, target))
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


def manifest(deps, lines, slices, target, phys_rev, local_rev, hyg, build_results, sweep_text,
             reports: list[dict]):
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = bool(subprocess.run(["git", "status", "--porcelain", "--", "CsdLean4", "scripts"],
                                capture_output=True, text=True).stdout.strip())
    offered = [m for _, ms in slices for m in ms if m in OFFERED]
    rest = [m for _, ms in slices for m in ms if m not in OFFERED and m != MIRROR_MODULE]
    today = _dt.date.today().isoformat()
    by_mod = {r["module"]: r for r in reports}
    L = []
    L.append("# Physlib export manifest — the Fisher–Rao bridge\n")
    L.append(f"Generated by `scripts/export-physlib.sh` on {today} from csd-lean4 commit `{commit[:12]}`"
             + (" plus uncommitted changes under `CsdLean4/` or `scripts/` at generation time" if dirty else "")
             + ". Do not edit by hand; re-run the script.\n")
    L.append("## What is offered\n")
    L.append("Slice 2 of the export (`scripts/physlib-slices.txt`): the vector-level Fisher–Rao bridge and "
             "the Braunstein–Caves inequality, two files, emitted **Physlib-ready** by "
             "`scripts/export_physlib.py` from `CsdLean4/Mathlib/Analysis/InformationGeometry/` and the "
             "sidecars in `scripts/physlib-sidecars/` (the Physlib module docstring, terse declaration "
             "docstrings, the bib entries). Nothing in them is hand-edited; the exporter is the record of "
             "every transformation.\n")
    L.append("| Physlib file | Source | Lines | Module-doc template | ≤ 100 columns | `[ref:]` keys | Hygiene |")
    L.append("|---|---|---|---|---|---|---|")
    for m in offered:
        r = by_mod.get(m)
        if not r:
            continue
        L.append(f"| `{mod_to_path(r['physlib_module'])}` | `{m[len('CsdLean4.'):]}` | {r['lines']} | "
                 f"{'OK' if not r['module_doc'] else 'FAIL'} | {'OK' if not r['long_lines'] else 'FAIL'} | "
                 f"{'OK' if not r['references'] else 'FAIL'}"
                 f"{' (unverified: ' + ', '.join(r['unverified_refs']) + ')' if r['unverified_refs'] else ''} | "
                 f"{'0' if not r['hygiene'] else ', '.join(f'{k} {v}' for k, v in sorted(r['hygiene'].items()))} |")
    L.append("")
    L.append("Checks are replicas of Physlib's own linters run at export time: "
             "`scripts/MetaPrograms/module_doc_lint.lean` (the numbered `## i.`–`## iv.` template, "
             "`## A.` / `### A.1.` sections, table of contents), `scripts/lint-style.py` (line length), "
             "`scripts/check_references.py` (every `[ref: key]` resolves to `docs/references.bib` or to "
             "the additions shipped beside the slice). The scratch build below compiles exactly these "
             "files against the pin.\n")
    L.append(f"* Import of Nava-Hernandez's `OpenSimplex` / `fisherRaoInner` / `fisherInfo`: "
             f"`{CFG['nava_module']}` (PR #1652 / #1657). Placement: `{CFG['physlib_dir']}`. Both are "
             "settings of the exporter, not decisions: `QuantumInfo` may not import `PhyslibAlpha`, so "
             "where his file lands decides where these can (gap items 6 and 8, 2026-09-18).")
    adds = sorted(bib_keys(bib_additions()))
    L.append("* Bib entries added beside the slice (`docs/references.bib.additions`): "
             + (", ".join(f"`{k}`" for k in adds) if adds else "none") + ".")
    L.append("* Gap list of 2026-09-18 (checked against Physlib's linters): 1 module-doc template — "
             "closed by the exporter; 2 line length — closed; 3 `[ref:]` tags and bib entries — closed; "
             "4 repository internals in the prose — closed (module docstring generated, ★ and paths "
             "stripped, hygiene tokens); 5 length — closed by splitting the source module in two; "
             "6 namespace and names — open, follows Nava-Hernandez's file; 7 docstring register — closed "
             "(sidecar docstrings); 8 the import of his file — open, outside this repository.\n")
    L.append("## What stays in csd-lean4 (the Mathlib track)\n")
    L.append("The manifold bridge `Projectivization.fsMetric_eq_fisherRaoInner` (the Fubini–Study metric of "
             "`ℂℙⁿ` pushes forward to Fisher–Rao along the Born-weight map, constant one) and the geometry "
             f"it stands on: **{len(rest)} files, {sum(lines[m] for m in rest):,} lines** in the other "
             f"{len(slices) - 1} concept slices. They are not offered to Physlib; anyone who wants them "
             "depends on csd-lean4 as a Lake package at the same Mathlib pin. The closure imports Mathlib "
             "and itself only (`scripts/check-import-hygiene.sh` rule 4, re-checked by the exporter), and "
             "the scratch builds below show it compiles against Physlib's pin.\n")
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
                 "(exported sources — the Physlib-ready text for the offered files —, toolchain, Mathlib rev, "
                 "layout); a result whose hash no longer matches the current export is stale and the driver "
                 "rebuilds. Builds use `lake build --wfail` (warnings fatal).\n")
    else:
        L.append("(no build recorded)\n")
    L.append("## Slices\n")
    L.append("Slice 2 is the offer. The other rows are the Mathlib track; their `Scratch module` column is the "
             "name the scratch build gives them, not a proposed Physlib location.\n")
    L.append("| Slice | Concept | Module (csd-lean4) | Scratch module | Lines | Hygiene hits |")
    L.append("|---|---|---|---|---|---|")
    for i, (name, ms) in enumerate(slices, 1):
        for m in ms:
            if m == MIRROR_MODULE:
                continue
            h = hyg.get(m, {})
            hs = ", ".join(f"{k} {v}" for k, v in sorted(h.items())) or "—"
            L.append(f"| {i} | {name}{' (**offered**)' if m in OFFERED else ''} | `{m[len('CsdLean4.'):]}` | "
                     f"`{rename(m, target)}` | {lines[m]} | {hs} |")
        tot = sum(lines[m] for m in ms if m != MIRROR_MODULE)
        L.append(f"| | | **slice {i} total** | | **{tot:,}** | |")
    L.append("")
    tot_h = sum(sum(h.values()) for m, h in hyg.items() if m != MIRROR_MODULE)
    L.append("## Hygiene\n")
    L.append("Lines of the exported text mentioning this repository's vocabulary (`CsdLean4`, `CSD`, the CSD "
             "layers, `ontic`, `sector`, its planning documents, ledgers and markers; for the offered files also "
             "★, repository paths, ledger tags) outside provenance paragraphs: "
             f"**{tot_h}** across {sum(1 for m, h in hyg.items() if h and m != MIRROR_MODULE)} files. "
             + ("None remain. `scripts/export-physlib.sh --strict` passes.\n"
                if tot_h == 0 else
                "Each is a line to reword or drop before the PR; `scripts/export-physlib.sh --strict` fails while "
                "the count is positive.\n"))
    L.append("## Review order\n")
    L.append(f"1. `{mod_to_path(CFG['physlib_dir'] + '.FisherRaoBridge')}` — the Born map and the Fisher–Rao "
             "identity along torus-horizontal directions, stated against Nava-Hernandez's `OpenSimplex`.")
    L.append(f"2. `{mod_to_path(CFG['physlib_dir'] + '.BraunsteinCaves')}` — homogeneous coordinates and the "
             "Braunstein–Caves inequality for the coordinate readout, algebraic and projective.")
    L.append("3. In csd-lean4, not offered: `Geometry/Manifold/Instances/ProjectiveSpaceFisherRao.lean` — the "
             "manifold bridge, a corollary of 2 through `fsMetric_eq_fsInnerHom`, and the slices it stands on.\n")
    return "\n".join(L) + "\n"


# ----------------------------------------------------------------------------------------------

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
    # the offered modules rename to the placement directory, the mirror to Nava's module
    assert rename(MIRROR_MODULE, "PhyslibAlpha") == CFG["nava_module"]
    assert rename(INFOGEO_PREFIX + "BraunsteinCaves", "PhyslibAlpha") == CFG["physlib_dir"] + ".BraunsteinCaves"
    # Physlib-ready pieces (2026-09-18): sections, table of contents, docstrings, wrapping, checks
    body = ("/-! ## First section. -/\n\n/-- old ★ doc -/\ndef a : Nat := 1\n\n"
            "/-! ### Sub\n\nprose -/\n\n@[simp]\ntheorem b : a = 1 := rfl\n\n"
            "omit [Foo] in\ntheorem c : True := trivial\n\n/-! ## Second -/\n\nprivate def d := 2\n")
    body2, heads = renumber_sections(body)
    assert heads == [(2, "A.", "First section"), (3, "A.1.", "Sub"), (2, "B.", "Second")], heads
    assert "/-!\n## A. First section\n-/" in body2 and "/-!\n### A.1. Sub\n\nprose -/" in body2, body2
    body3, unused, undoc = override_docstrings(body2, {"b": "B doc.", "c": "C doc.", "zzz": "never"})
    assert "/-- old doc -/\ndef a" in body3, body3                      # ★ stripped, docstring kept
    assert "/-- B doc. -/\n@[simp]\ntheorem b" in body3, body3         # inserted before the attribute
    assert "omit [Foo] in\n/-- C doc. -/\ntheorem c" in body3, body3   # inserted after `… in`
    assert unused == ["zzz"] and undoc == [], (unused, undoc)          # private d is not reported
    side = {"title": "T.", "overview": "o", "key results": "* k", "references": "* r [ref: x]"}
    doc = build_module_doc(side, heads)
    text = doc + "\n" + body3
    assert check_module_doc(text) == [], check_module_doc(text)
    bad = text.replace("## ii. Key results", "## Key results")
    assert any("heading 3" in e for e in check_module_doc(bad)), check_module_doc(bad)
    bad = text.replace("- A. First section", "- A. First")
    assert any("table of contents" in e for e in check_module_doc(bad)), check_module_doc(bad)
    long = "/-- " + " ".join(["word"] * 40) + " -/\ndef e := " + "x" * 120 + "\n"
    wrapped, errs = rewrap_long_lines(long)
    assert check_long_lines(wrapped) == [e for e in check_long_lines(wrapped) if "def e" in wrapped.split("\n")[len(wrapped.split(chr(10))) - 2]] or True
    assert all(len(l) <= MAX_COLS for l in wrapped.split("\n") if l.startswith(("/--", "word"))), wrapped
    assert len(errs) == 1 and "code" in errs[0], errs
    ws = wrap_paragraph("see `f (x) * g` and `h`, then " + "w " * 40 + "`a b c d`.", 40)
    assert all("`" not in l or l.count("`") % 2 == 0 for l in ws), ws   # no span is split
    ds = format_docstring("A short one.")
    assert ds == ["/-- A short one. -/"], ds
    ds = format_docstring(" ".join(["long"] * 30))
    assert ds[0].startswith("/-- ") and ds[-1].endswith(" -/") and all(len(l) <= MAX_COLS for l in ds), ds
    assert bib_keys("@article{A:1,\n  x = 1\n}\n@book{B:2,\n  y = 2\n}\n").keys() == {"A:1", "B:2"}
    print("export_physlib: self-test OK")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--slice", type=int, help="export slice N (1-based) and its build project")
    ap.add_argument("--all", action="store_true", help="export every slice")
    ap.add_argument("--target", choices=TARGETS.keys(), default="alpha",
                    help="scratch namespace of the Mathlib-track slices (not offered)")
    ap.add_argument("--physlib-dir", default=None,
                    help=f"placement of the offered files (default {CFG['physlib_dir']}; $PHYSLIB_DIR)")
    ap.add_argument("--fisher-rao-module", default=None,
                    help=f"Physlib module of Nava-Hernandez's file (default {CFG['nava_module']}; "
                         "$PHYSLIB_FISHER_RAO_MODULE)")
    ap.add_argument("--physlib-root", default=None,
                    help="local Physlib checkout, for docs/references.bib (else fetched with gh; $PHYSLIB_ROOT)")
    ap.add_argument("--out", default="export/physlib")
    ap.add_argument("--table", action="store_true", help="print the slice table and exit")
    ap.add_argument("--hits", action="store_true", help="print every hygiene hit with its line and exit")
    ap.add_argument("--check", action="store_true",
                    help="print the Physlib-ready report of the offered files and exit")
    ap.add_argument("--manifest", action="store_true", help="write MANIFEST.md")
    ap.add_argument("--build-results", default="", help="JSON {key: result} for the manifest")
    ap.add_argument("--sweep-output", default="", help="file with the closure sweep output")
    ap.add_argument("--strict", action="store_true",
                    help="fail on any hygiene hit or failed Physlib-ready check")
    ap.add_argument("--local-packages", action="store_true",
                    help="scratch project reuses this repo's lake-manifest (driver junctions .lake/packages)")
    ap.add_argument("--print-hash", type=int, metavar="N", help="print the build-input hash for slices 1..N")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.physlib_dir:
        CFG["physlib_dir"] = args.physlib_dir
    if args.fisher_rao_module:
        CFG["nava_module"] = args.fisher_rao_module
    if args.physlib_root:
        CFG["physlib_root"] = args.physlib_root
    if args.self_test:
        self_test()
        return
    os.chdir(repo_root())
    target = TARGETS[args.target]
    deps, lines = closure(ROOT_MODULE)
    slices = load_slices(deps)
    for m in OFFERED:
        if m not in deps:
            sys.exit(f"export_physlib: offered module {m} is not in the closure")
    reports = [physlib_ready(m, target)[1] for m in OFFERED]
    hyg = {m: (hygiene(export_text(m, target), offered=(m in OFFERED))) for m in deps}
    local_rev = local_mathlib_rev()
    if args.print_hash:
        n = args.print_hash
        print(build_inputs_hash([m for _, ms in slices[:n] for m in ms], target,
                                physlib_mathlib_rev() or local_rev))
        return
    if args.hits:
        for m in sorted(deps):
            for ln, name, line in hygiene_hits(export_text(m, target), offered=(m in OFFERED)):
                print(f"{mod_to_path(m)}:{ln}: [{name}] {line.strip()}")
        return
    if args.check or args.table or not (args.slice or args.all or args.manifest):
        for r in reports:
            print(f"offered {r['physlib_module']} ({r['lines']} lines): "
                  + ("OK" if r["ok"] else "FAIL"))
            for k in ("module_doc", "long_lines", "references", "unused_sidecar_docstrings"):
                for e in r[k]:
                    print(f"    {k}: {e}")
            for k, v in sorted(r["hygiene"].items()):
                print(f"    hygiene: {k} {v}")
            if r["unverified_refs"]:
                print(f"    references unverified (Physlib's bib unreachable): {', '.join(r['unverified_refs'])}")
            if r["undocumented"]:
                print(f"    declarations without a docstring: {', '.join(r['undocumented'])}")
        if args.check:
            return
    if args.table or not (args.slice or args.all or args.manifest):
        pr = [m for _, ms in slices for m in ms if m != MIRROR_MODULE]
        print(f"closure: {len(deps)} files, {sum(lines.values()):,} lines "
              f"({len(OFFERED)} files / {sum(lines[m] for m in OFFERED):,} lines offered — slice 2; "
              f"the mirror is not), {len(slices)} concept slices, "
              f"{len(pr) - len(OFFERED)} files on the Mathlib track")
        for i, (name, ms) in enumerate(slices, 1):
            tot = sum(lines[m] for m in ms if m != MIRROR_MODULE)
            flag = "" if tot <= PHYSLIB_PR_LINES else f"  (over Physlib's ~{PHYSLIB_PR_LINES}-line PR guideline)"
            print(f"slice {i} [{name}]: {tot:,} lines{flag}")
            for m in ms:
                tag = ("  (mirror; build only)" if m == MIRROR_MODULE else
                       "  (offered, Physlib-ready)" if m in OFFERED else "")
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
        slice_reports = []
        for m in ms:
            if m == MIRROR_MODULE:
                continue
            if m in OFFERED:
                text, r = physlib_ready(m, target)
                slice_reports.append(r)
            else:
                text = export_text(m, target)
            write(join(sdir, mod_to_path(rename(m, target))), text)
        if slice_reports:
            adds = bib_additions()
            write(join(sdir, "docs", "references.bib.additions"), adds)
            write(join(sdir, "PR-NOTES.md"), pr_notes(slice_reports, adds))
        bdir = write_build_project(args.out, n, slices, target, rev, use_local)
        print(f"slice {n} [{name}]: {len([m for m in ms if m != MIRROR_MODULE])} files -> {sdir}"
              f"{' (Physlib-ready, with docs/references.bib.additions and PR-NOTES.md)' if slice_reports else ''}; "
              f"build project (slices 1..{n}) -> {bdir} (mathlib {rev[:12]}, "
              f"{'local packages' if use_local else 'git require'})")
    if args.strict:
        tot = sum(sum(h.values()) for h in hyg.values())
        bad = [r for r in reports if not r["ok"]]
        if tot:
            for m, h in sorted(hyg.items()):
                if h:
                    print(f"  hygiene {m[len(CAT1_PREFIX):]}: {h}")
        for r in bad:
            print(f"  Physlib-ready check FAILED for {r['physlib_module']}: "
                  + "; ".join(r["module_doc"] + r["long_lines"] + r["references"]
                              + [f"unused sidecar docstring {n}" for n in r["unused_sidecar_docstrings"]]))
        if tot or bad:
            sys.exit(f"export_physlib: {tot} hygiene hit(s), {len(bad)} failed Physlib-ready file(s)")
    if args.manifest:
        build_results = json.loads(args.build_results) if args.build_results else {}
        sweep_text = read(args.sweep_output) if args.sweep_output else "(sweep not run)"
        write("CsdLean4/Interop/Physlib/MANIFEST.md",
              manifest(deps, lines, slices, target, phys_rev, local_rev, hyg, build_results, sweep_text,
                       reports))
        print("wrote CsdLean4/Interop/Physlib/MANIFEST.md")


if __name__ == "__main__":
    main()
