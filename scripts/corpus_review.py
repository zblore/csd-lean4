#!/usr/bin/env python3
"""Track human review evidence; never infer mathematical correctness from a scan."""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
from collections import Counter
from datetime import date

ROOT = Path(__file__).resolve().parents[1]
LEDGER = "specs/corpus-review.tsv"
FIELDS = [
    "path", "stratum", "lines", "blob", "context_hash", "status",
    "review_scope", "reviewed_blob", "reviewed_context", "review_commit",
    "reviewer", "reviewed_on", "code", "comments", "validation_status",
    "validation", "evidence", "issues", "prior_evidence",
]
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)\s*$")


def git(*args: str, cwd: Path | None = None) -> str:
    return subprocess.run(
        ["git", *args], cwd=cwd or ROOT, check=True, capture_output=True,
        encoding="utf-8",
    ).stdout.strip()


def lean_code(src: str) -> str:
    """Mask nested comments and quoted strings, retaining line boundaries."""
    out = []
    i, depth, quoted = 0, 0, False
    while i < len(src):
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif quoted:
            if c == "\\" and i + 1 < len(src):
                out.append("  ")
                i += 2
            else:
                quoted = c != '"'
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif src.startswith("--", i):
            end = src.find("\n", i)
            if end < 0:
                end = len(src)
            out.append(" " * (end - i))
            i = end
        elif c == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def stratum(path: str) -> str:
    if "/Tests/" in path or path in {"CsdLean4.lean", "CsdLean4/Basic.lean", "CsdLean4/Headlines.lean"}:
        return "tests-facades"
    if "/Mathlib/" in path:
        return "library"
    if "/Empirical/" in path:
        return "empirical"
    if any("/" + part + "/" in path for part in ("LF1", "LF2", "LF3", "Framework")):
        return "foundations"
    return "record-dynamics-other"


def digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def inventory() -> dict[str, dict[str, str]]:
    paths = sorted(p for p in git("ls-files", "-z").split("\0") if p.endswith(".lean"))
    if any("\n" in p or '"' in p for p in paths):
        raise ValueError("Unsupported newline/quote in tracked Lean path")
    # Git applies the path's clean filters, avoiding CRLF-only invalidation.
    result = subprocess.run(
        ["git", "hash-object", "--stdin-paths"], cwd=ROOT,
        input="\n".join(paths) + "\n", capture_output=True, encoding="utf-8", check=True,
    )
    hashes = dict(zip(paths, result.stdout.splitlines(), strict=True))
    sources = {p: (ROOT / p).read_text(encoding="utf-8") for p in paths}
    modules = {p[:-5].replace("/", "."): p for p in paths}
    deps: dict[str, set[str]] = {}
    for p, src in sources.items():
        deps[p] = set()
        for line in lean_code(src).splitlines():
            match = IMPORT.fullmatch(line)
            if not match:
                if re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\b", line):
                    raise ValueError(f"Unsupported import syntax in {p}: {line}")
                continue
            mod = match[1]
            if mod in modules:
                deps[p].add(modules[mod])
            elif mod == "CsdLean4" or mod.startswith("CsdLean4."):
                raise ValueError(f"Untracked/missing local import {mod} in {p}")
    env = {
        p: (ROOT / p).read_text(encoding="utf-8")
        for p in ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json")
        if (ROOT / p).exists()
    }
    mathlib = ROOT / ".lake/packages/mathlib"
    if mathlib.exists():
        env["mathlib_head"] = git("rev-parse", "HEAD", cwd=mathlib)
        if git("status", "--porcelain", "--untracked-files=no", cwd=mathlib):
            raise ValueError("Mathlib has tracked local edits; dependency context is not reproducible")
    else:
        env["mathlib_head"] = "not-installed"
    rows = {}
    for p in paths:
        seen, todo = set(), [p]
        while todo:
            q = todo.pop()
            if q not in seen:
                seen.add(q)
                todo.extend(deps[q])
        rows[p] = dict(
            path=p, stratum=stratum(p), lines=str(len(sources[p].splitlines())),
            blob=hashes[p], context_hash=digest([env, sorted((q, hashes[q]) for q in seen)]),
        )
    return rows


def read_ledger() -> dict[str, dict[str, str]]:
    path = ROOT / LEDGER
    if not path.exists():
        return {}
    with path.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != FIELDS:
            raise ValueError("Unexpected ledger schema")
        rows = list(reader)
    if len({r["path"] for r in rows}) != len(rows):
        raise ValueError("Duplicate ledger paths")
    return {r["path"]: r for r in rows}


def effective(row: dict[str, str]) -> str:
    if not row["reviewed_blob"]:
        return "historical" if row["prior_evidence"] else "unreviewed"
    if not row["blob"]:
        return "retired"
    if row["blob"] != row["reviewed_blob"]:
        return "stale-source"
    if row["context_hash"] != row["reviewed_context"]:
        return "stale-dependency"
    if row["review_scope"] == "partial":
        return "partial"
    return "reviewed" if row["validation_status"] == "passed" else "source-reviewed"


def reconcile(old: dict[str, dict[str, str]], live: dict[str, dict[str, str]]) -> dict[str, dict[str, str]]:
    rows = {}
    for path in sorted(old.keys() | live.keys()):
        row = {key: "" for key in FIELDS}
        row.update(old.get(path, {}))
        if path in live:
            row.update(live[path])
            row["status"] = effective(row)
        else:
            row.update(blob="", context_hash="", status="retired")
        rows[path] = row
    return rows


def serialize(rows: dict[str, dict[str, str]]) -> str:
    stream = io.StringIO(newline="")
    # Quote empty final fields so valid TSV records do not end in whitespace.
    writer = csv.DictWriter(stream, FIELDS, delimiter="\t", lineterminator="\n",
                            quoting=csv.QUOTE_ALL)
    writer.writeheader()
    writer.writerows(rows.values())
    return stream.getvalue()


def save(rows: dict[str, dict[str, str]]) -> None:
    (ROOT / LEDGER).write_text(serialize(rows), encoding="utf-8", newline="")


def report(rows: dict[str, dict[str, str]]) -> None:
    live = [r for r in rows.values() if r["status"] != "retired"]
    counts = Counter(r["status"] for r in live)
    done = counts["reviewed"]
    print(json.dumps({
        "commit": git("rev-parse", "HEAD"), "tracked_lean_files": len(live),
        "status_counts": dict(sorted(counts.items())),
        "current_full_review_percent": round(100 * done / len(live), 2) if live else 0,
        "note": "Review completion is separate from repair/issue closure; inspect linked evidence.",
    }, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("sync", "status", "check"):
        sub.add_parser(name)
    rec = sub.add_parser("record", help="Record an actual human review, never an automated scan")
    rec.add_argument("paths", nargs="+")
    rec.add_argument("--scope", choices=("full", "partial"), required=True)
    rec.add_argument("--reviewer", required=True)
    rec.add_argument("--code", choices=("pass", "findings"), required=True)
    rec.add_argument("--comments", choices=("pass", "findings"), required=True)
    rec.add_argument("--evidence", required=True, help="Existing report path, relative to repository")
    rec.add_argument("--validation-status", choices=("passed", "pending"), required=True)
    rec.add_argument("--validation", required=True)
    rec.add_argument("--issues", default="")
    args = parser.parse_args()
    old = read_ledger()
    live = inventory()
    rows = reconcile(old, live)
    if args.command == "record":
        if not (ROOT / args.evidence).is_file():
            parser.error("Evidence report must exist before recording a review")
        for path in args.paths:
            if path not in live:
                parser.error(f"Not a current tracked Lean file: {path}")
        for path in args.paths:
            row = rows[path]
            # Earlier reports remain reachable after a subsequent review.
            if row["evidence"] and row["evidence"] != args.evidence:
                row["prior_evidence"] = ";".join(filter(None, [row["prior_evidence"], row["evidence"]]))
            row.update(
                review_scope=args.scope, reviewed_blob=row["blob"],
                reviewed_context=row["context_hash"], review_commit=git("rev-parse", "HEAD"),
                reviewer=args.reviewer, reviewed_on=date.today().isoformat(),
                code=args.code, comments=args.comments, evidence=args.evidence,
                validation_status=args.validation_status, validation=args.validation, issues=args.issues,
            )
            row["status"] = effective(row)
        save(rows)
    elif args.command == "sync":
        save(rows)
    elif args.command == "check":
        if serialize(rows) != serialize(old):
            print("Inventory/status drift: run python -B scripts/corpus_review.py sync")
            raise SystemExit(1)
    report(rows)


if __name__ == "__main__":
    main()
