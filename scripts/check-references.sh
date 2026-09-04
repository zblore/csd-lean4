#!/usr/bin/env bash
# check-references.sh
#
# `REFERENCES.json` (CONVENTIONS.md §8.2) is the machine-readable provenance file: one entry
# per source, cited from prose by key. This guard keeps it honest in the two ways it can rot.
#
#   (1) Every `cited_by` path must exist. A citation record pointing at a file that has moved
#       or gone is worse than no record: it reads as provenance and resolves to nothing. This
#       is the same defect the module-path check in `check-doc-promises.sh` was added for
#       (2026-09-04, 510 broken paths across the Lean headers and the documents).
#   (2) Every `[Key]` citation used in prose must be a key in the file, and every key must be
#       cited somewhere. An unresolvable key is a dangling citation; an uncited key is a
#       reference nobody reads, which is how the seed rots into decoration.
#
# The file is SEEDED, not complete (its own `$comment` says so, and CONVENTIONS §8.2 keeps the
# one-entry-per-source obligation open in the BACKLOG). This guard therefore checks the
# entries that exist; it does NOT check coverage, and passing it says nothing about how much
# of the corpus is cited.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

python - <<'PY'
import json, os, re, subprocess, sys

with open("REFERENCES.json", encoding="utf-8") as fh:
    data = json.load(fh)

refs = data.get("references", [])
keys = [r.get("key") for r in refs]
findings = []

if len(keys) != len(set(keys)):
    dup = sorted({k for k in keys if keys.count(k) > 1})
    findings.append("duplicate key(s): %s" % ", ".join(dup))

for r in refs:
    key = r.get("key", "<no key>")
    # An entry is auditable if a reader can find the source. Authors + year + a venue string
    # ("Phys. Rev. Lett. 67, 661") does that; the title is a convenience. The 2026-09-04 harvest
    # took its data from the citing modules' `## Source` blocks, which record venue/volume/page
    # but often no title — and supplying titles from memory is exactly the fabrication this file
    # exists to prevent. So: `title` OR `venue`, plus a year.
    if not (r.get("title") or r.get("venue")) or not r.get("year"):
        findings.append("%s: needs a year and at least one of title / venue" % key)
    for p in r.get("cited_by", []):
        if not os.path.exists(p):
            findings.append("%s: cited_by names `%s`, which is not a file in this tree" % (key, p))
    for d in r.get("relevant_declarations", []):
        if not d.get("name"):
            findings.append("%s: a relevant_declarations entry has no name" % key)

# Citations in prose: `[Key]` or `[Key, ...]`, over tracked prose and Lean docstrings.
files = [p for p in subprocess.run(
    ["git", "ls-files", "*.md", "specs/*.md", "docs/*.md", "CsdLean4/**/*.lean", "CsdLean4/*.lean"],
    capture_output=True, text=True).stdout.split() if p]
cite = re.compile(r"\[([A-Z][A-Za-z]+\d{4}[A-Za-z]*)(?:,[^\]]*)?\]")
used = {}
for f in sorted(set(files)):
    with open(f, encoding="utf-8", errors="replace") as fh:
        for m in cite.findall(fh.read()):
            used.setdefault(m, set()).add(f)

for k, where in sorted(used.items()):
    if k not in keys:
        findings.append("`[%s]` cited in %s but is not a key in REFERENCES.json"
                        % (k, sorted(where)[0]))

uncited = [k for k in keys if k not in used and not any(
    os.path.exists(p) for p in next(r for r in refs if r.get("key") == k).get("cited_by", []))]
for k in uncited:
    findings.append("%s: no `[%s]` citation in prose and no existing cited_by file" % (k, k))

if findings:
    print("check-references: FAIL — %d finding(s):" % len(findings))
    for f in findings:
        print("    %s" % f)
    sys.exit(1)

print("check-references: OK (%d entr%s, every cited_by resolves, every `[Key]` citation is known)"
      % (len(refs), "y" if len(refs) == 1 else "ies"))

# COVERAGE, reported and NOT gated. The §8.2 obligation is one entry per source; the file is
# a seed. This measures the gap instead of leaving it vague: distinct `Author YYYY`-shaped
# citations in Lean docstrings, against the keys that exist. It is deliberately not a ratchet
# — the pattern also catches dated prose ("Corrected 2026"), so the number is an upper bound
# on real sources, not a defect count.
noise = re.compile(r"^(Corrected|DISCHARGED|The|Landed|Added|Fixed|Superseded|Delivered|Scoped|Done|Closed|Updated|Reopened|Withdrawn|Verified|Adopted|Extracted|Relocated|Corrections?|Correction)$")
authoryear = re.compile(r"([A-Z][a-zA-Z]+(?:[–-][A-Z][a-zA-Z]+)*)\s+((?:19|20)\d\d)")
lean = [p for p in subprocess.run(["git", "ls-files", "CsdLean4/**/*.lean"],
                                  capture_output=True, text=True).stdout.split() if p]
cited = set()
for f in lean:
    with open(f, encoding="utf-8", errors="replace") as fh:
        for m in authoryear.finditer(fh.read()):
            if not noise.match(m.group(1)):
                cited.add("%s %s" % (m.group(1), m.group(2)))
print("  coverage: %d entr%s against ~%d distinct `Author YYYY` citations in Lean docstrings"
      % (len(refs), "y" if len(refs) == 1 else "ies", len(cited)))
print("            (§8.2 obligation — one entry per source plus line-precise citations — is OPEN;")
print("             see specs/BACKLOG.md. This line measures the gap, it does not gate it.)")
PY
