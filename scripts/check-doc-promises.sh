#!/usr/bin/env bash
# check-doc-promises.sh
#
# Catches a module docstring that ADVERTISES a declaration the file does not have.
#
# Motivating case (2026-08-19): `Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`
# listed under "Main definitions"
#
#     - `defaultPoint`, `defaultFubiniStudyMeasure` — canonical choice
#
# and neither existed. Not a stale name, not a rename: they had never been written. The
# header promised an API the code did not have, in a Category 1 file staged for
# upstreaming, and nothing caught it because the file compiled perfectly. A build only
# checks what IS written; this checks what was PROMISED.
#
# This is the mirror image of check-glossary.sh. That one guards prose against the Lean
# tree moving underneath it. This one guards the Lean tree's own prose against never
# having been true in the first place.
#
# WHAT IT REPORTS
#   A docstring bullet naming a declaration (`* \`foo_bar\` — …`) where that name appears
#   NOWHERE in the corpus outside comments. Confined to the leading backticked token of a
#   bullet, in the module docstring only, because that is the position that reads as a
#   promise rather than a mention.
#
# WHAT IT DELIBERATELY DOES NOT DO
#   It does not check that the promised declaration lives in the file that promises it
#   (cross-module "see also" bullets are legitimate), and it does not read prose. A
#   bullet that describes a step informally rather than naming a declaration is not a
#   defect, which is what the exceptions list below is for. Each exception carries its
#   reason: an unexplained entry there is how a guard rots into decoration.
#
# Usage:  bash scripts/check-doc-promises.sh
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python - <<'PY'
import os, re, subprocess, sys

# ---------------------------------------------------------------------------
# EXCEPTIONS — informal names in explanatory bullets, not promised declarations.
# Each needs a reason. Format: "file::token".
# ---------------------------------------------------------------------------
EXCEPT = {
    # Step-by-step sketches of an algorithm's action on a state. `H_anc` and `cSWAP`
    # name the mathematical steps ("apply Hadamard to the ancilla"), not Lean constants;
    # the file's actual declarations are named differently and do exist.
    "CsdLean4/Empirical/QM/Algorithms/HadamardTest.lean::H_anc",
    "CsdLean4/Empirical/QM/Algorithms/SwapTest.lean::H_anc",
    "CsdLean4/Empirical/QM/Algorithms/SwapTest.lean::cSWAP",
    # Bullets naming sibling MODULES, not declarations — the backticks hold a filename.
    "CsdLean4/RecordLayer/CircleFibre.lean::KSigmaRecord.lean",
    "CsdLean4/RecordLayer/CircleFibre.lean::FibredSigma.lean",
    # `modConstMul` names the OPERATION (c·a mod N by repeated modular addition) that the
    # whole theorem family is named after — modConstMul_correct, _preserves_operand,
    # _in_range, _toffoli all exist. The circuit itself is `constMulCirc`. A naming
    # inconsistency worth knowing about, but the bullet is describing the operation, not
    # promising a constant.
    "CsdLean4/Mathlib/QuantumInfo/Reversible/ModularConst.lean::modConstMul",
}

files = []
for dp, dn, fn in os.walk("CsdLean4"):
    for f in fn:
        if f.endswith(".lean"):
            files.append(os.path.join(dp, f).replace("\\", "/"))

TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?]*")

def strip_comments(src):
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    src = re.sub(r"--[^\n]*", " ", src)
    return src

code_tokens, srcs = set(), {}
for p in files:
    s = open(p, encoding="utf-8", errors="replace").read()
    srcs[p] = s
    for t in TOKEN.findall(strip_comments(s)):
        code_tokens.add(t)
        for part in t.split("."):
            code_tokens.add(part)

BULLET = re.compile(r"^\s*[-*]\s+`([^`]+)`")
LOOKS_DECL = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")

findings = []
for p in files:
    m = re.search(r"/-!(.*?)-/", srcs[p], re.S)
    if not m:
        continue
    for line in m.group(1).split("\n"):
        b = BULLET.match(line)
        if not b:
            continue
        head = re.split(r"[\s,/]+", b.group(1).strip())[0].strip()
        if not LOOKS_DECL.match(head) or len(head) < 4:
            continue
        # Require a declaration-shaped name: snake_case, dotted, or camelCase. A bare
        # single word in a bullet is usually a variable or an English word.
        if not ("_" in head or "." in head or re.search(r"[a-z][A-Z]", head)):
            continue
        if head in code_tokens or head.split(".")[-1] in code_tokens:
            continue
        if (p + "::" + head) in EXCEPT:
            continue
        findings.append((p, head, " ".join(line.split())[:96]))

# ---------------------------------------------------------------------------
# (B) The same defect in the VALIDATION LEDGER: a claim naming a constant that does
# not resolve. `check-validation-ledger.sh` verifies that a row's module and constant
# are LINKED, not that the constant exists under that exact name — so CL-006 recorded
# `CSD.LF2.weights_sum_eq_one` for years while the declaration sits inside
# `namespace POVM` and is really `CSD.LF2.POVM.weights_sum_eq_one`. The ledger checker
# reported OK. Same class as the docstring case above: a name asserted in prose or data
# that no declaration answers to.
# ---------------------------------------------------------------------------
import csv
pinned = set()
for dp, dn, fn in os.walk("CsdLean4/Tests"):
    for f in fn:
        if f.endswith(".lean"):
            for mm in re.finditer(r"#print axioms\s+([A-Za-z_][A-Za-z0-9_.'!?]*)",
                                  open(os.path.join(dp, f), encoding="utf-8",
                                       errors="replace").read()):
                pinned.add(mm.group(1))

ledger = "specs/validation-claims.tsv"
if os.path.exists(ledger):
    with open(ledger, encoding="utf-8") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            const = (row.get("constant") or "").strip()
            mod = "CsdLean4/" + (row.get("module") or "").strip()
            if not const or not os.path.exists(mod):
                continue
            # Regex cannot decide this: a declaration may be written at any level of
            # qualification depending on open namespaces, so strict matching gives false
            # positives and suffix matching gives false negatives — suffix matching would
            # have accepted the very CL-006 error that motivated this check, because the
            # final segment resolved while the namespace was wrong.
            #
            # The audit pin settles it instead. `#print axioms <name>` is elaborated by
            # Lean, so a pin naming a constant that does not resolve fails the build. A
            # ledger constant that appears verbatim in a pin is therefore a constant Lean
            # itself has confirmed. Requiring the pin does double duty: it is promotion
            # criterion 2 (the axiom footprint is evidenced) AND the name check.
            # A pin may be written partially qualified, because the audit parts `open`
            # the layer namespaces — `#print axioms OperationalPackage.effect_gleason…`
            # elaborates to the full name. So a pin counts when it is a dot-aligned
            # SUFFIX of the recorded constant: opens only ever shorten a name, never
            # lengthen it. That asymmetry is what still catches CL-006, where the pin
            # (`CSD.LF2.POVM.weights_sum_eq_one`) was LONGER than the ledger's recorded
            # `CSD.LF2.weights_sum_eq_one` — a wrong namespace, not an open.
            if any(const == p or const.endswith("." + p) for p in pinned):
                continue
            findings.append((ledger, const,
                             "ledger row %s: headline constant is not axiom-pinned under this "
                             "exact name — so neither its axiom footprint nor its spelling is "
                             "checked by anything" % row.get("id")))

# ---------------------------------------------------------------------------
# Module PATHS named in prose must exist too (added 2026-09-04).
#
# WHY. The SigmaLayer -> RecordLayer split left 303 references to
# `SigmaLayer/X.lean` in 87 module headers, pointing at files that had moved. A
# reader following a header's "References" section landed nowhere, and nothing
# noticed for months: this guard checked that named DECLARATIONS exist and said
# nothing about named FILES. Paths under `Mathlib/` are exempt — they are usually
# references to upstream Mathlib, which is not in this tree.
# Paths that a document names DELIBERATELY although they do not exist: the subject of a
# rename sentence, a file recorded as never created, a proposed future companion. Fixing
# these would falsify the record. Each carries its reason.
PATH_EXCEPT = {
    # "File rename: X -> Y" — the old name IS the subject.
    ("specs/pre-LF4-plan.md", "LF3/BranchSeparation.lean"),
    ("specs/pre-LF4-plan.md", "LF3/Projectors/BranchWeight.lean"),
    # "(moved from Empirical/Bell.lean)" — same.
    ("specs/empirical-csd-bridge-plan.md", "Empirical/Bell.lean"),
    # A proposed companion that was never built.
    ("specs/empirical-csd-bridge-plan.md", "Empirical/Bohmian/Bell.lean"),
    # "No Tests/AxiomAudit/C1.lean was created" — an assertion that it does NOT exist.
    ("specs/c1-closure-report.md", "Tests/AxiomAudit/C1.lean"),
    ("specs/c1-correction-plan.md", "Tests/AxiomAudit/C1.lean"),
    # A scoping note names its own deliverable before it is built. REMOVE the entry when the
    # brick lands — a stale exception silently weakens the guard for that pair. (The two
    # `ozawa-scoping.md` entries were removed on 2026-09-04 when that brick landed.)
    ("specs/local-friendliness-scoping.md", "Empirical/CSD/LocalFriendliness.lean"),
}

corpus_tops = {d for d in os.listdir("CsdLean4") if os.path.isdir(os.path.join("CsdLean4", d))} - {"Mathlib"}
path_re = re.compile(r"(?:CsdLean4/)?(?:[A-Za-z][A-Za-z0-9]*/)+[A-Z][A-Za-z0-9]*\.lean")
# Markdown carries the same references and rots the same way — the SigmaLayer -> RecordLayer
# split left 207 broken paths in 22 documents, including the A2 row that README sends readers
# to for the axiom-level audit.
doc_files = [p for p in subprocess.run(
    ["git", "ls-files", "*.md", "specs/*.md", "docs/*.md", "specs/**/*.md", "docs/**/*.md"],
    capture_output=True, text=True).stdout.split() if p]

path_findings = []
for f in files + sorted(set(doc_files)):
    with open(f, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    for m in sorted(set(path_re.findall(text))):
        rel = m[len("CsdLean4/"):] if m.startswith("CsdLean4/") else m
        if rel.split("/")[0] not in corpus_tops:
            continue
        if (f, rel) in PATH_EXCEPT:
            continue
        if not os.path.exists(os.path.join("CsdLean4", rel)):
            path_findings.append((f, m))

# ---------------------------------------------------------------------------
# Spec/doc references from Lean docstrings must resolve too (added 2026-09-04).
#
# WHY. The module-path check above covers `CsdLean4/...` targets. Lean headers also cite
# `specs/*.md` and `docs/*.md` 691 times, and those rot the same way: the reversible
# substrate carried four references to `specs/ecdlp-resource-plan.md` for weeks after that
# plan moved to the separate Ecdsafail repository.
#
# CROSS-REPO references are legitimate and are declared by PREFIX, not one by one: a path
# under a prefix below is owned by another repository, so its absence here is expected.
CROSS_REPO = {
    "specs/ecdsa/": "the Ecdsafail repository (one-way dependency; see CLAUDE.md)",
}
docref_re = re.compile(r"(?:`|\()((?:specs|docs)/[A-Za-z0-9._/-]+\.md)")
for f in files:
    with open(f, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    for m in sorted(set(docref_re.findall(text))):
        if any(m.startswith(pre) for pre in CROSS_REPO):
            continue
        if not os.path.exists(m):
            path_findings.append((f, m))

if path_findings:
    print("check-doc-promises: FAIL — %d module path(s) named in prose do not exist:"
          % len(path_findings))
    print()
    for f, m in path_findings:
        print("  %s" % f)
        print("      names `%s`, which is not a file in this tree" % m)
    print()
    print("  A moved module leaves every header that cited it pointing at nothing.")
    print("  Fix the path, or drop the reference.")
    sys.exit(1)

if findings:
    print("check-doc-promises: FAIL — %d docstring promise(s) with no declaration:" % len(findings))
    print()
    for p, h, l in findings:
        print("  %s" % p)
        print("      promises `%s`, which is declared nowhere in the corpus" % h)
        print("      bullet: %s" % l)
        print()
    print("  Fix by writing the declaration, correcting the name, or deleting the bullet.")
    print("  If the bullet names a step or a file rather than a declaration, add it to")
    print("  EXCEPT in this script WITH ITS REASON.")
    sys.exit(1)

print("check-doc-promises: OK — every declaration and module path named in a docstring exists.")
print("  (%d files scanned, %d exception(s) declared.)" % (len(files), len(EXCEPT)))
PY
