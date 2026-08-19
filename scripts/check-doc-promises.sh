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
import os, re, sys

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

print("check-doc-promises: OK — every declaration named in a module docstring exists.")
print("  (%d files scanned, %d exception(s) declared.)" % (len(files), len(EXCEPT)))
PY
