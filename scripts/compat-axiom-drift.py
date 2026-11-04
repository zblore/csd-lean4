#!/usr/bin/env python3
"""Classify a forward-compat `lake build CsdLeanTests` log: axiom-pin drift or real failure.

Used only by the Compat workflow's forward job (`.github/workflows/compat.yml`). The axiom-audit
pins (`CsdLean4/Tests/AxiomAudit/*.lean`) record the EXACT axiom set of each constant at the pinned
Mathlib. Against a newer Mathlib a constant can pick up axioms through upstream lemmas (2026-11-04:
seven SigmaLayer constants became classical on master), and no single pin string matches both
versions. The author's decision (2026-11-04): report such drift as warnings, fail only on real build
errors. The pinned CI (`ci.yml`) keeps the exact pins.

Usage: compat-axiom-drift.py BUILD_LOG
Exit 0 when the log has no errors, or when every error is a `#guard_msgs` mismatch in an
AxiomAudit file whose diff lines are all `depends on axioms` lines; one `::warning::` annotation is
printed per drifted constant. Exit 1 otherwise, printing the offending lines.
"""

import re
import sys

GUARD = re.compile(
    r"^error: (CsdLean4/Tests/AxiomAudit/[^:]+):(\d+):\d+: .*Docstring on `#guard_msgs` does not "
    r"match generated message:\s*$")
BENIGN = re.compile(r"^error: (build failed|Lean exited with code \d+)\s*$")
DIFF = re.compile(r"^([-+]) info: '([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)\s*$")


def strip_prefix(line: str) -> str:
    # `gh run view --log` lines carry "job<TAB>step<TAB>timestamp " prefixes; raw lake output does not.
    if "\t" in line:
        line = line.split("\t")[-1]
        line = re.sub(r"^\d{4}-\d\d-\d\dT[0-9:.]+Z ", "", line)
    return line.rstrip("\n")


def main(path: str) -> int:
    lines = [strip_prefix(l) for l in open(path, encoding="utf-8", errors="replace")]
    bad = []
    drift = {}
    in_guard = False
    for line in lines:
        if line.startswith("error: "):
            m = GUARD.match(line)
            if m:
                in_guard = True
                continue
            in_guard = False
            if BENIGN.match(line):
                continue
            bad.append(line)
            continue
        if not in_guard:
            continue
        if line[:2] in ("- ", "+ "):
            d = DIFF.match(line)
            if not d:
                bad.append(line)
                continue
            drift.setdefault(d.group(2), {})[d.group(1)] = d.group(3) or ""
        elif line.strip():
            # the diff block ends at the first non-blank line that is not a diff line
            in_guard = False
    if bad:
        print("Real forward-compat failures (not axiom-pin drift):")
        for b in bad:
            print("  " + b)
        return 1
    for name, sides in sorted(drift.items()):
        print(f"::warning::axiom-pin drift on the forward Mathlib: {name}: "
              f"pinned [{sides.get('-', '?')}] -> forward [{sides.get('+', '?')}]")
    print(f"{len(drift)} axiom-pin drift(s), no other errors.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
