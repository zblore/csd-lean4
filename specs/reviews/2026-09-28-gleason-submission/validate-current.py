"""Run saved audits against this checkout, after building both Lake targets.

Run: lake env python -u -B specs/reviews/2026-09-28-gleason-submission/validate-current.py
Historical run.py/probe.py instead reproduce the original pinned snapshot.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

repo = Path.cwd()
evidence = repo / "specs/reviews/2026-09-28-gleason-submission"
manifest = json.loads((evidence / "snapshot.json").read_text(encoding="utf-8"))
output = evidence / "integration"
output.mkdir(exist_ok=True)
env = os.environ.copy()
env["LEAN_NUM_THREADS"] = "2"
results = []
inputs = [evidence / name for name in
          ["EndpointAudit.lean", "RealAudit.lean", "DependencyAudit.lean", "BoundaryAudit.lean"]]
inputs.append(repo / "scripts/gleason-free.lean")
for path in inputs:
    relative = path.relative_to(repo).as_posix()
    cmd = ["lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
           "-DwarningAsError=true", relative]
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=repo, env=env, capture_output=True, encoding="utf-8")
    log = result.stdout + result.stderr
    (output / (path.name + ".log")).write_text(log, encoding="utf-8", newline="\n")
    results.append({"file": relative, "exit_code": result.returncode,
                    "seconds": round(time.monotonic() - start, 2),
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    print(relative, "PASS" if result.returncode == 0 else "FAIL", flush=True)
    if log:
        print(log, flush=True)
    if result.returncode:
        sys.exit(result.returncode)
paths = [v["path"] for v in manifest["modules"].values()]
paths += ["scripts/gleason-free.lean", "scripts/check-gleason-free.sh",
          "lean-toolchain", "lakefile.toml", "lake-manifest.json"]
record = {"date": "2026-09-29", "base_commit": subprocess.check_output(
    ["git", "rev-parse", "HEAD"], encoding="utf-8").strip(),
    "note": "Source hashes identify the checked working tree, including uncommitted corrections.",
    "lean": subprocess.check_output(["lean", "--version"], encoding="utf-8").strip(),
    "checks": results,
    "source_sha256": {path: hashlib.sha256((repo/path).read_bytes()).hexdigest() for path in paths}}
(output / "validation.json").write_text(json.dumps(record, indent=2), encoding="utf-8")
print("All current-tree audits and the production dependency guard passed.", flush=True)
