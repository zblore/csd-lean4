from pathlib import Path
import os, json, subprocess, sys, hashlib
repo=Path.cwd()
evidence=repo/"specs/reviews/2026-09-28-gleason-submission"
audit=repo/".lake/gleason-submission-5f77294d"
m=json.loads((audit/"environment.json").read_text())
env=os.environ.copy(); env["LEAN_PATH"]=m["lean_path"]; env["LEAN_NUM_THREADS"]="2"
results=[]
result_path=evidence/"probe-results.json"
previous=json.loads(result_path.read_text()) if result_path.exists() else []
for name in sys.argv[1:] or ["EndpointAudit.lean", "RealAudit.lean", "DependencyAudit.lean", "BoundaryAudit.lean"]:
    data=(evidence/name).read_bytes(); (audit/name).write_bytes(data)
    cmd=[m["lean"],"-DautoImplicit=false","-DrelaxedAutoImplicit=false","-DwarningAsError=true",name]
    p=subprocess.run(cmd,cwd=audit,env=env,capture_output=True,encoding="utf-8")
    (evidence/(name+".log")).write_text(p.stdout+p.stderr,encoding="utf-8")
    print(name, "EXIT", p.returncode, flush=True)
    print(p.stdout+p.stderr,flush=True)
    results.append({"file":name,"sha256":hashlib.sha256(data).hexdigest(),"exit_code":p.returncode})
    if p.returncode: sys.exit(p.returncode)
merged={v["file"]:v for v in previous}
merged.update({v["file"]:v for v in results})
result_path.write_text(json.dumps(list(merged.values()),indent=2),encoding="utf-8")
