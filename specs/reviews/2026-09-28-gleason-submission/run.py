from pathlib import Path
import subprocess, os, json, re, hashlib, time, sys, shutil
sys.stdout.reconfigure(encoding="utf-8")
repo=Path.cwd()
audit=repo/".lake/gleason-submission-5f77294d"
commit="5f77294d6c327d37fe824e6829097600050b1de7"
def git(*args):
    return subprocess.check_output(["git", *args], cwd=repo)
mods={}; order=[]
def visit(mod):
    if mod in mods: return
    path=mod.replace(".","/")+".lean"
    data=git("show",commit+":"+path)
    mods[mod]={"path":path,"blob":git("rev-parse",commit+":"+path).decode().strip(),"sha256":hashlib.sha256(data).hexdigest()}
    target=audit/path; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data)
    for dep in re.findall(r"^(?:public )?import\s+(\S+)",data.decode(),re.M):
        if dep.startswith("CsdLean4."): visit(dep)
    order.append(mod)
for mod in ["CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.RealFrame","CsdLean4.LF2.EffectGleason"]: visit(mod)
for path in ["lean-toolchain","lakefile.toml","lake-manifest.json"]:
    data=git("show",commit+":"+path)
    if data != (repo/path).read_bytes(): raise RuntimeError("Dependency config differs: "+path)
    (audit/path).write_bytes(data)
lib=audit/".lake/build/lib/lean"; lib.mkdir(parents=True,exist_ok=True)
env=os.environ.copy()
oldlib=str(repo/".lake/build/lib/lean")
paths=[p for p in env["LEAN_PATH"].split(os.pathsep) if os.path.normcase(os.path.normpath(p))!=os.path.normcase(os.path.normpath(oldlib))]
env["LEAN_PATH"]=os.pathsep.join([str(lib),*paths]); env["LEAN_NUM_THREADS"]="2"
lean=shutil.which("lean")
manifest={"commit":commit,"lean":lean,"lean_version":subprocess.check_output([lean,"--version"],env=env).decode().strip(),"lean_path":env["LEAN_PATH"],"modules":mods,"build_order":order,"results":[]}
(audit/"environment.json").write_text(json.dumps(manifest,indent=2),encoding="utf-8")
print("Fresh isolated compilation of",len(order),"modules at",commit,flush=True)
for mod in order:
    out=lib/(mod.replace(".","/")+".olean"); out.parent.mkdir(parents=True,exist_ok=True)
    cmd=[lean,"-DautoImplicit=false","-DrelaxedAutoImplicit=false","-DwarningAsError=true","-o",str(out),mod.replace(".","/")+".lean"]
    start=time.monotonic(); r=subprocess.run(cmd,cwd=audit,env=env,capture_output=True,encoding="utf-8")
    log=r.stdout+r.stderr
    (audit/(mod.split(".")[-1]+".build.log")).write_text(log,encoding="utf-8")
    manifest["results"].append({"module":mod,"returncode":r.returncode,"seconds":round(time.monotonic()-start,2),"command":cmd})
    (audit/"environment.json").write_text(json.dumps(manifest,indent=2),encoding="utf-8")
    print(mod, "PASS" if r.returncode==0 else "FAIL",manifest["results"][-1]["seconds"],flush=True)
    if log: print(log,flush=True)
    if r.returncode: sys.exit(r.returncode)
print("ALL TARGET MODULES PASSED",flush=True)
