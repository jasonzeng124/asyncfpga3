#!/usr/bin/env python3
"""Private olean build of a Mathlib-free module closure (shard B), for checking while
lake/Mathlib is busy.  usage: privbuild.py OUTDIR MODULE... (run from formal/lean)
Compiles each module of the import closure in topological order with
`lean -DautoImplicit=false -o`, through formal/slot.sh, -j2. Fails on any Mathlib import."""
import os, re, subprocess, sys, concurrent.futures as cf
out = os.path.abspath(sys.argv[1]); mods = sys.argv[2:]
deps = {}
def go(m):
    if m in deps: return
    if m.startswith("Mathlib"): sys.exit("Mathlib import: " + m)
    if not m.startswith("Formal"): deps[m] = []; return
    p = m.replace(".", "/") + ".lean"
    ds = [mm.group(1) for l in open(p) for mm in [re.match(r"import\s+(\S+)", l)] if mm]
    deps[m] = [d for d in ds if d.startswith("Formal")]
    for d in ds: go(d)
for m in mods: go(m)
done = set(); env = dict(os.environ, LEAN_PATH=out)
slot = os.path.abspath("../slot.sh")
def build(m):
    p = m.replace(".", "/") + ".lean"; o = os.path.join(out, m.replace(".", "/"))
    os.makedirs(os.path.dirname(o), exist_ok=True)
    if os.path.exists(o + ".olean") and os.path.getmtime(o + ".olean") > os.path.getmtime(p) \
       and all(os.path.getmtime(os.path.join(out, d.replace(".", "/")) + ".olean") <= os.path.getmtime(o + ".olean") for d in deps[m]):
        return m, 0, ""
    r = subprocess.run([slot, "lean", "-DautoImplicit=false", "-o", o + ".olean", "-i", o + ".ilean", p],
                       env=dict(env, FORMAL_SLOT_CWD=os.getcwd()), capture_output=True, text=True)
    return m, r.returncode, r.stdout + r.stderr
pending = set(deps); running = {}
with cf.ThreadPoolExecutor(int(os.environ.get("PJ", "2"))) as ex:
    while pending or running:
        for m in sorted(pending):
            if all(d in done for d in deps[m]) and len(running) < int(os.environ.get("PJ", "2")):
                running[ex.submit(build, m)] = m; pending.discard(m)
        f = next(cf.as_completed(running)); m, rc, log = f.result(); del running[f]
        if rc != 0 or "sorry" in log or "error" in log:
            print("FAIL", m); print(log[-4000:]); sys.exit(1)
        done.add(m); print("ok", m, flush=True)
print("ALL OK", len(done))
