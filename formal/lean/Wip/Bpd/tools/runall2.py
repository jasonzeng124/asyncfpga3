#!/usr/bin/env python3
"""Compile the Wip/Bpd shadow tree through bcheck.py, one file per call, in dependency
order, 3 workers; a file whose shadow dependency failed is reported SKIP."""
import json, subprocess, os
PFX = os.environ.get("PFX", "Wip/Bpd/")
import json as _j, sys, threading, time, re
ROOT = "/home/user/asyncfpga3/formal/lean"
d = json.load(open("/tmp/claude-0/probes/Bpd/closure.json"))
CL = d["closure"]; CLS = set(CL); IM = d["imports"]
only = set(sys.argv[2:]) if len(sys.argv) > 2 else None
LOG = sys.argv[1]
deps = {m: [i for i in IM[m] if i in CLS] for m in CL}
status = {}
import hashlib, os
P = "/tmp/claude-0/bolean"
def fresh(m):
    p = PFX + m.replace(".", "/") + ".lean"
    st = os.path.join(P, p[:-5] + ".olean.sha")
    h = hashlib.sha256(open(os.path.join(ROOT, p), "rb").read()).hexdigest()
    return os.path.exists(st) and open(st).read() == h
redo = set(m for m in CL if not fresh(m))
ch = True
while ch:
    ch = False
    for m in CL:
        if m not in redo and any(x in redo for x in deps[m]): redo.add(m); ch = True
for m in CL:
    if m not in redo: status[m] = "OK"
print("recompiling", len(redo), sorted(redo), flush=True)
lock = threading.Lock()
out = open(LOG, "a")
def run(m):
    p = PFX + m.replace(".", "/") + ".lean"
    t0 = time.time()
    r = subprocess.run(["/tmp/claude-0/btools/bcheck.py", p], cwd=ROOT, capture_output=True, text=True)
    ok = r.returncode == 0 and re.search(r"^== .*: OK", r.stdout, re.M)
    res = "OK" if ok else ("NEEDS_MATHLIB" if "NEEDS_MATHLIB" in r.stdout else "FAIL")
    with lock:
        status[m] = res
        out.write(f"#### {m} {res} {time.time()-t0:.0f}s\n")
        if res != "OK":
            out.write((r.stdout + r.stderr)[-4000:] + "\n")
        out.flush()
running = set()
def worker():
    while True:
        with lock:
            todo = [m for m in CL if m not in status and m not in running]
            if not todo: return
            pick = None
            for m in todo:
                if any(status.get(x) not in (None, "OK") for x in deps[m]):
                    status[m] = "SKIP"; out.write(f"#### {m} SKIP\n"); out.flush(); continue
                if all(status.get(x) == "OK" for x in deps[m]):
                    pick = m; break
            if pick is None:
                if not [m for m in CL if m not in status and m not in running]: return
                wait = True
            else:
                running.add(pick); wait = False
        if wait:
            time.sleep(2); continue
        run(pick)
        with lock: running.discard(pick)
ts = [threading.Thread(target=worker) for _ in range(3)]
for t in ts: t.start()
for t in ts: t.join()
from collections import Counter
out.write("SUMMARY " + str(Counter(status.values())) + "\n")
