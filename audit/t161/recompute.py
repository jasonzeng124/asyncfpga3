#!/usr/bin/env python3
"""Independent recompute of the fifteen/README headline from raw farm results (read-only)."""
import glob, math, os, re, statistics as st, sys
R = "/root/agentF/raw/results"
SUITES = ["suite6", "suite3a", "suite3b", "suite8", "suite7"]
def gm(v): return math.exp(sum(map(math.log, v))/len(v)) if v else None
dy = {}
for p in sys.argv[1:]:
    for l in open(p):
        if l.startswith("#") or not l.strip(): continue
        f = l.rstrip("\n").split("\t"); dy[f[0]] = (float(f[1]), f[2])
rows = {}; tasks = {}
for s in SUITES:
    st_ = {}
    for l in open(f"{R}/{s}/status.txt"):
        t = l.split()
        if t and t[0].isdigit(): st_[t[0]] = t[1]
    for d in sorted(glob.glob(f"{R}/{s}/*/")):
        n = os.path.basename(d.rstrip("/"))
        task = open(d+"task.txt").read().split() if os.path.exists(d+"task.txt") else []
        kern, seed = (task[2], task[4]) if len(task) >= 5 else ("?", "?")
        res = open(d+"result.txt").read().strip() if os.path.exists(d+"result.txt") else None
        # verify draws from draws.txt
        dr = open(d+"draws.txt").read() if os.path.exists(d+"draws.txt") else ""
        tasks.setdefault(kern, []).append((s, n, seed, st_.get(n), res))
        if res:
            dd = dict(re.findall(r"(\w+)=(\S+)", res))
            rows.setdefault(kern, []).append(dd)
for k in sorted(tasks):
    ts = tasks[k]; rs = rows.get(k, [])
    j = [r for r in rs if r.get("status") in ("PASS","FAIL")]
    dp = sum(int(r["draws"].split("/")[0]) for r in j); dn = sum(int(r["draws"].split("/")[1]) for r in j)
    Ps = [int(r["P"])/1000 for r in j if r.get("P","NA").isdigit()]
    nc = sum(1 for r in j if r.get("rule") == "not-clean")
    Pm = st.median(Ps) if Ps else None
    d = dy.get(k); ratio = Pm/d[0] if (Pm and d) else None
    print(f"{k:15s} tasks={len(ts):2d} timeout={sum(1 for t in ts if t[3]=='TIMEOUT')} built={len(rs)} judged={len(j)} draws={dp}/{dn} notclean={nc}/{len(j)} P={['%.2f'%p for p in sorted(Ps)]} med={Pm and round(Pm,2)} dyn={d} ratio={ratio and round(ratio,2)}")
    for t in ts:
        if t[3] != "COMPLETED" or not t[4] or "status=PASS" not in t[4]:
            print("     absent/nonpass:", t[0], "task", t[1], "seed", t[2], t[3], (t[4] or "NO result.txt")[:110])
