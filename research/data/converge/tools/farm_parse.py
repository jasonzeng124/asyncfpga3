#!/usr/bin/env python3
"""farm_parse.py RESULTS OUT.json: every auto_size loop the farm returned (RESULTS/<REQ>/<T>/auto/: log.txt, ratchet_I,
neg_I, lines_I_C, ca_I_C, sizes_I) into one JSON for finish_misses.py.  RESULTS: git archive origin/claude/cluster
results/<REQ>... | tar -x (subagent converge used suite6 suite9 suite9r3 suite9r4 norw1 norw1r2 gifast1 nsearch1 suite10b muxn1
divsize1 split1 split1r2 conv1)."""
import glob, json, os, re, sys
BASE = sys.argv[1]; OUT = sys.argv[2]
def rdvh(p):
    d = {}
    if os.path.exists(p):
        for ln in open(p):
            m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
            if m: d[m.group(1)] = int(m.group(2))
    return d
def rdlines(p):
    d = {}
    if not os.path.exists(p): return None
    for ln in open(p):
        f = ln.rstrip("\n").split("\t")
        if len(f) < 8 or f[0] == "macro": continue
        d[f[0]] = dict(size=int(f[1]), prop=int(f[2]), D=int(f[3]), Dn=int(f[4]), crm=int(f[5]), ncons=int(f[6]), why=f[7])
    return d
def rdneg(p):
    if not os.path.exists(p): return None
    rows = []
    for ln in open(p):
        f = ln.rstrip("\n").split("\t")
        if len(f) < 5 or f[0] == "rule": continue
        rows.append(dict(rule=f[0], margin=int(f[1]), key=f[2], fix=f[3], corner=f[4]))
    return rows
RE_ROW = re.compile(r"^  (\S+)\s+(-?\d+)\s+(\S+)")
def rdca(p):
    """negative rows at this corner with their 'depends on' lines, and c_lo"""
    if not os.path.exists(p): return None
    rows, clo, cur, inneg = [], None, None, False
    for ln in open(p):
        m = re.search(r"c_lo (\d+) ps", ln)
        if m: clo = int(m.group(1))
        if ln.startswith("negative at this corner"): inneg = True; continue
        if ln.startswith("proposal"): inneg = False
        if not inneg: continue
        m = RE_ROW.match(ln)
        if m and not ln.startswith("            "):
            cur = dict(rule=m.group(1), margin=int(m.group(2)), inst=m.group(3), deps=[], text=ln.strip()[:400]); rows.append(cur); continue
        m = re.match(r"^\s+depends on: (.*)$", ln)
        if m and cur is not None:
            cur["deps"] = ["BD_SZ_" + x.strip() for x in m.group(1).split(",") if x.strip()]
    return dict(rows=rows, clo=clo)
loops = []
for d in sorted(glob.glob(BASE + "/*/*/auto")):
    t = os.path.dirname(d); req, task = t.split("/")[-2:]
    if not os.path.exists(d + "/log.txt"): continue
    log = open(d + "/log.txt").read().splitlines()
    head = log[0] if log else ""
    m = re.match(r"auto_size (\S+) kernel (\S+) seed (\d+) maxit (\d+)", head)
    name = kern = seed = None
    if m: name, kern, seed = m.group(1), m.group(2), int(m.group(3))
    else:
        m = re.match(r"auto_size (\S+) RESUMED", head)
        if m: name = m.group(1)
    if kern is None:
        tt = open(t + "/task.txt").readline() if os.path.exists(t + "/task.txt") else ""
        m = re.search(r"kernel (\S+) seed (\d+)", tt)
        if m: kern, seed = m.group(1), int(m.group(2))
    its, p2 = {}, None
    for ln in log:
        m = re.match(r"^it (\d+) (\S+) (\S+) (P=\S+).*?(?:\| (raised .*))?$", ln)
        if m:
            i = int(m.group(1)); its[i] = dict(route=m.group(2), sdf=m.group(3), summ=m.group(5) or "", ro="--raise-only" in ln)
        m = re.match(r"^phase 2 \(raise-only\) from it (\d+)", ln)
        if m: p2 = int(m.group(1))
    res = open(d + "/result.txt").read().strip().splitlines() if os.path.exists(d + "/result.txt") else []
    final = {}
    for ln in log:
        m = re.match(r"^final it (\d+) (\S+) (\S+) P=(\S+)", ln)
        if m: final[int(m.group(1))] = dict(sdf=m.group(3), P=m.group(4))
    L = dict(req=req, task=task, name=name, kernel=kern, seed=seed, p2=p2, result=res[-1] if res else "", final=final, its={})
    for i in sorted(its):
        it = its[i]
        it["neg"] = rdneg("%s/neg_%d.txt" % (d, i))
        it["lines"] = {c: rdlines("%s/lines_%d_%s.txt" % (d, i, c)) for c in ("0.20", "0.31")}
        it["ca"] = {c: rdca("%s/ca_%d_%s.txt" % (d, i, c)) for c in ("0.20", "0.31")}
        it["sizes"] = rdvh("%s/sizes_%d.vh" % (d, i))
        rp = "%s/ratchet_%d.txt" % (d, i)
        it["raised"] = []
        if os.path.exists(rp):
            for ln in open(rp):
                m = re.match(r"\s+raised (\S+) (\d+)->(\d+)", ln)
                if m: it["raised"].append((m.group(1), int(m.group(2)), int(m.group(3))))
        L["its"][i] = it
    nx = max(its) + 1 if its else 0
    L["sizes_next"] = rdvh("%s/sizes_%d.vh" % (d, nx))
    loops.append(L)
json.dump(loops, open(OUT, "w"))
print(len(loops), "loops")
