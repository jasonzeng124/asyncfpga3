#!/usr/bin/env python3
"""Independent recomputation of the 56-of-62 headline (README 94fb37931 / 34bde912c).
usage: mytable2.py RESULTS_ROOT RESEARCH_TREE [variant]
variant: none | c64s8 (no-op marker) ; prints per-kernel rows, provenance per counted route, summary numbers."""
import os, re, sys, glob, math, statistics as st
ROOT, RS = sys.argv[1], sys.argv[2]
VAR = sys.argv[3] if len(sys.argv) > 3 else ""
ORDER0 = [("suite3a", None), ("suite3b", None), ("suite8", None), ("suite7", None), ("suite6", range(25, 33)),
         ("suite9", None), ("suite9r3", None), ("norw1", None), ("norw1r2", None), ("gifast1", None), ("nsearch1", None),
         ("suite10b", None), ("muxn1", None), ("suite9r4", None), ("divsize1", None), ("divres1", None),
         ("suite10c", None), ("ifl1", None), ("ringfuse1", range(33, 45))]
ORDER = [(x, None) for x in sorted(os.listdir(ROOT), key=lambda n: (n.split("_r")[0], n)) if x.startswith("suite13t_s5a_v10")]
CORR = os.path.join(RS, "research/data/suite/corrections/v10_nest3_s4")
commit = {}
allruns = {}
for s, tasks in ORDER:
    d = os.path.join(ROOT, s)
    commit[s] = open(os.path.join(d, "status.txt")).read().split("commit")[1].split()[0][:9]
    for t in sorted((x for x in os.listdir(d) if x.isdigit()), key=int):
        if tasks and int(t) not in tasks: continue
        f = os.path.join(d, t, "result.txt")
        if not os.path.exists(f): continue
        for l in open(f):
            tok = l.split()
            if len(tok) < 3: continue
            kv = dict(re.findall(r"(\w+)=(\S+)", l)); kv["status"] = tok[2].split("=")[1]
            kv["_dir"] = os.path.join(d, t); kv["_src"] = "%s/%s" % (s, t); kv["_l"] = l.strip()
            allruns.setdefault((tok[0], tok[1]), []).append(kv)
if VAR != "nocorr":
    l = open(os.path.join(CORR, "result.txt")).read().strip(); tok = l.split()
    kv = dict(re.findall(r"(\w+)=(\S+)", l)); kv["status"] = tok[2].split("=")[1]; kv["_src"] = "CORR/x"; kv["_l"] = l
    old = allruns[(tok[0], tok[1])][-1]; kv["_dir"] = old["_dir"]; commit["CORR"] = "local"
    allruns[(tok[0], tok[1])].append(kv)
latest = {kk: v[-1] for kk, v in allruns.items()}
for kk, v in allruns.items():
    if len([x for x in v if x["_src"] != "CORR/x"]) > 1: print("DUP", kk, [x["_src"] + ":" + x["status"] for x in v])

def tsv(p):
    for l in open(os.path.join(RS, p)):
        if l.startswith("#") or not l.strip(): continue
        yield l.rstrip("\n").split("\t")
dyn = {}
for p in ("research/data/suite/dynamatic/dynamatic_est.tsv", "research/tools/suite/dynamatic_ref.tsv"):
    for f in tsv(p): dyn[f[0]] = (float(f[1]), f[2])
dlat = {}
for f in tsv("research/data/suite/dynamatic/dynamatic_lat.tsv"):
    f = f + [""] * 12
    dlat[f[0]] = dict(n=int(f[1]), mean=float(f[2]), tag=f[3], cp=float(f[8]), nl=int(f[9] or 0),
                      ex=[int(x) for x in f[10].split(",")] if f[10] not in ("", "-") else None)
kernels = []
for ln in open(os.path.join(RS, "research/tools/suite/kernels.txt")):
    for k in ln.split("#")[0].split():
        if k not in kernels: kernels.append(k)

def benchlat(r):
    per = {}; fclk = None
    for f in glob.glob(os.path.join(r["_dir"], "benchres_*.txt")):
        for l in open(f):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "batch" in d and "latmin" in d:
                fclk = int(d.get("fclk_ps", 12000))
                per.setdefault(int(d["batch"]), []).append(int(d["latmin"]) * fclk / 1000)
    return ([st.median(per[b]) for b in sorted(per)], fclk) if per else (None, None)

def slope(x, y):
    mx, my = sum(x) / len(x), sum(y) / len(y); sxx = sum((a - mx) ** 2 for a in x)
    return None if sxx == 0 else sum((a - mx) * (b - my) for a, b in zip(x, y)) / sxx
g = lambda v: math.exp(sum(map(math.log, v)) / len(v)) if v else float("nan")
R = lambda v: "%.2f (%.2f-%.2f)" % (st.median(v), min(v), max(v))
npass = 0; ratios = []; lrs = []; rows = {}
for k in sorted(set(kernels) | {k for k, _ in latest}):
    rs = sorted([latest[x] | {"seed": x[1]} for x in latest if x[0] == k], key=lambda r: int(r["seed"]))
    if not rs: rows[k] = "NO RESULT"; print("%-18s NO RESULT" % k); continue
    J = [r for r in rs if r["status"] in ("PASS", "FAIL")]
    C = [r for r in J if r.get("rule") == "clean"]; N = [r for r in J if r.get("rule") != "clean"]
    dd = lambda x: (sum(int(r["draws"].split("/")[0]) for r in x), sum(int(r["draws"].split("/")[1]) for r in x))
    ok = bool(C) and all(r["status"] == "PASS" for r in J) and dd(J)[0] == dd(J)[1]
    npass += ok
    Pc, Pn, Fc, Fn, L, nv = [], [], [], [], [], []
    dl = dlat.get(k)
    for r in J:
        v, fclk = benchlat(r)
        P = int(r["P"]) if r.get("P", "NA").isdigit() else None
        if P is not None and P % (fclk or 12000) == 0: P = None
        if P is not None: (Pc if r.get("rule") == "clean" else Pn).append(P / 1000)
        if r.get("rule") != "clean": pass
        elif v: L.append(sum(v) / len(v)); nv.append(len(v))
        elif r.get("lat_call_sum_ns", "").isdigit() and r.get("nvec", "0").isdigit() and int(r["nvec"]):
            L.append(int(r["lat_call_sum_ns"]) / int(r["nvec"])); nv.append(int(r["nvec"]))
        if P is not None and v and dl and dl["ex"] and len(dl["ex"]) == len(v):
            b = slope(dl["ex"], v); x = dl["ex"]; n = len(x); mx = sum(x) / n; my = sum(v) / n
            se = (math.sqrt(sum((yy - my - b * (xx - mx)) ** 2 for xx, yy in zip(x, v)) / (n - 2) / sum((xx - mx) ** 2 for xx in x)) if (b is not None and n > 2) else None)
            if b and b > 0 and se is not None and abs(P / 1000 - b) > max(0.15 * b, 3 * se):
                print("  REFUSE %s s%s P=%.2f slope=%.2f" % (k, r["seed"], P / 1000, b)); (Pc if r.get("rule") == "clean" else Pn).remove(P / 1000); P = None
        if P is None and v and dl and dl["ex"] and len(dl["ex"]) == len(v):
            b = slope(dl["ex"], v)
            if b is not None: (Fc if r.get("rule") == "clean" else Fn).append(b)
    fit = not Pc and bool(Fc); Pv = Pc or (Fc if fit else [])
    ratio = st.median(Pv) / dyn[k][0] if (Pv and k in dyn) else None
    if ok and ratio and k not in ("isprime", "stencil_2d"): ratios.append((k, ratio, "ESTIMATE" not in dyn[k][1]))
    lr = None
    if dl and L and nv and all(n == dl["n"] for n in nv):
        lr = st.median(L) / dl["mean"]
        extrap = "ESTIMATE" in dl["tag"] and dl["cp"] < 15.03 / 2
        if ok and not extrap and k != "isprime": lrs.append((k, lr))
    lat = [int(r["lat_max_cyc"]) * 12 for r in J if r.get("lat_max_cyc", "").isdigit()]
    st_ = "PASS" if ok else (("UNFINISHED" if all(r["status"] == "PASS" for r in J) and dd(J)[0] == dd(J)[1] else "WRONG") if J else "/".join(sorted({r["status"] for r in rs})))
    row = "%s %d+%d/%d %d/%d;%d/%d P=%s [%s] lat=%s dyn=%s ratio=%s L=%s lr=%s" % (
        st_, len(C), len(N), len(rs), *dd(C), *dd(N), ("fit " if fit else "") + R(Pv) if Pv else "-",
        R(Pn) if Pn else (("fit " + R(Fn)) if Fn else "-"), max(lat) if lat else "-",
        dyn.get(k, ("-",))[0], "%.2f" % ratio if ratio else "-", R(L) if L else "-", "%.2f" % lr if lr else "-")
    rows[k] = row
    print("%-18s %s" % (k, row))
    print("%-18s   routes: %s" % ("", "; ".join("s%s %s@%s %s %s %s P=%s" % (r["seed"], r["_src"], commit[r["_src"].split("/")[0]],
          r["status"], r.get("rule"), r.get("draws"), r.get("P")) for r in rs)))
    hist = ["s%s: " % x[1] + " > ".join("%s %s %s %s" % (q["_src"], q["status"], q.get("rule"), q.get("draws")) for q in allruns[x])
            for x in sorted(allruns, key=lambda x: int(x[1])) if x[0] == k and len(allruns[x]) > 1]
    if hist: print("%-18s   superseded: %s" % ("", " | ".join(hist)))
m = [r for _, r, mm in ratios if mm]
print("\npass %d of %d" % (npass, len(set(kernels) | {k for k, _ in latest})))
print("gmean measured n=%d %.3f [%s]" % (len(m), g(m), ",".join(k for k, _, mm in ratios if mm)))
print("gmean all n=%d %.3f [%s]" % (len(ratios), g([r for _, r, _ in ratios]), ",".join("%s:%.2f" % (k, r) for k, r, _ in ratios)))
print("gmean all, estimates only n=%d %.3f" % (len([1 for _,_,mm in ratios if not mm]), g([r for _, r, mm in ratios if not mm])))
print("latency gmean n=%d %.3f [%s]" % (len(lrs), g([r for _, r in lrs]), ",".join("%s:%.2f" % x for x in lrs)))
