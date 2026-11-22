#!/usr/bin/env python3
"""collect.py RUNS OUT_DIR -- every GATE_RUNTS run under RUNS/g/<route>/<col>/<col>/ as one table row, plus the
per-net table of every run with a pulse narrower than T3 (runts_<route>_<col>.txt) and, for the suite6 routes, the
rule's negative sized rows next to the nets hit (s6_rows.txt).

Row: route, corner, gate verdict (answers), pulses < 150 / 500 / 1000 ps, x pulses, nets hit / watched, classes hit,
narrowest pulse of any width on any watched net (ps), longest kernel loop at the corner (ps)."""
import os, re, sys, glob, collections
RUNS, OUT = sys.argv[1], sys.argv[2]
os.makedirs(OUT, exist_ok=True)
rows = []
for rl in sorted(glob.glob(os.path.join(RUNS, "g", "*", "*", "*", "run.log"))):
    wd = os.path.dirname(rl); col = os.path.basename(wd); route = os.path.basename(os.path.dirname(os.path.dirname(wd)))
    gate = os.path.join(os.path.dirname(wd), "gate.txt")
    v = open(gate).read().strip() if os.path.exists(gate) else ""
    if not v:
        g = glob.glob(os.path.join(RUNS, "s6", route[3:], "gate_%s.txt" % col))
        v = open(g[0]).read().strip().splitlines()[-1] if g and open(g[0]).read().strip() else ""
    rsum, rcls, rnet = None, {}, {}
    for l in open(rl):
        if l.startswith("RUNTSUM "): rsum = dict(re.findall(r"(\w+)=(\S+)", l))
        elif l.startswith("RUNTCLS "):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "minall" in d: rcls[d["cls"]] = d
        elif l.startswith("RUNTMON batch="):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "net" in d: rnet[int(d["k"])] = d
    if rsum is None or not v:   # no monitor output, or the run has not finished
        continue
    verdict = " ".join(v.split()[:2]) if v else "?"
    hitc = ",".join("%s %s" % (c, d["hit"]) for c, d in sorted(rcls.items()) if int(d["hit"]))
    rows.append((route, col, verdict, rsum["n1"], rsum["n2"], rsum["n3"], rsum["x"], "%s/%s" % (rsum["hit"], rsum["nets"]),
                 hitc or "-", rsum["minall"], rsum.get("tloopmax", "-"), rsum["batch"]))
    if rnet:
        with open(os.path.join(OUT, "runts_%s_%s.txt" % (route, col)), "w") as f:
            f.write("# %s %s: %s\n# k cls inst role net n<%s n<%s n<%s hi lo x narrowest_0/1_ps first_ps\n" % (
                route, col, v, rsum["t1"], rsum["t2"], rsum["t3"]))
            for d in sorted(rnet.values(), key=lambda d: (-(int(d["n3"]) + int(d["x"])), d["cls"], d["inst"])):
                f.write(" ".join(d[c] for c in ("k", "cls", "inst", "role", "net", "n1", "n2", "n3", "hi", "lo", "x", "min",
                                                 "first")) + "\n")
with open(os.path.join(OUT, "runs.tsv"), "w") as f:
    f.write("# route\tcorner\tverdict\tn<150\tn<500\tn<1000\tx\tnets_hit/watched\tclasses_hit\tnarrowest_any_ps\t"
            "longest_loop_ps\tlast_batch\n")
    for r in rows:
        f.write("\t".join(map(str, r)) + "\n")
for r in rows:
    print("%-20s %-12s %-10s %5s %5s %5s %3s %8s %-40s %6s %5s" % r[:11])
# the rule's NOT CLEAN rows (merged over its two corners, auto_size.sh's negative_sized.tsv) beside the nets hit
with open(os.path.join(OUT, "s6_rows.txt"), "w") as f:
    for d in sorted(glob.glob(os.path.join(RUNS, "s6", "*"))):
        name = os.path.basename(d); neg = os.path.join(d, "negative_sized.tsv")
        if not os.path.exists(neg): continue
        neg_rows = [l.rstrip("\n").split("\t") for l in open(neg) if l.strip() and not l.startswith("rule\t")]
        b = open(os.path.join(d, "build.txt")).read().split("\n")[0] if os.path.exists(os.path.join(d, "build.txt")) else ""
        f.write("== %s (%s)\n" % (name, b))
        insts = collections.OrderedDict()
        for r in neg_rows:
            m = re.search(r"bridge_i\.udut\.([A-Za-z0-9_]+)", r[2])
            insts.setdefault(m.group(1) if m else r[2], []).append("%s %s (%s)" % (r[0], r[1], r[4]))
        f.write("   rule rows: %s\n" % ("; ".join("%s: %s" % (k, ", ".join(v)) for k, v in insts.items()) or "none (CLEAN)"))
        for g in sorted(glob.glob(os.path.join(d, "runts_*.txt"))):
            hit = [l.split() for l in open(g) if not l.startswith("#")]
            f.write("   gate %s: %s\n" % (os.path.basename(g)[6:-4], "; ".join(
                "%s %s.%s n<1ns %s (narrowest %s ps)" % (h[1], h[2], h[3], int(h[7]) + int(h[10]), h[11]) for h in hit) or "no pulse < 1 ns"))
print(open(os.path.join(OUT, "s6_rows.txt")).read())
