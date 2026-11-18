#!/usr/bin/env python3
"""suite_table.py RESULT_FILE... -- the compiler suite's table (PROGRAM "A benchmark suite for the compiler").
Reads suite_one.sh result lines ("KERNEL SEED status=... P=.. lat_max_cyc=.. luts=.. draws=p/n ...") from the files or
directories given (a directory: every */result.txt below it, e.g. $RUNS/suite or a farm results/NAME), one row per
kernel over its seeds: status, routes judged (board routes: EQUIVALENT and ffmux-clean), draws passing, ns/iteration
(the timed event graph's period P: median and range over the routes judged), worst latency per call, kernel LUTs,
Dynamatic's figure where one exists (research/tools/suite/dynamatic_ref.tsv; each figure says how it was obtained)
and the ratio.  A kernel passes when every draw on every judged route returned every right answer and at least one
route was judged.  Last line: how many of N pass, and the geometric mean of the ratio over kernels with a figure."""
import glob, math, os, re, statistics as st, sys

def lines(args):
    for a in args:
        # a directory: $RUNS/suite (K_S/result.txt) or a farm results/NAME (TASK/result.txt); never the loop's own
        # result.txt that farm requests copy into TASK/auto/
        fs = sorted(glob.glob(os.path.join(a, "*", "result.txt"))) if os.path.isdir(a) else [a]
        for f in fs:
            if not os.path.exists(f):
                print("suite_table.py: no result file %s (the run died before writing it)" % f, file=sys.stderr)
                continue
            for l in open(f):
                if l.strip():
                    yield l.strip()

def hand_ref():
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hand_ref.tsv")
    out = {}
    if os.path.exists(p):
        for l in open(p):
            if l.startswith("#") or not l.strip():
                continue
            k, ns, how = (l.rstrip("\n").split("\t") + ["", ""])[:3]
            out[k] = (float(ns), how)
    return out

def dyn_ref():
    """Dynamatic's figure per kernel: dynamatic_ref.tsv (measured routes) first, then the estimator's table
    (research/data/suite/dynamatic/dynamatic_est.tsv: simulated on-merges cycles x an ESTIMATED period)."""
    here = os.path.dirname(os.path.abspath(__file__))
    out = {}
    for p in (os.path.join(here, "../../data/suite/dynamatic/dynamatic_est.tsv"), os.path.join(here, "dynamatic_ref.tsv")):
        if os.path.exists(p):
            for l in open(p):
                if l.startswith("#") or not l.strip():
                    continue
                k, ns, tag, how = (l.rstrip("\n").split("\t") + ["", "", ""])[:4]
                out[k] = (float(ns), tag, how)   # the later file (measured) overrides the estimate
    return out

rows = {}
for l in lines(sys.argv[1:]):
    t = l.split()
    if len(t) < 3:
        continue
    d = dict(re.findall(r"(\w+)=(\S+)", l))
    rows.setdefault(t[0], []).append(dict(seed=t[1], _l=l, **d))
DY = dyn_ref(); HD = hand_ref()
print("| kernel | status | routes judged / built | draws passing | ns per iteration (P), median (range) | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns |")
print("|---|---|---|---|---|---|---|---|---|---|")
npass, ratios = 0, []
for k in sorted(rows):
    rs = rows[k]
    judged = [r for r in rs if r.get("status") in ("PASS", "FAIL")]
    stats = sorted({r.get("status", "?") for r in rs})
    dp = sum(int(r["draws"].split("/")[0]) for r in judged if "draws" in r)
    dn = sum(int(r["draws"].split("/")[1]) for r in judged if "draws" in r)
    Ps = [int(r["P"]) / 1000 for r in judged if r.get("P", "NA").isdigit()]
    lat = [int(r["lat_max_cyc"]) * 12 for r in judged if r.get("lat_max_cyc", "NA").isdigit()]
    luts = [int(r["luts"]) for r in judged if r.get("luts", "").isdigit()]
    ok = bool(judged) and dp == dn and all(r.get("status") == "PASS" for r in judged)
    if not judged:
        why = [re.search(r"status=\S+ \(([^)]*)\)", r["_l"]) for r in rs]
        status = "/".join(stats) + "".join(" (%s)" % w.group(1) for w in why[:1] if w)
    else:
        status = "PASS" if ok else "WRONG ANSWER under draws"
    npass += ok
    Pm = st.median(Ps) if Ps else None
    dy = DY.get(k)
    ratio = (Pm / dy[0]) if (Pm and dy) else None
    if ratio and ok:
        ratios.append((ratio, "ESTIMATE" not in dy[1]))
    hd = HD.get(k)
    print("| %s | %s | %d / %d | %s | %s | %s | %s | %s | %s | %s |" % (
        k, status, len(judged), len(rs), ("%d / %d" % (dp, dn)) if dn else "-",
        ("%.2f (%.2f-%.2f)" % (Pm, min(Ps), max(Ps))) if Ps else "-",
        ("%d" % max(lat)) if lat else "-", ("%d" % st.median(luts)) if luts else "-",
        ("%.2f (%s)" % dy[:2]) if dy else "-", ("%.2f" % ratio) if ratio else "-",
        ("%.2f" % hd[0]) if hd else "-"))
notes = sorted({(k, v[2]) for k, v in DY.items() if k in rows})
hnotes = sorted({(k, v[1]) for k, v in HD.items() if k in rows})
if hnotes:
    print()
    print("Hand recipes (per-kernel knobs and sizes, the column the automatic path has to close): " + "; ".join("%s: %s" % kv for kv in hnotes) + ".")
if notes:
    print()
    print("Dynamatic's figures: " + "; ".join("%s: %s" % kv for kv in notes) + ".")
def gmean(v):
    return math.exp(sum(map(math.log, v)) / len(v)) if v else None
gm_m = gmean([r for r, m in ratios if m]); gm_a = gmean([r for r, _ in ratios])
print()
print("%d of %d kernels pass; geometric mean of the ratio (ns per iteration / Dynamatic's) over passing kernels with a "
      "MEASURED Dynamatic figure (n = %d): %s; including ESTIMATED figures (n = %d): %s. Our ns are the simulation's "
      "(about 8 %% slower per iteration than the August board on the same bitstreams, research/SIM-VS-BOARD.md); "
      "Dynamatic's measured figures are single nextpnr routes (Fmax), not board runs."
      % (npass, len(rows), sum(1 for _, m in ratios if m), ("%.2f" % gm_m) if gm_m else "-",
         len(ratios), ("%.2f" % gm_a) if gm_a else "-"))
