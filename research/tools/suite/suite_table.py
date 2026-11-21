#!/usr/bin/env python3
"""suite_table.py RESULT_FILE... -- the compiler suite's table (PROGRAM "A benchmark suite for the compiler").
Reads suite_one.sh result lines ("KERNEL SEED status=... P=.. lat_max_cyc=.. luts=.. draws=p/n ...") from the files or
directories given (a directory: every */result.txt below it, e.g. $RUNS/suite or a farm results/NAME), one row per
kernel over its seeds: status, routes judged (board routes: EQUIVALENT and ffmux-clean), draws passing, ns/iteration
(the timed event graph's period P: median and range over the routes judged), worst latency per call, kernel LUTs,
Dynamatic's figure where one exists (research/tools/suite/dynamatic_ref.tsv; each figure says how it was obtained)
and the ratio.  A kernel passes when every draw on every judged route returned every right answer and at least one
rule-CLEAN route was judged (since 2026-11-20, formal C68: one judged only on routes its loop left NOT CLEAN is
UNFINISHED, counted apart).  Last line: how many of N pass, and the geometric mean of the ratio over kernels with a figure.

Three additions (dynfig, 2026-11-18):
- Latency per call, both sides, on the SAME calls: ours = per vector the median over a route's draws of the bench's
  latmin (BENCHRES, host cycles x fclk_ps; the BENCHRES files beside result.txt, else lat_call_sum_ns / nvec), the
  mean over the vectors, the median over the routes judged; Dynamatic's = research/data/suite/dynamatic/
  dynamatic_lat.tsv (simulated cycles per call on the suite's own vectors x the ESTIMATED period), and their ratio.
  This is the figure for a kernel with no loop, where "ns per iteration" is undefined on both sides.  Ours includes
  the bench's issue, synchroniser and capture (a constant kernel, test_int16, takes 5 host cycles = 60 ns), and is
  quantised to the host clock; Dynamatic's is the kernel alone.
- A route's P is refused when it is an exact multiple of the bench's host clock period: such a marker is clocked by
  the host (the memory's host port during the array fill: dot2's 156000 ps = 13 x 12 ns), not the kernel's loop.
- Where a judged route has no usable P and the kernel has one loop whose trip count varies over the vectors (trip
  counts per call: dynamatic_lat.tsv, the C's loop executed by Dynamatic's simulated circuit, answers = C), the
  per-iteration figure is the least-squares slope of our call latencies on the trip counts ("fit"; the column says
  so).  Dynamatic's per-iteration figure is the same kind of slope (cycles per header execution x period)."""
import glob, math, os, re, statistics as st, sys

HERE = os.path.dirname(os.path.abspath(__file__))


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
                    yield l.strip(), os.path.dirname(os.path.abspath(f))

def hand_ref():
    p = os.path.join(HERE, "hand_ref.tsv")
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
    out = {}
    for p in (os.path.join(HERE, "../../data/suite/dynamatic/dynamatic_est.tsv"), os.path.join(HERE, "dynamatic_ref.tsv")):
        if os.path.exists(p):
            for l in open(p):
                if l.startswith("#") or not l.strip():
                    continue
                k, ns, tag, how = (l.rstrip("\n").split("\t") + ["", "", ""])[:4]
                out[k] = (float(ns), tag, how)   # the later file (measured) overrides the estimate
    return out

# Dynamatic's per-call figure is flagged (and kept out of the latency mean) when its period is extrapolated far below
# the calibration: model path under half the shortest calibrated one (xorshift's 15.03 ns; the fit's points are
# 15.0-21.6 ns), e.g. unused_arg's 1.23 ns path -> 0.97 ns, which no FPGA clocks.
CAL_MIN_PATH_NS = 15.03

def dyn_lat():
    """Dynamatic's latency per call on the suite's calls: research/data/suite/dynamatic/dynamatic_lat.tsv."""
    p = os.path.join(HERE, "../../data/suite/dynamatic/dynamatic_lat.tsv")
    out = {}
    if os.path.exists(p):
        for l in open(p):
            if l.startswith("#") or not l.strip():
                continue
            f = l.rstrip("\n").split("\t")
            k, n, mean, tag, vec, md5, cyc, per, cp, nl, ex, how = (f + [""] * 12)[:12]
            out[k] = dict(n=int(n), mean=float(mean), tag=tag, vectors=vec, period=float(per), cp=float(cp),
                          nloops=int(nl or 0), execs=[int(x) for x in ex.split(",")] if ex not in ("", "-") else None,
                          how=how, extrap="ESTIMATE" in tag and float(cp) < CAL_MIN_PATH_NS / 2)
    return out

def route_lat(r):
    """Our latency per call on one route, ns: per vector (BENCHRES batch) the median over the route's draws of latmin x
    fclk_ps (suite_one.sh's own computation), in vector order; and the host clock period.  None without BENCHRES."""
    per, fclk = {}, None
    for f in glob.glob(os.path.join(r["_dir"], "benchres_*.txt")):
        for l in open(f):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "batch" in d and "latmin" in d:
                fclk = int(d.get("fclk_ps", 12000))
                per.setdefault(int(d["batch"]), []).append(int(d["latmin"]) * fclk / 1000.0)
    if not per:
        return None, None
    return [st.median(x) for _, x in sorted(per.items())], fclk

def route_runts(r):
    """The narrowest-pulse evidence of a route's draws (draws.txt beside its result.txt, suite_one.sh's GATE_RUNTS=1
    report): the largest count of pulses under 150 / 500 / 1000 ps on kernel handshake nets in any one draw, or None
    when no draw line carries the field (older runs)."""
    f = os.path.join(r["_dir"], "draws.txt")
    if not os.path.exists(f):
        return None
    best = None
    for l in open(f):
        m = re.search(r"runts <150/500/1000 ps (\d+)/(\d+)/(\d+)", l)
        if m:
            v = tuple(int(x) for x in m.groups())
            best = v if best is None else tuple(max(a, b) for a, b in zip(best, v))
    return best

def slope(x, y):
    """Least-squares slope of y on x, or None when x does not vary."""
    n = len(x)
    mx, my = sum(x) / n, sum(y) / n
    sxx = sum((a - mx) ** 2 for a in x)
    if sxx == 0:
        return None
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / sxx

def slope_se(x, y):
    """(slope, its standard error from the residuals), or (None, None) when x does not vary or n < 3."""
    n = len(x)
    b = slope(x, y)
    if b is None or n < 3:
        return b, None
    mx, my = sum(x) / n, sum(y) / n
    sxx = sum((a - mx) ** 2 for a in x)
    rss = sum((c - (my + b * (a - mx))) ** 2 for a, c in zip(x, y))
    return b, math.sqrt(rss / (n - 2) / sxx)

def fmt_range(v):
    return "%.2f (%.2f-%.2f)" % (st.median(v), min(v), max(v))

# --kernels FILE (kernels.txt's format): every kernel listed gets a row, also one with no result line (owner, auditor
# T161: "the headline counts what was attempted"); --reasons FILE (TSV kernel<TAB>reason) says why a kernel has none.
# --no-ratio K1,K2: kernels whose P is not comparable with Dynamatic's per-iteration figure (isprime: our P is the outer
# trial's period, Dynamatic's the inner shift's cycle): the ratio is shown, marked, and kept out of every mean.
def _opt(name):
    if name in sys.argv:
        i = sys.argv.index(name); v = sys.argv[i + 1]; del sys.argv[i:i + 2]; return v
    return None
KLIST, REASONS, NORATIO = _opt("--kernels"), _opt("--reasons"), set((_opt("--no-ratio") or "").split(",")) - {""}
listed = []
if KLIST:
    for ln in open(KLIST):
        ln = ln.split("#")[0].split()
        listed += [k for k in ln if k not in listed]
reasons = {}
if REASONS:
    for ln in open(REASONS):
        if ln.strip() and not ln.startswith("#") and "\t" in ln:
            k, w = ln.rstrip("\n").split("\t", 1); reasons[k] = w
rows = {}
for l, d0 in lines(sys.argv[1:]):
    t = l.split()
    if len(t) < 3:
        continue
    d = dict(re.findall(r"(\w+)=(\S+)", l))
    # one route per (kernel, seed): a later argument (a later request) supersedes an earlier one for the same seed
    rows.setdefault(t[0], [])
    rows[t[0]] = [r for r in rows[t[0]] if r["seed"] != t[1]]
    rows[t[0]].append(dict(seed=t[1], _l=l, _dir=d0, **d))
DY = dyn_ref(); HD = hand_ref(); DL = dyn_lat()
print("| kernel | status | routes judged (rule-clean + NOT CLEAN) / built | draws passing (clean; not clean) | ns per iteration (P) on clean routes, median (range) [on NOT CLEAN routes] | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns | latency per call, ns: ours, mean over the calls, median (range) over routes | Dynamatic, latency per call, ns | latency ratio |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
npass, nunf, ratios, lratios, nfit, hostP, notes_k, runty = 0, 0, [], [], 0, [], {}, []
# P against the bench (2026-11-19, research/data/suite/pslope/p_vs_slope.txt): on all 19 single-loop kernels with a varying
# trip count, P / slope is 0.94-1.04 on every route; on a kernel with several loops the auto marker may sit on another loop
# than the most executed one (branchloop 0.45, gcd 2.16, isprime 7.07), and Dynamatic's figure is that loop's slope.  A P
# off its route's slope by more than this is refused, and the slope (the same convention as Dynamatic's figure) is used.
PSLOPE_TOL = 0.15
offP = []
nlist = 0
for k in sorted(set(rows) | set(listed)):
    rs = rows.get(k, [])
    nlist += 1
    if not rs:
        print("| %s | NO RESULT (%s) | 0 / 0 | - | - | - | - | %s | - | - | - | - | - |" % (
            k, reasons.get(k, "no result line: every task hit its time limit, or none ran"),
            ("%.2f (%s)" % DY[k][:2]) if k in DY else "-"))
        continue
    judged = [r for r in rs if r.get("status") in ("PASS", "FAIL")]
    clean = [r for r in judged if r.get("rule") == "clean"]
    nclean = [r for r in judged if r.get("rule") != "clean"]
    stats = sorted({r.get("status", "?") for r in rs})
    dp = sum(int(r["draws"].split("/")[0]) for r in judged if "draws" in r)
    dn = sum(int(r["draws"].split("/")[1]) for r in judged if "draws" in r)
    lat = [int(r["lat_max_cyc"]) * 12 for r in judged if r.get("lat_max_cyc", "NA").isdigit()]
    luts = [int(r["luts"]) for r in judged if r.get("luts", "").isdigit()]
    ok_all = bool(judged) and dp == dn and all(r.get("status") == "PASS" for r in judged)
    # 2026-11-20: a clean route is passing evidence only if its draws also had no pulse under 1 ns on a kernel handshake
    # net (bench_gate.sh GATE_RUNTS=1, report-only in the draws; GATE_RUNTS=fail is the board items' gate).  Over the 378
    # farm routes with runt-monitored draws, the 4 that ever had such a pulse were all NOT CLEAN (exit1 spmv s1 among
    # them, the route formal C68 shows hanging: our draw 10102 there had 72 pulses under 150 ps and passed); no clean
    # route had one.  Formal's simulator lets such pulses through and hangs; our resolver absorbs them; silicon is
    # BOARD-QUEUE item 2.  So the pulse is counted against the route, the conservative reading.
    for r in judged:
        rr = route_runts(r)
        if rr and rr[2] > 0:
            runty.append("%s seed %s (%s, pulses <150/500/1000 ps %d/%d/%d in its worst draw)"
                         % (k, r["seed"], "clean" if r.get("rule") == "clean" else "NOT CLEAN", *rr))
    clean = [r for r in clean if not ((route_runts(r) or (0, 0, 0))[2] > 0)]
    # a kernel passes only on a route the sizing loop finished (rule-CLEAN) -- 2026-11-20, formal C68: exit1 spmv s1, the
    # least-short NOT CLEAN route its loop shipped, passed its 4 draws here and hangs in 11 of 32 draws of the same model
    # at the cell the rule called short; 4 draws cannot see a 1-in-3 failure (0.65^4 = 18 %).  Every draw on every judged
    # route, clean or not, must still pass: a wrong answer anywhere is a wrong answer.
    ok = ok_all and bool(clean)
    if not judged:
        why = [re.search(r"status=\S+ \(([^)]*)\)", r["_l"]) for r in rs]
        status = "/".join(stats) + "".join(" (%s)" % w.group(1) for w in why[:1] if w)
    elif ok:
        status = "PASS"
    elif ok_all:
        status = "UNFINISHED (draws pass on NOT CLEAN routes only)"
        nunf += 1
    else:
        status = "WRONG ANSWER under draws"
    npass += ok
    dl = DL.get(k)
    # per route: P (refused when it is a multiple of the host clock, or when it departs from the route's own slope of call
    # latency on the most executed loop's trip counts by more than PSLOPE_TOL), our call latencies, the fit where P is
    # missing or refused
    Ps, Fs, Ls, Pnc, Fnc, Lnc = [], [], [], [], [], []
    for r in judged:
        v, fclk = route_lat(r)
        P = int(r["P"]) if r.get("P", "NA").isdigit() else None
        if P is not None and P % (fclk or 12000) == 0:
            hostP.append("%s seed %s P=%d = %d x %d ps" % (k, r["seed"], P, P // (fclk or 12000), fclk or 12000))
            P = None
        b, se = slope_se(dl["execs"], v) if (v and dl and dl["execs"] and len(dl["execs"]) == len(v)) else (None, None)
        # refused only when the gap is also beyond 3 standard errors of the slope: a trip count that barely varies over
        # the vectors gives a slope too noisy (12 ns quantisation per call) to overrule P
        if P is not None and b and b > 0 and se is not None and abs(P / 1000.0 - b) > max(PSLOPE_TOL * b, 3 * se):
            offP.append("%s seed %s P=%.2f ns against a slope of %.2f ns (%.2fx)" % (k, r["seed"], P / 1000.0, b, P / 1000.0 / b))
            P = None
        if P is not None:
            (Ps if r.get("rule") == "clean" else Pnc).append(P / 1000)
        LL = Ls if (r.get("rule") == "clean" or not clean) else Lnc   # latency: clean routes where any (as P)
        if v:
            LL.append(sum(v) / len(v))
        elif r.get("lat_call_sum_ns", "NA").isdigit() and r.get("nvec", "0").isdigit() and int(r["nvec"]):
            LL.append(int(r["lat_call_sum_ns"]) / int(r["nvec"]))
        if P is None and b is not None and b > 0:
            (Fs if r.get("rule") == "clean" else Fnc).append(b)
    fit = not Ps and bool(Fs)
    Pv = Ps or (Fs if fit else [])
    Pm = st.median(Pv) if Pv else None
    dy = DY.get(k)
    ratio = (Pm / dy[0]) if (Pm and dy) else None
    if ratio and ok and k not in NORATIO:
        ratios.append((ratio, "ESTIMATE" not in dy[1], fit))
        nfit += fit
    # latency per call: the same calls on both sides (the vector counts must agree)
    lcell, dcell, lrcell = "-", "-", "-"
    if Ls:
        lcell = fmt_range(Ls) + (" [%s]" % fmt_range(Lnc) if Lnc else "")
    if dl:
        dcell = "%.2f (%s%s)" % (dl["mean"], dl["tag"], "; period extrapolated, model path %.2f ns" % dl["cp"] if dl["extrap"] else "")
        # the calls each route's latency is over (routes without any latency data, older result lines, are left out)
        nv = [n for n in (len(route_lat(r)[0] or []) or int(r.get("nvec", "0") if r.get("nvec", "0").isdigit() else 0)
                          for r in (clean or judged)) if n]
        if Ls and nv and all(n == dl["n"] for n in nv):
            lr = st.median(Ls) / dl["mean"]
            lrcell = "%.2f%s" % (lr, " (extrapolated period)" if dl["extrap"] else "")
            if ok and not dl["extrap"] and k not in NORATIO:
                lratios.append((lr, k))
        elif Ls:
            lrcell = "- (vectors differ: %s calls here, %d in Dynamatic's)" % (sorted(set(nv)), dl["n"])
    hd = HD.get(k)
    def _dr(rr):
        a = sum(int(r["draws"].split("/")[0]) for r in rr if "draws" in r)
        b = sum(int(r["draws"].split("/")[1]) for r in rr if "draws" in r)
        return ("%d / %d" % (a, b)) if b else "-"
    pcell = ((("fit %s (slope of call latency on trip count; no event-graph P)" if fit else "%s") % fmt_range(Pv))
             if Pv else "-")
    if Pnc:
        pcell += " [%s]" % fmt_range(Pnc)
    elif Fnc:
        pcell += " [fit %s]" % fmt_range(Fnc)
    print("| %s | %s | %d + %d / %d | %s; %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
        k, status, len(clean), len(nclean), len(rs), _dr(clean), _dr(nclean), pcell,
        ("%d" % max(lat)) if lat else "-", ("%d" % st.median(luts)) if luts else "-",
        ("%.2f (%s)" % dy[:2]) if dy else "-",
        ("%.2f%s%s" % (ratio, " (fit)" if fit else "", " (not comparable: out of the mean)" if k in NORATIO else
                       (" (Dynamatic ESTIMATED: out of the measured mean)" if "ESTIMATE" in dy[1] else "")))
        if ratio else "-",
        ("%.2f" % hd[0]) if hd else "-", lcell, dcell, lrcell))
notes = sorted({(k, v[2]) for k, v in DY.items() if k in rows})
hnotes = sorted({(k, v[1]) for k, v in HD.items() if k in rows})
if hnotes:
    print()
    print("Hand recipes (per-kernel knobs and sizes, the column the automatic path has to close): " + "; ".join("%s: %s" % kv for kv in hnotes) + ".")
if notes:
    print()
    print("Dynamatic's figures: " + "; ".join("%s: %s" % kv for kv in notes) + ".")
if any(k in DL for k in rows):
    print()
    print("Latency per call: ours includes the bench's issue, synchroniser and capture and is quantised to its clock (12 ns; "
          "a kernel that is a constant, test_int16, takes 5 host cycles = 60 ns), Dynamatic's is the kernel alone: "
          "simulated cycles per call on the same calls (dynamatic_est.py's model) x the routed period where the cell says "
          "'period measured' (research/data/suite/dynamatic/routed/), else x the ESTIMATED period "
          "(research/data/suite/dynamatic/README.md); a period extrapolated below half the calibrated range is marked "
          "and left out of the mean.")
if offP:
    print()
    print("P refused (off its route's own slope of call latency on the most executed loop's trip counts by more than %d %%: "
          "the event graph's marker was on another loop; the slope is used): " % round(PSLOPE_TOL * 100) + "; ".join(offP) + ".")
if runty:
    print()
    print("Routes whose draws had a pulse under 1 ns on a kernel handshake net (not counted as passing evidence, "
          "whatever their answers): " + "; ".join(runty) + ".")
if hostP:
    print()
    print("P refused (an exact multiple of the bench's host clock period: a host-clocked marker, not the kernel's loop): "
          + "; ".join(hostP) + ".")
def gmean(v):
    return math.exp(sum(map(math.log, v)) / len(v)) if v else None
gm_m = gmean([r for r, m, _ in ratios if m]); gm_a = gmean([r for r, _, _ in ratios])
gm_l = gmean([r for r, _ in lratios])
print()
print("%d of %d kernels attempted pass (a kernel passes when it has a judged rule-CLEAN route and every draw on every judged route, clean or not, returned every right answer; ns per iteration, latency and the ratios are over rule-CLEAN routes only, the NOT CLEAN routes' figures in brackets); %d more pass every draw only on routes the sizing loop left NOT CLEAN (UNFINISHED: the rule names a short constraint on each, and such a route can pass 4 draws and fail the model a third of the time, formal C68), not counted; geometric mean of the ratio (ns per iteration / Dynamatic's) over passing kernels with a "
      "MEASURED Dynamatic figure (n = %d): %s; including ESTIMATED figures (n = %d%s): %s. Our ns are the simulation's "
      "(about 8 %% slower per iteration than the August board on the same bitstreams, research/SIM-VS-BOARD.md); "
      "Dynamatic's measured figures are routed static timing (nextpnr's Fmax with --ignore-loops, an I/O wrapper "
      "without BRAM, mean of 4 placer seeds) x dynamatic_est.py's simulated cycles, not board runs: the two sides are "
      "measured differently. Latency per call (ours / Dynamatic's, same calls; Dynamatic's = simulated cycles x the "
      "routed period where measured, else x the ESTIMATED period; ours includes the bench): geometric mean over "
      "passing kernels (n = %d): %s."
      % (npass, nlist, nunf, sum(1 for _, m, _ in ratios if m), ("%.2f" % gm_m) if gm_m else "-",
         len(ratios), ("; %d with our figure from the latency fit" % nfit) if nfit else "", ("%.2f" % gm_a) if gm_a else "-",
         len(lratios), ("%.2f" % gm_l) if gm_l else "-"))
