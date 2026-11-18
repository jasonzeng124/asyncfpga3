#!/usr/bin/env python3
"""bandfit.py KERNEL X0 LOG [LOG ...] -- research/data/bandfit: ns per iteration of one August bench build at
(x = LUT + interconnect band, y = CARRY4 / SELMUX2_1 / SLICE_FFX band), against the board.
bandfit.py --cmp KERNEL LOG [LOG ...] -- the same logs side by side, per vector: latmin / latmax / result / status.
bandfit.py --lat KERNEL LOG [LOG ...] -- the same at picosecond resolution: each call's kernel latency from lat_mon.py's
LATMON lines (run1.sh LATMON=1), its difference from the first log's, and ns/iter from those latencies.
bandfit.py --xor LOG TABLE [TABLE ...] -- xorshift's archived bit against board tables of xorshift builds (see xor()).

Each LOG is run1.sh's (ps7_bench.v BENCHRES lines, FCLK 100 MHz, at band X0 with its own y in the header).
Board latmin / odata: research/data/aug_kernels/KERNEL_bench_gen_board.tsv (aug_board_vectors.py, from the logs);
gcd: research/board/aug/logs/gcd_cost.tsv (the board's cost table, same build).
FAST_MIN / SLOW_MAX per vector: research/data/aug_kernels/KERNEL_bench_gen_{min,max}.log (same build, same harness);
gcd: research/data/aug_gcd/gcd_bench_gen_aug_{min,max}.log.
Iterations from the C: collatz / collatz64 = the result (steps), ipow = bit length of e; gcd = the board table's loop
counters (k, ctz-pre, main, ctz-in): ns per main-loop iteration from the least-squares cost model of aug_cost_fit.py.
ns/iter = 10 ns x least-squares slope of latmin on iterations.  Refitted x at that y: x0 + (board - sim) / (max - min)
on the slopes (latency is linear in the band: aug_x.py's per-vector spread ~0.01); per vector the same, median.
Every simulated result is checked against the C oracle (vec/NAME.exp beside the log's vec/NAME.hex, written by
research/tools/fifteen/kernel_oracle.sh from the kernel's C) AND the board's; a batch that hung, whose two runs
disagree (mism_st bit 0) or whose result is wrong is listed and left out of the fit."""
import os, re, sys
import numpy as np
H = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(H, "..", "aug_kernels")
G = os.path.join(H, "..", "aug_gcd")
BOARD_GCD = os.path.join(H, "..", "..", "board", "aug", "logs", "gcd_cost.tsv")


def bench(path):
    out = {}
    for ln in open(path):
        if ln.startswith("BENCHRES"):
            d = dict(re.findall(r"(\w+)=(\S+)", ln))
            d["status"] = ln.split()[-1]
            out[(int(d["op0"], 16), int(d["op1"], 16))] = d
    return out


def board_of(k):
    """(op0, op1) -> (board latmin, board result, loop counters or None)"""
    b = {}
    if k == "gcd":
        for ln in open(BOARD_GCD).read().splitlines()[1:]:
            f = ln.split("\t")
            b[(int(f[0]), int(f[1]))] = (int(f[8]), int(f[6]), [int(v) for v in f[2:6]])
    else:
        for ln in list(open(f"{D}/{k}_bench_gen_board.tsv"))[1:]:
            f = ln.split("\t")
            b[(int(f[0]), int(f[1]))] = (int(f[2]), int(f[4]), None)
    return b


def corners(k):
    """FAST_MIN / SLOW_MAX runs of the same build; a batch that did not complete, whose runs disagree (mism_st bit 0)
    or differ by more than 3 cycles (the August harness's latch race: 10 of gcd's 24 at SLOW_MAX) is left out"""
    def clean(r):
        return {v: d for v, d in r.items() if d["status"] == "DONE" and d["completed"] == d["n"]
                and not int(d["mism_st"], 16) & 1 and int(d["latmax"]) - int(d["latmin"]) <= 3}
    if k == "gcd":
        return clean(bench(f"{G}/gcd_bench_gen_aug_min.log")), clean(bench(f"{G}/gcd_bench_gen_aug_max.log"))
    return clean(bench(f"{D}/{k}_bench_gen_min.log")), clean(bench(f"{D}/{k}_bench_gen_max.log"))


def oracle(lg):
    """the C oracle's results for the log's vector file: vec/NAME.exp beside vec/NAME.hex"""
    hdr = open(lg).readline()
    vec = re.search(r"vec=(\S+)", hdr).group(1)
    hx = os.path.join(H, "vec", vec)
    ex = hx[:-4] + ".exp"
    if not os.path.exists(ex):
        sys.exit("bandfit.py: no oracle %s (research/tools/fifteen/kernel_oracle.sh KERNEL < %s > %s)" % (ex, hx, ex))
    vs = [tuple(int(w, 16) for w in ln.split()) for ln in open(hx) if ln.strip()]
    es = [int(ln, 16) for ln in open(ex) if ln.strip()]
    assert len(vs) == len(es), (hx, ex)
    return dict(zip(vs, es))


def check(d, exp, bo):
    """'' if the batch is right, else why not"""
    why = []
    if d["status"] != "DONE" or d["completed"] != d["n"]:
        why.append("HANG (completed %s/%s)" % (d["completed"], d["n"]))
    if int(d["mism_st"], 16) & 1:
        why.append("runs disagree (mism_st %s)" % d["mism_st"])
    od = int(d["odata"], 16)
    if exp is None or od != exp & 0xFFFFFFFF:
        why.append("odata %08x != C %s" % (od, "?" if exp is None else "%08x" % (exp & 0xFFFFFFFF)))
    if bo is not None and od != bo & 0xFFFFFFFF:
        why.append("odata %08x != board %08x" % (od, bo & 0xFFFFFFFF))
    return "; ".join(why)


def iters(k, a, b, od):
    return od if k.startswith("collatz") else b.bit_length()


def slope(k, rows, col):
    """ns per iteration from rows (iters-or-counters, values)"""
    if k == "gcd":   # base + per k + per ctz-pre + per main + per ctz-in; return the main-loop cost
        A = np.array([[1.0] + list(r[0]) for r in rows]); y = np.array([10.0 * r[col] for r in rows])
        if len(rows) < 6:
            return float("nan")
        return np.linalg.lstsq(A, y, rcond=None)[0][3]
    it = np.array([r[0] for r in rows], float)
    if len(rows) < 2:
        return float("nan")
    return 10 * np.polyfit(it, [r[col] for r in rows], 1)[0]


def fit(k, x0, logs):
    board = board_of(k)
    mn, mx = corners(k)
    for lg in logs:
        hdr = open(lg).readline().strip()
        y = re.search(r"y=(\S+)", hdr).group(1)
        r = bench(lg); ex = oracle(lg); bad = []; X = []
        for v, d in sorted(r.items(), key=lambda t: board[t[0]][0]):
            bl, bo, cnt = board[v]
            why = check(d, ex.get(v), bo)
            if why:
                bad.append("%s: %s" % (v, why)); continue
            # sim latmin in the board's 10 ns counts (a run with the bench at another aclk, e.g. 25 MHz, is rescaled)
            X.append((tuple(cnt) if k == "gcd" else iters(k, *v, bo), bl, int(d["latmin"]) * int(d["fclk_ps"]) / 10000.0,
                      int(mn[v]["latmin"]) if v in mn else None, int(mx[v]["latmin"]) if v in mx else None))
        print("%s y=%s: %d vectors, %d right, %d wrong/hung   [%s]" % (k, y, len(r), len(X), len(bad), hdr[2:]))
        if any(d["fclk_ps"] != "10000" for d in r.values()):
            print("   NOTE: bench aclk is not 100 MHz: its fixed synchroniser overhead is larger, so only the slope (ns/iter)\n"
                  "   and the LATMON picoseconds compare with the board; the x refit and the summed latency do not.")
        for b in bad:
            print("   WRONG", b)
        if len(X) >= 2:
            sb = slope(k, X, 1); ss = slope(k, X, 2)
            full = [t for t in X if t[3] is not None and t[4] is not None]
            smin, smax = slope(k, full, 3), slope(k, full, 4)
            sb_f, ss_f = slope(k, full, 1), slope(k, full, 2)
            xs = x0 + (sb_f - ss_f) / (smax - smin)
            xv = [x0 + (t[1] - t[2]) / (t[4] - t[3]) for t in full if t[1] >= 50]
            print("   ns/iter board %.2f sim %.2f (%+.2f%%) | refit x: slope %.4f, per-vector median %.4f (%.4f-%.4f, "
                  "%d vec >= 50 cyc; slope on %d vec with both corners: FAST_MIN %.2f SLOW_MAX %.2f)" % (
                      sb, ss, 100 * (ss / sb - 1), xs, np.median(xv) if xv else float("nan"),
                      min(xv) if xv else 0, max(xv) if xv else 0, len(xv), len(full), smin, smax))
            print("   summed latmin over the %d right vectors: sim / board = %.0f / %d (%+.2f%%)" % (
                len(X), sum(t[2] for t in X), sum(t[1] for t in X), 100 * (sum(t[2] for t in X) / sum(t[1] for t in X) - 1)))
            print("   iters/board/sim:", " ".join(("%s:%d/%g" % ((t[0] if k != "gcd" else "-".join(map(str, t[0]))),
                                                                 t[1], t[2])) for t in X))
        summ = re.search(r"BENCHSUMMARY.*", open(lg).read())
        print("   ", summ.group(0) if summ else "NO BENCHSUMMARY (run cut?)")


def cmp(k, logs):
    board = board_of(k)
    R = [(re.search(r"y=(\S+)", open(lg).readline()).group(1), bench(lg), oracle(lg)) for lg in logs]
    keys = sorted(set().union(*[set(r[1]) for r in R]), key=lambda v: board[v][0] if v in board else 0)
    print("%-22s %6s  %s" % ("op0,op1", "board", "  ".join("%-24s" % ("y=" + y) for y, _, _ in R)))
    for v in keys:
        cells = []
        for y, r, ex in R:
            if v not in r:
                cells.append("%-24s" % "-"); continue
            d = r[v]; why = check(d, ex.get(v), board[v][1] if v in board else None)
            u = "" if d["fclk_ps"] == "10000" else "x%gns" % (int(d["fclk_ps"]) / 1000.0)
            cells.append("%-24s" % ("%s-%s%s %s" % (d["latmin"], d["latmax"], u, "ok" if not why else "BAD:" + why[:40])))
        print("%-22s %6s  %s" % ("%x,%x" % v, board[v][0] if v in board else "-", "  ".join(cells)))
    same = all(R[0][1].get(v, {}).get("latmin") == r.get(v, {}).get("latmin") for _, r, _ in R for v in keys)
    print("latmin identical in every log for every vector:", same)


def latmon(lg):
    """LATMON lines (lat_mon.py) -> {vector: [lat_ps of each run]}: the bench runs NRUNS calls per batch, in order"""
    txt = open(lg).read()
    lats = [int(v) for v in re.findall(r"^LATMON n=\d+ lat_ps=(\d+)", txt, re.M)]
    res = [ln for ln in txt.splitlines() if ln.startswith("BENCHRES")]
    out, i = {}, 0
    for ln in res:
        d = dict(re.findall(r"(\w+)=(\S+)", ln))
        n = int(d["completed"])
        out[(int(d["op0"], 16), int(d["op1"], 16))] = lats[i:i + n]
        i += n
    return out, len(lats), i


def lat(k, logs):
    """per-call kernel latency in ps (LATMON), per vector, each log against the first; ns/iter from the ps latencies"""
    board = board_of(k)
    R = []
    for lg in logs:
        y = re.search(r"y=(\S+)", open(lg).readline()).group(1)
        L, nl, nc = latmon(lg)
        if nl != nc:
            print("   %s: %d LATMON lines for %d completed calls -- not paired, skipped" % (lg, nl, nc)); continue
        R.append((y, L, bench(lg), oracle(lg)))
    if not R:
        return
    y0, L0, r0, ex0 = R[0]
    print("%-22s %s" % ("op0,op1", "  ".join("%-26s" % ("y=%s lat_ps (d vs y=%s)" % (y, y0)) for y, _, _, _ in R)))
    for v in sorted(L0, key=lambda v: board[v][0] if v in board else 0):
        cells = []
        for y, L, r, ex in R:
            a = L.get(v, [])
            why = check(r[v], ex.get(v), board[v][1] if v in board else None) if v in r else "missing"
            d = ["%+d" % (u - w) for u, w in zip(a, L0.get(v, []))]
            cells.append("%-26s" % ("%s (%s)%s" % ("/".join(map(str, a)), "/".join(d), "" if not why else " BAD")))
        print("%-22s %s" % ("%x,%x" % v, "  ".join(cells)))
    if k != "gcd":
        for y, L, r, ex in R:
            pts = [(iters(k, *v, board[v][1]), a[0]) for v, a in L.items() if a and v in board and
                   not check(r[v], ex.get(v), board[v][1]) and (not k.startswith("collatz") or board[v][0] >= 50)]
            if len(pts) >= 2:
                it = np.array([p[0] for p in pts], float)
                print("   y=%s: ns/iter from the first call's lat_ps, %d vectors: %.3f" % (
                    y, len(pts), np.polyfit(it, [p[1] / 1000.0 for p in pts], 1)[0]))


def xor(lg, tables):
    """xorshift: the archived August bit's simulated latency per rounds against board tables of xorshift builds
    (cells/hw/xorshift_cost_*.tsv: rounds cycles latmin latmax result, FIXED N=200, 100 MHz); ns per round = 10 x the
    least-squares slope of latmin on rounds >= 8.  No corner runs exist for this build, so no x is fitted: the question
    is only which measured build, if any, the archived bit behaves like."""
    r = bench(lg); ex = oracle(lg)
    sim = {}
    for v, d in r.items():
        why = check(d, ex.get(v), None)
        print("   rounds %3d: sim latmin %4s latmax %4s  %s" % (v[1], d["latmin"], d["latmax"], why or "right (C oracle)"))
        if not why:
            sim[v[1]] = int(d["latmin"])
    lat = {k: v for k, v in latmon(lg)[0].items()}

    def slope(m):
        rr = sorted(k for k in m if k >= 8)
        return 10 * np.polyfit(rr, [m[k] for k in rr], 1)[0] if len(rr) >= 2 else float("nan")
    ss = slope(sim)
    lp = {v[1]: a[0] for v, a in lat.items() if a}
    print("sim (%s): %d right of %d; ns/round %.2f by latmin%s" % (os.path.basename(lg), len(sim), len(r), ss,
          "; %.3f by LATMON ps" % (np.polyfit(sorted(k for k in lp if k >= 8), [lp[k] / 1000.0 for k in sorted(k for k in lp if k >= 8)], 1)[0]) if lp else ""))
    for t in tables:
        b = {}
        for ln in open(t):
            f = ln.split()
            if f and f[0].isdigit():
                b[int(f[0])] = int(f[2])
        common = [k for k in sim if k in b]
        sb = slope(b)
        print("   %-48s ns/round %.2f; sim / board %.3f; latmin sim - board on %d common rounds: %s" % (
            os.path.basename(t), sb, ss / sb, len(common), " ".join("%d:%+d" % (k, sim[k] - b[k]) for k in sorted(common))))


if __name__ == "__main__":
    if sys.argv[1] == "--xor":
        xor(sys.argv[2], sys.argv[3:]); sys.exit()
    if sys.argv[1] == "--cmp":
        cmp(sys.argv[2], sys.argv[3:])
    elif sys.argv[1] == "--lat":
        lat(sys.argv[2], sys.argv[3:])
    else:
        fit(sys.argv[1], float(sys.argv[2]), sys.argv[3:])
