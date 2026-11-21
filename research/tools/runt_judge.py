#!/usr/bin/env python3
"""runt_judge.py MEASURED_TSV PREDICTED_TSV [--margin-ps N] -- where does a
C-element LUT loop stop capturing, against its own predicted loop delay?

    python3 research/tools/runt_judge.py cells/build/hw/runt_top/runt_measured.tsv \
        research/board/runt/predicted.tsv; echo "exit $?"

MEASURED_TSV: cells/hw/runt_measure.py's output (instance k ones
multi_edge_trials trials kind ... emit late raw; a '# rig OK|FAIL ...' line
first).  PREDICTED_TSV: instance, w_fastmin_ps, w_slowmax_ps, w_band_ps,
loop_band_ps -- the episode width at the CE LUT's pins (t(b) - t(a)) at the
two prjxray corners and at the band point, and the instance's own loop delay
(I0 -> O -> I2 back to the LUT) at the band point, from this build's routed
SDF.  One row per instance; extra columns are ignored.

What it reports, over the TEST instances only:

  the capture threshold w*: the w at which an isotonic (monotone
  non-decreasing, trial-weighted) fit of ones/trials against predicted w
  crosses 0.5, with the 0.1 .. 0.9 transition band -- once with w_band_ps,
  and again with each corner column, so the corner spread of the PREDICTION
  shows up as a spread of w*;

  the same threshold in x = w_band - loop_band, each instance against its own
  loop.  The zero-inertia (transport) picture puts the capture edge at x = 0:
  the fed-back q must reach I2 before b does.  A runt-killing fabric moves it;

  every instance with a multi-edge trial, with its predicted w and x.

Exit 0 only if (1) the rig's controls passed -- the '# rig OK' line AND a
recheck here of every NEG (all zero) and LONG (ones = trials, multi = 0) and
PULSE (ones = multi = 0) row, (2) at least 90% of TEST rows have a prediction,
and (3) the data is monotone enough to name a threshold: at least two TEST
instances captured cleanly (ones/T >= 0.9) and two rejected cleanly (<= 0.1),
fewer than 5% of (clean-capture, clean-reject) pairs are INVERTED (the capture
predicted shorter than the reject by more than --margin-ps, default 50), and
the fit crosses 0.5 inside the measured range.  Prints "=== PASS: ... ===" or
"=== FAIL: ... ===".
"""
import statistics as st
import sys


def read_tsv(path):
    head, rows, comments = None, [], []
    for ln in open(path).read().splitlines():
        if not ln.strip():
            continue
        if ln.startswith("#"):
            comments.append(ln)
            continue
        f = ln.split("\t")
        if head is None:
            head = f
            continue
        rows.append(dict(zip(head, f)))
    return head or [], rows, comments


def isotonic(xs, ys, ws):
    """Pool-adjacent-violators, non-decreasing; xs already sorted."""
    blocks = []                                  # [sum_wy, sum_w, n]
    for y, w in zip(ys, ws):
        blocks.append([y * w, w, 1])
        while len(blocks) > 1 and (blocks[-2][0] / blocks[-2][1]
                                   > blocks[-1][0] / blocks[-1][1]):
            a = blocks.pop()
            blocks[-1][0] += a[0]
            blocks[-1][1] += a[1]
            blocks[-1][2] += a[2]
    fit = []
    for swy, sw, n in blocks:
        fit += [swy / sw] * n
    return fit


def crossing(xs, fit, level):
    """First x where the fitted curve reaches `level`, interpolated linearly
    between the last point below and the first point at or above it."""
    for j, v in enumerate(fit):
        if v >= level:
            if j == 0:
                return None if fit[0] > level else xs[0]
            x0, x1, v0 = xs[j - 1], xs[j], fit[j - 1]
            return x0 + (x1 - x0) * (level - v0) / (v - v0) if v != v0 else x1
    return None


def kendall(xs, ys):
    c = d = 0
    for a in range(len(xs)):
        for b in range(a + 1, len(xs)):
            s = (xs[a] - xs[b]) * (ys[a] - ys[b])
            c += s > 0
            d += s < 0
    return (c - d) / (c + d) if c + d else 0.0


def threshold(points, label):
    """points: [(w, frac, trials)] -> (w*, w10, w90) or None, printed."""
    pts = sorted(points)
    xs = [p[0] for p in pts]
    fit = isotonic(xs, [p[1] for p in pts], [p[2] for p in pts])
    w50, w10, w90 = (crossing(xs, fit, v) for v in (0.5, 0.1, 0.9))
    fmt = lambda v: "none" if v is None else "%+.0f" % v
    print("  %-24s 0.5 at %s ps   (0.1 .. 0.9 band %s .. %s)" % (label, fmt(w50), fmt(w10), fmt(w90)))
    if w50 is not None and (fit[0] >= 0.5 or fit[-1] < 0.5):
        w50 = None                    # crossing pinned at an end: not inside
    return w50, w10, w90


def main():
    import argparse
    ap = argparse.ArgumentParser(usage=__doc__.split("\n\n")[0])
    ap.add_argument("measured")
    ap.add_argument("predicted")
    ap.add_argument("--margin-ps", type=float, default=50.0)
    ns = ap.parse_args()
    args, margin = [ns.measured, ns.predicted], ns.margin_ps
    _, meas, comments = read_tsv(args[0])
    _, pred, _ = read_tsv(args[1])
    why = []

    # ---- (1) the rig ------------------------------------------------------
    rig = [c for c in comments if c.startswith("# rig ")]
    if not rig or not rig[0].startswith("# rig OK"):
        why.append("measured TSV is not from a RIG OK run (%s)" % (rig[0][:60] if rig else "no rig line"))
    bad = []
    for r in meas:
        n, o, mu = int(r["trials"]), int(r["ones"]), int(r["multi_edge_trials"])
        e = int(r.get("emit", o))
        la = int(r.get("late", 0))
        kd = r.get("kind", "TEST")
        if kd == "NEG" and (o or mu or e or la):
            bad.append(r["instance"])
        elif kd == "LONG" and (o != n or mu or la):
            bad.append(r["instance"])
        elif kd == "PULSE" and (o or mu or la):
            bad.append(r["instance"])
    if bad:
        why.append("control row(s) wrong: %s" % ",".join(bad[:8]))
    print("rig       %s; controls rechecked here: %s" % (
        rig[0][6:60] if rig else "?", "ok" if not bad else "%d WRONG" % len(bad)))

    # ---- (2) the join -----------------------------------------------------
    P = {}
    for r in pred:
        try:
            P[r["instance"]] = dict(lo=float(r["w_fastmin_ps"]), hi=float(r["w_slowmax_ps"]),
                                    w=float(r["w_band_ps"]), loop=float(r["loop_band_ps"]))
        except (KeyError, ValueError):
            continue
    test = [r for r in meas if r.get("kind", "TEST") == "TEST" and int(r["trials"]) > 0]
    have = [r for r in test if r["instance"] in P]
    print("join      %d TEST rows measured, %d with a prediction" % (len(test), len(have)))
    if not test or len(have) < 0.9 * len(test):
        why.append("only %d of %d TEST rows have a prediction" % (len(have), len(test)))
    if not have:
        print("=== FAIL: %s ===" % "; ".join(why or ["nothing to judge"]))
        sys.exit(1)

    pts = []
    for r in have:
        p = P[r["instance"]]
        n = int(r["trials"])
        pts.append(dict(i=r["instance"], k=r["k"], n=n, f=int(r["ones"]) / n,
                        mu=int(r["multi_edge_trials"]), la=int(r.get("late", 0)),
                        e=int(r.get("emit", 0)), **p))

    # ---- (3) monotone enough? -------------------------------------------
    hi = [q for q in pts if q["f"] >= 0.9]
    lo = [q for q in pts if q["f"] <= 0.1]
    inv = sum(1 for a in hi for b in lo if a["w"] < b["w"] - margin)
    pairs = len(hi) * len(lo)
    tau = kendall([q["w"] for q in pts], [q["f"] for q in pts])
    print("monotone  %d clean captures, %d clean rejects, %d of %d pairs inverted "
          "by > %.0f ps; Kendall tau(w_band, ones/T) %+.2f" % (len(hi), len(lo), inv, pairs, margin, tau))
    if len(hi) < 2 or len(lo) < 2:
        why.append("need >= 2 clean captures and >= 2 clean rejects (have %d, %d)" % (len(hi), len(lo)))
    elif inv > 0.05 * pairs:
        why.append("%d of %d clean pairs inverted -- capture does not order by predicted w" % (inv, pairs))
        shown = 0
        for a in hi:
            for b in lo:
                if a["w"] < b["w"] - margin and shown < 5:
                    shown += 1
                    print("    inverted: inst %s captured %.2f at w %.0f, inst %s rejected %.2f at w %.0f"
                          % (a["i"], a["f"], a["w"], b["i"], b["f"], b["w"]))

    # ---- the threshold ------------------------------------------------------
    print("\ncapture threshold (isotonic fit of ones/trials crosses 0.5):")
    w50, _, _ = threshold([(q["w"], q["f"], q["n"]) for q in pts], "w_band_ps")
    threshold([(q["lo"], q["f"], q["n"]) for q in pts], "w_fastmin_ps")
    threshold([(q["hi"], q["f"], q["n"]) for q in pts], "w_slowmax_ps")
    x50, _, _ = threshold([(q["w"] - q["loop"], q["f"], q["n"]) for q in pts],
                          "x = w_band - loop_band")
    loops = [q["loop"] for q in pts]
    print("  loop_band_ps over TEST instances: median %.0f, range %.0f .. %.0f"
          % (st.median(loops), min(loops), max(loops)))
    if w50 is None:
        why.append("the capture fraction does not cross 0.5 inside the measured w range")
    else:
        print("  w* - median loop = %+.0f ps" % (w50 - st.median(loops)))
    if x50 is not None:
        print("  x* = %+.0f ps: the zero-inertia (transport) picture puts the capture "
              "edge at x = 0" % x50)

    # ---- multi-edge instances ---------------------------------------------
    multi = sorted((q for q in pts if q["mu"]), key=lambda q: q["w"])
    print("\nmulti-edge TEST instances (>= 2 rising edges in >= 1 trial): %d" % len(multi))
    if multi:
        print("  %5s %3s %8s %8s %8s %8s %8s  %7s %7s %7s" % (
            "inst", "k", "w_fmin", "w_band", "w_smax", "loop", "x", "multi", "late", "ones"))
        for q in multi:
            print("  %5s %3s %8.0f %8.0f %8.0f %8.0f %+8.0f  %7.3f %7.3f %7.3f" % (
                q["i"], q["k"], q["lo"], q["w"], q["hi"], q["loop"], q["w"] - q["loop"],
                q["mu"] / q["n"], q["la"] / q["n"], q["f"]))

    if why:
        print("\n=== FAIL: %s ===" % "; ".join(why))
        sys.exit(1)
    print("\n=== PASS: w* = %+.0f ps (band), x* = %s ps, %d multi-edge instance(s) ==="
          % (w50, "none" if x50 is None else "%+.0f" % x50, len(multi)))
    sys.exit(0)


if __name__ == "__main__":
    main()
