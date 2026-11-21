#!/usr/bin/env python3
"""ring128_fit.py MEASURED.tsv PRED.tsv -- the n=128 rings on their measured route against the full stack's delays.

    python3 research/tools/ring128_fit.py research/board/ro_many_aug/measured.tsv pred.tsv

PRED.tsv is cells/gls/fid/ring_predict.py ro_many_top <the route's nextpnr SDF> <xray_delay.py SDF of the same route>.
For each ring, x = (measured - FAST_MIN) / (SLOW_MAX - FAST_MIN): where silicon sits between the prjxray corners
(the full stack's --corner band is exactly this x, one number for the whole die).  Reported:
  * x over all rings and by length; the residual of ONE global x (the band model) per ring;
  * held-out tests, each fitting the median x on one part and predicting the rest, so the band is never judged on
    the rings it was fitted to: groups 0-7 -> 8-15 and back, short (7, 15) -> long (31, 63) and back, and
    leave-one-length-out;
  * the same residuals for the route's own (August, pre-lut-perm-sink) nextpnr SDF, scaled by one global factor.
Errors are (predicted / measured - 1) in percent; the pass test acceptance.py states for the band (median and every
length's median within +/-5%) is applied to each held-out prediction.
"""
import statistics as st
import sys


def pct(v, q):
    v = sorted(v)
    return v[min(len(v) - 1, max(0, int(round(q * (len(v) - 1)))))]


def main():
    meas = {}
    for ln in open(sys.argv[1]).read().splitlines()[1:]:
        g, b, n, m = ln.split("\t")[:4]
        meas["g%s.b%s" % (g, b)] = (int(g), int(n), float(m))
    rows = []
    for ln in open(sys.argv[2]).read().splitlines()[1:]:
        r, n, _, npr, f, _, s = ln.split("\t")
        g, n2, m = meas[r]
        assert int(n) == n2, r
        rows.append(dict(ring=r, g=g, n=n2, m=m, f=float(f), s=float(s), np=float(npr),
                         x=(m - float(f)) / (float(s) - float(f))))
    assert len(rows) == 128, len(rows)
    xs = [r["x"] for r in rows]
    print("rings %d; x = (measured - FAST_MIN)/(SLOW_MAX - FAST_MIN): median %.4f  p05 %.4f  p95 %.4f  min %.4f  max %.4f"
          % (len(xs), st.median(xs), pct(xs, .05), pct(xs, .95), min(xs), max(xs)))
    for n in (7, 15, 31, 63):
        v = [r["x"] for r in rows if r["n"] == n]
        print("  %2d links: median x %.4f  p05 %.4f  p95 %.4f" % (n, st.median(v), pct(v, .05), pct(v, .95)))
    inside = sum(1 for r in rows if r["f"] <= r["m"] <= r["s"])
    print("measured inside [FAST_MIN, SLOW_MAX]: %d/128" % inside)

    def judge(name, fit, test):
        x = st.median([r["x"] for r in fit])
        e = [100 * ((r["f"] + x * (r["s"] - r["f"])) / r["m"] - 1) for r in test]
        byl = {n: st.median([ei for ei, r in zip(e, test) if r["n"] == n]) for n in sorted({r["n"] for r in test})}
        ok = abs(st.median(e)) <= 5 and all(abs(v) <= 5 for v in byl.values())
        print("  %-34s fit x %.4f on %3d -> %3d rings: median %+.2f%%  p05 %+.2f  p95 %+.2f  |max| %.2f  by length %s  %s"
              % (name, x, len(fit), len(test), st.median(e), pct(e, .05), pct(e, .95), max(abs(v) for v in e),
                 " ".join("%d:%+.2f" % kv for kv in byl.items()), "PASS" if ok else "FAIL"))
    print("one global x (band model), held out:")
    judge("all -> all (in-sample, reference)", rows, rows)
    lo = [r for r in rows if r["g"] < 8]; hi = [r for r in rows if r["g"] >= 8]
    judge("groups 0-7 -> 8-15", lo, hi); judge("groups 8-15 -> 0-7", hi, lo)
    sh = [r for r in rows if r["n"] in (7, 15)]; lg = [r for r in rows if r["n"] in (31, 63)]
    judge("7,15 links -> 31,63", sh, lg); judge("31,63 links -> 7,15", lg, sh)
    for n in (7, 15, 31, 63):
        judge("all but %d links -> %d" % (n, n), [r for r in rows if r["n"] != n], [r for r in rows if r["n"] == n])
    judge("band 0.38 (the model as it was)", [dict(x=0.38)], rows)
    k = st.median([r["m"] / r["np"] for r in rows])
    e = [100 * (k * r["np"] / r["m"] - 1) for r in rows]
    print("the route's own nextpnr SDF (Aug), one global scale %.4f: median %+.2f%%  p05 %+.2f  p95 %+.2f  |max| %.2f"
          % (k, st.median(e), pct(e, .05), pct(e, .95), max(abs(v) for v in e)))
    for n in (7, 15, 31, 63):
        v = [ei for ei, r in zip(e, rows) if r["n"] == n]
        print("  %2d links: median %+.2f%%" % (n, st.median(v)))
    print("ring\tlinks\tmeasured_ps\tfastmin_ps\tslowmax_ps\tx")
    for r in rows:
        print("%s\t%d\t%.1f\t%d\t%d\t%.4f" % (r["ring"], r["n"], r["m"], r["f"], r["s"], r["x"]))


if __name__ == "__main__":
    main()
