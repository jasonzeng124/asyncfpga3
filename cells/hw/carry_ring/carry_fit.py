#!/usr/bin/env python3
"""carry_fit.py -- place this die in prjxray's CARRY4 and MUXF7 band from carry_ro_top's rings.

    python3 cells/hw/carry_ring/carry_fit.py PREDICTED.tsv MEASURED.tsv
    python3 cells/hw/carry_ring/carry_fit.py PREDICTED.tsv --selftest [x yc yf sigma [c_offset_ps]]
      (synthetic rings from the predicted terms; c_offset_ps adds a fixed cost to
       every carry ring -- the negative control, which must FAIL)

PREDICTED.tsv: carry_predict.py's per-ring terms of the bitstream that was run
(committed before the run).  For ring i the full-stack period is linear:
    P_i(x, yc, yf) = LO_i + x R_i + yc C_i + yf F_i
LO = FAST_MIN period, R = SLOW_MAX-FAST_MIN span of LUT + wire + site-pip arcs,
C = span of CARRY4 IOPATH arcs, F = span of SELMUX2_1 (MUXF7) IOPATH arcs --
exactly what cells/gls/gen.py annotates with GLS_SDF_FIELD=band GLS_SDF_BAND=x
GLS_SDF_BAND_CELL=CARRY4=yc,SELMUX2_1=yf (carry_predict.py --check-gen, and the
event GLS of the decoded bitstream, carry_gls.sh, agree with it to <= 15 ps).

MEASURED.tsv: carry_measure.py's per-ring table (g, b, kind, n, measured_ps,
spread).

THE FIT.  Least squares on the relative residual (m - P)/m over every ring
whose loop is all prjxray arcs (flag ok), three parameters x, yc, yf.  The L
rings carry only R, so they pin x; the C rings add C (S0->CO3 once, CIN->CO3
N-1 times); the F rings add F (MUXF7 S0->OUT once per stage).  Uncertainty:
the larger of (a) the residual scatter propagated through the normal
equations and (b) the jackknife over the 8 groups (each group is a different
placement of every kind).

IT JUDGES ITSELF.  PASS (exit 0) needs all of:
  1. >= 6 rings of every kind measured;
  2. median |residual| <= 3% (ring128 on this model: 0.76%): one x, one yc and
     one yf explain every ring;
  3. yc from the C16 rings alone and from the C32 rings alone (x and yf
     shared) agree within 3 sigma + 0.05, and yf from F8 alone vs F16 alone
     the same: the per-arc number does not depend on how many arcs are in the
     loop, which is what "a band position" means;
  4. sigma(yc) and sigma(yf) <= 0.10, so y = 0.2 and y = 1.0 are told apart;
  5. the SLOPE fit -- the same model plus a free fixed cost for every C ring
     and every F ring, so y comes from differences between chain lengths only
     -- agrees with the absolute fit within 3 sigma(slope) + 0.03.  A fixed
     cost the model misses (an extra arc at a chain's entry or exit) would
     bias the absolute fit but not the slope fit; the negative control
     (--selftest ... c_offset_ps = 500) is caught here.
Otherwise FAIL (exit 1) with the reason; a FAIL means the band model does not
describe these arcs on this die, and the y printed is not to be used.
Every ring outside its own [FAST_MIN, SLOW_MAX] period is listed (a warning:
the band model would need y outside [0, 1]).
"""
import csv
import math
import random
import statistics as st
import sys


def read(path):
    return list(csv.DictReader(open(path), delimiter="\t"))


def solve(A, b):
    """Gaussian elimination, small dense system"""
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        if abs(M[p][c]) < 1e-300:
            raise ZeroDivisionError("singular")
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def inverse(A):
    n = len(A)
    cols = [solve(A, [1.0 if i == j else 0.0 for i in range(n)]) for j in range(n)]
    return [[cols[j][i] for j in range(n)] for i in range(n)]


def fit(rows, free=("x", "yc", "yf"), fixed=None):
    """rows: dicts with lo, R, C, F, m.  Weighted (1/m) least squares on the
    free parameters; fixed: {name: value}.  -> (params, cov, residuals)"""
    fixed = fixed or {}
    col = {"x": "R", "yc": "C", "yf": "F", "oc": "IC", "of": "IF"}
    A = [[0.0] * len(free) for _ in free]
    bv = [0.0] * len(free)
    for r in rows:
        w = 1.0 / r["m"]
        y = (r["m"] - r["lo"] - sum(v * r[col[k]] for k, v in fixed.items())) * w
        a = [r[col[k]] * w for k in free]
        for i in range(len(free)):
            bv[i] += a[i] * y
            for j in range(len(free)):
                A[i][j] += a[i] * a[j]
    p = dict(zip(free, solve(A, bv)))
    p.update(fixed)
    res = [(r["m"] - pred(r, p)) / r["m"] for r in rows]
    dof = max(1, len(rows) - len(free))
    s2 = sum(e * e for e in res) / dof
    inv = inverse(A)
    cov = {k: math.sqrt(max(0.0, inv[i][i] * s2)) for i, k in enumerate(free)}
    return p, cov, res


def pred(r, p):
    return (r["lo"] + p["x"] * r["R"] + p["yc"] * r["C"] + p["yf"] * r["F"]
            + p.get("oc", 0.0) * r["IC"] + p.get("of", 0.0) * r["IF"])


def load(pred_path, meas_path=None, synth=None, seed=1):
    P = read(pred_path)
    rows, skipped = [], []
    meas = {}
    if meas_path:
        for r in read(meas_path):
            if r.get("measured_ps") not in (None, "", "nan"):
                meas[(int(r["g"]), int(r["b"]))] = float(r["measured_ps"])
    rng = random.Random(seed)
    for t in P:
        k = (int(t["g"]), int(t["b"]))
        r = dict(g=k[0], b=k[1], kind=t["kind"] + t["n"], lo=float(t["lo_ps"]), R=float(t["R_ps"]),
                 C=float(t["C_ps"]), F=float(t["F_ps"]), pmin=float(t["P_fastmin"]),
                 pmax=float(t["P_slowmax"]), flag=t["flag"],
                 IC=1.0 if t["kind"] == "C" else 0.0, IF=1.0 if t["kind"] == "F" else 0.0)
        if synth:
            x, yc, yf, sig, coff = (list(synth) + [0.0])[:5]
            r["m"] = pred(r, dict(x=x, yc=yc, yf=yf)) * (1 + sig * rng.gauss(0, 1))
            if r["kind"][0] == "C":
                r["m"] += coff      # negative control: an unmodelled fixed cost per carry ring
        elif k in meas:
            r["m"] = meas[k]
        else:
            continue
        (rows if r["flag"] == "ok" else skipped).append(r)
    return rows, skipped


def jackknife(rows):
    groups = sorted({r["g"] for r in rows})
    ests = []
    for g in groups:
        sub = [r for r in rows if r["g"] != g]
        try:
            ests.append(fit(sub)[0])
        except ZeroDivisionError:
            pass
    n = len(ests)
    out = {}
    for k in ("x", "yc", "yf"):
        v = [e[k] for e in ests]
        mu = sum(v) / n
        out[k] = math.sqrt((n - 1) / n * sum((a - mu) ** 2 for a in v))
    return out


def judge(rows, skipped, label=""):
    print("rings fitted: %d  (left out, a loop arc not from prjxray: %s)" % (
        len(rows), ", ".join("g%d.b%d %s" % (r["g"], r["b"], r["kind"]) for r in skipped) or "none"))
    why = []
    kinds = sorted({r["kind"] for r in rows} | {r["kind"] for r in skipped})
    for k in ("L8", "L16", "C1", "C4", "C16", "C32", "F8", "F16"):
        n = sum(1 for r in rows if r["kind"] == k)
        if n < 6:
            why.append("only %d %s rings" % (n, k))
    if any(sum(1 for r in rows if r["kind"] == k) < 2 for k in ("L8", "C32", "F16")):
        print("=== FAIL === too few rings to fit: %s" % "; ".join(why))
        return 1
    p, sig, res = fit(rows)
    jk = jackknife(rows)
    s = {k: max(sig[k], jk[k]) for k in sig}
    absr = sorted(abs(e) for e in res)
    print("fit: x = %.4f +- %.4f   yc (CARRY4) = %.4f +- %.4f   yf (MUXF7) = %.4f +- %.4f" % (
        p["x"], s["x"], p["yc"], s["yc"], p["yf"], s["yf"]))
    print("     (normal-equation sigma x/yc/yf %.4f/%.4f/%.4f; jackknife over groups %.4f/%.4f/%.4f)" % (
        sig["x"], sig["yc"], sig["yf"], jk["x"], jk["yc"], jk["yf"]))
    print("residual |m-P|/m: median %.2f%%, p90 %.2f%%, max %.2f%%" % (
        100 * st.median(absr), 100 * absr[int(0.9 * (len(absr) - 1))], 100 * absr[-1]))
    print()
    print("kind  n  measured_med  P(y=0.2)  P(y=1.0)  P(fit)  med_resid   [x = fitted x in every column]")
    for k in ("L8", "L16", "C1", "C4", "C16", "C32", "F8", "F16"):
        v = [(r, e) for r, e in zip(rows, res) if r["kind"] == k]
        if not v:
            continue
        med = lambda f: st.median(f(r) for r, _ in v)
        print("%-4s %2d  %10.0f  %9.0f %9.0f %7.0f  %+7.2f%%" % (
            k, len(v), med(lambda r: r["m"]),
            med(lambda r: pred(r, dict(p, yc=0.2, yf=0.2))), med(lambda r: pred(r, dict(p, yc=1.0, yf=1.0))),
            med(lambda r: pred(r, p)), 100 * st.median(e for _, e in v)))
    out = [r for r in rows + skipped if not (r["pmin"] <= r["m"] <= r["pmax"])]
    if out:
        print("WARNING: %d ring(s) outside their own [FAST_MIN, SLOW_MAX] period: %s" % (
            len(out), ", ".join("g%d.b%d %s %.0f [%.0f, %.0f]" % (r["g"], r["b"], r["kind"], r["m"], r["pmin"], r["pmax"])
                                for r in out[:6])))
    # ---- the slope fit: a free fixed cost per carry ring and per F ring ----
    # Lengths 1..32 / 8..16 give the lever arm; the fixed cost absorbs anything
    # shared by every ring of a class (an under-modelled entry / exit arc, the
    # 5 lead-in LUTs' placement next to a chain), so yc and yf here are the
    # PER-ARC band positions from differences between lengths alone.
    q, qsig, _ = fit(rows, free=("x", "yc", "yf", "oc", "of"))
    print("slope fit (free fixed cost per C / F ring): yc = %.4f +- %.4f, yf = %.4f +- %.4f, "
          "C fixed cost %+.0f +- %.0f ps, F fixed cost %+.0f +- %.0f ps" % (
              q["yc"], qsig["yc"], q["yf"], qsig["yf"], q["oc"], qsig["oc"], q["of"], qsig["of"]))
    for k in ("yc", "yf"):
        d = abs(q[k] - p[k])
        tol = 3 * qsig[k] + 0.03
        if not d <= tol:
            why.append("%s: absolute fit %.3f vs slope fit %.3f differ by %.3f (> %.3f): the rings carry a "
                       "fixed cost the model does not charge" % (k, p[k], q[k], d, tol))
        if not qsig[k] <= 0.10:
            why.append("slope sigma(%s) = %.3f > 0.10" % (k, qsig[k]))
    # ---- check 3: the per-arc number must not depend on the arc count ----
    split = {}
    for name, par, other in (("C16", "yc", None), ("C32", "yc", None), ("F8", "yf", None), ("F16", "yf", None)):
        sub = [r for r in rows if r["kind"][0] == "L" or r["kind"] == name]
        try:
            sp, ss, _ = fit(sub, free=("x", par), fixed={("yf" if par == "yc" else "yc"): 0.0})
            split[name] = (sp[par], ss[par])
        except ZeroDivisionError:
            split[name] = (float("nan"), float("inf"))
    print()
    print("split: yc from C16 only %.3f +- %.3f, C32 only %.3f +- %.3f;  yf from F8 only %.3f +- %.3f, F16 only %.3f +- %.3f" % (
        *split["C16"], *split["C32"], *split["F8"], *split["F16"]))
    for a, b_ in (("C16", "C32"), ("F8", "F16")):
        d = abs(split[a][0] - split[b_][0])
        tol = 3 * math.hypot(split[a][1], split[b_][1]) + 0.05
        if not d <= tol:
            why.append("%s vs %s disagree by %.3f (> %.3f): the per-arc delay depends on the chain length" % (a, b_, d, tol))
    if st.median(absr) > 0.03:
        why.append("median residual %.2f%% > 3%%: one band position per arc class does not explain these rings"
                   % (100 * st.median(absr)))
    for k in ("yc", "yf"):
        if not s[k] <= 0.10:
            why.append("sigma(%s) = %.3f > 0.10" % (k, s[k]))
    c32 = [r for r in rows if r["kind"] == "C32"]
    f16 = [r for r in rows if r["kind"] == "F16"]
    print()
    print("CARRY_BAND y=%.2f +-%.2f [slope fit %.2f +-%.2f] (sim, x=%.3f: C32 median %.2f ns at y=0.2, %.2f ns at y=1.0; measured %.2f ns)%s" % (
        p["yc"], s["yc"], q["yc"], qsig["yc"], p["x"], st.median(pred(r, dict(p, yc=0.2)) for r in c32) / 1000,
        st.median(pred(r, dict(p, yc=1.0)) for r in c32) / 1000, st.median(r["m"] for r in c32) / 1000, label))
    print("F7_BAND    y=%.2f +-%.2f [slope fit %.2f +-%.2f] (sim, x=%.3f: F16 median %.2f ns at y=0.2, %.2f ns at y=1.0; measured %.2f ns)%s" % (
        p["yf"], s["yf"], q["yf"], qsig["yf"], p["x"], st.median(pred(r, dict(p, yf=0.2)) for r in f16) / 1000,
        st.median(pred(r, dict(p, yf=1.0)) for r in f16) / 1000, st.median(r["m"] for r in f16) / 1000, label))
    print("LUT_BAND   x=%.3f +-%.3f (ring128, August route: 0.288)" % (p["x"], s["x"]))
    if why:
        print("=== FAIL === " + "; ".join(why))
        return 1
    print("=== PASS === (the draws' CARRY4 / F7F8 range [0.20, 1.0] can be replaced by y +- 3 sigma above)")
    return 0


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    if sys.argv[2] == "--selftest":
        a = [float(v) for v in sys.argv[3:8]] or [0.288, 0.31, 0.31, 0.01]
        rc = 0
        print("SELFTEST: synthetic rings at x=%.3f yc=%.3f yf=%.3f, %.1f%% gaussian per-ring scatter" % (
            a[0], a[1], a[2], 100 * a[3]))
        rows, sk = load(sys.argv[1], synth=a)
        rc = judge(rows, sk, label="  [synthetic]")
        return rc
    rows, sk = load(sys.argv[1], sys.argv[2])
    return judge(rows, sk)


if __name__ == "__main__":
    sys.exit(main())
