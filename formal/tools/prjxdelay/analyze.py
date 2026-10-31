#!/usr/bin/env python3
"""Compare ringdelay.py's prjxray periods with the SDF and with silicon.

    python3 formal/tools/prjxdelay/analyze.py build/ro_many_top_s*/prjx.json -- build/ro_top_s*/prjx.json

The per-ring silicon data (build/hw/ro_many_top/raw/gNN.log) is NOT in the tree
and the measured routes cannot be rebuilt (different nextpnr binary; see the
notes), so silicon enters only as what cells/hw/README.md records:
  * ro_many_top, 128 rings, measured/SDF per length: median, p90, p99, max;
    the 2-parameter fit measured = 0.9383 * SDF + 988 ps;
  * ro_top, two routes x 5 rings: measured period and SDF period per ring.
Every comparison below is therefore population-level (same design, same flow,
different routes), never ring-by-ring.
"""
import json
import statistics as st
import sys

# cells/hw/README.md, "The population, 2026-08-23"
SIL_MANY = {7: dict(med=1.176, p90=1.438, p99=1.470, mx=1.470),
            15: dict(med=0.987, p90=1.117, p99=1.203, mx=1.203),
            31: dict(med=0.959, p90=1.085, p99=1.142, mx=1.142),
            63: dict(med=0.969, p90=1.059, p99=1.134, mx=1.134)}
SIL_MIN7 = 0.773
# cells/hw/README.md, ro_top tables (links, measured ps, SDF ps)
SIL_TOP = {"2026-08-03": [(7, 8093, 8290), (15, 12204, 13576), (31, 22924, 24842),
                          (63, 52075, 56784), (127, 103094, 103418)],
           "2026-08-18": [(7, 6293, 4674), (15, 12140, 12008), (31, 27784, 28228),
                          (63, 54772, 55548), (127, 103409, 112972)]}
DEN = "sdf_period_ps"
C = ["fast_min", "fast_max", "slow_min", "slow_max"]


def q(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(p * (len(xs) - 1))))]


def linfit(x, y):
    mx, my = st.mean(x), st.mean(y)
    b = sum((a - mx) * (c - my) for a, c in zip(x, y)) / sum((a - mx) ** 2 for a in x)
    return b, my - b * mx


def spearman(x, y):
    def rank(v):
        o = sorted(range(len(v)), key=lambda i: v[i])
        r = [0] * len(v)
        for k, i in enumerate(o):
            r[i] = k
        return r
    rx, ry = rank(x), rank(y)
    return st.correlation(rx, ry)


def load(paths):
    out = []
    for p in paths:
        j = json.load(open(p))
        name = p.split("/")[-2]
        for r in j["rings"]:
            r["route"] = name
            out.append(r)
    return out


def main():
    args = sys.argv[1:]
    global DEN
    if args and args[0] == "--prepatch":
        DEN = "sdf_prepatch_period_ps"
        args = args[1:]
        print("#### denominator: the PRE-PATCH SDF (emulated; what silicon was compared against) ####")
    else:
        print("#### denominator: the CURRENT SDF (lut-perm-sink patched) ####")
    k = args.index("--") if "--" in args else len(args)
    many, top = load(args[:k]), load(args[k + 1:])
    routes = sorted({r["route"] for r in many})

    print("== ro_many_top: model / SDF per length (all routes pooled; per-route medians in []) ==")
    print("links  n   SDF_med  " + "  ".join(f"{c}/SDF med" for c in C) + "   silicon/SDF med p90 max")
    for L in (7, 15, 31, 63):
        rs = [r for r in many if r["links"] == L]
        line = f"{L:5d} {len(rs):3d} {st.median(r[DEN] for r in rs):8.0f}  "
        for i in range(4):
            v = [r["prjx_period_ps"][i] / r[DEN] for r in rs]
            line += f"{st.median(v):12.3f}       "
        s = SIL_MANY[L]
        line += f"{s['med']:.3f} {s['p90']:.3f} {s['mx']:.3f}"
        print(line)
    print("per-route median slow_max/SDF by length:")
    for rt in routes:
        print("  %-24s " % rt + "  ".join(
            "%d:%.3f" % (L, st.median(r["prjx_period_ps"][3] / r[DEN]
                                      for r in many if r["route"] == rt and r["links"] == L))
            for L in (7, 15, 31, 63)))

    # Shape test.  If the prjxray model explained the silicon residual, then
    # silicon/SDF (per length) should look like s * model/SDF for ONE global
    # scale s (a die sits at one place in the corner band).  Pick s so the
    # pooled medians agree, then compare per length.
    print("\n== shape: does s * (model/SDF) reproduce silicon/SDF per length? ==")
    sil_all_med = 0.989
    for i, c in enumerate(C):
        allv = [r["prjx_period_ps"][i] / r[DEN] for r in many]
        s = sil_all_med / st.median(allv)
        row = []
        for L in (7, 15, 31, 63):
            v = [s * r["prjx_period_ps"][i] / r[DEN] for r in many if r["links"] == L]
            row.append(f"{L}: med {st.median(v):.3f} p90 {q(v, .9):.3f} max {max(v):.3f} min {min(v):.3f}")
        print(f"{c:9s} s={s:.3f}  " + " | ".join(row))
    print("silicon             " + " | ".join(f"{L}: med {v['med']:.3f} p90 {v['p90']:.3f} max {v['mx']:.3f}"
                                         for L, v in SIL_MANY.items()) + f"  (7-link min {SIL_MIN7})")

    # spread: model's per-route scatter vs the SDF, after the per-length median
    print("\n== spread of model/SDF within a length (p90/med, max/med, min/med); silicon p90/med, max/med ==")
    for L in (7, 15, 31, 63):
        v = [r["prjx_period_ps"][3] / r[DEN] for r in many if r["links"] == L]
        m = st.median(v)
        s = SIL_MANY[L]
        print(f"{L:3d}: model {q(v, .9) / m:.3f} {max(v) / m:.3f} {min(v) / m:.3f}   silicon "
              f"{s['p90'] / s['med']:.3f} {s['mx'] / s['med']:.3f} {SIL_MIN7 / s['med'] if L == 7 else float('nan'):.3f}")

    # two-parameter fit of the model against the SDF, same form as the README's
    print("\n== model = a * SDF + b (all ro_many rings, all routes); silicon: 0.9383 * SDF + 988 ==")
    x = [r[DEN] for r in many]
    for i, c in enumerate(C):
        a, b = linfit(x, [r["prjx_period_ps"][i] for r in many])
        print(f"{c:9s} a={a:.4f}  b={b:+.0f} ps   b/a={b / a:+.0f} ps")

    # pin-delay difference vs model residual against the SDF
    print("\n== where the model differs from the SDF (slow_max, per ring, x2 traversals) ==")
    for L in (7, 15, 31, 63):
        rs = [r for r in many if r["links"] == L]
        sp = [r["slowmax_components_ps"]["site_pin"] - 2 * len(r["stages"]) * 25 for r in rs]
        rc = [r["slowmax_components_ps"]["rc"] for r in rs]
        res = [r["prjx_period_ps"][3] - r[DEN] for r in rs]
        rel = [r["prjx_period_ps"][3] / r[DEN] for r in rs]
        print(f"{L:3d}: model-SDF med {st.median(res):6.0f} ps; site-pin excess over 25 ps/pin med "
              f"{st.median(sp):6.0f} ps; RC med {st.median(rc):5.0f} ps; "
              f"spearman(site-pin excess / SDF, model/SDF) = "
              f"{spearman([a / r[DEN] for a, r in zip(sp, rs)], rel):+.2f}")
    allpins = [p for r in many for p in r["pins"]]
    print("physical pin use (all ring stages): " + " ".join(
        f"A{k}:{allpins.count('A%d' % k)}" for k in range(1, 7)))

    if top:
        print("\n== ro_top: re-routed model vs the two measured routes ==")
        print("route              ring links  SDF   fmin   fmax   smin   smax  smax/SDF")
        for r in top:
            p = r["prjx_period_ps"]
            print(f"{r['route']:18s} {r['ring']:4d} {r['links']:5d} {r[DEN]:6d} " +
                  " ".join(f"{x:6.0f}" for x in p) + f"  {p[3] / r[DEN]:.3f}")
        print("measured routes (README):")
        for k, rows in SIL_TOP.items():
            print("  " + k + ": " + "  ".join(f"{L}:{m}/{s}={m / s:.3f}" for L, m, s in rows))
        # ring 0 of the 2026-08-18 route: SDF 4674, measured 6293.  Its route is
        # gone; regress the model on the SDF over every 7-link ring we routed
        # (ro_top ring 0 and ro_many 7-link) and read the model at SDF = 4674.
        r7 = [r for r in many + top if r["links"] == 7]
        x7 = [r[DEN] for r in r7]
        print(f"\n== ring 0 (2026-08-18 route: SDF 4674, measured 6293): 7-link rings here have SDF "
              f"{min(x7)}..{max(x7)} ps (n={len(r7)}) ==")
        for i, c in enumerate(C):
            a, b = linfit(x7, [r["prjx_period_ps"][i] for r in r7])
            at = a * 4674 + b
            print(f"{c:9s} model = {a:.3f}*SDF {b:+.0f}  -> at SDF 4674: {at:6.0f} ps "
                  f"(measured/model {6293 / at:.3f}); at SDF 8290: {a * 8290 + b:6.0f} "
                  f"(measured 8093, ratio {8093 / (a * 8290 + b):.3f})")
        mins = [r[DEN] / (2 * r["n_luts"]) for r in r7]
        print(f"SDF per stage traversal, 7-link rings here: {min(mins):.0f}..{max(mins):.0f} ps; "
              f"the 2026-08-18 ring 0: {4674 / 16:.0f} ps")


if __name__ == "__main__" and "--extra" not in sys.argv:
    main()


def extra(paths_many, paths_top):
    """Decomposition: how much of the model-vs-pre-patch-SDF shape is the
    patch alone (current SDF / pre-patch SDF) and how much is prjxray on top
    (model / current SDF).  And ring 0 near its own pre-patch SDF."""
    many, top = load(paths_many), load(paths_top)
    sil_med = 0.989
    print("\n== decomposition, against the pre-patch SDF, one global scale each ==")
    for name, num in (("current SDF (patch only)", lambda r: r["sdf_period_ps"]),
                      ("prjxray slow_max", lambda r: r["prjx_period_ps"][3]),
                      ("prjxray fast_max", lambda r: r["prjx_period_ps"][1])):
        allv = [num(r) / r["sdf_prepatch_period_ps"] for r in many]
        s = sil_med / st.median(allv)
        row = []
        for L in (7, 15, 31, 63):
            v = [s * num(r) / r["sdf_prepatch_period_ps"] for r in many if r["links"] == L]
            row.append(f"{L}: med {st.median(v):.3f} p90/med {q(v, .9) / st.median(v):.3f}")
        x = [r["sdf_prepatch_period_ps"] for r in many]
        a, b = linfit(x, [num(r) for r in many])
        print(f"{name:26s} " + " | ".join(row) + f" | fit b/a {b / a:+.0f} ps")
    print("silicon                    " + " | ".join(
        f"{L}: med {v['med']:.3f} p90/med {v['p90'] / v['med']:.3f}" for L, v in SIL_MANY.items())
          + " | fit b/a +1053 ps")
    # ring 0: rings here whose pre-patch SDF is near 4674
    r7 = [r for r in many + top if r["links"] == 7]
    near = [r for r in r7 if abs(r["sdf_prepatch_period_ps"] - 4674) <= 700]
    print(f"\n== ring 0: 7-link rings here with pre-patch SDF within 700 ps of 4674 (n={len(near)}) ==")
    allv = [r["prjx_period_ps"][3] / r["sdf_prepatch_period_ps"] for r in many]
    s_sm = sil_med / st.median(allv)
    allc = [r["sdf_period_ps"] / r["sdf_prepatch_period_ps"] for r in many]
    s_c = sil_med / st.median(allc)
    for r in sorted(near, key=lambda r: r["sdf_prepatch_period_ps"]):
        print(f"  {r['route']:22s} {str(r['ring']):8s} prepatch {r['sdf_prepatch_period_ps']:5d} "
              f"current {r['sdf_period_ps']:5d} slow_max {r['prjx_period_ps'][3]:6.0f}  "
              f"pred(silicon) = s*model: prjx {s_sm * r['prjx_period_ps'][3]:5.0f}  "
              f"current-SDF {s_c * r['sdf_period_ps']:5.0f}  prepatch-SDF {sil_med * r['sdf_prepatch_period_ps']:5.0f}")
    if near:
        for nm, f in (("prjx slow_max", lambda r: s_sm * r["prjx_period_ps"][3]),
                      ("current SDF", lambda r: s_c * r["sdf_period_ps"]),
                      ("prepatch SDF", lambda r: sil_med * r["sdf_prepatch_period_ps"])):
            v = [f(r) for r in near]
            print(f"  {nm:14s} predicted ring-0 period: median {st.median(v):5.0f} range {min(v):5.0f}..{max(v):5.0f}"
                  f"  -> measured 6293 / median = {6293 / st.median(v):.3f}")
    print(f"  scales: s(prjx slow_max) = {s_sm:.3f}, s(current SDF) = {s_c:.3f}, s(prepatch SDF) = {sil_med}")


if __name__ == "__main__" and "--extra" in sys.argv:
    a = [x for x in sys.argv[1:] if x != "--extra"]
    k = a.index("--")
    extra(a[:k], a[k + 1:])
