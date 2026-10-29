#!/usr/bin/env python3
"""table2.py -- KapRes2 summary from runs<TAG>/<seed>/summary.json (kapres2.py) -> table2<TAG>.txt.

Per seed: per kappa the leaf cover (checked contiguous from 0 to 1, CornerCell.Chain), the
structural residual union (expected empty with xevents8), and per residual item the largest kappa
at which it is discharged on the whole cover (kappas descending; containment), plus the point
corners where it fails at each kappa (those survive any refinement at that kappa).
    python3 table2.py [TAG]
"""
import json
import os
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
SHORT = lambda k: k.replace("urig.udut.", "").replace(".many.stage", " s").replace(".u.ctl.u.u", "").replace(".u pin", " pin")


def main():
    tag = sys.argv[1] if len(sys.argv) > 1 else ""
    out = []
    for seed in ("d", "3", "4", "5"):
        p = os.path.join(HERE, "runs" + tag, seed, "summary.json")
        if not os.path.exists(p):
            out.append("seed %s: no summary" % seed)
            continue
        S = json.load(open(p))
        ks = list(S["kappas"])          # descending, as swept
        out.append("=== seed %s (checker %s; init %d cells, finest 1/%d)" % (
            seed, S.get("checker", "?"), S["init"], S["init"] * 2 ** S["depth"]))
        allitems = set()
        for kappa in ks:
            K = S["kappas"][kappa]
            cov = K["cover"]
            cs = sorted((Q(c["ca"]), Q(c["cb"])) for c in cov)
            ok = cs[0][0] == 0 and cs[-1][1] == 1 and all(a[1] == b[0] for a, b in zip(cs, cs[1:]))
            nrun = sum(1 for c in cov if c["by"].startswith("k%s_" % kappa))
            out.append("kappa %-5s cover %2d cells (%s; %d run at this kappa, %d implied by a clean run at a "
                       "larger kappa), structural residual items: %s; cells with timing items %d%s" % (
                           kappa, len(cov), "contiguous [0,1]" if ok else "NOT CONTIGUOUS", nrun, len(cov) - nrun,
                           K["struct_union"] or "none", sum(1 for c in cov if c["timing"]),
                           "  => CLEAN on all of c in [0,1]" if not K["items"] and not K["struct_union"] else ""))
            allitems |= set(K["items"]) | set(K["struct_union"])
        for item in sorted(allitems):
            best = None
            for kappa in ks:
                K = S["kappas"][kappa]
                if item not in K["items"] and item not in K["struct_union"]:
                    best = kappa
                    break
            fails = []
            for kappa in ks:
                K = S["kappas"][kappa]
                if item in K["items"]:
                    pts = K["point_fail"].get(item, [])
                    mm = min(x[2] for x in K["items"][item])
                    if pts:
                        fails.append("k%s: cells min %d, FAILS at point corners %s" % (
                            kappa, mm, " ".join("c=%s(%d)" % (c, m) for c, m in sorted(pts, key=lambda x: Q(x[0])))))
                    else:
                        fails.append("k%s: cells min %d, passes at every end corner run" % (kappa, mm))
            out.append("  %-62s largest kappa discharged on [0,1]: %-5s | %s" % (
                SHORT(item)[:62], best if best is not None else "NONE", "; ".join(fails)))
        out.append("")
    txt = "\n".join(out) + "\n"
    open(os.path.join(HERE, "table2%s.txt" % tag), "w").write(txt)
    print(txt)


if __name__ == "__main__":
    main()
