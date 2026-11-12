#!/usr/bin/env python3
"""table2.py -- KapRes2 summary from runs/<seed>/summary.json (kapres2.py) -> table2.txt.

Per seed and kappa: the leaf cover, the structural residual union (should be empty with xevents7),
every timing item left on some leaf cell (min margin over cells), and every item that fails at a
POINT corner (the corners and margins): those survive refinement at that kappa.
"""
import json
import os
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
SHORT = lambda k: k.replace("urig.udut.", "").replace(".many.stage", " s").replace(".u.ctl.u.u", "")


def main():
    out = []
    for seed in ("d", "3", "4", "5"):
        p = os.path.join(HERE, "runs", seed, "summary.json")
        if not os.path.exists(p):
            out.append("seed %s: no summary" % seed)
            continue
        S = json.load(open(p))
        out.append("=== seed %s (init %d cells, min width 1/%d)" % (seed, S["init"], S["init"] * 2 ** S["depth"]))
        for kappa, K in S["kappas"].items():
            cov = K["cover"]
            # contiguity of the cover
            cs = sorted((Q(c["ca"]), Q(c["cb"])) for c in cov)
            ok = cs[0][0] == 0 and cs[-1][1] == 1 and all(a[1] == b[0] for a, b in zip(cs, cs[1:]))
            nrun = sum(1 for c in cov if c["by"].startswith("k%s_" % kappa))
            dirty = [c for c in cov if c["timing"]]
            out.append("kappa %-6s cover %d cells (%s; %d run at this kappa, %d implied by a wider clean run), "
                       "structural union %s, cells with timing items %d"
                       % (kappa, len(cov), "contiguous [0,1]" if ok else "NOT CONTIGUOUS", nrun, len(cov) - nrun,
                          K["struct_union"] or "none", len(dirty)))
            if not K["items"]:
                out.append("    DISCHARGED on all of c in [0,1]: no residual item on any cell")
            for item, v in sorted(K["items"].items(), key=lambda kv: min(x[2] for x in kv[1])):
                pts = K["point_fail"].get(item, [])
                out.append("    item %-70s on %d cells, min margin %d; %s" % (
                    SHORT(item), len(v), min(x[2] for x in v),
                    ("FAILS at point corners " + ", ".join("c=%s (%d)" % (c, m) for c, m in sorted(pts, key=lambda x: Q(x[0]))))
                    if pts else "passes at every end corner run (cell-width artefact)"))
        out.append("")
    txt = "\n".join(out) + "\n"
    open(os.path.join(HERE, "table2.txt"), "w").write(txt)
    print(txt)


if __name__ == "__main__":
    main()
