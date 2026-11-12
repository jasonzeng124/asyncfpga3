#!/usr/bin/env python3
"""table.py -- per seed, per residual item of A-events6's indep (and gb) runs: the largest kappa in
KAPPAS for which xevents5 discharges it on a cover of the whole corner interval [0,1]; plus any
item that is residual anywhere in a cover, and the point corners where it fails.
Reads runs/<seed>/summary.json (kapres.py) and ../events6/xe5_<seed>_{indep,gb}.txt."""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from kapres import KAPPAS, parse  # noqa: E402


def main():
    for s in sys.argv[1:] or ["d", "3", "4", "5"]:
        sp = os.path.join(HERE, "runs", s, "summary.json")
        if not os.path.exists(sp):
            print("seed %s: no summary" % s)
            continue
        S = json.load(open(sp))
        base = set(parse(os.path.join(HERE, "..", "events6", "xe5_%s_slow.txt" % s))["struct"])
        ind = parse(os.path.join(HERE, "..", "events6", "xe5_%s_indep.txt" % s))
        gb = parse(os.path.join(HERE, "..", "events6", "xe5_%s_gb.txt" % s))
        items = dict(ind["timing"])
        for k, m in gb["timing"].items():
            items.setdefault(k, None)
        extra = set()
        for kp in S["kappas"].values():
            extra |= set(kp["items"])
            extra |= set(kp["struct_union"]) - base
        print("seed %s (cells: init 1/%d, finest 1/%d)" % (s, S["init"], S["init"] * 2 ** S["depth"]))
        for k in sorted(set(items) | extra):
            best = None
            for kappa in KAPPAS:          # descending
                kp = S["kappas"].get(kappa)
                if kp is None:
                    continue
                if k not in kp["items"] and k not in kp["struct_union"]:
                    best = kappa
                    break
            pts = {kappa: S["kappas"][kappa]["point_fail"].get(k) for kappa in S["kappas"]}
            pts = {a: b for a, b in pts.items() if b}
            print("  %-95s indep %5s gb %5s | largest kappa discharged: %s | fails at point corners: %s" % (
                k[:95], ind["timing"].get(k, "ok" if k not in ind["struct"] else "nocert"),
                gb["timing"].get(k, "ok"), best if best is not None else "NONE (not even 0)",
                {a: [(c, m) for c, m in b] for a, b in pts.items()} or "-"))
        cov = {kappa: (len(kp["cover"]), sum(1 for c in kp["cover"] if c["timing"]))
               for kappa, kp in S["kappas"].items()}
        print("  cover per kappa (leaf cells, with timing items):", cov)
        newstruct = {kappa: sorted(set(kp["struct_union"]) - base) for kappa, kp in S["kappas"].items()}
        print("  structural items beyond the slow-corner 45:", {a: b for a, b in newstruct.items() if b} or "none")


if __name__ == "__main__":
    main()
