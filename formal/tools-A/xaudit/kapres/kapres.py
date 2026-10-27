#!/usr/bin/env python3
"""kapres.py -- corner-model sweep of xevents5 (A-events6's checker) over shared-corner cells.

    python3 kapres.py SEED KAPPA [--init N] [--depth D] [--jobs J]

For one seed and one scatter kappa, covers the corner interval [0,1] by cells [ca,cb]
(start: N equal cells; a cell whose run has a TIMING residual item -- "margin m" -- is
bisected, down to width 1/(N*2^D)).  Each cell run is
    cornerband.py (fast, slow, ca, cb, kappa) -> events4/skel.py -> events6/cert6.py (untrusted)
    -> xe5.sh (xevents5 = committed Events5Main.lean, lean --run, through slot.sh)
At every leaf cell that still has timing items, the two point corners [ca,ca], [cb,cb] are
also run (a point run that fails shows the item fails AT that corner, not only on the cell).
Output: runs/<seed>/k<kappa>_<ca>_<cb>.txt (xevents5 stdout) and a JSON summary
runs/<seed>/sum_k<kappa>.json: cover (list of leaf cells and their items) and point runs.
Inputs: /tmp/kapres/in/<seed>/{net,fast.bands,slow.bands}.json (see run.sh).
"""
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
IN = "/tmp/kapres/in"
WORK = "/tmp/kapres/work"
RES = re.compile(r"^\s+RESIDUAL (Back|Line|Excl) (.*?): (margin (-?\d+).*|no certificate.*)$")


def fs(q):
    return "%d-%d" % (q.numerator, q.denominator) if q.denominator != 1 else str(q.numerator)


def run_cell(seed, kappa, ca, cb):
    tag = "k%s_%s_%s" % (kappa, fs(ca), fs(cb))
    outd = os.path.join(HERE, "runs", seed)
    os.makedirs(outd, exist_ok=True)
    out = os.path.join(outd, tag + ".txt")
    if not (os.path.exists(out) and "VERDICT" in open(out).read()):
        w = os.path.join(WORK, seed, tag)
        os.makedirs(w, exist_ok=True)
        env = dict(os.environ, PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1")
        py = lambda *a, **kw: subprocess.run(["python3"] + list(a), check=True, env=env, **kw)
        py(os.path.join(HERE, "cornerband.py"), "%s/%s/fast.bands.json" % (IN, seed),
           "%s/%s/slow.bands.json" % (IN, seed), str(ca), str(cb), kappa, w + "/bands.json")
        py(os.path.join(HERE, "..", "events4", "skel.py"), "%s/%s/net.json" % (IN, seed), w + "/bands.json",
           w + "/skel.json", w + "/skel_bands.json", stdout=subprocess.DEVNULL)
        with open(w + "/cert.txt", "w") as f:
            py(os.path.join(HERE, "..", "events6", "cert6.py"), w + "/skel.json", w + "/skel_bands.json",
               w + "/cert.json", stdout=f, stderr=subprocess.STDOUT)
        with open(out + ".part", "w") as f:
            subprocess.run([os.path.join(HERE, "xe5.sh"), w + "/skel.json", w + "/skel_bands.json",
                            w + "/cert.json"], stdout=f, stderr=subprocess.STDOUT)
        os.replace(out + ".part", out)
        for fn in ("bands.json", "skel_bands.json", "cert.json"):
            try:
                os.remove(os.path.join(w, fn))
            except OSError:
                pass
    return parse(out)


def parse(path):
    timing, struct, verdict, head = {}, [], None, []
    for ln in open(path):
        m = RES.match(ln)
        if m:
            key = "%s %s" % (m.group(1), m.group(2))
            if m.group(4) is not None:
                timing[key] = int(m.group(4))
            else:
                struct.append(key)
        elif ln.startswith("VERDICT"):
            verdict = ln.strip()
        elif ln.startswith("[xevents5]"):
            head.append(ln.strip())
    return {"timing": timing, "struct": struct, "verdict": verdict, "head": head}


def main():
    seed, kappa = sys.argv[1], sys.argv[2]
    args = sys.argv[3:]
    opt = lambda k, d: int(args[args.index(k) + 1]) if k in args else d
    N, D, J = opt("--init", 8), opt("--depth", 2), opt("--jobs", 2)
    minw = Q(1, N * 2 ** D)
    todo = [(Q(i, N), Q(i + 1, N)) for i in range(N)]
    leaves, points = [], {}
    with cf.ThreadPoolExecutor(J) as ex:
        while todo:
            res = list(ex.map(lambda c: (c, run_cell(seed, kappa, *c)), todo))
            todo = []
            for (ca, cb), r in res:
                if r["verdict"] is None:
                    sys.exit("no verdict for %s %s %s-%s" % (seed, kappa, ca, cb))
                if r["timing"] and cb - ca > minw:
                    mid = (ca + cb) / 2
                    todo += [(ca, mid), (mid, cb)]
                else:
                    leaves.append(((ca, cb), r))
        pts = sorted({c for (ca, cb), r in leaves if r["timing"] for c in (ca, cb)})
        for c, r in ex.map(lambda c: (c, run_cell(seed, kappa, c, c)), pts):
            points[c] = r
    leaves.sort()
    summ = {"seed": seed, "kappa": kappa, "init": N, "depth": D,
            "cover": [{"ca": str(ca), "cb": str(cb), "timing": r["timing"], "struct": r["struct"],
                       "verdict": r["verdict"]} for (ca, cb), r in leaves],
            "points": [{"c": str(c), "timing": r["timing"], "struct": r["struct"]} for c, r in sorted(points.items())]}
    json.dump(summ, open(os.path.join(HERE, "runs", seed, "sum_k%s.json" % kappa), "w"), indent=1)
    bad = {}
    for (ca, cb), r in leaves:
        for k, m in r["timing"].items():
            bad.setdefault(k, []).append((str(ca), str(cb), m))
    print("%s kappa %s: %d leaf cells, %d with timing items; items: %s" % (
        seed, kappa, len(leaves), sum(1 for _, r in leaves if r["timing"]),
        {k: min(x[2] for x in v) for k, v in bad.items()}))


if __name__ == "__main__":
    main()
